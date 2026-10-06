theory Reverse_Threshold_Cocycle
  imports Reverse_Factored_Channels
begin

text \<open>The Boolean coordinate is decimal parity.  The only nonlinear
piece left by the F5/parity sum is the ordinary decimal carry cocycle.  These
are scalar digit laws, not recursive spatial or 196-closure theorems.\<close>

text \<open>Native domain/F5/parity transducer. Carries are derived from the
one forward domain fold. A growth appends the CRT encoding of digit one before
reflection. These word semantics specify the rope gates; their proof does not
assert a bound on newly constructed rope nodes.\<close>

fun native_emit :: "bool \<Rightarrow> native_cocycle list \<Rightarrow> (nat * nat) list" where
  "native_emit c [] = []"
| "native_emit c ((g,a,e)#xs) =
    ((a + (if c then 1 else 0)) mod 5,
     (e + (if c then 1 else 0)) mod 2) # native_emit (carry_apply g c) xs"

lemma native_emit_refines:
  "native_emit c (map encode_cocycle ss) = map digit_channels (emit c ss)"
  by (induction ss arbitrary: c)
    (simp_all add: encode_cocycle_def digit_channels_def
      mod_mod_cancel mod_add_left_eq)

definition native_growth :: "native_cocycle list \<Rightarrow> bool" where
  "native_growth xs = fold (\<lambda>(g,a,e) c. carry_apply g c) xs False"

lemma native_growth_refines:
  "native_growth (map encode_cocycle ss) = carry_out False ss"
  by (simp add: native_growth_def carry_out_def encode_cocycle_def fold_map comp_def)

definition native_digits :: "native_cocycle list \<Rightarrow> (nat * nat) list" where
  "native_digits xs = native_emit False xs @ (if native_growth xs then [(1,1)] else [])"

lemma native_digits_refines:
  "native_digits (map encode_cocycle ss) = map digit_channels (digits ss)"
  by (simp add: native_digits_def digits_def native_emit_refines
      native_growth_refines digit_channels_def)

definition native_add :: "(nat * nat) \<Rightarrow> (nat * nat) \<Rightarrow> native_cocycle" where
  "native_add x y =
    (cocycle_output_domain (crt_digit (fst x) (snd x)) (crt_digit (fst y) (snd y)),
     (fst x + fst y) mod 5, (snd x + snd y) mod 2)"

lemma native_add_refines:
  assumes "x < 10" "y < 10"
  shows "native_add (digit_channels x) (digit_channels y) = encode_cocycle (x+y)"
  using crt_digit_inverse[OF assms(1)] crt_digit_inverse[OF assms(2)]
    kappa_and_eq_domain_exact(2)[OF assms]
  by (simp add: native_add_def digit_channels_def encode_cocycle_def mod_add_eq)

definition native_step :: "native_cocycle list \<Rightarrow> native_cocycle list" where
  "native_step xs = map (\<lambda>(a,b). native_add a b)
    (zip (native_digits xs) (rev (native_digits xs)))"

theorem native_step_refines:
  "native_step (map encode_cocycle ss) = map encode_cocycle (step ss)"
proof -
  have add: "native_add (digit_channels a) (digit_channels b) = encode_cocycle (a+b)"
    if "(a,b) \<in> set (zip (digits ss) (rev (digits ss)))" for a b
    using that digits_bounded set_zip_leftD set_zip_rightD
    by (intro native_add_refines) fastforce+
  show ?thesis
    unfolding native_step_def step_def native_digits_refines rev_map zip_map_map map_map
    by (rule map_cong; auto simp: comp_def split: prod.splits; metis add)
qed

fun native_macro :: "nat \<Rightarrow> native_cocycle list \<Rightarrow> native_cocycle list" where
  "native_macro 0 xs = (native_step ^^ 4) xs"
| "native_macro (Suc level) xs = native_macro level (native_macro level xs)"

lemma native_iteration_refines:
  "(native_step ^^ n) (map encode_cocycle ss) = map encode_cocycle ((step ^^ n) ss)"
  by (induction n arbitrary: ss)
    (simp_all del: funpow.simps(2) add: funpow_Suc_right native_step_refines)

lemma native_terminal_emission_refines:
  "native_digits ((native_step ^^ n) (map encode_cocycle ss)) =
    map digit_channels (digits ((step ^^ n) ss))"
  by (simp add: native_iteration_refines native_digits_refines)

theorem native_macro_refines:
  "native_macro level (map encode_cocycle ss) =
    map encode_cocycle ((step ^^ (4*2^level)) ss)"
proof (induction level arbitrary: ss)
  case 0
  show ?case by (simp add: native_iteration_refines)
next
  case (Suc level)
  have double: "(4::nat)*2^(Suc level) = 4*2^level + 4*2^level"
    by (simp add: power_Suc algebra_simps)
  show ?case
    by (simp only: native_macro.simps Suc.IH double funpow_add comp_apply)
qed

lemma native_emit_length:
  "length (native_emit c xs) = length xs"
proof (induction xs arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain g a e where x: "x = (g,a,e)" by (cases x) auto
  have ih: "length (native_emit (carry_apply g c) xs) = length xs"
    using Cons.IH[of "carry_apply g c"] .
  show ?case using x ih by simp
qed

lemma native_digits_length:
  "length (native_digits xs) = length xs +
    (if native_growth xs then 1 else 0)"
  unfolding native_digits_def
  by (simp add: native_emit_length)

lemma native_step_length:
  "length (native_step xs) = length xs +
    (if native_growth xs then 1 else 0)"
  unfolding native_step_def
  by (simp add: native_digits_length)

text \<open>The growth count is the chronological sum of producer growth flags
along the actual native successor states. It is not defined as an endpoint
length difference. The terminal digit word is a separate projection: after
n pair steps, it may include the next producer's final carry bit.\<close>

fun native_growth_count :: "nat \<Rightarrow> native_cocycle list \<Rightarrow> nat" where
  "native_growth_count 0 xs = 0"
| "native_growth_count (Suc n) xs =
    (if native_growth xs then 1 else 0) +
      native_growth_count n (native_step xs)"

lemma native_growth_count_add:
  "native_growth_count (m + n) xs =
    native_growth_count m xs +
      native_growth_count n ((native_step ^^ m) xs)"
proof (induction m arbitrary: n xs)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
    using Suc.IH[of n "native_step xs"]
    by (simp del: funpow.simps(2)
        add: funpow_Suc_right add.assoc)
qed

lemma native_iteration_length:
  "length ((native_step ^^ n) xs) =
    length xs + native_growth_count n xs"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    using Suc.IH[of "native_step xs"] native_step_length[of xs]
    by (simp del: funpow.simps(2)
        add: funpow_Suc_right native_growth_count.simps add.assoc)
qed

theorem native_source_growth_count_add:
  "native_growth_count (m + n) (map encode_cocycle ss) =
    native_growth_count m (map encode_cocycle ss) +
      native_growth_count n (map encode_cocycle ((step ^^ m) ss))"
  using native_growth_count_add[of m n "map encode_cocycle ss"]
    native_iteration_refines[of m ss]
  by simp

theorem native_source_width:
  "length ((step ^^ n) ss) =
    length ss + native_growth_count n (map encode_cocycle ss)"
  using native_iteration_length[of n "map encode_cocycle ss"]
    native_iteration_refines[of n ss]
  by simp

theorem native_terminal_output_length:
  "length (native_digits ((native_step ^^ n) (map encode_cocycle ss))) =
    length ((step ^^ n) ss) +
      (if carry_out False ((step ^^ n) ss) then 1 else 0)"
  using native_digits_length[of "(native_step ^^ n) (map encode_cocycle ss)"]
    native_iteration_refines[of n ss]
    native_growth_refines[of "(step ^^ n) ss"]
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms crt_digit_coordinates_exact crt_digit_inverse
      parity_addition_coordinates parity_normalization_exact
      decimal_sum_digit_mod kappa_and_eq_domain_exact
      output_crt_threshold_exact normalized_output_crt_threshold_exact
      decimal_kappa_cocycle native_emit_refines native_growth_refines
      native_emit_length native_digits_length native_step_length
      native_growth_count_add native_iteration_length
      native_source_growth_count_add native_source_width
      native_terminal_output_length
      native_digits_refines native_add_refines native_step_refines
      native_iteration_refines native_terminal_emission_refines native_macro_refines}) then ()
    else error "Threshold cocycle proof depends on an oracle";
\<close>

end
