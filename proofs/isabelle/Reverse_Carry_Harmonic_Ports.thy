theory Reverse_Carry_Harmonic_Ports
  imports Reverse_Residuals
begin

text \<open>Port-conditioned carry harmonics for the alternating 2,3 radix over
F5.  This is a spatial emitting carry action.  The theory proves its exact
composition and the first-decisive-domain coalescence law.  It does not assert
that the action is closed under a temporal reverse-and-add successor.\<close>

datatype harmonic_channel = Radix2 | Radix3

fun harmonic_weight :: "harmonic_channel \<Rightarrow> bool \<Rightarrow> nat" where
  "harmonic_weight Radix2 False = 1"
| "harmonic_weight Radix2 True = 2"
| "harmonic_weight Radix3 False = 1"
| "harmonic_weight Radix3 True = 3"

lemma harmonic_weight_mod_five [simp]:
  "harmonic_weight k p mod 5 = harmonic_weight k p"
  by (cases k; cases p) simp_all

fun carry_finish :: "bool \<Rightarrow> carry_domain list \<Rightarrow> bool" where
  "carry_finish c [] = c"
| "carry_finish c (d # ds) = carry_finish (carry_apply d c) ds"

fun advance_phase :: "bool \<Rightarrow> carry_domain list \<Rightarrow> bool" where
  "advance_phase p [] = p"
| "advance_phase p (_ # ds) = advance_phase (\<not> p) ds"

fun harmonic_emit ::
    "harmonic_channel \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
      carry_domain list \<Rightarrow> nat" where
  "harmonic_emit k p c [] = 0"
| "harmonic_emit k p c (d # ds) =
    ((if c then harmonic_weight k p else 0) +
      harmonic_emit k (\<not> p) (carry_apply d c) ds) mod 5"

definition port_action ::
    "bool \<Rightarrow> carry_domain list \<Rightarrow> bool \<Rightarrow> bool \<times> nat \<times> nat" where
  "port_action p ds c =
    (carry_finish c ds, harmonic_emit Radix2 p c ds,
      harmonic_emit Radix3 p c ds)"

lemma harmonic_emit_less_five:
  "harmonic_emit k p c ds < 5"
  by (cases ds) simp_all

lemma harmonic_emit_mod_five [simp]:
  "harmonic_emit k p c ds mod 5 = harmonic_emit k p c ds"
  using harmonic_emit_less_five by simp

lemma carry_finish_fold:
  "carry_finish c ds = fold carry_apply ds c"
  by (induction ds arbitrary: c) simp_all

lemma carry_finish_append [simp]:
  "carry_finish c (xs @ ys) = carry_finish (carry_finish c xs) ys"
  by (simp only: carry_finish_fold fold_append comp_apply)

lemma advance_phase_append [simp]:
  "advance_phase p (xs @ ys) = advance_phase (advance_phase p xs) ys"
  by (induction xs arbitrary: p) simp_all

lemma advance_phase_by_length:
  "advance_phase p xs = (if even (length xs) then p else \<not> p)"
  by (induction xs arbitrary: p) simp_all

theorem harmonic_emit_append:
  "harmonic_emit k p c (xs @ ys) =
    (harmonic_emit k p c xs +
      harmonic_emit k (advance_phase p xs) (carry_finish c xs) ys) mod 5"
  by (induction xs arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)

theorem port_action_spatial_composition:
  "port_action p (xs @ ys) c =
    (carry_finish (carry_finish c xs) ys,
      (harmonic_emit Radix2 p c xs +
        harmonic_emit Radix2 (advance_phase p xs)
          (carry_finish c xs) ys) mod 5,
      (harmonic_emit Radix3 p c xs +
        harmonic_emit Radix3 (advance_phase p xs)
          (carry_finish c xs) ys) mod 5)"
  by (simp add: port_action_def harmonic_emit_append)

fun prefix_harmonic :: "harmonic_channel \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat" where
  "prefix_harmonic k p 0 = 0"
| "prefix_harmonic k p (Suc n) =
    (harmonic_weight k p + prefix_harmonic k (\<not> p) n) mod 5"

lemma prefix_harmonic_ten_period:
  "prefix_harmonic k p (n + 10) = prefix_harmonic k p n"
proof (induction n arbitrary: p)
  case 0
  have ten: "(10 :: nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))"
    by simp
  then show ?case
    by (cases k; cases p;
        simp only: prefix_harmonic.simps harmonic_weight.simps ten;
        simp)
next
  case (Suc n)
  have length_step: "Suc n + 10 = Suc (n + 10)" by simp
  show ?case
    using Suc.IH[of "\<not> p"]
    by (simp only: length_step prefix_harmonic.simps)
qed

lemma prefix_harmonic_add_tens:
  "prefix_harmonic k p (n + 10 * q) = prefix_harmonic k p n"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have arithmetic: "n + 10 * Suc q = (n + 10 * q) + 10" by simp
  show ?case
  proof (subst arithmetic)
    show "prefix_harmonic k p (n + 10 * q + 10) =
        prefix_harmonic k p n"
      using Suc.IH prefix_harmonic_ten_period by metis
  qed
qed

lemma carry_finish_equal_prefix [simp]:
  "carry_finish c (replicate n Equal @ ds) = carry_finish c ds"
  by (induction n arbitrary: c) simp_all

theorem first_decisive_carry_coalesces:
  assumes "d \<noteq> Equal"
  shows "carry_finish False (replicate j Equal @ d # ds) =
    carry_finish True (replicate j Equal @ d # ds)"
  using assms by (cases d) simp_all

theorem first_decisive_harmonic_difference:
  assumes "d \<noteq> Equal"
  shows "harmonic_emit k p True (replicate j Equal @ d # ds) =
    (prefix_harmonic k p (Suc j) +
      harmonic_emit k p False (replicate j Equal @ d # ds)) mod 5"
  using assms
proof (induction j arbitrary: p)
  case 0
  then show ?case
    by (cases d;
        simp add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)
next
  case (Suc j)
  then show ?case
    by (simp add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)
qed

text \<open>The two incoming-carry trajectories differ exactly on the incoming
positions zero through j, hence on a prefix of length j+1.  The preceding two
lemmas show why only j modulo ten is visible to these emissions.\<close>

fun even_population :: "bool \<Rightarrow> bool \<Rightarrow> carry_domain list \<Rightarrow> nat" where
  "even_population p c [] = 0"
| "even_population p c (d # ds) =
    (if \<not> p \<and> c then 1 else 0) +
      even_population (\<not> p) (carry_apply d c) ds"

fun odd_population :: "bool \<Rightarrow> bool \<Rightarrow> carry_domain list \<Rightarrow> nat" where
  "odd_population p c [] = 0"
| "odd_population p c (d # ds) =
    (if p \<and> c then 1 else 0) +
      odd_population (\<not> p) (carry_apply d c) ds"

theorem radix2_population:
  "harmonic_emit Radix2 p c ds =
    (even_population p c ds + 2 * odd_population p c ds) mod 5"
  by (induction ds arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq
      add.assoc algebra_simps)

theorem radix3_population:
  "harmonic_emit Radix3 p c ds =
    (even_population p c ds + 3 * odd_population p c ds) mod 5"
  by (induction ds arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq
      add.assoc algebra_simps)

lemma even_odd_linear_inversion:
  fixes ev od :: int
  shows "((ev + 3 * od) - (ev + 2 * od)) mod 5 = od mod 5"
    and "(3 * (ev + 2 * od) - 2 * (ev + 3 * od)) mod 5 = ev mod 5"
  by simp_all

text \<open>The following cardinalities concern length-indexed reduced-code
spaces.  At one fixed length, the unique all-Equal word contributes one code.
It must not be identified with all-Equal words at other lengths because its
incoming-one emissions depend on the length modulo ten.\<close>

definition nonidentity_occupancy_codes ::
    "(bool \<times> nat \<times> nat \<times> nat) set" where
  "nonidentity_occupancy_codes = UNIV \<times> {0..<10} \<times> {0..<5} \<times> {0..<5}"

definition fixed_length_occupancy_codes ::
    "(bool \<times> nat \<times> nat \<times> nat) option set" where
  "fixed_length_occupancy_codes =
    insert None (Some ` nonidentity_occupancy_codes)"

theorem occupancy_code_capacity:
  "card nonidentity_occupancy_codes = 500"
  "card fixed_length_occupancy_codes = 501"
  by (simp_all add: nonidentity_occupancy_codes_def
      fixed_length_occupancy_codes_def card_image)

definition nonidentity_border_codes :: "(bool \<times> bool \<times> nat) set" where
  "nonidentity_border_codes = UNIV \<times> UNIV \<times> {0..<5}"

definition fixed_length_border_codes :: "(bool \<times> bool \<times> nat) option set" where
  "fixed_length_border_codes = insert None (Some ` nonidentity_border_codes)"

theorem border_code_capacity:
  "card nonidentity_border_codes = 20"
  "card fixed_length_border_codes = 21"
  by (simp_all add: nonidentity_border_codes_def fixed_length_border_codes_def
      card_image)

lemma all_equal_carry [simp]:
  "carry_finish c (replicate n Equal) = c"
  by (induction n arbitrary: c) simp_all

lemma all_equal_false_emission [simp]:
  "harmonic_emit k p False (replicate n Equal) = 0"
  by (induction n arbitrary: p) simp_all

lemma all_equal_true_emission:
  "harmonic_emit k p True (replicate n Equal) = prefix_harmonic k p n"
  by (induction n arbitrary: p) simp_all

theorem all_equal_actions_are_length_indexed:
  "port_action False [] True \<noteq> port_action False [Equal] True"
  by (simp add: port_action_def)

theorem all_equal_action_ten_period:
  "port_action p (replicate (n + 10) Equal) c =
    port_action p (replicate n Equal) c"
  by (cases c; simp add: port_action_def all_equal_true_emission
      prefix_harmonic_ten_period)

ML \<open>
  val checked = @{thms carry_finish_fold carry_finish_append
    harmonic_emit_append port_action_spatial_composition
    prefix_harmonic_ten_period first_decisive_carry_coalesces
    first_decisive_harmonic_difference radix2_population radix3_population
    even_odd_linear_inversion occupancy_code_capacity border_code_capacity
    all_equal_actions_are_length_indexed all_equal_action_ten_period};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Carry harmonic port proof depends on an oracle";
\<close>

end
