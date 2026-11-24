theory Mahler_CF_Fractional_Guard_Compiler
  imports Mahler_CF_Ordered_Row_Blocks "HOL-Number_Theory.Modular_Inverse"
begin

text \<open>Only the three physically issued batch forms are admitted. Their
word, affine multiplier, correction and physical duration are kept together.\<close>

datatype mahler_cf_guard_batch = Zero_Run nat | Odd_Single | Odd_Then_Zero

fun mahler_cf_batch_word :: "mahler_cf_guard_batch \<Rightarrow> nat list" where
  "mahler_cf_batch_word (Zero_Run q) = replicate q 0"
| "mahler_cf_batch_word Odd_Single = [1]"
| "mahler_cf_batch_word Odd_Then_Zero = [1,0]"

fun mahler_cf_batch_gain :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_gain (Zero_Run q) = 3^q"
| "mahler_cf_batch_gain Odd_Single = 3"
| "mahler_cf_batch_gain Odd_Then_Zero = 9"

fun mahler_cf_batch_modulus :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_modulus (Zero_Run q) = 2^q"
| "mahler_cf_batch_modulus Odd_Single = 2"
| "mahler_cf_batch_modulus Odd_Then_Zero = 4"

fun mahler_cf_batch_correction :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_correction (Zero_Run q) = 0"
| "mahler_cf_batch_correction Odd_Single = 1"
| "mahler_cf_batch_correction Odd_Then_Zero = 3"

lemma mahler_cf_batch_positive:
  "0 < mahler_cf_batch_gain batch" "0 < mahler_cf_batch_modulus batch"
  by (cases batch; simp_all)+

lemma mahler_cf_batch_apply:
  "mahler_cf_physical_apply (mahler_cf_batch_word batch) x =
    mahler_cf_lean_fraction (mahler_cf_batch_gain batch)
      (mahler_cf_batch_modulus batch) (mahler_cf_batch_correction batch) x"
  by (cases batch) (simp_all add: mahler_cf_apply_zero_row mahler_cf_lean_fraction_def
      power_divide field_simps algebra_simps)

lemma mahler_cf_batch_safe:
  assumes inlet: "mahler_cf_safe_fraction x"
    and terminal: "mahler_cf_safe_fraction (mahler_cf_physical_apply (mahler_cf_batch_word batch) x)"
  shows "mahler_cf_physical_safe (mahler_cf_batch_word batch) x"
proof (cases batch)
  case (Zero_Run q)
  then show ?thesis using inlet terminal
    by (simp only: mahler_cf_batch_word.simps mahler_cf_safe_zero_row mahler_cf_apply_zero_row)
next
  case Odd_Single
  then show ?thesis using inlet terminal
    by (simp add: mahler_cf_safe_fraction_def)
next
  case Odd_Then_Zero
  then show ?thesis using inlet terminal
    by (simp only: mahler_cf_batch_word.simps mahler_cf_safe_odd_even_batch
        mahler_cf_physical_apply.simps of_nat_0 of_nat_1; simp add: field_simps)
qed

record mahler_cf_compiled_guard =
  cf_gain :: real
  cf_modulus :: real
  cf_innovation :: real
  cf_lower :: real
  cf_upper :: real
  cf_word :: "nat list"
  cf_ticks :: nat

definition mahler_cf_guard_initial :: mahler_cf_compiled_guard where
  "mahler_cf_guard_initial = \<lparr>cf_gain=1, cf_modulus=1, cf_innovation=0,
    cf_lower=0, cf_upper=1/2, cf_word=[], cf_ticks=0\<rparr>"

definition mahler_cf_guard_step ::
  "mahler_cf_compiled_guard \<Rightarrow> mahler_cf_guard_batch \<Rightarrow> mahler_cf_compiled_guard" where
  "mahler_cf_guard_step st batch =
    (let a = mahler_cf_batch_gain batch; m = mahler_cf_batch_modulus batch;
         b = mahler_cf_batch_correction batch;
         g = a * cf_gain st; z = m * cf_modulus st;
         j = a * cf_innovation st + cf_modulus st * b
     in \<lparr>cf_gain=g, cf_modulus=z, cf_innovation=j,
        cf_lower=max (cf_lower st) (j/g),
        cf_upper=min (cf_upper st) ((2*j+z)/(2*g)),
        cf_word=cf_word st @ mahler_cf_batch_word batch,
        cf_ticks=cf_ticks st + length (mahler_cf_batch_word batch)\<rparr>)"

definition mahler_cf_guard_compile :: "mahler_cf_guard_batch list \<Rightarrow> mahler_cf_compiled_guard" where
  "mahler_cf_guard_compile batches = foldl mahler_cf_guard_step mahler_cf_guard_initial batches"

definition mahler_cf_guard_invariant :: "mahler_cf_compiled_guard \<Rightarrow> bool" where
  "mahler_cf_guard_invariant st \<longleftrightarrow>
    0 < cf_gain st \<and> 0 < cf_modulus st \<and>
    cf_ticks st = length (cf_word st) \<and>
    (\<forall>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x) \<and>
    (\<forall>x. cf_lower st \<le> x \<and> x < cf_upper st \<longrightarrow>
      mahler_cf_physical_safe (cf_word st) x)"

lemma mahler_cf_guard_initial_invariant:
  "mahler_cf_guard_invariant mahler_cf_guard_initial"
  by (simp add: mahler_cf_guard_invariant_def mahler_cf_guard_initial_def
      mahler_cf_lean_fraction_def mahler_cf_safe_fraction_def)

lemma mahler_cf_physical_safe_endpoint:
  "mahler_cf_physical_safe word x \<Longrightarrow>
    mahler_cf_safe_fraction (mahler_cf_physical_apply word x)"
  by (induction word arbitrary: x) auto

lemma mahler_cf_guard_step_invariant:
  assumes inv: "mahler_cf_guard_invariant st"
  shows "mahler_cf_guard_invariant (mahler_cf_guard_step st batch)"
proof -
  have gain: "0 < cf_gain st" and modulus: "0 < cf_modulus st"
    and ticks: "cf_ticks st = length (cf_word st)"
    and action: "\<And>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x"
    and prior: "\<And>x. cf_lower st \<le> x \<Longrightarrow> x < cf_upper st \<Longrightarrow>
      mahler_cf_physical_safe (cf_word st) x"
    using inv by (auto simp: mahler_cf_guard_invariant_def)
  have ag: "0 < mahler_cf_batch_gain batch" and am: "0 < mahler_cf_batch_modulus batch"
    by (rule mahler_cf_batch_positive)+
  have new_gain: "0 < cf_gain (mahler_cf_guard_step st batch)"
    using gain ag by (simp add: mahler_cf_guard_step_def Let_def)
  have new_modulus: "0 < cf_modulus (mahler_cf_guard_step st batch)"
    using modulus am by (simp add: mahler_cf_guard_step_def Let_def)
  have new_action: "\<And>x. mahler_cf_physical_apply (cf_word (mahler_cf_guard_step st batch)) x =
      mahler_cf_lean_fraction (cf_gain (mahler_cf_guard_step st batch))
        (cf_modulus (mahler_cf_guard_step st batch)) (cf_innovation (mahler_cf_guard_step st batch)) x"
    using mahler_cf_lean_action_composition[of "cf_modulus st" "mahler_cf_batch_modulus batch"]
      gain modulus ag am
    by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_apply_append
        action mahler_cf_batch_apply mahler_cf_lean_fraction_def field_simps algebra_simps)
  have new_safe: "\<And>x. cf_lower (mahler_cf_guard_step st batch) \<le> x \<Longrightarrow>
      x < cf_upper (mahler_cf_guard_step st batch) \<Longrightarrow>
      mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st batch)) x"
  proof -
    fix x assume lo: "cf_lower (mahler_cf_guard_step st batch) \<le> x"
      and hi: "x < cf_upper (mahler_cf_guard_step st batch)"
    have nested: "cf_lower st \<le> cf_lower (mahler_cf_guard_step st batch)"
      "cf_upper (mahler_cf_guard_step st batch) \<le> cf_upper st"
      by (simp_all add: mahler_cf_guard_step_def Let_def)
    have lower: "cf_innovation (mahler_cf_guard_step st batch) /
        cf_gain (mahler_cf_guard_step st batch) \<le> x"
      using lo by (simp add: mahler_cf_guard_step_def Let_def)
    have upper: "x < (2 * cf_innovation (mahler_cf_guard_step st batch) +
        cf_modulus (mahler_cf_guard_step st batch)) /
        (2 * cf_gain (mahler_cf_guard_step st batch))"
      using hi by (simp add: mahler_cf_guard_step_def Let_def)
    have left: "0 \<le> cf_gain (mahler_cf_guard_step st batch)*x -
        cf_innovation (mahler_cf_guard_step st batch)"
      using lower new_gain by (simp add: divide_le_eq mult.commute; linarith)
    have right: "2 * (cf_gain (mahler_cf_guard_step st batch)*x -
        cf_innovation (mahler_cf_guard_step st batch)) <
        cf_modulus (mahler_cf_guard_step st batch)"
      using upper new_gain by (simp add: less_divide_eq mult.commute; linarith)
    have safe_action: "mahler_cf_safe_fraction (mahler_cf_lean_fraction
        (cf_gain (mahler_cf_guard_step st batch)) (cf_modulus (mahler_cf_guard_step st batch))
        (cf_innovation (mahler_cf_guard_step st batch)) x)"
      using left right new_modulus
      by (simp add: mahler_cf_safe_fraction_def mahler_cf_lean_fraction_def divide_less_eq; linarith)
    have terminal: "mahler_cf_safe_fraction
        (mahler_cf_physical_apply (mahler_cf_batch_word batch) (mahler_cf_physical_apply (cf_word st) x))"
      using safe_action new_action[of x]
      by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_apply_append)
    have prior_x: "mahler_cf_physical_safe (cf_word st) x"
      by (rule prior) (use lo hi nested in auto)
    have prior_end: "mahler_cf_safe_fraction (mahler_cf_physical_apply (cf_word st) x)"
      by (rule mahler_cf_physical_safe_endpoint[OF prior_x])
    have batch_safe: "mahler_cf_physical_safe (mahler_cf_batch_word batch)
        (mahler_cf_physical_apply (cf_word st) x)"
      by (rule mahler_cf_batch_safe[OF prior_end terminal])
    show "mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st batch)) x"
      using prior_x batch_safe
      by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_safe_append)
  qed
  show ?thesis using new_gain new_modulus ticks new_action new_safe
    by (auto simp: mahler_cf_guard_invariant_def mahler_cf_guard_step_def Let_def)
qed

lemma mahler_cf_guard_fold_invariant:
  assumes "mahler_cf_guard_invariant st"
  shows "mahler_cf_guard_invariant (foldl mahler_cf_guard_step st batches)"
  using assms by (induction batches arbitrary: st) (auto intro: mahler_cf_guard_step_invariant)

theorem mahler_cf_guard_compiler_correct:
  "mahler_cf_guard_invariant (mahler_cf_guard_compile batches)"
  unfolding mahler_cf_guard_compile_def
  by (rule mahler_cf_guard_fold_invariant[OF mahler_cf_guard_initial_invariant])


lemma mahler_cf_guard_fold_word:
  "cf_word (foldl mahler_cf_guard_step st batches) =
    cf_word st @ concat (map mahler_cf_batch_word batches)"
  by (induction batches arbitrary: st)
    (simp_all add: mahler_cf_guard_step_def Let_def append_assoc)

lemma mahler_cf_guard_compile_word:
  "cf_word (mahler_cf_guard_compile (pre @ post)) =
    cf_word (mahler_cf_guard_compile pre) @ concat (map mahler_cf_batch_word post)"
  by (simp add: mahler_cf_guard_compile_def foldl_append mahler_cf_guard_fold_word)

theorem mahler_cf_compiled_stall_not_guarded:
  fixes pre post :: "mahler_cf_guard_batch list" and st finished :: mahler_cf_compiled_guard
    and F :: "real \<Rightarrow> real"
  defines "st \<equiv> mahler_cf_guard_compile pre"
    and "finished \<equiv> mahler_cf_guard_compile (pre @ post)"
    and "F \<equiv> (\<lambda>x. (cf_gain st*x - cf_innovation st)/cf_modulus st)"
  assumes prefix: "mahler_cf_prefix digits = (q,r,p,s)"
    and stalled: "\<not> (0 \<le> F (mahler_cf_low q r p s) \<and>
      F (mahler_cf_high q r p s) \<le> 1/2 \<and>
      (F (mahler_cf_high q r p s) \<le> 1/3 \<or>
       1/3 \<le> F (mahler_cf_low q r p s)))"
    and later: "concat (map mahler_cf_batch_word post) \<noteq> []"
  shows "\<not> mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished) digits"
proof -
  have st: "mahler_cf_guard_invariant st" and fin: "mahler_cf_guard_invariant finished"
    by (simp_all add: st_def finished_def mahler_cf_guard_compiler_correct)
  have gain: "0 < cf_gain st" and modulus: "0 < cf_modulus st"
    and action: "\<And>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x"
    using st by (auto simp: mahler_cf_guard_invariant_def)
  have safe: "\<And>x. cf_lower finished \<le> x \<Longrightarrow> x < cf_upper finished \<Longrightarrow>
      mahler_cf_physical_safe (cf_word st @ concat (map mahler_cf_batch_word post)) x"
    using fin by (auto simp: mahler_cf_guard_invariant_def finished_def st_def mahler_cf_guard_compile_word)
  show ?thesis
    using mahler_cf_stalled_prefix_from_safe_continuation[
      where gain="cf_gain st" and modulus="cf_modulus st" and innovation="cf_innovation st"
        and pre="cf_word st" and suffix="concat (map mahler_cf_batch_word post)",
      OF gain modulus prefix] stalled later safe action by (simp add: F_def)
qed

lemma mahler_cf_compiled_later_ticks:
  assumes later: "cf_ticks (mahler_cf_guard_compile pre) <
    cf_ticks (mahler_cf_guard_compile (pre @ post))"
  shows "concat (map mahler_cf_batch_word post) \<noteq> []"
proof
  assume empty: "concat (map mahler_cf_batch_word post) = []"
  have a: "cf_ticks (mahler_cf_guard_compile pre) =
      length (cf_word (mahler_cf_guard_compile pre))"
    using mahler_cf_guard_compiler_correct[of pre] by (simp add: mahler_cf_guard_invariant_def)
  have b: "cf_ticks (mahler_cf_guard_compile (pre @ post)) =
      length (cf_word (mahler_cf_guard_compile (pre @ post)))"
    using mahler_cf_guard_compiler_correct[of "pre @ post"] by (simp add: mahler_cf_guard_invariant_def)
  show False using later a b empty mahler_cf_guard_compile_word[of pre post] by simp
qed

lemma mahler_cf_guard_scaled_update:
  fixes gain scale low high innovation modulus :: real
  assumes "0 < gain" "0 < scale"
  shows "max (low / gain) (innovation / (scale*gain)) =
      max (scale*low) innovation / (scale*gain)"
    "min (high / (2*gain)) ((2*innovation+modulus)/(2*(scale*gain))) =
      min (scale*high) (2*innovation+modulus) / (2*(scale*gain))"
  using mahler_cf_lean_scaled_guard_refinement[OF assms] .

lemma mahler_cf_zero_endpoint_cancel:
  fixes n d k :: nat
  assumes "0 < k"
  shows "2*(3^k*n) \<le> d*2^k \<longleftrightarrow>
    3^k*n \<le> d*2^(k-1)"
  using assms by (cases k) (simp_all add: power_Suc algebra_simps)

lemma mahler_cf_zero_endpoint_first:
  fixes n d :: nat
  shows "2*(3*n) \<le> d*2 \<longleftrightarrow> 3*n \<le> d"
    "2*(9*n) \<le> d*4 \<longleftrightarrow> 9*n \<le> 2*d"
  by simp_all

lemma mahler_cf_inverse_power_transport:
  fixes modulus :: int and exponent :: nat
  assumes modulus: "1 < modulus" and coprime: "coprime (3::int) modulus"
  shows "modular_inverse modulus ((3::int)^exponent) =
    (modular_inverse modulus 3)^exponent mod modulus"
proof (induction exponent)
  case 0
  then show ?case using modulus by (simp add: modular_inverse_1)
next
  case (Suc k)
  have power_coprime: "coprime ((3::int)^k) modulus"
    using coprime by (simp add: coprime_power_left_iff)
  have product: "modular_inverse modulus ((3::int)^k * 3) =
      (modular_inverse modulus 3 * modular_inverse modulus (3^k)) mod modulus"
    by (rule modular_inverse_int_mult[OF power_coprime coprime]) (use modulus in simp)
  have step: "modular_inverse modulus ((3::int)^k * 3) =
      (modular_inverse modulus 3 * ((modular_inverse modulus 3)^k mod modulus)) mod modulus"
    using product Suc.IH by (simp only: Suc.IH)
  also have "... = (modular_inverse modulus 3 * (modular_inverse modulus 3)^k) mod modulus"
    by (rule mod_mult_right_eq)
  finally show ?case by (simp only: power_Suc mult.commute)
qed

lemma mahler_cf_inverse_unit_modulus:
  "modular_inverse (1::int) ((3::int)^k) = 0"
  by (simp add: modular_inverse_def)

lemma mahler_cf_three_dyadic_coprime:
  "coprime (3::int) (2^k)"
  by (simp add: coprime_power_right_iff)

ML \<open>
  val checked = @{thms mahler_cf_inverse_unit_modulus mahler_cf_three_dyadic_coprime
    mahler_cf_inverse_power_transport mahler_cf_zero_endpoint_cancel
    mahler_cf_zero_endpoint_first mahler_cf_guard_compiler_correct
    mahler_cf_guard_compile_word
    mahler_cf_compiled_stall_not_guarded mahler_cf_compiled_later_ticks
    mahler_cf_guard_scaled_update};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "CF guard compiler oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "CF guard compiler skipped proof" else ();
\<close>

end
