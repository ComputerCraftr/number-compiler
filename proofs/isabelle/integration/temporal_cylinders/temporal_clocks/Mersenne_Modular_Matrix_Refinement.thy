theory Mersenne_Modular_Matrix_Refinement
  imports Mersenne_Matrix_Source_Refinement
    Shared_Carry_Dynamics.Finite_Transfer_Power
begin

text \<open>The runtime stores a row-major four-tuple of integer residues and
multiplies it modulo a positive natural modulus.  The candidate period is not
a proof: only the computed modular matrix identity below licenses exponent
reduction.  This theory makes no assertion about the SL2 cardinality formula
or primality.\<close>

type_synonym runtime_matrix2 = "int \<times> int \<times> int \<times> int"

definition runtime_matrix_to_nested :: "runtime_matrix2 \<Rightarrow> int mersenne_matrix2" where
  "runtime_matrix_to_nested A =
    ((fst A, fst (snd A)),
      (fst (snd (snd A)), snd (snd (snd A))))"

definition runtime_matrix_from_nested :: "int mersenne_matrix2 \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_from_nested A =
    (fst (fst A), snd (fst A), fst (snd A), snd (snd A))"

lemma runtime_matrix_conversion_roundtrip:
  "runtime_matrix_from_nested (runtime_matrix_to_nested A) = A"
  by (cases A) (simp add: runtime_matrix_to_nested_def runtime_matrix_from_nested_def)

lemma runtime_nested_conversion_roundtrip:
  "runtime_matrix_to_nested (runtime_matrix_from_nested A) = A"
  by (cases A) (simp add: runtime_matrix_to_nested_def runtime_matrix_from_nested_def)

definition runtime_matrix_raw_multiply ::
    "runtime_matrix2 \<Rightarrow> runtime_matrix2 \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_raw_multiply A B =
    runtime_matrix_from_nested
      (mersenne_matrix2_multiply
        (runtime_matrix_to_nested A) (runtime_matrix_to_nested B))"

lemma runtime_matrix_raw_multiply_assoc:
  "runtime_matrix_raw_multiply
      (runtime_matrix_raw_multiply A B) C =
    runtime_matrix_raw_multiply A (runtime_matrix_raw_multiply B C)"
  by (cases A; cases B; cases C;
      simp add: runtime_matrix_raw_multiply_def runtime_matrix_to_nested_def
        runtime_matrix_from_nested_def mersenne_matrix2_multiply_assoc)

lemma runtime_matrix_raw_one_left:
  "runtime_matrix_raw_multiply (1,0,0,1) A = A"
  by (cases A; simp add: runtime_matrix_raw_multiply_def
      runtime_matrix_to_nested_def runtime_matrix_from_nested_def
      mersenne_matrix2_one_def mersenne_matrix2_multiply_def)

lemma runtime_matrix_raw_one_right:
  "runtime_matrix_raw_multiply A (1,0,0,1) = A"
  by (cases A; simp add: runtime_matrix_raw_multiply_def
      runtime_matrix_to_nested_def runtime_matrix_from_nested_def
      mersenne_matrix2_one_def mersenne_matrix2_multiply_def)

definition runtime_matrix_normalize :: "nat \<Rightarrow> runtime_matrix2 \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_normalize modulus A =
    (fst A mod int modulus, fst (snd A) mod int modulus,
     fst (snd (snd A)) mod int modulus,
     snd (snd (snd A)) mod int modulus)"

definition runtime_matrix_normalized :: "nat \<Rightarrow> runtime_matrix2 \<Rightarrow> bool" where
  "runtime_matrix_normalized modulus A \<longleftrightarrow>
    runtime_matrix_normalize modulus A = A"

lemma runtime_matrix_normalize_idempotent:
  "runtime_matrix_normalize modulus
      (runtime_matrix_normalize modulus A) =
    runtime_matrix_normalize modulus A"
  by (cases A; simp add: runtime_matrix_normalize_def)

lemma runtime_int_mod_two_products_left:
  fixes a b c d modulus :: int
  shows "((a mod modulus) * b + (c mod modulus) * d) mod modulus =
    (a * b + c * d) mod modulus"
proof -
  have "((a mod modulus) * b + (c mod modulus) * d) mod modulus =
      (((a mod modulus) * b) mod modulus +
        ((c mod modulus) * d) mod modulus) mod modulus"
    by (rule mod_add_eq[symmetric])
  also have "... = ((a * b) mod modulus + (c * d) mod modulus) mod modulus"
    by (simp only: mod_mult_left_eq)
  also have "... = (a * b + c * d) mod modulus"
    by (rule mod_add_eq)
  finally show ?thesis .
qed

lemma runtime_int_mod_two_products_right:
  fixes a b c d modulus :: int
  shows "(a * (b mod modulus) + c * (d mod modulus)) mod modulus =
    (a * b + c * d) mod modulus"
proof -
  have "(a * (b mod modulus) + c * (d mod modulus)) mod modulus =
      ((a * (b mod modulus)) mod modulus +
        (c * (d mod modulus)) mod modulus) mod modulus"
    by (rule mod_add_eq[symmetric])
  also have "... = ((a * b) mod modulus + (c * d) mod modulus) mod modulus"
    by (simp only: mod_mult_right_eq)
  also have "... = (a * b + c * d) mod modulus"
    by (rule mod_add_eq)
  finally show ?thesis .
qed

lemma runtime_matrix_normalize_raw_multiply_left:
  assumes "0 < modulus"
  shows "runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply
        (runtime_matrix_normalize modulus A) B) =
    runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply A B)"
  using assms
  by (cases A; cases B;
      simp add: runtime_matrix_normalize_def runtime_matrix_raw_multiply_def
        runtime_matrix_to_nested_def runtime_matrix_from_nested_def
        mersenne_matrix2_multiply_def runtime_int_mod_two_products_left)

lemma runtime_matrix_normalize_raw_multiply_right:
  assumes "0 < modulus"
  shows "runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply A
        (runtime_matrix_normalize modulus B)) =
    runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply A B)"
  using assms
  by (cases A; cases B;
      simp add: runtime_matrix_normalize_def runtime_matrix_raw_multiply_def
        runtime_matrix_to_nested_def runtime_matrix_from_nested_def
        mersenne_matrix2_multiply_def runtime_int_mod_two_products_right)

lemma runtime_matrix_normalize_raw_multiply_both:
  assumes "0 < modulus"
  shows "runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply
        (runtime_matrix_normalize modulus A)
        (runtime_matrix_normalize modulus B)) =
    runtime_matrix_normalize modulus
      (runtime_matrix_raw_multiply A B)"
proof -
  have left:
    "runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply
          (runtime_matrix_normalize modulus A)
          (runtime_matrix_normalize modulus B)) =
      runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply A
          (runtime_matrix_normalize modulus B))"
    using runtime_matrix_normalize_raw_multiply_left[OF assms, of A
        "runtime_matrix_normalize modulus B"] .
  have right:
    "runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply A
          (runtime_matrix_normalize modulus B)) =
      runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply A B)"
    using runtime_matrix_normalize_raw_multiply_right[OF assms, of A B] .
  show ?thesis using left right by simp
qed

definition runtime_matrix_multiply ::
    "nat \<Rightarrow> runtime_matrix2 \<Rightarrow> runtime_matrix2 \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_multiply modulus A B =
    runtime_matrix_normalize modulus (runtime_matrix_raw_multiply A B)"

lemma runtime_matrix_multiply_normalized:
  "runtime_matrix_normalize modulus
      (runtime_matrix_multiply modulus A B) =
    runtime_matrix_multiply modulus A B"
  by (simp add: runtime_matrix_multiply_def runtime_matrix_normalize_idempotent)

lemma runtime_matrix_multiply_normalization_compatibility:
  assumes "0 < modulus"
  shows "runtime_matrix_multiply modulus
      (runtime_matrix_normalize modulus A)
      (runtime_matrix_normalize modulus B) =
    runtime_matrix_multiply modulus A B"
  using runtime_matrix_normalize_raw_multiply_both[OF assms, of A B]
  by (simp add: runtime_matrix_multiply_def)

lemma runtime_matrix_multiply_assoc:
  assumes modulus: "1 < modulus"
  shows "runtime_matrix_multiply modulus
      (runtime_matrix_multiply modulus A B) C =
    runtime_matrix_multiply modulus A
      (runtime_matrix_multiply modulus B C)"
proof -
  have positive: "0 < modulus" using modulus by simp
  have lhs:
    "runtime_matrix_multiply modulus
        (runtime_matrix_multiply modulus A B) C =
      runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply
          (runtime_matrix_raw_multiply A B) C)"
    using positive
    by (simp add: runtime_matrix_multiply_def
        runtime_matrix_normalize_raw_multiply_left
        runtime_matrix_normalize_raw_multiply_right
        runtime_matrix_normalize_idempotent)
  have rhs:
    "runtime_matrix_multiply modulus A
        (runtime_matrix_multiply modulus B C) =
      runtime_matrix_normalize modulus
        (runtime_matrix_raw_multiply A
          (runtime_matrix_raw_multiply B C))"
    using positive
    by (simp add: runtime_matrix_multiply_def
        runtime_matrix_normalize_raw_multiply_left
        runtime_matrix_normalize_raw_multiply_right
        runtime_matrix_normalize_idempotent)
  show ?thesis
    unfolding lhs rhs
    by (simp add: runtime_matrix_raw_multiply_assoc)
qed

definition runtime_matrix_one :: "nat \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_one modulus =
    runtime_matrix_normalize modulus (1,0,0,1)"

lemma runtime_matrix_one_normalized:
  "runtime_matrix_normalize modulus (runtime_matrix_one modulus) =
    runtime_matrix_one modulus"
  by (simp add: runtime_matrix_one_def runtime_matrix_normalize_idempotent)

lemma runtime_matrix_multiply_one_left:
  assumes "1 < modulus"
      and "runtime_matrix_normalized modulus A"
  shows "runtime_matrix_multiply modulus
      (runtime_matrix_one modulus) A = A"
  using assms
  by (cases A; simp add: runtime_matrix_multiply_def runtime_matrix_one_def
      runtime_matrix_normalized_def runtime_matrix_normalize_def
      runtime_matrix_raw_multiply_def runtime_matrix_to_nested_def
      runtime_matrix_from_nested_def mersenne_matrix2_multiply_def mod_simps)

lemma runtime_matrix_multiply_one_right:
  assumes "1 < modulus"
      and "runtime_matrix_normalized modulus A"
  shows "runtime_matrix_multiply modulus A
      (runtime_matrix_one modulus) = A"
  using assms
  by (cases A; simp add: runtime_matrix_multiply_def runtime_matrix_one_def
      runtime_matrix_normalized_def runtime_matrix_normalize_def
      runtime_matrix_raw_multiply_def runtime_matrix_to_nested_def
      runtime_matrix_from_nested_def mersenne_matrix2_multiply_def mod_simps)

fun runtime_matrix_power ::
    "nat \<Rightarrow> runtime_matrix2 \<Rightarrow> nat \<Rightarrow> runtime_matrix2" where
  "runtime_matrix_power modulus A 0 = runtime_matrix_one modulus"
| "runtime_matrix_power modulus A (Suc n) =
    runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A n) A"

lemma runtime_matrix_power_normalized:
  "runtime_matrix_normalize modulus
      (runtime_matrix_power modulus A exponent) =
    runtime_matrix_power modulus A exponent"
proof (induction exponent)
  case 0
  then show ?case
    by (simp add: runtime_matrix_one_normalized)
next
  case (Suc exponent)
  then show ?case
    by (simp add: runtime_matrix_multiply_normalized)
qed

lemma runtime_matrix_power_add:
  assumes modulus: "1 < modulus"
  shows "runtime_matrix_power modulus A (first + second) =
    runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A first)
      (runtime_matrix_power modulus A second)"
proof (induction second)
  case 0
  have normalized:
    "runtime_matrix_normalized modulus (runtime_matrix_power modulus A first)"
    by (simp add: runtime_matrix_normalized_def runtime_matrix_power_normalized)
  have right_identity:
    "runtime_matrix_multiply modulus
        (runtime_matrix_power modulus A first)
        (runtime_matrix_one modulus) =
      runtime_matrix_power modulus A first"
    by (rule runtime_matrix_multiply_one_right[OF modulus normalized])
  show ?case using right_identity by simp
next
  case (Suc second)
  have exponent: "first + Suc second = Suc (first + second)"
    by simp
  have first_step:
    "runtime_matrix_power modulus A (first + Suc second) =
      runtime_matrix_multiply modulus
        (runtime_matrix_power modulus A (first + second)) A"
    by (simp only: exponent runtime_matrix_power.simps)
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_multiply modulus
        (runtime_matrix_power modulus A first)
        (runtime_matrix_power modulus A second)) A"
    by (simp only: Suc.IH)
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A first)
      (runtime_matrix_multiply modulus
        (runtime_matrix_power modulus A second) A)"
    by (rule runtime_matrix_multiply_assoc[OF modulus])
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A first)
      (runtime_matrix_power modulus A (Suc second))"
    by (simp only: runtime_matrix_power.simps)
  finally show ?case .
qed

lemma runtime_matrix_power_period_multiple:
  assumes modulus: "1 < modulus"
      and period: "0 < period"
      and normalized: "runtime_matrix_normalized modulus A"
      and checked: "runtime_matrix_power modulus A period =
        runtime_matrix_one modulus"
  shows "runtime_matrix_power modulus A (period * count) =
    runtime_matrix_one modulus"
proof (induction count)
  case 0
  then show ?case by simp
next
  case (Suc count)
  have exponent: "period * Suc count = period * count + period"
    by simp
  have add:
    "runtime_matrix_power modulus A (period * count + period) =
      runtime_matrix_multiply modulus
        (runtime_matrix_power modulus A (period * count))
        (runtime_matrix_power modulus A period)"
    by (rule runtime_matrix_power_add[OF modulus])
  have one_normalized:
    "runtime_matrix_normalized modulus (runtime_matrix_one modulus)"
    unfolding runtime_matrix_normalized_def
    by (rule runtime_matrix_one_normalized)
  have one_idempotent:
    "runtime_matrix_multiply modulus
        (runtime_matrix_one modulus) (runtime_matrix_one modulus) =
      runtime_matrix_one modulus"
    by (rule runtime_matrix_multiply_one_left[OF modulus one_normalized])
  have "runtime_matrix_power modulus A (period * Suc count) =
      runtime_matrix_power modulus A (period * count + period)"
    by (simp only: exponent)
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A (period * count))
      (runtime_matrix_power modulus A period)"
    by (rule add)
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_one modulus) (runtime_matrix_one modulus)"
    by (simp only: Suc.IH checked)
  also have "... = runtime_matrix_one modulus"
    by (rule one_idempotent)
  finally show ?case .
qed

theorem runtime_matrix_power_reduces_at_checked_period:
  assumes modulus: "1 < modulus"
      and period: "0 < period"
      and normalized: "runtime_matrix_normalized modulus A"
      and checked: "runtime_matrix_power modulus A period =
        runtime_matrix_one modulus"
  shows "runtime_matrix_power modulus A exponent =
    runtime_matrix_power modulus A (exponent mod period)"
proof -
  have division:
    "exponent = period * (exponent div period) + exponent mod period"
    using div_mult_mod_eq[of exponent period]
    by (simp add: mult.commute)
  have dead:
    "runtime_matrix_power modulus A
        (period * (exponent div period)) = runtime_matrix_one modulus"
    using runtime_matrix_power_period_multiple[OF modulus period normalized checked,
        of "exponent div period"] .
  have remainder_normalized:
    "runtime_matrix_normalized modulus
        (runtime_matrix_power modulus A (exponent mod period))"
    unfolding runtime_matrix_normalized_def
    by (rule runtime_matrix_power_normalized)
  have remove_period:
    "runtime_matrix_multiply modulus (runtime_matrix_one modulus)
        (runtime_matrix_power modulus A (exponent mod period)) =
      runtime_matrix_power modulus A (exponent mod period)"
    by (rule runtime_matrix_multiply_one_left[OF modulus remainder_normalized])
  have split_power:
    "runtime_matrix_power modulus A exponent =
      runtime_matrix_power modulus A
        (period * (exponent div period) + exponent mod period)"
    by (rule arg_cong[OF division])
  have "runtime_matrix_power modulus A exponent =
      runtime_matrix_power modulus A
        (period * (exponent div period) + exponent mod period)"
    by (rule split_power)
  also have "... = runtime_matrix_multiply modulus
      (runtime_matrix_power modulus A
        (period * (exponent div period)))
      (runtime_matrix_power modulus A (exponent mod period))"
    by (rule runtime_matrix_power_add[OF modulus])
  also have "... = runtime_matrix_power modulus A (exponent mod period)"
    using dead remove_period by simp
  finally show ?thesis .
qed

theorem runtime_checked_dyadic_matrix_power_reduction:
  assumes modulus: "1 < modulus"
      and period: "0 < period"
      and normalized: "runtime_matrix_normalized modulus A"
      and checked: "runtime_matrix_power modulus A period =
        runtime_matrix_one modulus"
  shows "runtime_matrix_power modulus A (2^steps) =
    runtime_matrix_power modulus A ((2^steps) mod period)"
  by (rule runtime_matrix_power_reduces_at_checked_period
      [OF modulus period normalized checked])

text \<open>The shared integer-loop state is relation-valued.  This graph
relation embeds the exact row-major modular multiplication operation into the
loop invariant: a completed run from identity returns the same matrix power
as the runtime accumulator.  This is a source-level operation model, not a
claim that Isabelle extracts or executes the Python implementation; the
external source, proposed-period check, and cache authority remain obligations
of their runtime owners.\<close>

definition runtime_matrix_right_relation ::
    "nat \<Rightarrow> runtime_matrix2 \<Rightarrow> (runtime_matrix2 \<times> runtime_matrix2) set" where
  "runtime_matrix_right_relation modulus A =
    {(source,target). target = runtime_matrix_multiply modulus source A}"

lemma runtime_matrix_right_relation_power:
  assumes modulus: "1 < modulus"
  shows "runtime_matrix_normalized modulus initial \<longrightarrow>
      ((initial,target) \<in> runtime_matrix_right_relation modulus A ^^ exponent \<longleftrightarrow>
      target = runtime_matrix_multiply modulus initial
        (runtime_matrix_power modulus A exponent))"
proof (induction exponent arbitrary: initial target)
  case 0
  show ?case
  proof
    assume source: "runtime_matrix_normalized modulus initial"
    have identity:
      "runtime_matrix_multiply modulus initial (runtime_matrix_one modulus) = initial"
      by (rule runtime_matrix_multiply_one_right[OF modulus source])
    have relation_zero:
      "(initial,target) \<in>
          runtime_matrix_right_relation modulus A ^^ 0 \<longleftrightarrow>
        initial = target"
      by simp
    have power_zero:
      "target = runtime_matrix_multiply modulus initial
          (runtime_matrix_power modulus A 0) \<longleftrightarrow>
        target = initial"
      by (simp only: runtime_matrix_power.simps identity)
    show "(initial,target) \<in>
        runtime_matrix_right_relation modulus A ^^ 0 \<longleftrightarrow>
        target = runtime_matrix_multiply modulus initial
          (runtime_matrix_power modulus A 0)"
    proof -
      have "(initial,target) \<in>
          runtime_matrix_right_relation modulus A ^^ 0 \<longleftrightarrow>
          initial = target"
        by (rule relation_zero)
      also have "... \<longleftrightarrow> target = initial"
        by (rule eq_commute)
      also have "... \<longleftrightarrow>
          target = runtime_matrix_multiply modulus initial
            (runtime_matrix_power modulus A 0)"
        by (rule power_zero[symmetric])
      finally show ?thesis .
    qed
  qed
next
  case (Suc exponent)
  show ?case
  proof
    assume initial_normalized: "runtime_matrix_normalized modulus initial"
    show "(initial,target) \<in>
        runtime_matrix_right_relation modulus A ^^ Suc exponent \<longleftrightarrow>
      target = runtime_matrix_multiply modulus initial
        (runtime_matrix_power modulus A (Suc exponent))"
    proof
      assume path:
        "(initial,target) \<in>
          runtime_matrix_right_relation modulus A ^^ Suc exponent"
      obtain middle where previous:
          "(initial,middle) \<in>
            runtime_matrix_right_relation modulus A ^^ exponent"
        and final_step:
          "(middle,target) \<in> runtime_matrix_right_relation modulus A"
        using relpow_Suc_E[OF path] by blast
      have middle_value:
        "middle = runtime_matrix_multiply modulus initial
          (runtime_matrix_power modulus A exponent)"
        using Suc.IH initial_normalized previous by blast
      have target_value:
        "target = runtime_matrix_multiply modulus middle A"
        using final_step by (simp add: runtime_matrix_right_relation_def)
      show "target = runtime_matrix_multiply modulus initial
          (runtime_matrix_power modulus A (Suc exponent))"
      proof -
        have "target = runtime_matrix_multiply modulus
            (runtime_matrix_multiply modulus initial
              (runtime_matrix_power modulus A exponent)) A"
          using target_value middle_value by simp
        also have "... = runtime_matrix_multiply modulus initial
            (runtime_matrix_multiply modulus
              (runtime_matrix_power modulus A exponent) A)"
          by (rule runtime_matrix_multiply_assoc[OF modulus])
        also have "... = runtime_matrix_multiply modulus initial
            (runtime_matrix_power modulus A (Suc exponent))"
          by simp
        finally show ?thesis .
      qed
    next
      assume target_value:
        "target = runtime_matrix_multiply modulus initial
          (runtime_matrix_power modulus A (Suc exponent))"
      let ?middle = "runtime_matrix_multiply modulus initial
        (runtime_matrix_power modulus A exponent)"
      have previous:
        "(initial,?middle) \<in>
          runtime_matrix_right_relation modulus A ^^ exponent"
        using Suc.IH[of initial ?middle] initial_normalized by simp
      have final_step: "(?middle,target) \<in>
          runtime_matrix_right_relation modulus A"
      proof -
        have step_value:
          "target = runtime_matrix_multiply modulus ?middle A"
        proof -
          have "target = runtime_matrix_multiply modulus initial
              (runtime_matrix_multiply modulus
                (runtime_matrix_power modulus A exponent) A)"
            using target_value by simp
          also have "... = runtime_matrix_multiply modulus ?middle A"
            by (rule sym[OF runtime_matrix_multiply_assoc[OF modulus]])
          finally show ?thesis .
        qed
        show ?thesis
          using step_value by (simp add: runtime_matrix_right_relation_def)
      qed
      show "(initial,target) \<in>
          runtime_matrix_right_relation modulus A ^^ Suc exponent"
        by (rule relpow_Suc_I[OF previous final_step])
    qed
  qed
qed

theorem runtime_matrix_binary_power_refines_relation:
  "transfer_binary_power (runtime_matrix_right_relation modulus A) bits =
    runtime_matrix_right_relation modulus A ^^ transfer_binary_value bits"
  by (rule transfer_binary_power_exact)

theorem runtime_matrix_binary_power_from_identity:
  assumes modulus: "1 < modulus"
  shows "(runtime_matrix_one modulus,target) \<in>
      transfer_binary_power (runtime_matrix_right_relation modulus A) bits
      \<longleftrightarrow>
    target = runtime_matrix_power modulus A (transfer_binary_value bits)"
proof -
  have initial:
    "runtime_matrix_normalized modulus (runtime_matrix_one modulus)"
    unfolding runtime_matrix_normalized_def
    by (rule runtime_matrix_one_normalized)
  have relation:
    "(runtime_matrix_one modulus,target) \<in>
        transfer_binary_power (runtime_matrix_right_relation modulus A) bits
      \<longleftrightarrow>
      (runtime_matrix_one modulus,target) \<in>
        runtime_matrix_right_relation modulus A ^^ transfer_binary_value bits"
    by (simp only: runtime_matrix_binary_power_refines_relation)
  have action:
    "(runtime_matrix_one modulus,target) \<in>
        runtime_matrix_right_relation modulus A ^^ transfer_binary_value bits
      \<longleftrightarrow>
      target = runtime_matrix_multiply modulus (runtime_matrix_one modulus)
        (runtime_matrix_power modulus A (transfer_binary_value bits))"
    using runtime_matrix_right_relation_power[OF modulus,
        where A = A and initial = "runtime_matrix_one modulus"
          and target = target and exponent = "transfer_binary_value bits"]
    by (simp add: initial)
  have powered_normalized:
    "runtime_matrix_normalized modulus
        (runtime_matrix_power modulus A (transfer_binary_value bits))"
    by (simp add: runtime_matrix_normalized_def runtime_matrix_power_normalized)
  have identity:
    "runtime_matrix_multiply modulus (runtime_matrix_one modulus)
        (runtime_matrix_power modulus A (transfer_binary_value bits)) =
      runtime_matrix_power modulus A (transfer_binary_value bits)"
    by (rule runtime_matrix_multiply_one_left[OF modulus powered_normalized])
  show ?thesis using relation action identity by simp
qed

lemma transfer_binary_value_surjective:
  "\<exists>bits. transfer_binary_value bits = exponent"
proof (induction exponent rule: less_induct)
  case (less exponent)
  show ?case
  proof (cases exponent)
    case 0
    have empty_value: "transfer_binary_value ([] :: bool list) = exponent"
      using 0 by simp
    show ?thesis using empty_value by blast
  next
    case (Suc predecessor)
    have half_less: "exponent div 2 < exponent"
      using Suc by simp
    obtain bits where bits_value:
      "transfer_binary_value bits = exponent div 2"
      using less.IH[OF half_less] by blast
    have division:
      "exponent = exponent mod 2 + 2 * (exponent div 2)"
      using div_mult_mod_eq[of exponent 2] by (simp add: ac_simps)
    have remainder: "exponent mod 2 < 2" by simp
    have low_bit:
      "(if exponent mod 2 = 1 then 1 else 0) = exponent mod 2"
      using remainder by presburger
    have witness_value:
      "transfer_binary_value ((exponent mod 2 = 1) # bits) = exponent"
      using bits_value division low_bit
      by (simp add: transfer_binary_value.simps; presburger)
    show ?thesis using witness_value by blast
  qed
qed

corollary runtime_matrix_binary_power_integer_exponent:
  assumes modulus: "1 < modulus"
  shows "\<exists>bits. transfer_binary_value bits = exponent \<and>
      ((runtime_matrix_one modulus,target) \<in>
        transfer_binary_power (runtime_matrix_right_relation modulus A) bits
        \<longleftrightarrow>
       target = runtime_matrix_power modulus A exponent)"
proof -
  obtain bits where bits_value: "transfer_binary_value bits = exponent"
    using transfer_binary_value_surjective by blast
  have action:
    "(runtime_matrix_one modulus,target) \<in>
        transfer_binary_power (runtime_matrix_right_relation modulus A) bits
      \<longleftrightarrow>
      target = runtime_matrix_power modulus A (transfer_binary_value bits)"
    by (rule runtime_matrix_binary_power_from_identity[OF modulus,
        where A = A and target = target and bits = bits])
  show ?thesis
    using bits_value action by blast
qed

theorem runtime_matrix_integer_loop_refinement:
  assumes modulus: "1 < modulus"
  shows "\<exists>accumulator current.
      transfer_binary_loop_reaches
        (Id,runtime_matrix_right_relation modulus A,exponent)
        (accumulator,current,0) \<and>
      (\<forall>target. ((runtime_matrix_one modulus,target) \<in> accumulator) \<longleftrightarrow>
        target = runtime_matrix_power modulus A exponent)"
proof -
  let ?action = "runtime_matrix_right_relation modulus A"
  obtain accumulator current where reached:
    "transfer_binary_loop_reaches (Id,?action,exponent)
      (accumulator,current,0)"
      and exact: "accumulator = ?action ^^ exponent"
    using transfer_binary_loop_terminates_exactly[
        where R="?action" and duration=exponent]
    by blast
  have identity_normalized:
    "runtime_matrix_normalized modulus (runtime_matrix_one modulus)"
    unfolding runtime_matrix_normalized_def
    by (rule runtime_matrix_one_normalized)
  have powered_normalized:
    "runtime_matrix_normalized modulus
      (runtime_matrix_power modulus A exponent)"
    by (simp add: runtime_matrix_normalized_def runtime_matrix_power_normalized)
  have identity_action:
    "runtime_matrix_multiply modulus (runtime_matrix_one modulus)
        (runtime_matrix_power modulus A exponent) =
      runtime_matrix_power modulus A exponent"
    by (rule runtime_matrix_multiply_one_left[OF modulus powered_normalized])
  have endpoint:
    "\<forall>target. ((runtime_matrix_one modulus,target) \<in> accumulator) \<longleftrightarrow>
      target = runtime_matrix_power modulus A exponent"
  proof
    fix target
    have path:
      "((runtime_matrix_one modulus,target) \<in> accumulator) \<longleftrightarrow>
        target = runtime_matrix_multiply modulus (runtime_matrix_one modulus)
          (runtime_matrix_power modulus A exponent)"
      using exact runtime_matrix_right_relation_power[OF modulus,
          where A = A and initial = "runtime_matrix_one modulus"
            and target = target and exponent = exponent]
        identity_normalized by simp
    show "((runtime_matrix_one modulus,target) \<in> accumulator) \<longleftrightarrow>
      target = runtime_matrix_power modulus A exponent"
      using path identity_action by simp
  qed
  show ?thesis using reached endpoint by blast
qed

text \<open>The runtime source tuple is the normalized row-major companion
matrix.  In particular the negative-one entry is represented by the
canonical residue rather than by an unbounded signed entry.\<close>

lemma runtime_matrix_companion_source:
  assumes "1 < modulus"
  shows "runtime_matrix_normalize modulus (trace, -1, 1, 0) =
    (trace mod int modulus, int modulus - 1, 1, 0)"
  using assms
  by (simp add: runtime_matrix_normalize_def zmod_minus1)

lemma runtime_matrix_companion_matches_formal:
  "runtime_matrix_normalize modulus (trace, -1, 1, 0) =
    runtime_matrix_normalize modulus
      (runtime_matrix_from_nested (mersenne_companion_matrix trace))"
  by (simp add: runtime_matrix_from_nested_def runtime_matrix_normalize_def
      mersenne_companion_matrix_def)

ML \<open>
  val checked = @{thms runtime_matrix_multiply_normalization_compatibility
    runtime_matrix_multiply_assoc runtime_matrix_power_add
    runtime_matrix_power_period_multiple
    runtime_matrix_power_reduces_at_checked_period
    runtime_checked_dyadic_matrix_power_reduction
    runtime_matrix_right_relation_power
    runtime_matrix_binary_power_refines_relation
    runtime_matrix_binary_power_from_identity
    transfer_binary_value_surjective
    runtime_matrix_binary_power_integer_exponent
    runtime_matrix_integer_loop_refinement
    runtime_matrix_companion_source runtime_matrix_companion_matches_formal};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mersenne modular matrix refinement depends on an oracle";
  val _ = if not (Thm_Deps.has_skip_proof checked) then ()
    else error "Mersenne modular matrix refinement contains a skipped proof";
\<close>

end
