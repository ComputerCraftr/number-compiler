theory Antihydra_Exact_Run_Candidate_Refinement
  imports Antihydra_Arithmetic_Cylinder_Lift
begin

text \<open>The bounded exact-source constructor publishes a full integer skew,
the source endpoint, the ordered ledger summary, and the count of odd h
symbols.  Once its run traversal has established the exact family endpoint,
the reconstructed affine offset is not an independent action: it is exactly
the offset in the canonical admitted family block.  This bridge does not
prove that a source-free finite matrix is repeatable or transfer an exact
source action to another source.\<close>

definition antihydra_exact_run_offset :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "antihydra_exact_run_offset h width =
    int (antihydra_family_orbit h width) * int (2^width) -
      int (3^width) * int h"

definition antihydra_exact_run_odd_symbols :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_exact_run_odd_symbols h width =
    sum_list (antihydra_family_bits h width)"

lemma antihydra_fixed_source_orbit_and_word:
  "antihydra_family_orbit 1 n = 1"
  "antihydra_family_bits 1 n = replicate n 1"
  by (induction n; simp add: antihydra_family_step_def)+

lemma antihydra_fixed_source_word_delta:
  "ledger_word_delta (replicate n 1) = - int n"
  by (induction n; simp)

lemma antihydra_fixed_source_word_minimum:
  "ledger_word_minprefix (replicate n 1) = - int n"
  by (induction n; simp add: min_def)

lemma antihydra_zero_source_orbit_and_word:
  "antihydra_family_orbit 0 n = 0"
  "antihydra_family_bits 0 n = replicate n 0"
  by (induction n; simp add: antihydra_family_step_def)+

lemma antihydra_zero_source_word_fields:
  "ledger_word_delta (replicate n 0) = 2 * int n"
  "ledger_word_minprefix (replicate n 0) = 0"
  by (induction n; simp add: algebra_simps)+

theorem antihydra_zero_source_leaf_fields:
  "antihydra_family_orbit 0 n = 0"
  "antihydra_family_balance 0 0 n = 2 * int n"
  "antihydra_family_minimum 0 0 n = 0"
  "antihydra_exact_run_odd_symbols 0 n = 0"
  by (simp_all only: antihydra_zero_source_orbit_and_word
      antihydra_zero_source_word_fields antihydra_family_balance_def
      antihydra_family_minimum_def antihydra_exact_run_odd_symbols_def
      sum_list_replicate mult_zero_right add.left_neutral)

theorem antihydra_zero_cylinder_leaf_fields:
  "antihydra_family_orbit (2^n*q) n = 3^n*q"
  "antihydra_family_balance (2^n*q) 0 n = 2 * int n"
  "antihydra_family_minimum (2^n*q) 0 n = 0"
  "antihydra_family_bits (2^n*q) n = replicate n 0"
  using antihydra_family_orbit_cylinder_transport[of 0 n q]
    antihydra_family_balance_cylinder_transport[of 0 n q 0]
    antihydra_family_minimum_cylinder_transport[of 0 n q 0]
    antihydra_family_bits_cylinder_transport[of 0 n q]
    antihydra_zero_source_leaf_fields antihydra_zero_source_orbit_and_word
  by (simp_all only: add.left_neutral)

theorem antihydra_fixed_source_leaf_fields:
  "antihydra_family_orbit 1 n = 1"
  "antihydra_family_balance 1 0 n = - int n"
  "antihydra_family_minimum 1 0 n = - int n"
  "antihydra_exact_run_odd_symbols 1 n = n"
  by (simp_all only: antihydra_fixed_source_orbit_and_word
      antihydra_fixed_source_word_delta antihydra_fixed_source_word_minimum
      antihydra_family_balance_def antihydra_family_minimum_def
      antihydra_exact_run_odd_symbols_def sum_list_replicate of_nat_id
      mult.right_neutral add.left_neutral)

lemma antihydra_binary_word_sum_is_one_count:
  assumes binary: "\<And>b. b \<in> set bits \<Longrightarrow> b < 2"
  shows "sum_list bits = count_list bits 1"
  using binary
proof (induction bits)
  case Nil
  then show ?case by simp
next
  case (Cons b bits)
  have b_bound: "b < 2" using Cons.prems by simp
  have b: "b = 0 \<or> b = 1" using b_bound by arith
  have tail_binary: "\<And>item. item \<in> set bits \<Longrightarrow> item < 2"
    using Cons.prems by simp
  have tail:
    "sum_list bits = count_list bits 1"
    using Cons.IH[OF tail_binary] .
  show ?case using b tail by (cases b) simp_all
qed

theorem antihydra_exact_run_candidate_fields:
  assumes endpoint:
    "observed_endpoint = antihydra_family_orbit h width"
  shows
    "int (3^width) = sk_A (antihydra_arithmetic_block h width)"
    "antihydra_exact_run_offset h width =
        sk_J (antihydra_arithmetic_block h width)"
    "int (2^width) = sk_D (antihydra_arithmetic_block h width)"
    "antihydra_exact_run_odd_symbols h width =
        count_list (antihydra_family_bits h width) 1"
    "sk_delta (antihydra_arithmetic_block h width) =
        antihydra_family_balance h 0 width"
    "sk_minprefix (antihydra_arithmetic_block h width) =
        antihydra_family_minimum h 0 width"
proof -
  let ?block = "antihydra_arithmetic_block h width"
  show "int (3^width) = sk_A ?block"
    by (simp add: antihydra_arithmetic_block_def)
  show offset:
    "antihydra_exact_run_offset h width = sk_J ?block"
  proof -
    have application:
      "sk_D ?block * int (antihydra_family_orbit h width) =
        sk_A ?block * int h + sk_J ?block"
      using antihydra_arithmetic_block_skew_application[of h width]
      by (simp add: skew_numerator_def)
    have coefficients:
      "sk_A ?block = int (3^width)"
      "sk_D ?block = int (2^width)"
      by (simp_all add: antihydra_arithmetic_block_def)
    have endpoint_int:
      "int (antihydra_family_orbit h width) = int observed_endpoint"
      using endpoint by simp
    have application':
      "int (2^width) * int observed_endpoint =
        int (3^width) * int h + sk_J ?block"
      using application coefficients(1) coefficients(2) endpoint_int
      by simp
    have rearranged:
      "int observed_endpoint * int (2^width) -
          int (3^width) * int h = sk_J ?block"
      using application' by (simp add: algebra_simps)
    show ?thesis
      unfolding antihydra_exact_run_offset_def
      using rearranged endpoint_int
      by (simp add: algebra_simps)
  qed
  show "int (2^width) = sk_D ?block"
    by (simp add: antihydra_arithmetic_block_def)
  show "antihydra_exact_run_odd_symbols h width =
      count_list (antihydra_family_bits h width) 1"
    unfolding antihydra_exact_run_odd_symbols_def
    by (rule antihydra_binary_word_sum_is_one_count;
        rule antihydra_family_bits_binary)
  show "sk_delta ?block = antihydra_family_balance h 0 width"
    and "sk_minprefix ?block = antihydra_family_minimum h 0 width"
    by (simp_all add: antihydra_arithmetic_block_ledger_projection)
qed

theorem antihydra_exact_run_candidate_composes:
  "antihydra_arithmetic_block h (left + right) =
    skew_then (antihydra_arithmetic_block h left)
      (antihydra_arithmetic_block
        (antihydra_family_orbit h left) right)"
  by (rule antihydra_arithmetic_block_composition)

theorem antihydra_rotated_phase_ordered_correction:
  "sk_J (skew_word (suffix @ prefix)) =
    3^(length prefix) * sk_J (skew_word suffix) +
      2^(length suffix) * sk_J (skew_word prefix)"
  by (simp add: skew_word_append skew_then_def mult.commute)

theorem antihydra_rotated_source_guard_pullback:
  fixes h endpoint prefix_correction rotated inverse :: nat
  assumes physical: "3^cut * h = 2^cut * endpoint + prefix_correction"
    and seam: "endpoint mod 2^width = rotated mod 2^width"
    and inverse: "(inverse * 3^cut) mod 2^(width + cut) = 1"
  shows "h mod 2^(width + cut) =
    (inverse * (prefix_correction + 2^cut * rotated)) mod 2^(width + cut)"
proof -
  let ?M = "2^(width + cut)"
  have blocks: "(2^cut * endpoint) mod ?M = (2^cut * rotated) mod ?M"
    using seam by (simp only: add.commute power_add mod_mult_mult1)
  have transport: "(3^cut * h) mod ?M =
      (prefix_correction + 2^cut * rotated) mod ?M"
  proof -
    have "(3^cut * h) mod ?M = (2^cut * endpoint + prefix_correction) mod ?M"
      by (simp only: physical)
    also have "... = (2^cut * rotated + prefix_correction) mod ?M"
      by (rule mod_add_cong[OF blocks refl])
    also have "... = (prefix_correction + 2^cut * rotated) mod ?M"
      by (simp only: add.commute)
    finally show ?thesis .
  qed
  have source:
      "(inverse * 3^cut * h) mod ?M = h mod ?M"
  proof -
    have "(inverse * 3^cut * h) mod ?M = (((inverse * 3^cut) mod ?M) * h) mod ?M"
      by (rule mod_mult_left_eq[symmetric])
    also have "... = h mod ?M" using inverse by simp
    finally show ?thesis .
  qed
  have multiplied: "(inverse * (3^cut * h)) mod ?M =
      (inverse * (prefix_correction + 2^cut * rotated)) mod ?M"
    by (rule mod_mult_cong) (simp_all add: transport)
  show ?thesis using source multiplied by (simp add: mult.assoc)
qed

theorem antihydra_source_rotated_phase_minimum:
  assumes word: "antihydra_family_bits h (length suffix + length prefix) =
    suffix @ prefix"
  shows "antihydra_family_minimum h 0 (length suffix + length prefix) =
    min (sk_minprefix (skew_word suffix))
      (sk_delta (skew_word suffix) + sk_minprefix (skew_word prefix))"
  using word antihydra_arithmetic_block_ledger_projection(2)
    [of h "length suffix + length prefix"]
  by (simp add: antihydra_arithmetic_block_def skew_word_append skew_then_def)

text \<open>For the repeat prefilter, the centered source is inspected at
24 bits.  Transporting the omitted high part through the physical eight-step
orbit changes the endpoint by a multiple of 2^16.  The centered and physical
endpoint differences coincide because both coordinates translate by one.\<close>

lemma antihydra_repeat_low24_endpoint_mod16:
  "antihydra_family_orbit (d + 1) 8 mod 2^16 =
    antihydra_family_orbit (d mod 2^24 + 1) 8 mod 2^16"
proof -
  have decomposition:
    "d + 1 = (d mod 2^24 + 1) + 2^8 * (2^16 * (d div 2^24))"
    using div_mult_mod_eq[of d "2^24"] by (simp add: algebra_simps)
  have transported:
    "antihydra_family_orbit (d + 1) 8 =
      antihydra_family_orbit (d mod 2^24 + 1) 8 +
        3^8 * (2^16 * (d div 2^24))"
    using antihydra_family_orbit_cylinder_transport[
      of "d mod 2^24 + 1" 8 "2^16 * (d div 2^24)"] decomposition
    by simp
  have shift:
    "3^8 * (2^16 * (d div 2^24)) =
      (3^8 * (d div 2^24)) * 2^16"
    by (simp only: mult.assoc mult.commute mult.left_commute)
  show ?thesis by (simp only: transported shift mod_mult_self1)
qed

theorem antihydra_repeat_low24_difference_mod16:
  "(int (antihydra_family_orbit (d + 1) 8) - int (d + 1)) mod 2^16 =
    (int (antihydra_family_orbit (d mod 2^24 + 1) 8) -
      int (d mod 2^24 + 1)) mod 2^16"
proof -
  have reduced:
    "d mod 2^24 mod 2^16 = d mod 2^16"
    by (rule mod_mod_cancel) simp
  have source:
    "(d + 1) mod 2^16 = (d mod 2^24 + 1) mod 2^16"
    using mod_add_left_eq[of d "2^16" 1]
      mod_add_left_eq[of "d mod 2^24" "2^16" 1] reduced
    by metis
  have source_int:
    "int (d + 1) mod (2::int)^16 =
      int (d mod 2^24 + 1) mod (2::int)^16"
    using arg_cong[OF source, of int] by (simp add: zmod_int)
  have endpoint_int:
    "int (antihydra_family_orbit (d + 1) 8) mod (2::int)^16 =
      int (antihydra_family_orbit (d mod 2^24 + 1) 8) mod (2::int)^16"
    using arg_cong[OF antihydra_repeat_low24_endpoint_mod16[of d], of int]
    by (simp add: zmod_int)
  let ?x = "int (antihydra_family_orbit (d + 1) 8)"
  let ?y = "int (d + 1)"
  let ?x' = "int (antihydra_family_orbit (d mod 2^24 + 1) 8)"
  let ?y' = "int (d mod 2^24 + 1)"
  let ?m = "(2::int)^16"
  have "(?x - ?y) mod ?m = (?x mod ?m - ?y mod ?m) mod ?m"
    by (rule mod_diff_eq[symmetric])
  also have "... = (?x' mod ?m - ?y' mod ?m) mod ?m"
    by (simp only: source_int endpoint_int)
  also have "... = (?x' - ?y') mod ?m"
    by (rule mod_diff_eq)
  finally show ?thesis .
qed

lemma antihydra_repeat_affine_difference:
  fixes a b j x y z :: int
  assumes first: "b * y = a * x + j"
      and second: "b * z = a * y + j"
  shows "b * (z - y) = a * (y - x)"
  using first second by (simp add: algebra_simps)

lemma antihydra_repeat_prefix_extremes:
  fixes displacement minimum :: int
  shows "min minimum (minimum + displacement) =
    minimum + min 0 displacement"
  by (simp add: min_def)

fun antihydra_repeat_gain :: "nat \<Rightarrow> nat" where
  "antihydra_repeat_gain 0 = 0"
| "antihydra_repeat_gain (Suc r) =
    6561 * antihydra_repeat_gain r + 256^r"

lemma antihydra_repeat_gain_geometric:
  "6305 * antihydra_repeat_gain r + 256^r = 6561^r"
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have algebra_generic:
    "\<And>u v :: nat. 6305 * (6561 * u + v) + v * 256 =
      6561 * (6305 * u + v)"
    by (simp add: algebra_simps; linarith)
  have algebra:
    "6305 * (6561 * antihydra_repeat_gain r + 256^r) + 256^r * 256 =
      6561 * (6305 * antihydra_repeat_gain r + 256^r)"
    by (rule algebra_generic)
  have step:
    "6305 * (6561 * antihydra_repeat_gain r + 256^r) + 256^r * 256 =
      6561^r * 6561"
    using algebra Suc.IH by (simp only: mult.commute)
  show ?case using step
    by (simp only: antihydra_repeat_gain.simps power_Suc)
qed


fun antihydra_cyclic_repeat_gain :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_cyclic_repeat_gain atom 0 = 0"
| "antihydra_cyclic_repeat_gain atom (Suc r) =
    3^atom * antihydra_cyclic_repeat_gain atom r + (2^atom)^r"

theorem antihydra_cyclic_repeat_source_endpoint:
  assumes first: "antihydra_family_orbit h atom = h + (2^atom)^r * k"
  shows "antihydra_family_orbit h (atom * Suc r) =
    h + antihydra_cyclic_repeat_gain atom (Suc r) * k"
  using first
proof (induction r arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have first_previous:
    "antihydra_family_orbit h atom = h + (2^atom)^r * (2^atom * k)"
    using Suc.prems by (simp add: power_Suc algebra_simps)
  have previous:
    "antihydra_family_orbit h (atom * Suc r) =
      h + antihydra_cyclic_repeat_gain atom (Suc r) * (2^atom * k)"
    by (rule Suc.IH[OF first_previous])
  have transported:
    "antihydra_family_orbit (h + 2^atom * (antihydra_cyclic_repeat_gain atom (Suc r) * k)) atom =
      antihydra_family_orbit h atom + 3^atom * (antihydra_cyclic_repeat_gain atom (Suc r) * k)"
    by (rule antihydra_family_orbit_cylinder_transport)
  have composition:
    "antihydra_family_orbit h (atom * Suc (Suc r)) =
      antihydra_family_orbit (antihydra_family_orbit h (atom * Suc r)) atom"
    using antihydra_family_orbit_add[of h "atom * Suc r" atom]
    by (simp add: algebra_simps)
  show ?case
    using composition previous transported Suc.prems
    by (simp add: antihydra_cyclic_repeat_gain.simps algebra_simps)
qed

theorem antihydra_cyclic_repeat_partial_source:
  assumes first: "antihydra_family_orbit h atom = h + (2^atom)^r * k"
  defines "whole \<equiv> atom * Suc r"
    and "seam \<equiv> h + antihydra_cyclic_repeat_gain atom (Suc r) * k"
  shows "antihydra_family_orbit h (whole + tail) = antihydra_family_orbit seam tail"
    and "antihydra_family_balance h 0 (whole + tail) =
      antihydra_family_balance h 0 whole + antihydra_family_balance seam 0 tail"
    and "antihydra_family_minimum h 0 (whole + tail) =
      min (antihydra_family_minimum h 0 whole)
        (antihydra_family_balance h 0 whole + antihydra_family_minimum seam 0 tail)"
proof -
  have endpoint: "antihydra_family_orbit h whole = seam"
    unfolding whole_def seam_def
    by (rule antihydra_cyclic_repeat_source_endpoint[OF first])
  show "antihydra_family_orbit h (whole + tail) = antihydra_family_orbit seam tail"
    using antihydra_family_orbit_add[of h whole tail] endpoint by simp
  have bits: "antihydra_family_bits h (whole + tail) =
      antihydra_family_bits h whole @ antihydra_family_bits seam tail"
    using antihydra_family_bits_append[of h whole tail] endpoint by simp
  show "antihydra_family_balance h 0 (whole + tail) =
      antihydra_family_balance h 0 whole + antihydra_family_balance seam 0 tail"
    using bits by (simp add: antihydra_family_balance_def ledger_word_delta_append)
  show "antihydra_family_minimum h 0 (whole + tail) =
      min (antihydra_family_minimum h 0 whole)
        (antihydra_family_balance h 0 whole + antihydra_family_minimum seam 0 tail)"
    using bits by (simp add: antihydra_family_balance_def antihydra_family_minimum_def
        ledger_word_minprefix_append)
qed

lemma antihydra_eight_repeat_gain:
  "antihydra_cyclic_repeat_gain 8 r = antihydra_repeat_gain r"
  by (induction r) simp_all

theorem antihydra_repeat_source_endpoint:
  assumes first: "antihydra_family_orbit h 8 = h + 256^r * k"
  shows "antihydra_family_orbit h (8 * Suc r) =
    h + antihydra_repeat_gain (Suc r) * k"
  using antihydra_cyclic_repeat_source_endpoint[of h 8 r k] first
  by (simp only: antihydra_eight_repeat_gain; simp)

ML \<open>
  val checked = @{thms antihydra_binary_word_sum_is_one_count
    antihydra_fixed_source_leaf_fields
    antihydra_zero_source_leaf_fields
    antihydra_zero_cylinder_leaf_fields
    antihydra_exact_run_candidate_fields
    antihydra_exact_run_candidate_composes
    antihydra_rotated_phase_ordered_correction antihydra_rotated_source_guard_pullback
    antihydra_source_rotated_phase_minimum
    antihydra_repeat_low24_difference_mod16
    antihydra_repeat_affine_difference antihydra_repeat_prefix_extremes
    antihydra_repeat_gain_geometric antihydra_cyclic_repeat_source_endpoint
    antihydra_cyclic_repeat_partial_source
    antihydra_eight_repeat_gain antihydra_repeat_source_endpoint};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Antihydra exact run candidate refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Antihydra exact run candidate refinement proof" else ();
\<close>

end
