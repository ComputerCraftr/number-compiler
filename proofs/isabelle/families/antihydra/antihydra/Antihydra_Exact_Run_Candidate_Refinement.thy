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

ML \<open>
  val checked = @{thms antihydra_binary_word_sum_is_one_count
    antihydra_exact_run_candidate_fields
    antihydra_exact_run_candidate_composes};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Antihydra exact run candidate refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Antihydra exact run candidate refinement proof" else ();
\<close>

end
