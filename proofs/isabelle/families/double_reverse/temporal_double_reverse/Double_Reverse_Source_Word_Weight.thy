theory Double_Reverse_Source_Word_Weight
  imports Double_Reverse_Four_Port_Numeric_Refinement
begin

text \<open>The weight is the scalar decimal value of the exact source word.
It is the increment of A-B over one even-normalized T-squared step. This
does not assert a polynomial-valued accumulator recurrence, a temporal
period, or that a supplied list of source words is a physical trajectory.\<close>

definition double_reverse_normalized_middle :: "nat \<Rightarrow> nat" where
  "double_reverse_normalized_middle source =
    double_reverse_reverse10 (double_reverse_T source)"

definition double_reverse_accumulator_pair_step ::
    "nat \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "double_reverse_accumulator_pair_step source accumulators =
    (let middle = int (double_reverse_normalized_middle source)
     in (fst accumulators + middle, snd accumulators + middle - int source))"

lemma double_reverse_normalized_middle_endpoint:
  "double_reverse_T_run 2 source =
    2 * double_reverse_normalized_middle source"
  by (simp add: double_reverse_T_run_def numeral_2_eq_2
      double_reverse_T_def double_reverse_normalized_middle_def)

lemma double_reverse_accumulator_source_increment:
  "fst (double_reverse_accumulator_pair_step source accumulators) -
      snd (double_reverse_accumulator_pair_step source accumulators) =
    fst accumulators - snd accumulators + int source"
  by (simp add: double_reverse_accumulator_pair_step_def Let_def algebra_simps)

lemma double_reverse_accumulator_source_sum:
  assumes source: "fst accumulators + snd accumulators = int source"
  shows "fst (double_reverse_accumulator_pair_step source accumulators) +
      snd (double_reverse_accumulator_pair_step source accumulators) =
    int (double_reverse_T_run 2 source)"
  using source
  by (simp add: double_reverse_accumulator_pair_step_def Let_def
      double_reverse_normalized_middle_endpoint; linarith)

theorem double_reverse_four_port_source_weight_refines:
  assumes canonical: "double_reverse_canonical_source source"
      and source_sum: "fst accumulators + snd accumulators =
        int (double_reverse_msf_value source)"
  defines "result \<equiv> double_reverse_accumulator_pair_step
    (double_reverse_msf_value source) accumulators"
  shows "fst result + snd result =
      int (double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0)))"
    and "fst result - snd result =
      fst accumulators - snd accumulators + int (double_reverse_msf_value source)"
proof -
  have endpoint:
    "double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0)) =
      double_reverse_T_run 2 (double_reverse_msf_value source)"
    by (rule double_reverse_four_port_closed_word_numeric_t2[OF canonical])
  show "fst result + snd result =
      int (double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0)))"
    unfolding result_def
    using double_reverse_accumulator_source_sum[OF source_sum] endpoint by simp
  show "fst result - snd result =
      fst accumulators - snd accumulators + int (double_reverse_msf_value source)"
    unfolding result_def by (rule double_reverse_accumulator_source_increment)
qed

fun double_reverse_source_weight_run :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_source_weight_run 0 source = 0"
| "double_reverse_source_weight_run (Suc n) source =
    int source + double_reverse_source_weight_run n (double_reverse_T_run 2 source)"

fun double_reverse_accumulator_pair_run ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "double_reverse_accumulator_pair_run 0 source accumulators = accumulators"
| "double_reverse_accumulator_pair_run (Suc n) source accumulators =
    double_reverse_accumulator_pair_run n (double_reverse_T_run 2 source)
      (double_reverse_accumulator_pair_step source accumulators)"

theorem double_reverse_source_weight_run_exact:
  "fst (double_reverse_accumulator_pair_run n source accumulators) -
      snd (double_reverse_accumulator_pair_run n source accumulators) =
    fst accumulators - snd accumulators + double_reverse_source_weight_run n source"
proof (induction n arbitrary: source accumulators)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note ih = Suc.IH[of "double_reverse_T_run 2 source"
    "double_reverse_accumulator_pair_step source accumulators"]
  show ?case
    using ih double_reverse_accumulator_source_increment[of source accumulators]
    by (simp only: double_reverse_accumulator_pair_run.simps
        double_reverse_source_weight_run.simps; linarith)
qed

lemma double_reverse_source_weight_chronological_join:
  "double_reverse_source_weight_run (n + m) source =
    double_reverse_source_weight_run n source +
      double_reverse_source_weight_run m ((double_reverse_T_run 2 ^^ n) source)"
  by (induction n arbitrary: source)
    (simp_all add: funpow_Suc_right funpow_swap1 algebra_simps)

lemma double_reverse_source_word_weight_append:
  "int (double_reverse_msf_value (left @ right)) =
    int (10 ^ length right) * int (double_reverse_msf_value left) +
      int (double_reverse_msf_value right)"
  by (simp add: double_reverse_msf_value_append)

text \<open>Trailing-zero contraction preserves the endpoint but changes this
source weight. An accumulator consumer must retain its actual source word;
the normalized four-port input cannot silently replace that occurrence.\<close>

lemma double_reverse_source_weight_not_trailing_zero_invariant:
  assumes positive: "source > 0"
  shows "double_reverse_T_run 2 (10 * source) = double_reverse_T_run 2 source"
    and "double_reverse_source_weight_run 1 (10 * source) \<noteq>
      double_reverse_source_weight_run 1 source"
proof -
  show "double_reverse_T_run 2 (10 * source) = double_reverse_T_run 2 source"
    by (simp add: double_reverse_T_run_def numeral_2_eq_2
        double_reverse_T_ignores_trailing_zero)
  show "double_reverse_source_weight_run 1 (10 * source) \<noteq>
      double_reverse_source_weight_run 1 source"
    using positive by simp
qed

ML \<open>
  val checked = @{thms double_reverse_four_port_source_weight_refines
    double_reverse_source_weight_run_exact
    double_reverse_source_weight_chronological_join
    double_reverse_source_word_weight_append
    double_reverse_source_weight_not_trailing_zero_invariant};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source-word weight refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped source-word weight refinement proof" else ();
\<close>

end
