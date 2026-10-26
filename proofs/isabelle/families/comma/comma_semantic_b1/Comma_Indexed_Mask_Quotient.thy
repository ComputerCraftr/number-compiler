theory Comma_Indexed_Mask_Quotient
  imports Comma_Semantic_Graph_Phase_Fold
begin

lemma comma_indexed_phase_union_class_fold:
  "comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) words =
    comma_mask_union (map (\<lambda>(slot,bits).
      comma_phase_class period 0 slot AND bits)
      (zip [0..<length words] words))"
  unfolding comma_indexed_phase_union_def
  by (simp add: comma_phase_class_def)

text \<open>
An indexed phase union with one repeated row is exactly that row restricted
to the authenticated 924-phase domain.  The local-period rows are only a
partition of the phase guard; they do not create distinct observer values.
\<close>

lemma comma_indexed_phase_union_constant_rows:
  assumes positive: "0 < period"
    and length: "length words = period"
    and uniform_rows: "list_all (\<lambda>word. word = bits) words"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period = slot) words =
    take_bit 924 bits"
proof (rule bit_eqI)
  fix r
  show "bit (comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period = slot) words) r =
    bit (take_bit 924 bits) r"
  proof (cases "r < 924")
    case True
    let ?slot = "r mod period"
    have slot_bound: "?slot < length words"
      using positive length by simp
    have slot_member: "words ! ?slot \<in> set words"
      by (rule nth_mem[OF slot_bound])
    have selected_word: "words ! ?slot = bits"
      using uniform_rows slot_member by (simp add: list_all_iff)
    have selected:
      "comma_phase_member
          (comma_indexed_phase_union
            (\<lambda>slot phase. phase mod period = slot) words) r =
        comma_phase_member (words ! ?slot) r"
      by (rule comma_indexed_phase_union_select[OF positive length])
    have union_bit: "bit (comma_indexed_phase_union
        (\<lambda>slot phase. phase mod period = slot) words) r = bit bits r"
      using selected selected_word True
      by (simp add: comma_phase_member_def)
    have truncated_bit: "bit (take_bit 924 bits) r = bit bits r"
      using True by (simp add: bit_take_bit_iff)
    show ?thesis using union_bit truncated_bit by simp
  next
    case False
    then show ?thesis
      by (auto simp: comma_indexed_phase_union_def comma_mask_union_bit
          comma_phase_class_def comma_phase_mask_bit bit_take_bit_iff bit_simps)
  qed
qed

ML \<open>
  val indexed_mask_rules = @{thms comma_indexed_phase_union_class_fold
    comma_indexed_phase_union_constant_rows};
  Thm.consolidate indexed_mask_rules;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Indexed phase-mask quotient" indexed_mask_rules;
\<close>

end
