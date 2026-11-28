theory Double_Reverse_Birth_Low_Collar
  imports Double_Reverse_Temporal_Refinement.Double_Reverse_Four_Port_Numeric_Refinement
begin

lemma double_reverse_t2_stencil_word_length:
  "length (double_reverse_four_port_t2_stencil_word previous source) = length source"
  by (induction source arbitrary: previous) simp_all

lemma double_reverse_t2_stencil_word_selected:
  "double_reverse_four_port_t2_stencil_word previous
       (prefix @ [a,b,c] @ suffix) ! (length prefix + 1) =
    double_reverse_t2_digit a b c"
  by (induction prefix arbitrary: previous) simp_all

theorem double_reverse_birth_first_low_collar:
  fixes prefix suffix source :: "nat list" and a b c :: nat
  defines "source \<equiv> prefix @ [a,b,c] @ suffix"
  assumes canonical: "double_reverse_canonical_source source"
    and birth: "double_reverse_forward_out (double_reverse_four_port_row source 0 0) = 1"
  shows "rev (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) ! (length suffix + 2) =
    double_reverse_t2_digit a b c"
proof -
  have decimal: "list_all (\<lambda>d. d < 10) source"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have word: "double_reverse_four_port_closed_word (double_reverse_four_port_row source 0 0) =
    (if double_reverse_reverse_out (double_reverse_four_port_row source 0 0) = 1
      then [1] else []) @ double_reverse_four_port_t2_stencil_word 0 source @ [2]"
    using double_reverse_four_port_canonical_birth_word[OF canonical]
      double_reverse_four_port_stencil_radix5_selector[OF decimal, of 0] birth
    by simp
  have length: "length (double_reverse_four_port_t2_stencil_word 0 source) =
      length prefix + 3 + length suffix"
    by (simp add: source_def double_reverse_t2_stencil_word_length)
  have bound: "length suffix + 1 < length (double_reverse_four_port_t2_stencil_word 0 source)"
    using length by simp
  have index: "length (double_reverse_four_port_t2_stencil_word 0 source) -
      Suc (length suffix + 1) = length prefix + 1"
    using length by simp
  have selected: "rev (double_reverse_four_port_t2_stencil_word 0 source) !
      (length suffix + 1) = double_reverse_t2_digit a b c"
  proof -
    have reversed: "rev (double_reverse_four_port_t2_stencil_word 0 source) !
        (length suffix + 1) = double_reverse_four_port_t2_stencil_word 0 source !
          (length prefix + 1)"
      using rev_nth[OF bound] index by simp
    show ?thesis using reversed
      by (simp only: source_def double_reverse_t2_stencil_word_selected)
  qed
  show ?thesis
    using word selected bound by (simp add: nth_append)
qed

corollary double_reverse_birth_first_low_collar_physical:
  fixes prefix suffix source :: "nat list" and a b c :: nat
  assumes source: "source = prefix @ [a,b,c] @ suffix"
    and canonical: "double_reverse_canonical_source source"
    and birth: "double_reverse_forward_out (double_reverse_four_port_row source 0 0) = 1"
  shows "rev (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) ! (length suffix + 2) =
      double_reverse_t2_digit a b c \<and>
    double_reverse_msf_value (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
      double_reverse_T_run 2 (double_reverse_msf_value source)"
proof
  show "rev (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) ! (length suffix + 2) =
      double_reverse_t2_digit a b c"
    unfolding source
    by (rule double_reverse_birth_first_low_collar[where prefix=prefix and suffix=suffix])
       (use source canonical birth in simp_all)
  show "double_reverse_msf_value (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
      double_reverse_T_run 2 (double_reverse_msf_value source)"
    by (rule double_reverse_four_port_closed_word_numeric_t2[OF canonical])
qed

ML \<open>
  val checked = @{thms double_reverse_t2_stencil_word_length
    double_reverse_t2_stencil_word_selected double_reverse_birth_first_low_collar
    double_reverse_birth_first_low_collar_physical};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "birth low collar uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "birth low collar has skipped proofs" else ();
\<close>
end
