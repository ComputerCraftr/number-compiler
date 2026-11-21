theory Double_Reverse_C0_Physical_Palindrome
  imports Double_Reverse_Mixed_Adic_Quotient
begin

text \<open>The mixed-adic physical run theorem obtains each successor from the
actual decimal forward pass and its one inward carry. Its source premise is
the canonical physical word and its source-issued closed border.\<close>

lemma double_reverse_closed_word_nonpalindrome:
  assumes canonical: "double_reverse_canonical_source word"
      and long: "4 \<le> length word"
      and admitted: "double_reverse_word_border word \<in> double_reverse_closed_border"
  shows "decimal_reverse (double_reverse_msf_value word) \<noteq>
    double_reverse_msf_value word"
proof -
  obtain a b interior y z where shape: "word = [a,b] @ interior @ [y,z]"
    by (rule double_reverse_word_four_split[OF long]) blast
  have border: "double_reverse_word_border word = (a,b,y,z)"
    by (simp add: double_reverse_word_border_def shape)
  have unequal: "a \<noteq> z"
    using double_reverse_closed_border_unequal_ends[of a b y z] admitted border by simp
  have decimal: "list_all (\<lambda>d. d < 10) (rev word)"
    using canonical by (simp add: double_reverse_canonical_source_def)
  have nonempty: "rev word \<noteq> []" using long by auto
  have high: "last (rev word) > 0"
    using canonical by (simp add: double_reverse_canonical_source_def last_rev)
  have reverse_value:
    "decimal_reverse (double_reverse_msf_value word) = double_reverse_lsf_value word"
    using double_reverse_reverse10_lsf_value[OF decimal nonempty high]
    by (simp add: double_reverse_msf_value_def)
  have digits: "a < 10" "z < 10"
    using canonical shape by (auto simp: double_reverse_canonical_source_def list_all_iff)
  have reverse_last: "decimal_reverse (double_reverse_msf_value word) mod 10 = a"
  proof -
    have "decimal_reverse (double_reverse_msf_value word) mod 10 =
        double_reverse_lsf_value word mod 10"
      using reverse_value by simp
    also have "... = a"
    proof -
      have value_eq: "double_reverse_lsf_value word =
          a + 10 * double_reverse_lsf_value (b # interior @ [y,z])"
        by (simp only: shape append_Cons append_Nil double_reverse_lsf_value.simps)
      show ?thesis
        using double_reverse_decimal_split(2)
          [where q="double_reverse_lsf_value (b # interior @ [y,z])" and r=a,
            OF digits(1)]
        by (simp only: value_eq add.commute)
    qed
    finally show ?thesis .
  qed
  have original_last: "double_reverse_msf_value word mod 10 = z"
  proof -
    have last_shape: "word = ([a,b] @ interior @ [y]) @ [z]"
      using shape by simp
    show ?thesis using digits(2)
      by (simp only: last_shape double_reverse_msf_value_append_digit)
         simp
  qed
  show ?thesis using unequal reverse_last original_last by metis
qed

theorem double_reverse_c0_physical_palindrome_absence:
  assumes canonical: "double_reverse_canonical_source source"
      and long: "4 \<le> length source"
      and admitted: "double_reverse_word_border source \<in> double_reverse_closed_border"
  shows "decimal_reverse (double_reverse_T_run ticks (double_reverse_msf_value source))
    \<noteq> double_reverse_T_run ticks (double_reverse_msf_value source)"
proof -
  obtain final where final:
    "double_reverse_canonical_source final"
    "4 \<le> length final"
    "double_reverse_word_border final \<in> double_reverse_closed_border"
    "double_reverse_msf_value final = double_reverse_T_run ticks (double_reverse_msf_value source)"
    using double_reverse_mixed_adic_physical_run[OF canonical long admitted, of ticks]
    by blast
  show ?thesis using double_reverse_closed_word_nonpalindrome[OF final(1-3)] final(4)
    by simp
qed

end
