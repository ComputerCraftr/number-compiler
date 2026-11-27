theory Reflected_E_Word
  imports Reflected_M_Word
begin

text \<open>The finite E word is the reverse of the padded product of the
reversed input. Its exact source-index map includes the high carry column.\<close>

lemma reflected_padded_multiply_length:
  "length (reflected_padded_multiply multiplier source) = Suc (length source)"
  by (simp add: reflected_padded_multiply_def Let_def
      reflected_digit_pass_length split: prod.splits)

theorem reflected_padded_E_source_index:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_source (reflected_padded_E multiplier source) i =
    (if i < Suc (length source) then
      reflected_M_digit multiplier (reflected_padded_source (rev source))
        (length source - i)
     else 0)"
proof -
  have reversed: "list_all (\<lambda>digit. digit < 10) (rev source)"
    using digits by simp
  have projected:
    "reflected_padded_source (reflected_padded_multiply multiplier (rev source))
        (length source - i) =
      reflected_M_digit multiplier (reflected_padded_source (rev source))
        (length source - i)"
    by (rule reflected_padded_multiply_M_source[OF multiplier reversed])
  show ?thesis
  proof (cases "i < Suc (length source)")
    case True
    then have inside: "length source - i <
        length (reflected_padded_multiply multiplier (rev source))"
      by (simp add: reflected_padded_multiply_length)
    show ?thesis using True inside projected
      by (simp add: reflected_padded_E_def reflected_padded_source_def
          reflected_padded_multiply_length rev_nth)
  next
    case False
    then show ?thesis
      by (simp add: reflected_padded_E_def reflected_padded_source_def
          reflected_padded_multiply_length)
  qed
qed

theorem reflected_padded_E_interior_digit:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
    and lower: "0 < i" and upper: "i < length source"
  shows "reflected_padded_source (reflected_padded_E multiplier source) i =
    reflected_E_digit multiplier (reflected_padded_source source) i"
proof -
  let ?n = "length source"
  have inside: "i < Suc ?n" using upper by simp
  have current_inside: "?n - i < ?n" using lower upper by arith
  have previous_inside: "?n - i - 1 < ?n" using lower upper by arith
  have output_inside: "i - 1 < ?n" using lower upper by arith
  have current_index: "?n - Suc (?n - i) = i - 1" using lower upper by arith
  have previous_index: "?n - Suc (?n - i - 1) = i" using lower upper by arith
  have positive: "?n - i \<noteq> 0" using upper by arith
  have current:
    "reflected_padded_source (rev source) (?n - i) =
      reflected_padded_source source (i - 1)"
    using current_inside output_inside lower upper current_index
    by (simp add: reflected_padded_source_def rev_nth)
  have previous:
    "reflected_padded_source (rev source) (?n - i - 1) =
      reflected_padded_source source i"
    using previous_inside upper previous_index
    by (simp add: reflected_padded_source_def rev_nth)
  have not_zero: "i \<noteq> 0" using lower by arith
  have index_eq: "?n - Suc i = ?n - i - 1" using upper by arith
  have previous_suc:
    "reflected_padded_source (rev source) (?n - Suc i) =
      reflected_padded_source source i"
    using previous by (simp only: index_eq)
  have left:
    "reflected_padded_source (reflected_padded_E multiplier source) i =
      multiplier * (reflected_padded_source source (i - 1) mod (10 div multiplier)) +
        reflected_padded_source source i div (10 div multiplier)"
    using reflected_padded_E_source_index[OF multiplier digits, of i]
    by (simp only: if_P[OF inside] reflected_M_digit_def reflected_previous_def
        if_not_P[OF positive] current previous)
  have right:
    "reflected_E_digit multiplier (reflected_padded_source source) i =
      reflected_padded_source source i div (10 div multiplier) +
        multiplier * (reflected_padded_source source (i - 1) mod (10 div multiplier))"
    by (simp only: reflected_E_digit_def reflected_previous_def if_not_P[OF not_zero])
  show ?thesis using left right by (simp only: add.commute)
qed

theorem reflected_padded_E_source_digit:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_source (reflected_padded_E multiplier source) i =
    reflected_E_digit multiplier (reflected_padded_source source) i"
proof (cases "source = []")
  case True
  then show ?thesis
    by (cases i) (simp_all add: reflected_padded_E_def reflected_padded_multiply_def
        reflected_padded_source_def reflected_E_digit_def reflected_previous_def Let_def)
next
  case False
  let ?n = "length source"
  have positive: "0 < ?n" using False by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have last: "reflected_padded_source (rev source) (?n - 1) =
        reflected_padded_source source 0"
      using positive by (simp add: reflected_padded_source_def rev_nth)
    show ?thesis
      using reflected_padded_E_source_index[OF multiplier digits, of 0] True positive last
      by (simp add: reflected_M_digit_def reflected_E_digit_def
          reflected_previous_def reflected_padded_source_def)
  next
    case False
    show ?thesis
    proof (cases "i < ?n")
      case True
      show ?thesis by (rule reflected_padded_E_interior_digit[OF multiplier digits _ True])
        (use False in arith)
    next
      case False
      note not_inside = False
      show ?thesis
      proof (cases "i = ?n")
        case True
        have first: "reflected_padded_source (rev source) 0 =
            reflected_padded_source source (?n - 1)"
          using positive by (simp add: reflected_padded_source_def rev_nth)
        show ?thesis
          using reflected_padded_E_source_index[OF multiplier digits, of i]
            True False positive first
          by (simp add: reflected_M_digit_def reflected_E_digit_def
              reflected_previous_def reflected_padded_source_def)
      next
        case False
        have beyond: "?n < i" using not_inside False by arith
        have predecessor: "?n \<le> i - 1" using beyond by arith
        then show ?thesis
          using reflected_padded_E_source_index[OF multiplier digits, of i]
            beyond
          by (simp add: reflected_E_digit_def reflected_previous_def
              reflected_padded_source_def)
      qed
    qed
  qed
qed

theorem reflected_padded_H_source_digit:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_source (reflected_padded_H multiplier source) i =
    reflected_H_digit multiplier (reflected_padded_source source) i"
proof -
  have product_digits:
    "list_all (\<lambda>digit. digit < 10) (reflected_padded_multiply multiplier source)"
    by (rule reflected_padded_multiply_decimal[OF multiplier digits])
  have product_source:
    "reflected_padded_source (reflected_padded_multiply multiplier source) =
      reflected_M_digit multiplier (reflected_padded_source source)"
    by (rule ext) (rule reflected_padded_multiply_M_source[OF multiplier digits])
  show ?thesis
    unfolding reflected_padded_H_def reflected_H_digit_def
    using reflected_padded_E_source_digit[OF multiplier product_digits, of i]
      product_source by simp
qed

theorem reflected_padded_H_iter_source_digit:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_source (reflected_padded_H_iter multiplier steps source) i =
    reflected_H_digit_iter multiplier steps (reflected_padded_source source) i"
proof (induction steps arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have iter_digits: "list_all (\<lambda>digit. digit < 10)
      (reflected_padded_H_iter multiplier steps source)"
    by (rule reflected_padded_H_iter_decimal[OF multiplier digits])
  have iter_source:
    "reflected_padded_source (reflected_padded_H_iter multiplier steps source) =
      reflected_H_digit_iter multiplier steps (reflected_padded_source source)"
    by (rule ext) (rule Suc.IH)
  show ?case
    using reflected_padded_H_source_digit[OF multiplier iter_digits, of i] iter_source
    by simp
qed

corollary reflected_padded_H_dyadic_source_window:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
    and halo: "i + 2 ^ order < cell"
  shows "overlap_recursive order (reflected_pair_action multiplier)
      (\<lambda>j. reflected_pair_at (reflected_padded_source source) (cell - j)) i =
    (reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * (cell - i)),
     reflected_padded_source (reflected_padded_H_iter multiplier (2 ^ order) source)
       (2 * (cell - i) + 1))"
proof -
  have window:
    "overlap_recursive order (reflected_pair_action multiplier)
        (\<lambda>j. reflected_pair_at (reflected_padded_source source) (cell - j)) i =
      (reflected_H_digit_iter multiplier (2 ^ order) (reflected_padded_source source)
         (2 * (cell - i)),
       reflected_H_digit_iter multiplier (2 ^ order) (reflected_padded_source source)
         (2 * (cell - i) + 1))"
    by (rule reflected_H_dyadic_source_window[OF halo])
  show ?thesis using window reflected_padded_H_iter_source_digit[OF multiplier digits]
    by simp
qed

theorem reflected_padded_relative_H_interior:
  fixes a b shift i :: int
  assumes m: "m = 2 \<or> m = 5" and digits: "list_all (\<lambda>d. d < 10) source"
    and base: "0 \<le> a" and shift: "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two (reflected_source_two_gate m)
        (\<lambda>k. reflected_padded_source source (nat k)) j =
      reflected_padded_source source (nat (j - shift))"
    and bounds: "a + 2 * int n \<le> i" "i < b"
  shows "reflected_padded_source (reflected_padded_H_iter m n source) (nat i) =
    reflected_padded_source source (nat (i - int n * shift))"
  using reflected_padded_H_iter_source_digit[OF m digits, of n "nat i"]
    reflected_source_relative_H_interior[OF base shift returns bounds] by simp

ML \<open>
  val checked = @{thms reflected_padded_multiply_length reflected_padded_E_source_index
    reflected_padded_E_interior_digit reflected_padded_E_source_digit
    reflected_padded_H_source_digit reflected_padded_H_iter_source_digit
    reflected_padded_relative_H_interior
    reflected_padded_H_dyadic_source_window};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected E index proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected E index proof" else ();
\<close>

end
