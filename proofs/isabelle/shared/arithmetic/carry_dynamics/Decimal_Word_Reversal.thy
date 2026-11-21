theory Decimal_Word_Reversal
  imports Reflected_Padded_Digit_Word Shared_Decimal_Reversal
begin

lemma decimal_lsd_value_append_digit:
  "decimal_lsd_value (digits @ [digit]) =
    decimal_lsd_value digits + 10 ^ length digits * digit"
  using decimal_lsd_value_append[of digits "[digit]"] by simp

lemma decimal_lsd_value_positive:
  assumes nonempty: "digits \<noteq> []" and high: "last digits > 0"
  shows "decimal_lsd_value digits > 0"
  using nonempty high
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have source_high: "last (digit # rest) > 0"
    using Cons.prems(2) .
  have rest_ih:
    "rest \<noteq> [] \<Longrightarrow> last rest > 0 \<Longrightarrow>
      decimal_lsd_value rest > 0"
    using Cons.IH .
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis using source_high by simp
  next
    case (Cons next_digit tail)
    have rest_nonempty: "rest \<noteq> []" using Cons by simp
    have rest_high: "last rest > 0" using source_high Cons by simp
    have rest_positive: "decimal_lsd_value rest > 0"
      by (rule rest_ih[OF rest_nonempty rest_high])
    show ?thesis using rest_positive by simp
  qed
qed

lemma decimal_word_split:
  fixes q r :: nat
  assumes r_small: "r < 10"
  shows "(10 * q + r) div 10 = q"
    and "(10 * q + r) mod 10 = r"
  using r_small
  by (simp_all add: div_add1_eq mod_add_left_eq mult.commute)

lemma decimal_word_digits_shift:
  fixes digit q :: nat
  assumes digit_bound: "digit < 10" and q_positive: "q > 0"
  shows "decimal_digit_count (digit + 10 * q) =
    Suc (decimal_digit_count q)"
proof -
  have quotient_remainder:
    "(digit + 10 * q) div 10 = q"
    "(digit + 10 * q) mod 10 = digit"
    using decimal_word_split
      [where q=q and r=digit, OF digit_bound]
    by (simp_all add: add.commute)
  have at_least_ten: "digit + 10 * q \<ge> 10"
    using digit_bound q_positive by arith
  show ?thesis
    using quotient_remainder(1) at_least_ten
    by (simp add: decimal_digit_count.simps)
qed

lemma decimal_word_digits_lsd_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
      and nonempty: "digits \<noteq> []"
      and high: "last digits > 0"
  shows "decimal_digit_count
      (decimal_lsd_value digits) = length digits"
  using decimal nonempty high
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have rest_decimal: "list_all (\<lambda>item. item < 10) rest"
    using Cons.prems(1) by simp
  have source_high: "last (digit # rest) > 0"
    using Cons.prems(3) .
  have rest_ih:
    "list_all (\<lambda>item. item < 10) rest \<Longrightarrow>
      rest \<noteq> [] \<Longrightarrow> last rest > 0 \<Longrightarrow>
      decimal_digit_count (decimal_lsd_value rest) =
        length rest"
    using Cons.IH .
  show ?case
  proof (cases rest)
    case Nil
    have digit_positive: "digit > 0" using source_high Nil by simp
    show ?thesis using digit_bound digit_positive Nil by simp
  next
    case (Cons next_digit tail)
    have rest_nonempty: "rest \<noteq> []" using Cons by simp
    have rest_high: "last rest > 0" using source_high Cons by simp
    have rest_positive: "decimal_lsd_value rest > 0"
      by (rule decimal_lsd_value_positive[OF rest_nonempty rest_high])
    have tail_digits:
      "decimal_digit_count (decimal_lsd_value rest) = length rest"
      by (rule rest_ih[OF rest_decimal rest_nonempty rest_high])
    have shifted:
      "decimal_digit_count
        (digit + 10 * decimal_lsd_value rest) =
       Suc (decimal_digit_count (decimal_lsd_value rest))"
      by (rule decimal_word_digits_shift[OF digit_bound rest_positive])
    show ?thesis using shifted tail_digits by simp
  qed
qed

lemma decimal_reverse_lsd_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
      and nonempty: "digits \<noteq> []"
      and high: "last digits > 0"
  shows "decimal_reverse (decimal_lsd_value digits) =
    decimal_lsd_value (rev digits)"
  using decimal nonempty high
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have rest_decimal: "list_all (\<lambda>item. item < 10) rest"
    using Cons.prems(1) by simp
  have source_high: "last (digit # rest) > 0"
    using Cons.prems(3) .
  have rest_ih:
    "list_all (\<lambda>item. item < 10) rest \<Longrightarrow>
      rest \<noteq> [] \<Longrightarrow> last rest > 0 \<Longrightarrow>
      decimal_reverse (decimal_lsd_value rest) =
        decimal_lsd_value (rev rest)"
    using Cons.IH .
  show ?case
  proof (cases rest)
    case Nil
    have digit_positive: "digit > 0" using source_high Nil by simp
    show ?thesis using digit_bound digit_positive Nil by simp
  next
    case (Cons next_digit tail)
    have rest_nonempty: "rest \<noteq> []" using Cons by simp
    have rest_high: "last rest > 0" using source_high Cons by simp
    have rest_positive: "decimal_lsd_value rest > 0"
      by (rule decimal_lsd_value_positive[OF rest_nonempty rest_high])
    have rest_reverse:
      "decimal_reverse (decimal_lsd_value rest) =
        decimal_lsd_value (rev rest)"
      by (rule rest_ih[OF rest_decimal rest_nonempty rest_high])
    have rest_digits:
      "decimal_digit_count (decimal_lsd_value rest) = length rest"
      by (rule decimal_word_digits_lsd_value
        [OF rest_decimal rest_nonempty rest_high])
    have number_split:
      "decimal_lsd_value (digit # rest) =
        digit + 10 * decimal_lsd_value rest"
      by simp
    have quotient_remainder:
      "(digit + 10 * decimal_lsd_value rest) div 10 =
          decimal_lsd_value rest"
      "(digit + 10 * decimal_lsd_value rest) mod 10 = digit"
      using decimal_word_split
        [where q="decimal_lsd_value rest" and r=digit,
          OF digit_bound]
      by (simp_all add: add.commute)
    have value_large:
      "digit + 10 * decimal_lsd_value rest \<ge> 10"
      using rest_positive by arith
    have shifted_digits:
      "decimal_digit_count
        (digit + 10 * decimal_lsd_value rest) =
       Suc (decimal_digit_count (decimal_lsd_value rest))"
      by (rule decimal_word_digits_shift[OF digit_bound rest_positive])
    have reverse_step:
      "decimal_reverse
          (digit + 10 * decimal_lsd_value rest) =
        digit * 10 ^ decimal_digit_count
          (decimal_lsd_value rest) +
        decimal_reverse (decimal_lsd_value rest)"
    proof -
      have equation:
        "decimal_reverse
            (digit + 10 * decimal_lsd_value rest) =
          (if digit + 10 * decimal_lsd_value rest < 10
           then digit + 10 * decimal_lsd_value rest
           else (digit + 10 * decimal_lsd_value rest) mod 10 *
             10 ^ (decimal_digit_count
               (digit + 10 * decimal_lsd_value rest) - 1) +
             decimal_reverse
               ((digit + 10 * decimal_lsd_value rest) div 10))"
        by (rule decimal_reverse.simps)
      have not_less:
        "\<not> digit + 10 * decimal_lsd_value rest < 10"
        using value_large by arith
      show ?thesis
        using equation not_less quotient_remainder shifted_digits
        by (simp del: decimal_reverse.simps)
    qed
    show ?thesis
      using number_split rest_reverse rest_digits reverse_step
      by (simp add: decimal_lsd_value_append_digit algebra_simps)
  qed
qed

end
