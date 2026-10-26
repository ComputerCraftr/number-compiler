theory Double_Reverse_Four_Port_Numeric_Refinement
  imports Double_Reverse_Group_Ring_Four_Port
begin

text \<open>This theory connects one canonical, finite four-port source action to
its exact integer \(T^2\) endpoint. It handles the intermediate decimal
normalization and outer carry digits, but establishes no temporal period or
future closure.\<close>

fun double_reverse_lsf_value :: "nat list \<Rightarrow> nat" where
  "double_reverse_lsf_value [] = 0"
| "double_reverse_lsf_value (digit # digits) =
    digit + 10 * double_reverse_lsf_value digits"

definition double_reverse_msf_value :: "nat list \<Rightarrow> nat" where
  "double_reverse_msf_value digits =
    double_reverse_lsf_value (rev digits)"

lemma double_reverse_lsf_value_append:
  "double_reverse_lsf_value (left @ right) =
    double_reverse_lsf_value left +
      10 ^ length left * double_reverse_lsf_value right"
  by (induction left)
    (simp_all add: algebra_simps power_Suc)

lemma double_reverse_lsf_value_append_digit:
  "double_reverse_lsf_value (digits @ [digit]) =
    double_reverse_lsf_value digits + 10 ^ length digits * digit"
  using double_reverse_lsf_value_append[of digits "[digit]"] by simp

lemma double_reverse_msf_value_append:
  "double_reverse_msf_value (left @ right) =
    10 ^ length right * double_reverse_msf_value left +
      double_reverse_msf_value right"
  unfolding double_reverse_msf_value_def
  by (simp add: double_reverse_lsf_value_append algebra_simps)

lemma double_reverse_msf_value_empty:
  "double_reverse_msf_value [] = 0"
  unfolding double_reverse_msf_value_def by simp

lemma double_reverse_msf_value_singleton:
  "double_reverse_msf_value [digit] = digit"
  unfolding double_reverse_msf_value_def by simp

lemma double_reverse_msf_value_append_digit:
  "double_reverse_msf_value (digits @ [digit]) =
    10 * double_reverse_msf_value digits + digit"
  by (simp add: double_reverse_msf_value_append
      double_reverse_msf_value_singleton)

lemma double_reverse_msf_value_leading_zero:
  "double_reverse_msf_value (0 # digits) =
    double_reverse_msf_value digits"
  by (simp add: double_reverse_msf_value_def
      double_reverse_lsf_value_append_digit)

lemma double_reverse_lsf_value_positive:
  assumes nonempty: "digits \<noteq> []" and high: "last digits > 0"
  shows "double_reverse_lsf_value digits > 0"
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
      double_reverse_lsf_value rest > 0"
    using Cons.IH .
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis using source_high by simp
  next
    case (Cons next_digit tail)
    have rest_nonempty: "rest \<noteq> []" using Cons by simp
    have rest_high: "last rest > 0" using source_high Cons by simp
    have rest_positive: "double_reverse_lsf_value rest > 0"
      by (rule rest_ih[OF rest_nonempty rest_high])
    show ?thesis using rest_positive by simp
  qed
qed

lemma double_reverse_decimal_split:
  fixes q r :: nat
  assumes r_small: "r < 10"
  shows "(10 * q + r) div 10 = q"
    and "(10 * q + r) mod 10 = r"
  using r_small
  by (simp_all add: div_add1_eq mod_add_left_eq mult.commute)

lemma double_reverse_decimal_digits_shift:
  fixes digit q :: nat
  assumes digit_bound: "digit < 10" and q_positive: "q > 0"
  shows "double_reverse_decimal_digits (digit + 10 * q) =
    Suc (double_reverse_decimal_digits q)"
proof -
  have quotient_remainder:
    "(digit + 10 * q) div 10 = q"
    "(digit + 10 * q) mod 10 = digit"
    using double_reverse_decimal_split
      [where q=q and r=digit, OF digit_bound]
    by (simp_all add: add.commute)
  have at_least_ten: "digit + 10 * q \<ge> 10"
    using digit_bound q_positive by arith
  show ?thesis
    using quotient_remainder(1) at_least_ten
    by (simp add: double_reverse_decimal_digits.simps)
qed

lemma double_reverse_decimal_digits_lsf_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
      and nonempty: "digits \<noteq> []"
      and high: "last digits > 0"
  shows "double_reverse_decimal_digits
      (double_reverse_lsf_value digits) = length digits"
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
      double_reverse_decimal_digits (double_reverse_lsf_value rest) =
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
    have rest_positive: "double_reverse_lsf_value rest > 0"
      by (rule double_reverse_lsf_value_positive[OF rest_nonempty rest_high])
    have tail_digits:
      "double_reverse_decimal_digits (double_reverse_lsf_value rest) = length rest"
      by (rule rest_ih[OF rest_decimal rest_nonempty rest_high])
    have shifted:
      "double_reverse_decimal_digits
        (digit + 10 * double_reverse_lsf_value rest) =
       Suc (double_reverse_decimal_digits (double_reverse_lsf_value rest))"
      by (rule double_reverse_decimal_digits_shift[OF digit_bound rest_positive])
    show ?thesis using shifted tail_digits by simp
  qed
qed

lemma double_reverse_reverse10_lsf_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
      and nonempty: "digits \<noteq> []"
      and high: "last digits > 0"
  shows "double_reverse_reverse10 (double_reverse_lsf_value digits) =
    double_reverse_lsf_value (rev digits)"
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
      double_reverse_reverse10 (double_reverse_lsf_value rest) =
        double_reverse_lsf_value (rev rest)"
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
    have rest_positive: "double_reverse_lsf_value rest > 0"
      by (rule double_reverse_lsf_value_positive[OF rest_nonempty rest_high])
    have rest_reverse:
      "double_reverse_reverse10 (double_reverse_lsf_value rest) =
        double_reverse_lsf_value (rev rest)"
      by (rule rest_ih[OF rest_decimal rest_nonempty rest_high])
    have rest_digits:
      "double_reverse_decimal_digits (double_reverse_lsf_value rest) = length rest"
      by (rule double_reverse_decimal_digits_lsf_value
        [OF rest_decimal rest_nonempty rest_high])
    have number_split:
      "double_reverse_lsf_value (digit # rest) =
        digit + 10 * double_reverse_lsf_value rest"
      by simp
    have quotient_remainder:
      "(digit + 10 * double_reverse_lsf_value rest) div 10 =
          double_reverse_lsf_value rest"
      "(digit + 10 * double_reverse_lsf_value rest) mod 10 = digit"
      using double_reverse_decimal_split
        [where q="double_reverse_lsf_value rest" and r=digit,
          OF digit_bound]
      by (simp_all add: add.commute)
    have value_large:
      "digit + 10 * double_reverse_lsf_value rest \<ge> 10"
      using rest_positive by arith
    have shifted_digits:
      "double_reverse_decimal_digits
        (digit + 10 * double_reverse_lsf_value rest) =
       Suc (double_reverse_decimal_digits (double_reverse_lsf_value rest))"
      by (rule double_reverse_decimal_digits_shift[OF digit_bound rest_positive])
    have reverse_step:
      "double_reverse_reverse10
          (digit + 10 * double_reverse_lsf_value rest) =
        digit * 10 ^ double_reverse_decimal_digits
          (double_reverse_lsf_value rest) +
        double_reverse_reverse10 (double_reverse_lsf_value rest)"
    proof -
      have equation:
        "double_reverse_reverse10
            (digit + 10 * double_reverse_lsf_value rest) =
          (if digit + 10 * double_reverse_lsf_value rest < 10
           then digit + 10 * double_reverse_lsf_value rest
           else (digit + 10 * double_reverse_lsf_value rest) mod 10 *
             10 ^ (double_reverse_decimal_digits
               (digit + 10 * double_reverse_lsf_value rest) - 1) +
             double_reverse_reverse10
               ((digit + 10 * double_reverse_lsf_value rest) div 10))"
        by (rule double_reverse_reverse10.simps)
      have not_less:
        "\<not> digit + 10 * double_reverse_lsf_value rest < 10"
        using value_large by arith
      show ?thesis
        using equation not_less quotient_remainder shifted_digits
        by (simp del: double_reverse_reverse10.simps)
    qed
    show ?thesis
      using number_split rest_reverse rest_digits reverse_step
      by (simp add: double_reverse_lsf_value_append_digit algebra_simps)
  qed
qed

lemma double_reverse_forward_pass_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "double_reverse_lsf_value
        (fst (double_reverse_forward_pass source incoming)) +
      10 ^ length source * snd (double_reverse_forward_pass source incoming) =
    2 * double_reverse_lsf_value source + incoming"
  using decimal incoming
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have rest_decimal: "list_all (\<lambda>item. item < 10) rest"
    using Cons.prems(1) by simp
  have balance:
    "2 * digit + incoming = (2 * digit + incoming) mod 10 +
      10 * threshold5_digit digit"
    unfolding threshold5_digit_def
    by (rule decimal_double_digit_carry[OF digit_bound Cons.prems(2)])
  have carry_bound: "threshold5_digit digit \<le> 1"
    by (simp add: threshold5_digit_def)
  have single:
    "double_reverse_forward_pass [digit] incoming =
      ([(2 * digit + incoming) mod 10], threshold5_digit digit)"
    unfolding threshold5_digit_def
    by (rule double_reverse_forward_single_digit[OF digit_bound Cons.prems(2)])
  have quotient:
    "(2 * digit + incoming) div 10 = threshold5_digit digit"
    using single by (simp add: double_reverse_forward_pass.simps Let_def)
  have tail_value:
    "double_reverse_lsf_value
        (fst (double_reverse_forward_pass rest (threshold5_digit digit))) +
      10 ^ length rest * snd (double_reverse_forward_pass rest
          (threshold5_digit digit)) =
      2 * double_reverse_lsf_value rest + threshold5_digit digit"
    by (rule Cons.IH[OF rest_decimal carry_bound])
  obtain tail_output tail_outgoing where tail_pass:
    "double_reverse_forward_pass rest (threshold5_digit digit) =
      (tail_output, tail_outgoing)"
    by (cases "double_reverse_forward_pass rest (threshold5_digit digit)") auto
  have tail_value_explicit:
    "double_reverse_lsf_value tail_output +
       10 ^ length rest * tail_outgoing =
     2 * double_reverse_lsf_value rest + threshold5_digit digit"
    using tail_value tail_pass by simp
  have pass:
    "double_reverse_forward_pass (digit # rest) incoming =
      ((2 * digit + incoming) mod 10 # tail_output, tail_outgoing)"
    using tail_pass quotient
    by (simp add: double_reverse_forward_pass.simps Let_def)
  show ?case
    using pass tail_value_explicit balance
    by (simp add: double_reverse_lsf_value.simps power_Suc algebra_simps)
qed

lemma double_reverse_forward_pass_length:
  "length (fst (double_reverse_forward_pass source incoming)) =
    length source"
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  let ?next_carry = "(2 * digit + incoming) div 10"
  obtain tail_output tail_carry where tail_pass:
    "double_reverse_forward_pass rest ?next_carry =
      (tail_output, tail_carry)"
    by (cases "double_reverse_forward_pass rest ?next_carry") auto
  have tail_length: "length tail_output = length rest"
    using Cons.IH[of ?next_carry] tail_pass by simp
  have pass:
    "double_reverse_forward_pass (digit # rest) incoming =
      ((2 * digit + incoming) mod 10 # tail_output, tail_carry)"
    using tail_pass
    by (simp add: double_reverse_forward_pass.simps Let_def)
  show ?case using pass tail_length by simp
qed

lemma double_reverse_reverse_pass_length:
  "length (fst (double_reverse_reverse_pass source incoming)) =
    length source"
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  obtain tail_output tail_carry where tail_pass:
    "double_reverse_reverse_pass rest incoming =
      (tail_output, tail_carry)"
    by (cases "double_reverse_reverse_pass rest incoming") auto
  have tail_length: "length tail_output = length rest"
    using Cons.IH[of incoming] tail_pass by simp
  have pass:
    "double_reverse_reverse_pass (digit # rest) incoming =
      ((2 * digit + tail_carry) mod 10 # tail_output,
       (2 * digit + tail_carry) div 10)"
    using tail_pass
    by (simp add: double_reverse_reverse_pass.simps Let_def)
  show ?case using pass tail_length by simp
qed

lemma double_reverse_forward_pass_last_nonzero:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
      and nonempty: "source \<noteq> []"
      and high_positive: "last source > 0"
      and high_small: "last source < 5"
      and incoming: "incoming \<le> 1"
  shows "last (fst (double_reverse_forward_pass source incoming)) > 0"
proof -
  have all_incoming:
    "\<forall>carry_in. carry_in \<le> 1 \<longrightarrow>
      last (fst (double_reverse_forward_pass source carry_in)) > 0"
    using decimal nonempty high_positive high_small
  proof (induction source)
    case Nil
    then show ?case by simp
  next
    case (Cons digit rest)
    have digit_bound: "digit < 10" using Cons.prems(1) by simp
    have rest_decimal: "list_all (\<lambda>item. item < 10) rest"
      using Cons.prems(1) by simp
    have source_high: "last (digit # rest) > 0"
      using Cons.prems(3) .
    have source_high_below_five: "last (digit # rest) < 5"
      using Cons.prems(4) .
    have rest_ih:
      "list_all (\<lambda>item. item < 10) rest \<Longrightarrow>
        rest \<noteq> [] \<Longrightarrow> last rest > 0 \<Longrightarrow>
        last rest < 5 \<Longrightarrow>
        (\<forall>carry_in. carry_in \<le> 1 \<longrightarrow>
          last (fst (double_reverse_forward_pass rest carry_in)) > 0)"
      using Cons.IH .
    show ?case
    proof (intro allI impI)
      fix carry_in :: nat
      assume carry_bound: "carry_in \<le> 1"
      show "last (fst (double_reverse_forward_pass (digit # rest) carry_in)) > 0"
      proof (cases rest)
        case Nil
        have digit_positive: "digit > 0" using source_high Nil by simp
        have digit_small: "digit < 5"
          using source_high_below_five Nil by simp
        have lower: "2 * digit + carry_in > 0"
          using digit_positive by linarith
        have upper: "2 * digit + carry_in < 10"
          using digit_small carry_bound by linarith
        show ?thesis
          using lower upper Nil
          by (simp add: double_reverse_forward_pass.simps)
      next
        case (Cons next_digit tail)
        have tail_nonempty: "rest \<noteq> []" using Cons by simp
        have tail_positive: "last rest > 0" using source_high Cons by simp
        have tail_small: "last rest < 5"
          using source_high_below_five Cons by simp
        have single:
          "double_reverse_forward_pass [digit] carry_in =
            ([(2 * digit + carry_in) mod 10], threshold5_digit digit)"
          unfolding threshold5_digit_def
          by (rule double_reverse_forward_single_digit
            [OF digit_bound carry_bound])
        have quotient:
          "(2 * digit + carry_in) div 10 = threshold5_digit digit"
          using single
          by (simp add: double_reverse_forward_pass.simps Let_def)
        have next_bound: "threshold5_digit digit \<le> 1"
          by (simp add: threshold5_digit_def)
        have rest_law:
          "\<forall>carry. carry \<le> 1 \<longrightarrow>
            last (fst (double_reverse_forward_pass rest carry)) > 0"
          by (rule rest_ih[OF rest_decimal tail_nonempty tail_positive tail_small])
        have tail_nonzero:
          "last (fst (double_reverse_forward_pass rest
            (threshold5_digit digit))) > 0"
          using rest_law next_bound by blast
        obtain rest_output rest_outgoing where rest_pass:
          "double_reverse_forward_pass rest (threshold5_digit digit) =
            (rest_output, rest_outgoing)"
          by (cases "double_reverse_forward_pass rest
            (threshold5_digit digit)") auto
        have rest_output_length: "length rest_output = length rest"
          using double_reverse_forward_pass_length[of rest
            "threshold5_digit digit"] rest_pass by simp
        have rest_output_nonempty: "rest_output \<noteq> []"
          using rest_output_length tail_nonempty by auto
        have tail_output_nonzero: "last rest_output > 0"
          using tail_nonzero unfolding rest_pass by simp
        have pass:
          "double_reverse_forward_pass (digit # rest) carry_in =
            ((2 * digit + carry_in) mod 10 # rest_output,
             rest_outgoing)"
          using rest_pass quotient
          by (simp add: double_reverse_forward_pass.simps Let_def)
        show ?thesis
          using tail_output_nonzero rest_output_nonempty
          unfolding pass by simp
      qed
    qed
  qed
  show ?thesis using all_incoming incoming by blast
qed

lemma double_reverse_reverse_pass_is_reverse_forward_pass:
  "double_reverse_reverse_pass source incoming =
    (rev (fst (double_reverse_forward_pass (rev source) incoming)),
     snd (double_reverse_forward_pass (rev source) incoming))"
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  obtain tail_digits tail_carry where tail_forward:
    "double_reverse_forward_pass (rev rest) incoming =
      (tail_digits, tail_carry)"
    by (cases "double_reverse_forward_pass (rev rest) incoming") auto
  have tail_reverse:
    "double_reverse_reverse_pass rest incoming =
      (rev tail_digits, tail_carry)"
    using Cons.IH tail_forward by simp
  have singleton:
    "double_reverse_forward_pass [digit] tail_carry =
      ([(2 * digit + tail_carry) mod 10],
       (2 * digit + tail_carry) div 10)"
    by (simp add: double_reverse_forward_pass.simps Let_def)
  have forward_split:
    "double_reverse_forward_pass (rev (digit # rest)) incoming =
      (let (left, middle) = double_reverse_forward_pass (rev rest) incoming;
           (right, outgoing) = double_reverse_forward_pass [digit] middle
       in (left @ right, outgoing))"
    using double_reverse_forward_pass_append
      [of "rev rest" "[digit]" incoming]
    by simp
  show ?case
    using tail_reverse tail_forward singleton forward_split
    by (simp add: double_reverse_reverse_pass.simps Let_def)
qed

lemma double_reverse_reverse_pass_value:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "double_reverse_lsf_value
        (rev (fst (double_reverse_reverse_pass source incoming))) +
      10 ^ length source * snd (double_reverse_reverse_pass source incoming) =
    2 * double_reverse_lsf_value (rev source) + incoming"
proof -
  have reverse_decimal:
    "list_all (\<lambda>digit. digit < 10) (rev source)"
    using decimal by simp
  have pass_relation:
    "double_reverse_reverse_pass source incoming =
      (rev (fst (double_reverse_forward_pass (rev source) incoming)),
       snd (double_reverse_forward_pass (rev source) incoming))"
    by (rule double_reverse_reverse_pass_is_reverse_forward_pass)
  show ?thesis
    using double_reverse_forward_pass_value[OF reverse_decimal incoming]
      pass_relation by simp
qed

theorem double_reverse_four_port_closed_word_numeric_t2:
  assumes canonical: "double_reverse_canonical_source source"
  shows "double_reverse_msf_value
      (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
    double_reverse_T_run 2 (double_reverse_msf_value source)"
proof -
  have source_nonempty: "source \<noteq> []"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have source_decimal: "list_all (\<lambda>digit. digit < 10) source"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have source_high: "hd source > 0"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have source_last: "last source > 0"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have reverse_source_decimal:
    "list_all (\<lambda>digit. digit < 10) (rev source)"
    using source_decimal by simp
  have reverse_source_nonempty: "rev source \<noteq> []"
    using source_nonempty by simp
  have reverse_source_high: "last (rev source) > 0"
    using source_high source_nonempty by (cases source) simp_all
  have first_reverse:
    "double_reverse_reverse10 (double_reverse_msf_value source) =
      double_reverse_lsf_value source"
    unfolding double_reverse_msf_value_def
    using double_reverse_reverse10_lsf_value
      [OF reverse_source_decimal reverse_source_nonempty reverse_source_high]
    by simp
  have first_value:
    "double_reverse_T (double_reverse_msf_value source) =
      2 * double_reverse_lsf_value source"
    using first_reverse by (simp add: double_reverse_T_def)

  let ?middle = "fst (double_reverse_forward_pass source 0)"
  let ?forward = "snd (double_reverse_forward_pass source 0)"
  let ?middle_word = "?middle @ (if ?forward = 1 then [1] else [])"
  have forward_bound: "?forward \<le> 1"
    using double_reverse_forward_pass_final_carry[OF source_decimal, of 0]
      source_nonempty by (simp add: threshold5_digit_def)
  have forward_value:
    "double_reverse_lsf_value ?middle +
      10 ^ length source * ?forward =
       2 * double_reverse_lsf_value source"
    using double_reverse_forward_pass_value[OF source_decimal, of 0] by simp
  have middle_length: "length ?middle = length source"
    using double_reverse_forward_pass_length[of source 0] by simp
  have intermediate_value:
    "double_reverse_lsf_value ?middle_word =
       2 * double_reverse_lsf_value source"
    using forward_bound forward_value middle_length
    by (cases ?forward) (simp_all add: double_reverse_lsf_value_append_digit)
  have middle_decimal:
    "list_all (\<lambda>digit. digit < 10) ?middle"
    by (rule double_reverse_forward_pass_output_digits[OF source_decimal]) simp
  have intermediate_decimal:
    "list_all (\<lambda>digit. digit < 10) ?middle_word"
    using middle_decimal forward_bound
    by (cases ?forward) (simp_all add: list_all_iff)
  have intermediate_nonempty: "?middle_word \<noteq> []"
    using source_nonempty middle_length by (cases source) auto
  have forward_is_threshold:
    "?forward = threshold5_digit (last source)"
    using double_reverse_forward_pass_final_carry[OF source_decimal, of 0]
      source_nonempty by simp
  have intermediate_high: "last ?middle_word > 0"
  proof (cases ?forward)
    case 0
    have last_small: "last source < 5"
    proof (cases "5 \<le> last source")
      case True
      then show ?thesis
        using forward_is_threshold 0 by (simp add: threshold5_digit_def)
    next
      case False
      then show ?thesis by arith
    qed
    have middle_high: "last ?middle > 0"
      by (rule double_reverse_forward_pass_last_nonzero
        [OF source_decimal source_nonempty source_last last_small]) simp
    show ?thesis using middle_high 0 by simp
  next
    case (Suc count)
    have forward_is_one: "?forward = 1"
      using forward_bound Suc by simp
    show ?thesis using forward_is_one by simp
  qed
  have second_reverse:
    "double_reverse_reverse10 (double_reverse_lsf_value ?middle_word) =
      double_reverse_lsf_value (rev ?middle_word)"
    by (rule double_reverse_reverse10_lsf_value
      [OF intermediate_decimal intermediate_nonempty intermediate_high])
  have intermediate_reverse_value:
    "double_reverse_lsf_value (rev ?middle_word) =
      (if ?forward = 1 then
        1 + 10 * double_reverse_lsf_value (rev ?middle)
       else double_reverse_lsf_value (rev ?middle))"
  proof (cases ?forward)
    case 0
    then show ?thesis by simp
  next
    case (Suc count)
    have forward_is_one: "?forward = 1"
      using forward_bound Suc by simp
    have rev_append: "rev ?middle_word = 1 # rev ?middle"
      using forward_is_one by simp
    show ?thesis using rev_append forward_is_one by simp
  qed

  let ?reverse_result = "double_reverse_reverse_pass ?middle 0"
  let ?output = "fst ?reverse_result"
  let ?reverse = "snd ?reverse_result"
  let ?q = "double_reverse_lsf_value (rev ?middle)"
  have reverse_bound: "?reverse \<le> 1"
    using double_reverse_reverse_pass_final_carry
      [OF middle_decimal, of 0] by (simp add: threshold5_digit_def)
  have second_pass_value:
    "double_reverse_lsf_value (rev ?output) +
       10 ^ length ?middle * ?reverse = 2 * ?q"
    using double_reverse_reverse_pass_value[OF middle_decimal, of 0] by simp
  have row:
    "double_reverse_four_port_row source 0 0 =
       \<lparr>double_reverse_forward_out=?forward,
        double_reverse_reverse_out=?reverse,
        double_reverse_output_word=?output\<rparr>"
    unfolding double_reverse_four_port_row_def
    by (simp add: Let_def case_prod_beta)
  have row_closed:
    "double_reverse_four_port_closed_word
       (double_reverse_four_port_row source 0 0) =
      (if ?reverse = 1 then [1] else []) @ ?output @
        (if ?forward = 1 then [2] else [])"
    using row by (simp add: double_reverse_four_port_closed_word_def)
  have output_length: "length ?output = length ?middle"
    using double_reverse_reverse_pass_length[of ?middle 0] by simp
  have closed_value:
    "double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0)) =
      (if ?forward = 0 then 2 * ?q else 2 + 20 * ?q)"
  proof (cases ?forward)
    case 0
    have closed:
      "double_reverse_msf_value
        ((if ?reverse = 1 then [1] else []) @ ?output) =
       double_reverse_lsf_value (rev ?output) +
         10 ^ length ?middle * ?reverse"
      using output_length reverse_bound
      by (cases ?reverse) (simp_all add: double_reverse_msf_value_def
          double_reverse_lsf_value_append)
    show ?thesis using 0 row_closed second_pass_value closed
      by (simp add: double_reverse_msf_value_append)
  next
    case (Suc count)
    have forward_is_one: "?forward = 1"
      using forward_bound Suc by simp
    have closed:
      "double_reverse_msf_value
        ((if ?reverse = 1 then [1] else []) @ ?output @ [2]) =
       2 + 10 * (double_reverse_lsf_value (rev ?output) +
         10 ^ length ?middle * ?reverse)"
      using output_length reverse_bound
      by (cases ?reverse) (simp_all add: double_reverse_msf_value_def
          double_reverse_lsf_value_append algebra_simps)
    show ?thesis using forward_is_one row_closed second_pass_value closed
      by (simp add: algebra_simps)
  qed
  have second_value:
    "double_reverse_T
       (double_reverse_T (double_reverse_msf_value source)) =
      (if ?forward = 0 then 2 * ?q else 2 + 20 * ?q)"
  proof (cases ?forward)
    case 0
    show ?thesis
      using first_value intermediate_value second_reverse
        intermediate_reverse_value 0
      by (simp add: double_reverse_T_def)
  next
    case (Suc count)
    have forward_is_one: "?forward = 1"
      using forward_bound Suc by simp
    show ?thesis
      using first_value intermediate_value second_reverse
        intermediate_reverse_value forward_is_one
      by (simp add: double_reverse_T_def)
  qed
  have run_two:
    "double_reverse_T_run 2 (double_reverse_msf_value source) =
      double_reverse_T
        (double_reverse_T (double_reverse_msf_value source))"
    unfolding double_reverse_T_run_def
    by (simp only: numeral_2_eq_2 funpow.simps comp_apply id_apply)
  show ?thesis using closed_value second_value run_two by simp
qed

corollary double_reverse_four_port_closed_word_numeric_t2_zero_suffix:
  assumes canonical: "double_reverse_canonical_source source"
  shows "double_reverse_T_run 2
      (double_reverse_msf_value (source @ replicate zeros 0)) =
    double_reverse_msf_value
      (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0))"
proof -
  have zero_word_value:
    "double_reverse_msf_value (replicate zeros 0) = 0"
    by (induction zeros)
      (simp_all add: double_reverse_msf_value_leading_zero
        double_reverse_msf_value_empty)
  have zero_word_length: "length (replicate zeros 0) = zeros"
    by simp
  have source_value:
    "double_reverse_msf_value (source @ replicate zeros 0) =
      double_reverse_msf_value source * 10^zeros"
    using double_reverse_msf_value_append
      [of source "replicate zeros 0"] zero_word_value zero_word_length
    by (simp add: algebra_simps)
  have contracted:
    "double_reverse_T_run 2
      (double_reverse_msf_value (source @ replicate zeros 0)) =
     double_reverse_T_run 2 (double_reverse_msf_value source)"
    using source_value
      double_reverse_T2_ignores_zero_suffix[of "double_reverse_msf_value source" zeros]
    unfolding double_reverse_T_run_def
    by (simp only: numeral_2_eq_2 funpow.simps comp_apply id_apply
        source_value double_reverse_T2_ignores_zero_suffix)
  show ?thesis using contracted
    double_reverse_four_port_closed_word_numeric_t2[OF canonical] by simp
qed

lemmas double_reverse_four_port_numeric_refinement_audit_bundle =
  double_reverse_lsf_value_append
  double_reverse_lsf_value_append_digit
  double_reverse_msf_value_append
  double_reverse_msf_value_empty
  double_reverse_msf_value_singleton
  double_reverse_msf_value_append_digit
  double_reverse_msf_value_leading_zero
  double_reverse_lsf_value_positive
  double_reverse_decimal_split
  double_reverse_decimal_digits_shift
  double_reverse_decimal_digits_lsf_value
  double_reverse_reverse10_lsf_value
  double_reverse_forward_pass_value
  double_reverse_forward_pass_last_nonzero
  double_reverse_reverse_pass_is_reverse_forward_pass
  double_reverse_reverse_pass_value
  double_reverse_forward_pass_length
  double_reverse_reverse_pass_length
  double_reverse_four_port_closed_word_numeric_t2
  double_reverse_four_port_closed_word_numeric_t2_zero_suffix

ML \<open>
  val checked = @{thms double_reverse_four_port_numeric_refinement_audit_bundle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse four-port numeric refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse four-port numeric refinement proof" else ();
\<close>

end
