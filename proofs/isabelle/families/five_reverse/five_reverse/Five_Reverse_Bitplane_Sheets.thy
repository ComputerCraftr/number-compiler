theory Five_Reverse_Bitplane_Sheets
  imports Five_Reverse_Bitplane_Word
begin

lemma five_plane_encoded_drop:
  assumes source: "five_plane_encodes p a b c digits"
  shows "five_plane_encodes (drop_bit cut p) (drop_bit cut a)
      (drop_bit cut b) (drop_bit cut c) (drop cut digits)"
  using source unfolding five_plane_encodes_def
  by (auto simp: bit_drop_bit_eq nth_drop add.commute)

theorem five_plane_second_sheet_source_digit:
  assumes source: "five_plane_encodes p a b c digits"
    and bound: "i < length digits"
  shows "five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) i =
    5 * (digits ! i mod 2) +
      (if i = 0 then 0 else digits ! (i - 1) div 2)"
proof -
  have current: "five_plane_bit (bit p i) = digits ! i mod 2"
    by (rule five_plane_encoded_low_bit[OF source bound])
  have shifted: "five_plane_bit (bit (push_bit 1 a) i) +
      2 * five_plane_bit (bit (push_bit 1 b) i) +
      4 * five_plane_bit (bit (push_bit 1 c) i) =
        (if i = 0 then 0 else digits ! (i - 1) div 2)"
  proof (cases "i = 0")
    case True
    have zero_a: "\<not> bit (push_bit 1 a) 0"
      by (simp only: bit_push_bit_iff; simp)
    have zero_b: "\<not> bit (push_bit 1 b) 0"
      by (simp only: bit_push_bit_iff; simp)
    have zero_c: "\<not> bit (push_bit 1 c) 0"
      by (simp only: bit_push_bit_iff; simp)
    show ?thesis using True zero_a zero_b zero_c
      by (simp only: if_True five_plane_bit_def; simp)
  next
    case False
    have previous: "i - 1 < length digits" using bound False by arith
    have shifted_a: "bit (push_bit 1 a) i = bit a (i - 1)"
      using False by (simp only: bit_push_bit_iff; auto)
    have shifted_b: "bit (push_bit 1 b) i = bit b (i - 1)"
      using False by (simp only: bit_push_bit_iff; auto)
    have shifted_c: "bit (push_bit 1 c) i = bit c (i - 1)"
      using False by (simp only: bit_push_bit_iff; auto)
    show ?thesis using five_plane_encoded_high_bits[OF source previous]
      False shifted_a shifted_b shifted_c by simp
  qed
  show ?thesis unfolding five_plane_word_add5_lanes five_plane_add5_exact
    using current shifted by arith
qed

lemma five_plane_scalar_split:
  assumes "carry < 5"
  shows "five_plane_scalar digit carry = 5 * (digit mod 2) + carry"
proof -
  have cases: "carry = 0 \<or> carry = 1 \<or> carry = 2 \<or> carry = 3 \<or> carry = 4"
    using assms by arith
  have parity: "digit mod 2 = 0 \<or> digit mod 2 = 1" by arith
  have odd_digit: "odd digit \<longleftrightarrow> digit mod 2 = 1" by (fact odd_iff_mod_2_eq_one)
  show ?thesis using cases parity
    by (elim disjE; simp add: five_plane_scalar_def
      five_plane_add5_exact five_plane_bit_def odd_digit)
qed

lemma five_plane_multiply_nth:
  assumes "list_all (\<lambda>d. d < 10) digits" "carry < 5" "i < length digits"
  shows "five_plane_multiply digits carry ! i =
    5 * (digits ! i mod 2) + (if i = 0 then carry else digits ! (i - 1) div 2)"
  using assms
proof (induction digits arbitrary: i carry)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have d: "d < 10" and ds: "list_all (\<lambda>d. d < 10) ds" and c: "carry < 5"
    using Cons.prems by simp_all
  have carry: "d div 2 < 5" using d by (simp add: div_less_iff_less_mult)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis using five_plane_scalar_split[OF c] by simp
  next
    case (Suc j)
    have bound: "j < length ds" using Cons.prems Suc by simp
    show ?thesis using Cons.IH[OF ds carry bound] Suc by (cases j) simp_all
  qed
qed

theorem five_plane_second_sheet_exact_digits:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and bound: "i < length digits"
  shows "five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) i =
    five_plane_multiply digits 0 ! i"
  using five_plane_second_sheet_source_digit[OF source bound]
    five_plane_multiply_nth[OF decimal, of 0 i] bound by simp

lemma five_plane_multiply_length:
  "length (five_plane_multiply digits carry) = Suc (length digits)"
  by (induction digits arbitrary: carry) simp_all

lemma five_plane_multiply_nonempty [simp]:
  "five_plane_multiply digits carry \<noteq> []"
  using five_plane_multiply_length[of digits carry] by (metis Suc_neq_Zero length_0_conv)

lemma five_plane_multiply_last:
  "last (five_plane_multiply digits carry) =
    (if digits = [] then carry else last digits div 2)"
  by (induction digits arbitrary: carry) (simp_all add: five_plane_multiply_length)

definition five_plane_second_sheet_digits where
  "five_plane_second_sheet_digits p a b c digits =
    map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) i)
      [0..<length digits] @ [if digits = [] then 0 else last digits div 2]"

theorem five_plane_second_sheet_exact_word:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
  shows "five_plane_second_sheet_digits p a b c digits = five_plane_multiply digits 0"
proof (rule nth_equalityI)
  show "length (five_plane_second_sheet_digits p a b c digits) =
      length (five_plane_multiply digits 0)"
    by (simp add: five_plane_second_sheet_digits_def five_plane_multiply_length)
next
  fix i
  assume bound: "i < length (five_plane_second_sheet_digits p a b c digits)"
  show "five_plane_second_sheet_digits p a b c digits ! i = five_plane_multiply digits 0 ! i"
  proof (cases "i < length digits")
    case True
    then show ?thesis using five_plane_second_sheet_exact_digits[OF source decimal True]
      by (simp add: five_plane_second_sheet_digits_def nth_append)
  next
    case False
    have index: "i = length digits" using bound False
      by (simp add: five_plane_second_sheet_digits_def; arith)
    have last: "five_plane_multiply digits 0 ! length digits = last (five_plane_multiply digits 0)"
      using five_plane_multiply_nonempty[of digits 0]
      by (simp add: last_conv_nth five_plane_multiply_length)
    show ?thesis using five_plane_multiply_last[of digits 0] index last
      by (simp add: five_plane_second_sheet_digits_def nth_append)
  qed
qed

theorem five_plane_second_sheet_value:
  assumes "five_plane_encodes p a b c digits" "list_all (\<lambda>d. d < 10) digits"
  shows "five_plane_decimal (five_plane_second_sheet_digits p a b c digits) =
    5 * five_plane_decimal digits"
  using five_plane_second_sheet_exact_word[OF assms] five_plane_multiply_value[OF assms(2), of 0]
  by simp

lemma five_plane_second_sheet_terminal_digit:
  assumes source: "five_plane_encodes p a b c digits"
    and top: "\<not> bit p (length digits)"
  shows "five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) (length digits) =
    (if digits = [] then 0 else last digits div 2)"
proof (cases "digits = []")
  case True
  have a0: "\<not> bit (push_bit 1 a) 0" by (simp only: bit_push_bit_iff; simp)
  have b0: "\<not> bit (push_bit 1 b) 0" by (simp only: bit_push_bit_iff; simp)
  have c0: "\<not> bit (push_bit 1 c) 0" by (simp only: bit_push_bit_iff; simp)
  show ?thesis using top True a0 b0 c0
    by (simp only: five_plane_word_add5_lanes five_plane_add5_exact five_plane_bit_def;
      simp)
next
  case False
  let ?i = "length digits"
  have positive: "?i > 0" using False by simp
  have bound: "?i - 1 < length digits" using positive by arith
  have positive_bound: "1 \<le> ?i" using positive by arith
  have last: "digits ! (?i - 1) = last digits" using False by (simp add: last_conv_nth)
  have a: "bit (push_bit 1 a) ?i = bit a (?i - 1)"
    by (simp only: bit_push_bit_iff_nat positive_bound; simp)
  have b: "bit (push_bit 1 b) ?i = bit b (?i - 1)"
    by (simp only: bit_push_bit_iff_nat positive_bound; simp)
  have c: "bit (push_bit 1 c) ?i = bit c (?i - 1)"
    by (simp only: bit_push_bit_iff_nat positive_bound; simp)
  show ?thesis using top five_plane_encoded_high_bits[OF source bound] False a b c last
    by (simp add: five_plane_word_add5_lanes five_plane_add5_exact five_plane_bit_def)
qed

theorem five_plane_second_sheet_physical_value:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit p (length digits)"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) i)
      [0..<Suc (length digits)]) = 5 * five_plane_decimal digits"
proof -
  have word: "map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 p (push_bit 1 a) (push_bit 1 b) (push_bit 1 c)) i)
      [0..<Suc (length digits)] = five_plane_second_sheet_digits p a b c digits"
    using five_plane_second_sheet_terminal_digit[OF source top]
    by (simp add: five_plane_second_sheet_digits_def upt_Suc_append)
  show ?thesis using five_plane_second_sheet_value[OF source decimal] by (simp only: word)
qed


fun five_plane_first_emit :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "five_plane_first_emit [] previous = [5 * previous]"
| "five_plane_first_emit (digit # rest) previous =
    (digit div 2 + 5 * previous) # five_plane_first_emit rest (digit mod 2)"

lemma five_plane_first_emit_value:
  assumes "list_all (\<lambda>d. d < 10) digits"
  shows "five_plane_decimal (five_plane_first_emit digits previous) =
    five_reflected_E (five_plane_decimal digits) + 5 * previous"
  using assms
proof (induction digits arbitrary: previous)
  case Nil
  then show ?case by (simp add: five_reflected_E_def)
next
  case (Cons d ds)
  have d: "d < 10" and ds: "list_all (\<lambda>d. d < 10) ds"
    using Cons.prems by simp_all
  have quotient: "five_plane_decimal (d # ds) div 10 = five_plane_decimal ds"
    using d by simp
  have remainder: "five_plane_decimal (d # ds) mod 10 = d"
    using d by simp
  have cases: "d=0 \<or> d=1 \<or> d=2 \<or> d=3 \<or> d=4 \<or>
      d=5 \<or> d=6 \<or> d=7 \<or> d=8 \<or> d=9" using d by arith
  have digit: "(d + 99 * (d mod 2)) div 2 = d div 2 + 50 * (d mod 2)"
    using cases by (elim disjE; simp)
  have action: "five_reflected_E (five_plane_decimal (d # ds)) =
      10 * five_reflected_E (five_plane_decimal ds) + d div 2 + 50 * (d mod 2)"
    using five_reflected_E_digit_equation[of "five_plane_decimal (d # ds)"]
      quotient remainder digit by simp
  show ?case using Cons.IH[OF ds, of "d mod 2"] action
    by (simp only: five_plane_first_emit.simps five_plane_decimal.simps; arith)
qed

lemma five_plane_first_emit_nth:
  assumes "i < length digits"
  shows "five_plane_first_emit digits previous ! i = digits ! i div 2 +
      5 * (if i = 0 then previous else digits ! (i-1) mod 2)"
  using assms
proof (induction digits arbitrary: i previous)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have bound: "j < length ds" using Cons.prems Suc by simp
    show ?thesis using Cons.IH[OF bound, of "d mod 2"] Suc by (cases j) simp_all
  qed
qed

lemma five_plane_first_emit_length:
  "length (five_plane_first_emit digits previous) = Suc (length digits)"
  by (induction digits arbitrary: previous) simp_all

lemma five_plane_first_emit_nonempty [simp]:
  "five_plane_first_emit digits carry \<noteq> []"
  using five_plane_first_emit_length[of digits carry] by (metis Suc_neq_Zero length_0_conv)

lemma five_plane_first_emit_last:
  "last (five_plane_first_emit digits previous) =
    5 * (if digits = [] then previous else last digits mod 2)"
  by (induction digits arbitrary: previous) (simp_all add: five_plane_first_emit_length)

lemma five_plane_first_sheet_terminal_digit:
  assumes source: "five_plane_encodes p a b c digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
  shows "five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) (length digits) =
    5 * (if digits = [] then 0 else last digits mod 2)"
proof (cases "digits = []")
  case True
  have p0: "\<not> bit (push_bit 1 p) 0" by (simp only: bit_push_bit_iff; simp)
  show ?thesis using top True p0
    by (simp only: five_plane_word_add5_lanes five_plane_add5_exact five_plane_bit_def;
      simp)
next
  case False
  let ?i = "length digits"
  have positive: "?i > 0" using False by simp
  have bound: "?i - 1 < length digits" using positive by arith
  have positive_bound: "1 \<le> ?i" using positive by arith
  have last: "digits ! (?i - 1) = last digits" using False by (simp add: last_conv_nth)
  have p: "bit (push_bit 1 p) ?i = bit p (?i - 1)"
    by (simp only: bit_push_bit_iff_nat positive_bound; simp)
  show ?thesis using top five_plane_encoded_low_bit[OF source bound] False p last
    by (simp add: five_plane_word_add5_lanes five_plane_add5_exact five_plane_bit_def)
qed

theorem five_plane_first_sheet_exact_word:
  assumes source: "five_plane_encodes p a b c digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
  shows "map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i)
      [0..<Suc (length digits)] = five_plane_first_emit digits 0"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i)
      [0..<Suc (length digits)]) = length (five_plane_first_emit digits 0)"
    by (simp add: five_plane_first_emit_length)
next
  fix i
  assume bound: "i < length (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i) [0..<Suc (length digits)])"
  show "map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i)
      [0..<Suc (length digits)] ! i = five_plane_first_emit digits 0 ! i"
  proof (cases "i < length digits")
    case True
    show ?thesis using five_plane_first_sheet_source_digit[OF source True]
      five_plane_first_emit_nth[OF True, of 0] True by (simp add: nth_append)
  next
    case False
    have index: "i = length digits" using bound False by simp
    have last: "five_plane_first_emit digits 0 ! length digits = last (five_plane_first_emit digits 0)"
      using five_plane_first_emit_nonempty[of digits 0]
      by (simp add: last_conv_nth five_plane_first_emit_length)
    show ?thesis using five_plane_first_sheet_terminal_digit[OF source top]
      five_plane_first_emit_last[of digits 0] index last by (simp add: nth_append)
  qed
qed

theorem five_plane_first_sheet_physical_value:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i)
      [0..<Suc (length digits)]) = five_reflected_E (five_plane_decimal digits)"
  using five_plane_first_sheet_exact_word[OF source top] five_plane_first_emit_value[OF decimal, of 0]
  by simp

lemma five_plane_trim_low_value:
  assumes "list_all (\<lambda>d. d < 10) digits"
  shows "five_plane_decimal (dropWhile ((=) 0) digits) =
    five_reflected_normalize (five_plane_decimal digits)"
  using assms
proof (induction digits)
  case Nil
  then show ?case by (simp add: five_reflected_normalize.simps)
next
  case (Cons d ds)
  have digit: "d < 10" and tail: "list_all (\<lambda>d. d < 10) ds"
    using Cons.prems by simp_all
  show ?case
  proof (cases "d = 0")
    case True
    then show ?thesis using Cons.IH[OF tail]
      by (simp add: five_reflected_normalize_times_ten)
  next
    case False
    have residue: "five_plane_decimal (d # ds) mod 10 = d" using digit by simp
    have nonzero: "five_plane_decimal (d # ds) \<noteq> 0" using residue False by auto
    have normalized: "five_reflected_normalize (five_plane_decimal (d # ds)) =
        five_plane_decimal (d # ds)"
      using nonzero residue False by (subst five_reflected_normalize.simps) simp
    show ?thesis using False normalized by simp
  qed
qed

lemma five_plane_first_emit_decimal:
  assumes "list_all (\<lambda>d. d < 10) digits" "previous < 2"
  shows "list_all (\<lambda>d. d < 10) (five_plane_first_emit digits previous)"
  using assms
proof (induction digits arbitrary: previous)
  case Nil
  then show ?case by (simp; arith)
next
  case (Cons d ds)
  have d: "d < 10" and ds: "list_all (\<lambda>d. d < 10) ds" and p: "previous < 2"
    using Cons.prems by simp_all
  have half: "d div 2 < 5" using d by (simp add: div_less_iff_less_mult)
  have bit: "d mod 2 < 2" by simp
  show ?case using Cons.IH[OF ds bit] half p by (simp; arith)
qed

lemma five_plane_first_sheet_trimmed_value:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
  shows "five_plane_decimal (dropWhile ((=) 0)
      (map (\<lambda>i. five_plane_word_digit
        (five_plane_word_add5 (push_bit 1 p) a b c) i)
        [0..<Suc (length digits)])) =
    five_reflected_normalize (five_reflected_E (five_plane_decimal digits))"
proof -
  let ?output = "map (\<lambda>i. five_plane_word_digit
        (five_plane_word_add5 (push_bit 1 p) a b c) i) [0..<Suc (length digits)]"
  have word: "?output = five_plane_first_emit digits 0"
    by (rule five_plane_first_sheet_exact_word[OF source top])
  have valid: "list_all (\<lambda>d. d < 10) ?output"
    unfolding word by (rule five_plane_first_emit_decimal[OF decimal]) simp
  show ?thesis using five_plane_trim_low_value[OF valid]
    five_plane_first_sheet_physical_value[OF source decimal top] by simp
qed

theorem five_plane_two_sheet_physical_with_normalized_cut:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
    and cut_source: "five_plane_encodes q e f g cut_digits"
    and cut_decimal: "list_all (\<lambda>d. d < 10) cut_digits"
    and cut_top: "\<not> bit q (length cut_digits)"
    and normalized_cut: "five_plane_decimal cut_digits = five_reflected_normalize
      (five_plane_decimal (map (\<lambda>i. five_plane_word_digit
        (five_plane_word_add5 (push_bit 1 p) a b c) i)
        [0..<Suc (length digits)]))"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 q (push_bit 1 e) (push_bit 1 f) (push_bit 1 g)) i)
      [0..<Suc (length cut_digits)]) =
      five_reverse_step (five_reverse_step (five_plane_decimal digits))"
  using five_plane_first_sheet_physical_value[OF source decimal top]
    five_plane_second_sheet_physical_value[OF cut_source cut_decimal cut_top]
    five_reflected_physical_two_step[of "five_plane_decimal digits"] normalized_cut
  by simp

lemma five_plane_odd_lowbit:
  fixes a :: int
  assumes "odd a"
  shows "a AND (- a) = 1"
proof (rule bit_eqI)
  fix i :: nat
  have pred: "bit a i \<longleftrightarrow> bit (a - 1) i \<or> i = 0"
    by (rule odd_bit_iff_bit_pred[OF assms])
  have core: "bit (a AND (- a)) i \<longleftrightarrow> bit a i \<and> \<not> bit (a - 1) i"
    by (simp only: bit_and_iff bit_minus_iff; simp)
  show "bit (a AND (- a)) i = bit (1::int) i"
  proof (cases i)
    case 0
    have "bit a 0" using assms by (simp add: bit_0)
    moreover have "\<not> bit (a - 1) 0" using assms by (simp only: bit_0; simp)
    ultimately show ?thesis using core 0 by (simp only: bit_1_iff; simp)
  next
    case (Suc j)
    show ?thesis using core pred Suc by (simp only: bit_1_iff; auto)
  qed
qed

lemma five_plane_lowbit_factored:
  fixes a :: int
  assumes "odd a"
  shows "push_bit k a AND (- push_bit k a) = (2::int)^k"
proof -
  have "push_bit k a AND (- push_bit k a) = push_bit k (a AND (- a))"
    by (simp only: push_bit_minus[symmetric] push_bit_and)
  also have "... = (2::int)^k" using five_plane_odd_lowbit[OF assms]
    by (simp add: push_bit_eq_mult)
  finally show ?thesis .
qed

lemma five_plane_lowbit_from_bits:
  fixes support :: int
  assumes below: "take_bit k support = 0" and active: "bit support k"
  shows "support AND (- support) = (2::int)^k"
proof -
  have split: "support = push_bit k (drop_bit k support)"
    using bits_ident[of k support] below by simp
  have bit0: "bit (drop_bit k support) 0 = bit support k"
    by (simp only: bit_drop_bit_eq comp_apply add.right_neutral)
  have odd: "odd (drop_bit k support)" using active bit0 by (simp add: bit_0)
  have "support AND (- support) =
      push_bit k (drop_bit k support) AND (- push_bit k (drop_bit k support))"
    by (rule arg_cong[where f="\<lambda>x. x AND (- x)", OF split])
  also have "... = (2::int)^k" by (rule five_plane_lowbit_factored[OF odd])
  finally show ?thesis .
qed

lemma five_plane_digit_nonzero:
  "five_plane_digit p a b c \<noteq> 0 \<longleftrightarrow> p \<or> a \<or> b \<or> c"
  by (cases p; cases a; cases b; cases c; simp add: five_plane_digit_def five_plane_bit_def)

lemma five_plane_support_bit:
  fixes p a b c :: nat
  shows "bit (p OR a OR b OR c) i \<longleftrightarrow>
    five_plane_word_digit (p,a,b,c) i \<noteq> 0"
  by (simp only: five_plane_word_digit_def case_prod_conv bit_or_iff five_plane_digit_nonzero)

theorem five_plane_support_lowbit:
  fixes p a b c :: nat
  assumes low: "\<And>i. i < k \<Longrightarrow> five_plane_word_digit (p,a,b,c) i = 0"
    and active: "five_plane_word_digit (p,a,b,c) k \<noteq> 0"
  shows "int (p OR a OR b OR c) AND (- int (p OR a OR b OR c)) = (2::int)^k"
proof -
  let ?support = "p OR a OR b OR c"
  have lower: "take_bit k (int ?support) = 0"
  proof (rule bit_eqI)
    fix i
    show "bit (take_bit k (int ?support)) i = bit (0::int) i"
      using low[of i] five_plane_support_bit[of p a b c i]
      by (auto simp: bit_take_bit_iff bit_of_nat_iff)
  qed
  have set: "bit (int ?support) k"
    using active five_plane_support_bit[of p a b c k] by (simp add: bit_of_nat_iff)
  show ?thesis by (rule five_plane_lowbit_from_bits[OF lower set])
qed

function five_plane_bit_length :: "nat \<Rightarrow> nat" where
  "five_plane_bit_length n = (if n = 0 then 0 else Suc (five_plane_bit_length (n div 2)))"
  by pat_completeness auto
termination by (relation "measure id") auto

declare five_plane_bit_length.simps[simp del]

lemma five_plane_bit_length_power:
  "five_plane_bit_length (2^k) = Suc k"
proof (induction k)
  case 0
  show ?case by (simp add: five_plane_bit_length.simps)
next
  case (Suc k)
  have "(2::nat)^Suc k = 2 * 2^k" by (simp add: power_Suc)
  then show ?case using Suc.IH by (subst five_plane_bit_length.simps) simp
qed

definition five_plane_support_cut :: "nat \<Rightarrow> nat" where
  "five_plane_support_cut support =
    (if support = 0 then 0 else
      five_plane_bit_length (nat (int support AND (- int support))) - 1)"

theorem five_plane_support_cut_first_digit:
  fixes p a b c :: nat
  assumes low: "\<And>i. i < k \<Longrightarrow> five_plane_word_digit (p,a,b,c) i = 0"
    and active: "five_plane_word_digit (p,a,b,c) k \<noteq> 0"
  shows "five_plane_support_cut (p OR a OR b OR c) = k"
proof -
  have present: "bit (p OR a OR b OR c) k"
    using active by (simp only: five_plane_support_bit; simp)
  have nonzero: "p OR a OR b OR c \<noteq> 0"
    using present by (intro notI) simp
  have exact: "int (p OR a OR b OR c) AND (- int (p OR a OR b OR c)) = (2::int)^k"
    by (rule five_plane_support_lowbit[OF low active])
  show ?thesis using nonzero exact five_plane_bit_length_power[of k]
    by (simp add: five_plane_support_cut_def nat_power_eq)
qed

theorem five_plane_first_sheet_reflects_physical_odd:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (push_bit 1 p) a b c) i)
      [0..<Suc (length digits)]) =
    five_fixed_reverse (Suc (decimal_digit_count (five_plane_decimal digits)))
      (five_reverse_step (five_plane_decimal digits))"
proof -
  let ?source = "five_plane_decimal digits"
  let ?width = "decimal_digit_count ?source"
  have source_bound: "?source < (10::nat)^?width"
    by (rule decimal_source_below_digit_power)
  have carry: "(0::nat) < 5" by simp
  have reflected: "five_fixed_reverse (Suc ?width) (five_reverse_step ?source) =
      five_reflected_E ?source"
    using five_fixed_reverse_reflected_product[OF source_bound carry]
    by (simp only: five_reverse_step_def five_fixed_reverse_decimal
      mult_zero_left Nat.add_0_right)
  show ?thesis using five_plane_first_sheet_physical_value[OF source decimal top]
    reflected by simp
qed

lemma five_plane_drop_at_first_active:
  fixes digits :: "nat list"
  assumes bound: "k < length digits"
    and low: "\<And>i. i < k \<Longrightarrow> digits ! i = 0"
    and active: "digits ! k \<noteq> 0"
  shows "drop k digits = dropWhile ((=) 0) digits"
  using assms
proof (induction k arbitrary: digits)
  case 0
  then obtain d ds where digits: "digits = d # ds" by (cases digits) auto
  show ?case using 0 digits by simp
next
  case (Suc k)
  then obtain d ds where digits: "digits = d # ds" by (cases digits) auto
  have d: "d = 0" using Suc.prems(2)[of 0] digits by simp
  have bound: "k < length ds" using Suc.prems(1) digits by simp
  have low: "\<And>i. i < k \<Longrightarrow> ds ! i = 0"
    using Suc.prems(2) digits by (metis Suc_less_eq nth_Cons_Suc)
  have active: "ds ! k \<noteq> 0" using Suc.prems(3) digits by simp
  show ?case using Suc.IH[OF bound low active] digits d by simp
qed

lemma five_plane_word_encodes_digits:
  assumes exact: "map (five_plane_word_digit (p,a,b,c)) [0..<length digits] = digits"
  shows "five_plane_encodes p a b c digits"
  unfolding five_plane_encodes_def
proof (intro allI impI)
  fix i
  assume bound: "i < length digits"
  have "map (five_plane_word_digit (p,a,b,c)) [0..<length digits] ! i = digits ! i"
    using exact by simp
  then show "five_plane_digit (bit p i) (bit a i) (bit b i) (bit c i) = digits ! i"
    using bound by (simp add: five_plane_word_digit_def)
qed

theorem five_plane_two_sheet_with_checked_cut:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
    and first: "five_plane_word_add5 (push_bit 1 p) a b c = (q,e,f,g)"
    and cut: "drop k (five_plane_first_emit digits 0) =
      dropWhile ((=) 0) (five_plane_first_emit digits 0)"
    and cut_top: "\<not> bit (drop_bit k q) (length (drop k (five_plane_first_emit digits 0)))"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (drop_bit k q) (push_bit 1 (drop_bit k e))
        (push_bit 1 (drop_bit k f)) (push_bit 1 (drop_bit k g))) i)
      [0..<Suc (length (drop k (five_plane_first_emit digits 0)))]) =
      five_reverse_step (five_reverse_step (five_plane_decimal digits))"
proof -
  let ?first_digits = "five_plane_first_emit digits 0"
  let ?cut_digits = "drop k ?first_digits"
  have first_length: "length ?first_digits = Suc (length digits)"
    by (rule five_plane_first_emit_length)
  have first_exact: "map (five_plane_word_digit (q,e,f,g)) [0..<length ?first_digits] = ?first_digits"
    using five_plane_first_sheet_exact_word[OF source top] first first_length by simp
  have first_source: "five_plane_encodes q e f g ?first_digits"
    by (rule five_plane_word_encodes_digits[OF first_exact])
  have cut_source: "five_plane_encodes (drop_bit k q) (drop_bit k e)
      (drop_bit k f) (drop_bit k g) ?cut_digits"
    by (rule five_plane_encoded_drop[OF first_source])
  have first_valid: "list_all (\<lambda>d. d < 10) ?first_digits"
    by (rule five_plane_first_emit_decimal[OF decimal]) simp
  have cut_valid: "list_all (\<lambda>d. d < 10) ?cut_digits"
    using first_valid set_drop_subset[of k ?first_digits] by (auto simp: list_all_iff)
  have normalized: "five_plane_decimal ?cut_digits = five_reflected_normalize
      (five_plane_decimal (map (\<lambda>i. five_plane_word_digit
        (five_plane_word_add5 (push_bit 1 p) a b c) i)
        [0..<Suc (length digits)]))"
    using five_plane_trim_low_value[OF first_valid]
      five_plane_first_sheet_exact_word[OF source top] cut by simp
  show ?thesis
    by (rule five_plane_two_sheet_physical_with_normalized_cut
      [OF source decimal top cut_source cut_valid cut_top normalized])
qed

theorem five_plane_two_sheet_from_support:
  assumes source: "five_plane_encodes p a b c digits"
    and decimal: "list_all (\<lambda>d. d < 10) digits"
    and top: "\<not> bit a (length digits)" "\<not> bit b (length digits)"
      "\<not> bit c (length digits)"
    and first: "five_plane_word_add5 (push_bit 1 p) a b c = (q,e,f,g)"
    and bound: "k < length (five_plane_first_emit digits 0)"
    and low: "\<And>i. i < k \<Longrightarrow> five_plane_first_emit digits 0 ! i = 0"
    and active: "five_plane_first_emit digits 0 ! k \<noteq> 0"
    and cut_top: "\<not> bit (drop_bit k q) (length (drop k (five_plane_first_emit digits 0)))"
  defines "cut \<equiv> five_plane_support_cut (q OR e OR f OR g)"
  shows "five_plane_decimal (map (\<lambda>i. five_plane_word_digit
      (five_plane_word_add5 (drop_bit cut q) (push_bit 1 (drop_bit cut e))
        (push_bit 1 (drop_bit cut f)) (push_bit 1 (drop_bit cut g))) i)
      [0..<Suc (length (drop cut (five_plane_first_emit digits 0)))]) =
      five_reverse_step (five_reverse_step (five_plane_decimal digits))"
proof -
  let ?word = "five_plane_first_emit digits 0"
  have exact: "map (five_plane_word_digit (q,e,f,g)) [0..<length ?word] = ?word"
    using five_plane_first_sheet_exact_word[OF source top] first five_plane_first_emit_length by simp
  have digit: "five_plane_word_digit (q,e,f,g) i = ?word ! i" if "i < length ?word" for i
  proof -
    have "map (five_plane_word_digit (q,e,f,g)) [0..<length ?word] ! i = ?word ! i"
      using exact by simp
    then show ?thesis using that by simp
  qed
  have support_low: "five_plane_word_digit (q,e,f,g) i = 0" if "i < k" for i
    using low[OF that] digit[of i] that bound by simp
  have support_active: "five_plane_word_digit (q,e,f,g) k \<noteq> 0"
    using active digit[OF bound] by simp
  have selected: "cut = k"
    unfolding cut_def by (rule five_plane_support_cut_first_digit[OF support_low support_active])
  have trim: "drop k ?word = dropWhile ((=) 0) ?word"
    by (rule five_plane_drop_at_first_active[OF bound low active])
  show ?thesis unfolding selected
    by (rule five_plane_two_sheet_with_checked_cut[OF source decimal top first trim cut_top])
qed

lemma five_plane_step_positive:
  assumes "0 < source"
  shows "0 < five_reverse_step source"
  using five_decimal_reverse_units_nonzero[OF assms]
  by (auto simp: five_reverse_step_def)

lemma five_plane_orbit_positive:
  assumes "0 < source"
  shows "0 < five_reverse_orbit ticks source"
  using assms
  by (induction ticks) (simp_all add: five_plane_step_positive)

lemma five_plane_reflected_E_positive:
  assumes "0 < source"
  shows "0 < five_reflected_E source"
proof (rule ccontr)
  assume "\<not> 0 < five_reflected_E source"
  then have zero: "five_reflected_E source = 0" by simp
  have twice: "0 < five_reverse_step (five_reverse_step source)"
    by (rule five_plane_step_positive[OF five_plane_step_positive[OF assms]])
  show False using twice five_reflected_physical_two_step[of source] zero
    by (simp add: five_reflected_normalize.simps)
qed

lemma five_plane_positive_digit:
  assumes "0 < five_plane_decimal digits"
  shows "\<exists>k < length digits. digits ! k \<noteq> 0"
  using assms
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  show ?case
  proof (cases "d = 0")
    case False
    then show ?thesis by (intro exI[of _ 0]) simp
  next
    case True
    have "0 < five_plane_decimal ds" using Cons.prems True by simp
    then obtain k where bound: "k < length ds" and active: "ds ! k \<noteq> 0"
      using Cons.IH by blast
    show ?thesis using bound active by (intro exI[of _ "Suc k"]) simp
  qed
qed

lemma five_plane_first_emit_positive:
  assumes "0 < five_plane_decimal digits" "list_all (\<lambda>d. d < 10) digits"
  shows "0 < five_plane_decimal (five_plane_first_emit digits 0)"
  using five_plane_first_emit_value[OF assms(2), of 0]
    five_plane_reflected_E_positive[OF assms(1)] by simp

lemma five_plane_first_emit_has_first_active:
  assumes "0 < five_plane_decimal digits" "list_all (\<lambda>d. d < 10) digits"
  obtains k where "k < length (five_plane_first_emit digits 0)"
    "five_plane_first_emit digits 0 ! k \<noteq> 0"
    "\<And>i. i < k \<Longrightarrow> five_plane_first_emit digits 0 ! i = 0"
proof -
  let ?word = "five_plane_first_emit digits 0"
  have exists: "\<exists>k < length ?word. ?word ! k \<noteq> 0"
    by (rule five_plane_positive_digit[OF five_plane_first_emit_positive[OF assms]])
  let ?k = "LEAST k. k < length ?word \<and> ?word ! k \<noteq> 0"
  have selected: "?k < length ?word \<and> ?word ! ?k \<noteq> 0"
    by (rule LeastI_ex[OF exists])
  have low: "?word ! i = 0" if "i < ?k" for i
  proof (rule ccontr)
    assume "?word ! i \<noteq> 0"
    moreover have "i < length ?word" using that selected by arith
    ultimately have "i < length ?word \<and> ?word ! i \<noteq> 0" by simp
    then have "?k \<le> i" by (rule Least_le)
    with that show False by simp
  qed
  show thesis by (rule that[OF conjunct1[OF selected] conjunct2[OF selected] low])
qed

ML \<open>
  val checked = @{thms five_plane_second_sheet_exact_digits
    five_plane_second_sheet_exact_word five_plane_second_sheet_terminal_digit
    five_plane_second_sheet_physical_value five_plane_first_sheet_physical_value
    five_plane_first_sheet_trimmed_value
    five_plane_two_sheet_physical_with_normalized_cut
    five_plane_support_cut_first_digit five_plane_first_sheet_reflects_physical_odd
    five_plane_two_sheet_from_support five_plane_orbit_positive
    five_plane_reflected_E_positive five_plane_first_emit_has_first_active};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Second sheet source theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped second sheet source proof" else ();
\<close>

end
