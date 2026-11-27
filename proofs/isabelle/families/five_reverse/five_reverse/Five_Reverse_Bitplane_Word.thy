theory Five_Reverse_Bitplane_Word
  imports Five_Reverse_Bitplane_Lanes
begin

text \<open>Ordered decimal lanes in least-significant-first order.  The incoming
carry of each lane is the high part of the preceding physical digit.\<close>

definition five_plane_scalar :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_plane_scalar digit carry =
    five_plane_add5 (odd digit) (odd carry) (odd (carry div 2)) (odd (carry div 4))"

lemma five_plane_scalar_digit:
  fixes digit carry :: nat
  assumes "digit < 10" "carry < 5"
  shows "five_plane_scalar digit carry = (5 * digit + carry) mod 10"
proof -
  have digit_cases: "digit=0 \<or> digit=1 \<or> digit=2 \<or> digit=3 \<or> digit=4 \<or>
      digit=5 \<or> digit=6 \<or> digit=7 \<or> digit=8 \<or> digit=9"
    using assms by arith
  have carry_cases: "carry=0 \<or> carry=1 \<or> carry=2 \<or> carry=3 \<or> carry=4"
    using assms by arith
  show ?thesis using digit_cases carry_cases
    by (elim disjE; simp add: five_plane_scalar_def five_plane_add5_def
      five_plane_digit_def five_plane_bit_def)
qed

fun five_plane_decimal :: "nat list \<Rightarrow> nat" where
  "five_plane_decimal [] = 0"
| "five_plane_decimal (d # ds) = d + 10 * five_plane_decimal ds"

fun five_plane_multiply :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "five_plane_multiply [] carry = [carry]"
| "five_plane_multiply (d # ds) carry =
    five_plane_scalar d carry # five_plane_multiply ds (d div 2)"

theorem five_plane_multiply_value:
  assumes "list_all (\<lambda>d. d < 10) digits" "carry < 5"
  shows "five_plane_decimal (five_plane_multiply digits carry) =
    5 * five_plane_decimal digits + carry"
  using assms
proof (induction digits arbitrary: carry)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have digit: "d < 10" and tail: "list_all (\<lambda>d. d < 10) ds"
    using Cons.prems by simp_all
  have inlet: "carry < 5" using Cons.prems by simp
  have outlet: "d div 2 < 5" using digit by (simp add: div_less_iff_less_mult)
  have quotient: "(5 * d + carry) div 10 = d div 2"
    by (rule five_bcd_lane_carries(1)[OF digit inlet])
  have lane: "five_plane_scalar d carry = (5 * d + carry) mod 10"
    by (rule five_plane_scalar_digit[OF digit inlet])
  have split: "(5*d+carry) mod 10 + 10 * (d div 2) = 5*d+carry"
    using div_mult_mod_eq[of "5*d+carry" 10] quotient by arith
  show ?case using Cons.IH[OF tail outlet] lane split
    by (simp only: five_plane_multiply.simps five_plane_decimal.simps; arith)
qed

theorem five_plane_source_step:
  assumes "list_all (\<lambda>d. d < 10) digits"
    "five_plane_decimal digits = decimal_reverse source"
  shows "five_plane_decimal (five_plane_multiply digits 0) = five_reverse_step source"
  using five_plane_multiply_value[OF assms(1), of 0] assms(2)
  by (simp add: five_reverse_step_def)


text \<open>The source words carry the physical decimal digits at equal bit
positions.  The first executable sheet shifts the parity plane left by one;
the other three planes supply the high part of the same source digit.\<close>

definition five_plane_encodes ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "five_plane_encodes p a b c digits \<longleftrightarrow>
    (\<forall>i < length digits. five_plane_digit
      (bit p i) (bit a i) (bit b i) (bit c i) = digits ! i)"

lemma five_plane_digit_low_bit:
  "five_plane_digit p a b c mod 2 = five_plane_bit p"
  by (cases p; cases a; cases b; cases c;
      simp add: five_plane_digit_def five_plane_bit_def)

lemma five_plane_digit_high_bits:
  "five_plane_digit p a b c div 2 =
    five_plane_bit a + 2 * five_plane_bit b + 4 * five_plane_bit c"
  by (cases p; cases a; cases b; cases c;
      simp add: five_plane_digit_def five_plane_bit_def)

lemma five_plane_encoded_low_bit:
  assumes "five_plane_encodes p a b c digits" "i < length digits"
  shows "five_plane_bit (bit p i) = digits ! i mod 2"
  using assms five_plane_digit_low_bit[of "bit p i" "bit a i" "bit b i" "bit c i"]
  by (simp add: five_plane_encodes_def)

lemma five_plane_encoded_high_bits:
  assumes "five_plane_encodes p a b c digits" "i < length digits"
  shows "five_plane_bit (bit a i) + 2 * five_plane_bit (bit b i) +
    4 * five_plane_bit (bit c i) = digits ! i div 2"
  using assms five_plane_digit_high_bits[of "bit p i" "bit a i" "bit b i" "bit c i"]
  by (simp add: five_plane_encodes_def)

theorem five_plane_first_sheet_source_digit:
  assumes source: "five_plane_encodes p a b c digits"
    and bound: "i < length digits"
  shows "five_plane_word_digit (five_plane_word_add5 (push_bit 1 p) a b c) i =
    digits ! i div 2 +
      5 * (if i = 0 then 0 else digits ! (i - 1) mod 2)"
proof -
  have high: "five_plane_bit (bit a i) + 2 * five_plane_bit (bit b i) +
      4 * five_plane_bit (bit c i) = digits ! i div 2"
    by (rule five_plane_encoded_high_bits[OF source bound])
  have shifted: "five_plane_bit (bit (push_bit 1 p) i) =
      (if i = 0 then 0 else digits ! (i - 1) mod 2)"
  proof (cases "i = 0")
    case True
    have zero: "\<not> bit (push_bit 1 p) 0"
      by (simp only: bit_push_bit_iff; simp)
    show ?thesis using True zero
      by (simp only: if_True if_False five_plane_bit_def; simp)
  next
    case False
    have previous: "i - 1 < length digits" using bound False by arith
    have shifted_bit: "bit (push_bit 1 p) i = bit p (i - 1)"
      using False by (simp only: bit_push_bit_iff; auto)
    show ?thesis using five_plane_encoded_low_bit[OF source previous] False shifted_bit
      by (simp only: if_False)
  qed
  show ?thesis unfolding five_plane_word_add5_lanes five_plane_add5_exact
    using shifted high by arith
qed

ML \<open>
  val checked = @{thms five_plane_scalar_digit five_plane_multiply_value
    five_plane_source_step five_plane_first_sheet_source_digit};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Bitplane word theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped bitplane word proof" else ();
\<close>

end
