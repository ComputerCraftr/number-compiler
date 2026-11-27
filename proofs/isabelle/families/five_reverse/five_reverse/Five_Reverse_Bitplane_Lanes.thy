theory Five_Reverse_Bitplane_Lanes
  imports Five_Reverse_Packed_Consumer
begin

unbundle bit_operations_syntax

text \<open>The Boolean addition used by each five-reversal bitplane sheet.
The shifted inputs are supplied by the receiving physical boundary.\<close>

definition five_plane_bit :: "bool \<Rightarrow> nat" where
  "five_plane_bit b = (if b then 1 else 0)"

definition five_plane_digit :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "five_plane_digit p a b c =
    five_plane_bit p + 2 * five_plane_bit a +
    4 * five_plane_bit b + 8 * five_plane_bit c"

definition five_plane_add5 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "five_plane_add5 p a b c =
    five_plane_digit (p \<noteq> a) (b \<noteq> (p \<and> a))
      ((p \<noteq> c) \<noteq> (p \<and> a \<and> b))
      (p \<and> (c \<or> (p \<and> a \<and> b)))"

lemma five_plane_add5_exact:
  "five_plane_add5 p a b c =
    5 * five_plane_bit p + five_plane_bit a + 2 * five_plane_bit b +
      4 * five_plane_bit c"
  by (cases p; cases a; cases b; cases c;
      simp add: five_plane_add5_def five_plane_digit_def five_plane_bit_def)

lemma five_plane_sheet_physical_lane:
  "five_plane_add5 p a b c =
    5 * (five_plane_digit p a b c mod 2) + five_plane_digit p a b c div 2"
  by (cases p; cases a; cases b; cases c;
      simp add: five_plane_add5_def five_plane_digit_def five_plane_bit_def)

theorem five_plane_source_carry_digit:
  fixes digit carry :: nat
  assumes "digit < 10" "carry < 5"
    and "digit mod 2 = five_plane_bit p"
    and "carry = five_plane_bit a + 2 * five_plane_bit b + 4 * five_plane_bit c"
  shows "five_plane_add5 p a b c = (5 * digit + carry) mod 10"
  using five_bcd_lane_carries(2)[OF assms(1,2)] assms(3,4)
  by (simp add: five_plane_add5_exact)


text \<open>The concrete four-word bit operations are the same Boolean gates
used by the executable add-five sheet.  This statement applies at every bit
position, so it also covers unused positions outside a finite source word.\<close>

definition five_plane_word_add5 ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
  "five_plane_word_add5 p a b c =
    (p XOR a, b XOR (p AND a),
     p XOR c XOR (p AND a AND b), p AND (c OR (p AND a AND b)))"

definition five_plane_word_digit ::
    "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "five_plane_word_digit planes i =
    (case planes of (p, a, b, c) \<Rightarrow>
      five_plane_digit (bit p i) (bit a i) (bit b i) (bit c i))"

lemma five_plane_word_add5_lanes:
  "five_plane_word_digit (five_plane_word_add5 p a b c) i =
    five_plane_add5 (bit p i) (bit a i) (bit b i) (bit c i)"
  by (simp add: five_plane_word_digit_def five_plane_word_add5_def
      five_plane_add5_def bit_xor_iff bit_and_iff bit_or_iff;
      cases "bit p i"; cases "bit a i"; cases "bit b i"; cases "bit c i"; simp)

theorem five_plane_word_add5_physical_digit:
  assumes "digit < 10" "carry < 5"
    and "digit mod 2 = five_plane_bit (bit p i)"
    and "carry = five_plane_bit (bit a i) +
      2 * five_plane_bit (bit b i) + 4 * five_plane_bit (bit c i)"
  shows "five_plane_word_digit (five_plane_word_add5 p a b c) i =
    (5 * digit + carry) mod 10"
  unfolding five_plane_word_add5_lanes
  by (rule five_plane_source_carry_digit[OF assms])

ML \<open>
  val checked = @{thms five_plane_add5_exact five_plane_sheet_physical_lane
    five_plane_source_carry_digit five_plane_word_add5_lanes
    five_plane_word_add5_physical_digit};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Bitplane lane theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped bitplane lane proof" else ();
\<close>

end
