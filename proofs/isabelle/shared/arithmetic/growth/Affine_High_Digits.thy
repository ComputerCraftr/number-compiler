theory Affine_High_Digits
  imports Main
begin

text \<open>An admitted affine endpoint can be split into an unsigned lower
source component and a signed offset correction.  This theory records only
the integer quotient and high-window identities; it does not authenticate an
endpoint, choose a source, or predict a future family label.\<close>

definition affine_ceiling_shift :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "affine_ceiling_shift b d = -((-b) div (2::int)^d)"

definition affine_corrected_endpoint :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "affine_corrected_endpoint y b d = y - affine_ceiling_shift b d"

lemma affine_endpoint_floor_correction:
  fixes a b x y :: int
  assumes endpoint: "(2::int)^d * y = a*x + b"
  shows "(a*x) div (2::int)^d = affine_corrected_endpoint y b d"
proof -
  have nonzero: "(2::int)^d \<noteq> 0" by simp
  have rearranged: "a*x = -b + (2::int)^d*y"
    using endpoint by linarith
  have division:
    "(-b + (2::int)^d*y) div (2::int)^d =
      y + (-b) div (2::int)^d"
    using nonzero by (rule div_mult_self2)
  have quotient:
    "(a*x) div (2::int)^d = y + (-b) div (2::int)^d"
    using rearranged division by simp
  show ?thesis
    using quotient by (simp add: affine_corrected_endpoint_def
      affine_ceiling_shift_def)
qed

definition affine_signed_high_carry :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "affine_signed_high_carry after before cut_bit =
    after div (2::int)^cut_bit - before div (2::int)^cut_bit"

definition affine_binary_digit :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "affine_binary_digit n i = ((n div 2^i) mod 2 = 1)"

definition affine_high_xor_mask :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "affine_high_xor_mask after before cut_bit width =
    map (\<lambda>i. affine_binary_digit after (cut_bit+i) \<noteq>
      affine_binary_digit before (cut_bit+i)) [0..<width]"

lemma affine_high_xor_mask_nth:
  assumes "i < width"
  shows "affine_high_xor_mask after before cut_bit width ! i =
    (affine_binary_digit after (cut_bit+i) \<noteq>
      affine_binary_digit before (cut_bit+i))"
  using assms by (simp add: affine_high_xor_mask_def)

theorem affine_high_digit_transport:
  fixes a b x y :: int and cut_bit :: nat
  assumes endpoint: "(2::int)^d * y = a*x + b"
      and nonnegative_after: "0 \<le> y"
      and nonnegative_before: "0 \<le> affine_corrected_endpoint y b d"
      and position: "i < width"
  defines "before \<equiv> affine_corrected_endpoint y b d"
  shows "before = (a*x) div (2::int)^d"
    "affine_signed_high_carry y before cut_bit =
      y div (2::int)^cut_bit - ((a*x) div (2::int)^d) div (2::int)^cut_bit"
    "affine_high_xor_mask (nat y) (nat before) cut_bit width ! i =
      (affine_binary_digit (nat y) (cut_bit+i) \<noteq>
        affine_binary_digit (nat ((a*x) div (2::int)^d)) (cut_bit+i))"
  using affine_endpoint_floor_correction[OF endpoint]
    nonnegative_after nonnegative_before position
  by (simp_all add: affine_signed_high_carry_def affine_high_xor_mask_def
      before_def affine_binary_digit_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms affine_endpoint_floor_correction affine_high_xor_mask_nth
      affine_high_digit_transport}) then ()
    else error "Affine high-digit transport depends on an oracle";
\<close>

end
