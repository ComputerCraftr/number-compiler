theory Integer_Cylinder_Transport
  imports S_Arithmetic_Skew
begin

text \<open>A bounded source coset is an exact finite progression.  These laws
preserve its entire stride; source authority and family guards are separate
premises supplied by the family producer.\<close>

definition integer_progression :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set" where
  "integer_progression first stride count =
    (\<lambda>i. first + int i * stride) ` {..<count}"

lemma integer_progression_affine_point:
  fixes gain offset denominator first stride target target_stride :: int
  assumes denominator: "0 < denominator"
      and first: "gain * first + offset = denominator * target"
      and stride: "gain * stride = denominator * target_stride"
  shows "(gain * (first + int i * stride) + offset) div denominator =
    target + int i * target_stride"
proof -
  have numerator:
    "gain * (first + int i * stride) + offset =
      denominator * (target + int i * target_stride)"
  proof -
    have "gain * (first + int i * stride) + offset =
        (gain * first + offset) + int i * (gain * stride)"
      by (simp add: algebra_simps)
    also have "... = denominator * target + int i * (denominator * target_stride)"
      by (simp only: first stride)
    also have "... = denominator * (target + int i * target_stride)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis using denominator by (simp add: numerator)
qed

theorem integer_progression_affine_image:
  fixes gain offset denominator first stride target target_stride :: int
  assumes denominator: "0 < denominator"
      and first: "gain * first + offset = denominator * target"
      and stride: "gain * stride = denominator * target_stride"
  shows "(\<lambda>x. (gain*x+offset) div denominator) `
      integer_progression first stride count =
    integer_progression target target_stride count"
  unfolding integer_progression_def image_image
  using integer_progression_affine_point[OF denominator first stride]
  by auto

lemma integer_progression_card:
  assumes stride: "0 < stride"
  shows "card (integer_progression first stride count) = count"
proof -
  have injective: "inj_on (\<lambda>i::nat. first + int i * stride) {..<count}"
    using stride by (auto simp: inj_on_def)
  show ?thesis
    unfolding integer_progression_def using card_image[OF injective] by simp
qed

theorem integer_progression_transport_preserves_count:
  fixes gain offset denominator first stride target target_stride :: int
  assumes positive: "0 < gain" "0 < denominator" "0 < stride"
      and first: "gain * first + offset = denominator * target"
      and stride: "gain * stride = denominator * target_stride"
  shows "card ((\<lambda>x. (gain*x+offset) div denominator) `
      integer_progression first stride count) = count"
proof -
  have product_positive: "0 < gain * stride"
    by (rule mult_pos_pos[OF positive(1) positive(3)])
  have target_product_positive: "0 < denominator * target_stride"
    using product_positive stride by simp
  have target_positive: "0 < target_stride"
    using target_product_positive positive(2)
    by (simp add: zero_less_mult_iff)
  show ?thesis
    using integer_progression_affine_image[OF positive(2) first stride]
      integer_progression_card[OF target_positive, of target count] by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms integer_progression_affine_image
      integer_progression_transport_preserves_count}) then ()
    else error "Integer cylinder transport depends on an oracle";
\<close>

end
