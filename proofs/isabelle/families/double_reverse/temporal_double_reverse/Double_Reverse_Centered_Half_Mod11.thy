theory Double_Reverse_Centered_Half_Mod11
  imports Double_Reverse_F5_Action_Power
    Shared_Carry_Dynamics.Decimal_Normalization_Morphism
begin

text \<open>The centered-half observer is the mod-11 projection of the global
mod-99 clock, with the sign selected by the half-width parity and the odd
center digit added on odd widths.  This projection theorem concerns the
clock representation only until the split lemmas below connect it to exact
LSD-first half words.  No source recurrence or future authority is inferred.\<close>

definition double_reverse_center_sign11 :: "nat \<Rightarrow> nat" where
  "double_reverse_center_sign11 half_width = 10 ^ half_width mod 11"

definition double_reverse_centered_half_mod11 ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_centered_half_mod11 width center global_mod99 =
    (double_reverse_center_sign11 (width div 2) *
        (global_mod99 mod 11) +
      (if width mod 2 = 0 then 0 else center)) mod 11"

lemma double_reverse_decimal_lsd_value_append:
  "decimal_lsd_value (left @ right) =
    decimal_lsd_value left + 10 ^ length left * decimal_lsd_value right"
  by (induction left) (simp_all add: algebra_simps)

lemma double_reverse_ten_power_mod11_shift_two:
  fixes half_width :: nat
  shows "(10::nat) ^ (half_width + 2) mod (11::nat) =
    (10::nat) ^ half_width mod (11::nat)"
proof -
  have square: "(10::nat) ^ 2 mod (11::nat) = 1 mod (11::nat)"
    by simp
  have power:
    "(10::nat) ^ (half_width + 2) =
      (10::nat) ^ half_width * (10::nat) ^ 2"
    by (simp add: power_add)
  have product:
    "((10::nat) ^ half_width * (10::nat) ^ 2) mod (11::nat) =
      ((10::nat) ^ half_width * 1) mod (11::nat)"
    by (rule mod_mult_cong[OF refl square])
  show ?thesis by (simp only: power product mult_1_right)
qed

lemma double_reverse_ten_power_mod11_even:
  fixes half_width :: nat
  shows "(10::nat) ^ (2 * half_width) mod (11::nat) = 1"
proof (induction half_width)
  case 0
  then show ?case by simp
next
  case (Suc half_width)
  have exponent: "2 * Suc half_width = 2 * half_width + 2"
    by simp
  have shift:
    "(10::nat) ^ (2 * half_width + 2) mod (11::nat) =
      (10::nat) ^ (2 * half_width) mod (11::nat)"
    by (rule double_reverse_ten_power_mod11_shift_two)
  show ?case by (simp only: exponent shift Suc.IH)
qed

lemma double_reverse_decimal_lsd_reverse_mod11:
  "decimal_lsd_value (rev digits) mod 11 =
    (10 ^ Suc (length digits) * decimal_lsd_value digits) mod 11"
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  let ?h = "length digits"
  have reverse_value:
    "decimal_lsd_value (rev (digit # digits)) =
      decimal_lsd_value (rev digits) + 10 ^ ?h * digit"
    by (simp add: double_reverse_decimal_lsd_value_append)
  have reverse_tail:
    "decimal_lsd_value (rev digits) mod 11 =
      (10 ^ Suc ?h * decimal_lsd_value digits) mod 11"
    by (rule Cons.IH)
  have low_power:
    "(10::nat) ^ ?h mod (11::nat) =
      (10::nat) ^ (?h + 2) mod (11::nat)"
    by (rule sym[OF double_reverse_ten_power_mod11_shift_two[of ?h]])
  have high_power:
    "(10::nat) ^ Suc ?h mod (11::nat) =
      (10::nat) ^ (?h + 3) mod (11::nat)"
  proof -
    have shift:
      "(10::nat) ^ (Suc ?h + 2) mod (11::nat) =
        (10::nat) ^ Suc ?h mod (11::nat)"
      by (rule double_reverse_ten_power_mod11_shift_two[of "Suc ?h"])
    have reverse:
      "(10::nat) ^ Suc ?h mod (11::nat) =
        (10::nat) ^ (Suc ?h + 2) mod (11::nat)"
      by (rule sym[OF shift])
    have exponent: "Suc ?h + 2 = ?h + 3" by simp
    show ?thesis by (simp only: reverse exponent)
  qed
  have digit_term:
    "(10 ^ ?h * digit) mod 11 =
      (10 ^ (?h + 2) * digit) mod 11"
    by (rule mod_mult_cong[OF low_power refl])
  have tail_term:
    "(10 ^ Suc ?h * decimal_lsd_value digits) mod 11 =
      (10 ^ (?h + 3) * decimal_lsd_value digits) mod 11"
    by (rule mod_mult_cong[OF high_power refl])
  have left:
    "decimal_lsd_value (rev (digit # digits)) mod 11 =
      (10 ^ (?h + 3) * decimal_lsd_value digits +
        10 ^ (?h + 2) * digit) mod 11"
  proof -
    have first:
      "(decimal_lsd_value (rev digits) + 10 ^ ?h * digit) mod 11 =
        (10 ^ Suc ?h * decimal_lsd_value digits +
          10 ^ ?h * digit) mod 11"
      by (rule mod_add_cong[OF reverse_tail refl])
    have second:
      "(10 ^ Suc ?h * decimal_lsd_value digits +
          10 ^ ?h * digit) mod 11 =
        (10 ^ (?h + 3) * decimal_lsd_value digits +
          10 ^ (?h + 2) * digit) mod 11"
      by (rule mod_add_cong[OF tail_term digit_term])
    show ?thesis
      using reverse_value first second by simp
  qed
  show ?case
    using left
    by (simp add: decimal_lsd_value.simps
        power_Suc power_add algebra_simps mod_add_eq)
qed

lemma double_reverse_center_sign11_times_power:
  "(double_reverse_center_sign11 half_width *
      10 ^ half_width) mod 11 = 1"
proof -
  have sign:
    "double_reverse_center_sign11 half_width = 10 ^ half_width mod 11"
    by (simp add: double_reverse_center_sign11_def)
  have square:
    "((10::nat) ^ half_width * (10::nat) ^ half_width) mod (11::nat) = 1"
  proof -
    have exponent:
      "2 * half_width = half_width + half_width"
      by simp
    have expansion:
      "(10::nat) ^ half_width * (10::nat) ^ half_width =
        (10::nat) ^ (half_width + half_width)"
      by (simp add: power_add)
    have expanded_mod:
      "((10::nat) ^ half_width * (10::nat) ^ half_width) mod (11::nat) =
        ((10::nat) ^ (half_width + half_width)) mod (11::nat)"
      by (simp only: expansion)
    have exponent_mod:
      "(10::nat) ^ (half_width + half_width) mod (11::nat) =
        (10::nat) ^ (2 * half_width) mod (11::nat)"
      by (simp only: exponent[symmetric])
    have even_power:
      "(10::nat) ^ (2 * half_width) mod (11::nat) = 1"
      by (rule double_reverse_ten_power_mod11_even)
    show ?thesis
      by (simp only: expanded_mod exponent_mod even_power)
  qed
  show ?thesis
    using sign square
    by (simp add: mod_mult_left_eq)
qed

lemma double_reverse_center_sign11_left_half_term:
  "(double_reverse_center_sign11 half_width *
      (10 ^ half_width * value)) mod 11 = value mod 11"
proof -
  have coefficient:
    "(double_reverse_center_sign11 half_width * 10 ^ half_width) mod 11 = 1"
    by (rule double_reverse_center_sign11_times_power)
  have product:
    "((double_reverse_center_sign11 half_width *
        10 ^ half_width) * value) mod 11 = (1 * value) mod 11"
  proof -
    have coefficient_mod:
      "(double_reverse_center_sign11 half_width *
          10 ^ half_width) mod 11 = 1 mod 11"
      using coefficient by simp
    show ?thesis by (rule mod_mult_cong[OF coefficient_mod refl])
  qed
  have reassociate:
    "double_reverse_center_sign11 half_width *
        (10 ^ half_width * value) =
      (double_reverse_center_sign11 half_width * 10 ^ half_width) * value"
    by (rule sym, rule mult.assoc)
  show ?thesis by (simp only: reassociate product mult_1)
qed

lemma double_reverse_center_sign11_right_half_term:
  "(double_reverse_center_sign11 half_width *
      (10 ^ Suc half_width * value)) mod 11 =
    (10 * value) mod 11"
proof -
  have factor:
    "(double_reverse_center_sign11 half_width *
        10 ^ Suc half_width) mod 11 = 10"
  proof -
    have power:
      "(10::nat) ^ Suc half_width = (10::nat) ^ half_width * (10::nat)"
      by (simp add: power_Suc mult.commute)
    have base:
      "(double_reverse_center_sign11 half_width *
          10 ^ half_width) mod 11 = 1 mod 11"
      using double_reverse_center_sign11_times_power[of half_width] by simp
    have scaled:
      "((double_reverse_center_sign11 half_width *
          10 ^ half_width) * 10) mod 11 = (1 * 10) mod 11"
      by (rule mod_mult_cong[OF base refl])
    have reassociate:
      "double_reverse_center_sign11 half_width *
          (10 ^ half_width * 10) =
        (double_reverse_center_sign11 half_width * 10 ^ half_width) * 10"
      by (rule sym, rule mult.assoc)
    show ?thesis
      by (simp only: power reassociate scaled; simp)
  qed
  have product:
    "((double_reverse_center_sign11 half_width *
        10 ^ Suc half_width) * value) mod 11 = (10 * value) mod 11"
  proof -
    have factor_mod:
      "(double_reverse_center_sign11 half_width *
          10 ^ Suc half_width) mod 11 = 10 mod 11"
      using factor by simp
    show ?thesis by (rule mod_mult_cong[OF factor_mod refl])
  qed
  have reassociate:
    "double_reverse_center_sign11 half_width *
        (10 ^ Suc half_width * value) =
      (double_reverse_center_sign11 half_width * 10 ^ Suc half_width) * value"
    by (rule sym, rule mult.assoc)
  show ?thesis by (simp only: reassociate product)
qed

lemma double_reverse_decimal_even_half_split:
  assumes lengths: "length low = length high"
  shows "(double_reverse_center_sign11 (length low) *
      decimal_lsd_value (low @ high)) mod 11 =
    (decimal_lsd_value high +
      10 * decimal_lsd_value (rev low)) mod 11"
proof -
  let ?h = "length low"
  let ?low = "decimal_lsd_value low"
  let ?high = "decimal_lsd_value high"
  have whole:
    "decimal_lsd_value (low @ high) = ?low + 10 ^ ?h * ?high"
    by (simp add: double_reverse_decimal_lsd_value_append)
  have reverse:
    "decimal_lsd_value (rev low) mod 11 =
      (10 ^ Suc ?h * ?low) mod 11"
    by (rule double_reverse_decimal_lsd_reverse_mod11)
  have second:
    "(double_reverse_center_sign11 ?h * (10 ^ ?h * ?high)) mod 11 =
      ?high mod 11"
    by (rule double_reverse_center_sign11_left_half_term)
  have reflected:
    "(10 * decimal_lsd_value (rev low)) mod 11 =
      (double_reverse_center_sign11 ?h * ?low) mod 11"
  proof -
    have shift:
      "(10::nat) ^ (?h + 2) mod (11::nat) =
        double_reverse_center_sign11 ?h"
      unfolding double_reverse_center_sign11_def
      by (rule double_reverse_ten_power_mod11_shift_two)
    have shift_mod:
      "(10::nat) ^ (?h + 2) mod (11::nat) =
        double_reverse_center_sign11 ?h mod (11::nat)"
      using shift by simp
    have shifted:
      "(10 * (10 ^ Suc ?h * ?low)) mod 11 =
        (double_reverse_center_sign11 ?h * ?low) mod 11"
    proof -
      have power:
        "(10::nat) * (10::nat) ^ Suc ?h = (10::nat) ^ (?h + 2)"
        by (simp add: power_Suc power_add algebra_simps)
      have product:
        "((10::nat) ^ (?h + 2) * ?low) mod (11::nat) =
          (double_reverse_center_sign11 ?h * ?low) mod (11::nat)"
        by (rule mod_mult_cong[OF shift_mod refl])
      have reassociate:
        "10 * (10 ^ Suc ?h * ?low) =
          (10 * 10 ^ Suc ?h) * ?low"
        by (simp add: algebra_simps)
      show ?thesis
        by (simp only: reassociate power product)
    qed
    have multiply_reverse:
      "(10 * decimal_lsd_value (rev low)) mod 11 =
        (10 * (10 ^ Suc ?h * ?low)) mod 11"
      by (rule mod_mult_cong[OF refl reverse])
    show ?thesis using multiply_reverse shifted by simp
  qed
  have signed_whole:
    "(double_reverse_center_sign11 ?h *
        decimal_lsd_value (low @ high)) mod 11 =
      (?high + double_reverse_center_sign11 ?h * ?low) mod 11"
  proof -
    have sum_reduced:
      "(double_reverse_center_sign11 ?h * ?low +
          double_reverse_center_sign11 ?h * (10 ^ ?h * ?high)) mod 11 =
        (double_reverse_center_sign11 ?h * ?low + ?high) mod 11"
      by (rule mod_add_cong[OF refl second])
    show ?thesis
      using whole sum_reduced by (simp add: algebra_simps)
  qed
  show ?thesis
  proof -
    have target:
      "(decimal_lsd_value high +
          10 * decimal_lsd_value (rev low)) mod 11 =
        (decimal_lsd_value high +
          double_reverse_center_sign11 ?h * ?low) mod 11"
      by (rule mod_add_cong[OF refl reflected])
    show ?thesis by (rule trans[OF signed_whole target[symmetric]])
  qed
qed

lemma double_reverse_decimal_odd_half_split:
  assumes lengths: "length low = length high"
  shows "(decimal_lsd_value (center # high) +
      decimal_lsd_value (center # rev low)) mod 11 =
    (center + double_reverse_center_sign11 (length low) *
      decimal_lsd_value (low @ [center] @ high)) mod 11"
proof -
  let ?h = "length low"
  let ?low = "decimal_lsd_value low"
  let ?high = "decimal_lsd_value high"
  have whole:
    "decimal_lsd_value (low @ [center] @ high) =
      ?low + 10 ^ ?h * center + 10 ^ Suc ?h * ?high"
    by (simp add: double_reverse_decimal_lsd_value_append algebra_simps)
  have reverse:
    "decimal_lsd_value (rev low) mod 11 =
      (10 ^ Suc ?h * ?low) mod 11"
    by (rule double_reverse_decimal_lsd_reverse_mod11)
  have sign_center:
    "(double_reverse_center_sign11 ?h * (10 ^ ?h * center)) mod 11 =
      center mod 11"
    by (rule double_reverse_center_sign11_left_half_term)
  have sign_high:
    "(double_reverse_center_sign11 ?h *
        (10 ^ Suc ?h * ?high)) mod 11 =
      (10 * ?high) mod 11"
    by (rule double_reverse_center_sign11_right_half_term)
  have sign_low_reflected:
    "(10 * decimal_lsd_value (rev low)) mod 11 =
      (double_reverse_center_sign11 ?h * ?low) mod 11"
  proof -
    have shift:
      "(10::nat) ^ (?h + 2) mod (11::nat) =
        double_reverse_center_sign11 ?h"
      unfolding double_reverse_center_sign11_def
      by (rule double_reverse_ten_power_mod11_shift_two)
    have shift_mod:
      "(10::nat) ^ (?h + 2) mod (11::nat) =
        double_reverse_center_sign11 ?h mod (11::nat)"
      using shift by simp
    have shifted:
      "(10 * (10 ^ Suc ?h * ?low)) mod 11 =
        (double_reverse_center_sign11 ?h * ?low) mod 11"
    proof -
      have power:
        "(10::nat) * (10::nat) ^ Suc ?h = (10::nat) ^ (?h + 2)"
        by (simp add: power_Suc power_add algebra_simps)
      have product:
        "((10::nat) ^ (?h + 2) * ?low) mod (11::nat) =
          (double_reverse_center_sign11 ?h * ?low) mod (11::nat)"
        by (rule mod_mult_cong[OF shift_mod refl])
      have reassociate:
        "10 * (10 ^ Suc ?h * ?low) =
          (10 * 10 ^ Suc ?h) * ?low"
        by (simp add: algebra_simps)
      show ?thesis
        by (simp only: reassociate power product)
    qed
    have multiply_reverse:
      "(10 * decimal_lsd_value (rev low)) mod 11 =
        (10 * (10 ^ Suc ?h * ?low)) mod 11"
      by (rule mod_mult_cong[OF refl reverse])
    show ?thesis using multiply_reverse shifted by simp
  qed
  have left_expansion:
    "decimal_lsd_value (center # high) +
      decimal_lsd_value (center # rev low) =
      2 * center + 10 * ?high +
        10 * decimal_lsd_value (rev low)"
    by (simp add: decimal_lsd_value.simps algebra_simps)
  have right_expansion:
    "center + double_reverse_center_sign11 ?h *
      decimal_lsd_value (low @ [center] @ high) =
      center + double_reverse_center_sign11 ?h * ?low +
        double_reverse_center_sign11 ?h * (10 ^ ?h * center) +
        double_reverse_center_sign11 ?h * (10 ^ Suc ?h * ?high)"
    using whole by (simp add: algebra_simps)
  have left_cong:
    "(decimal_lsd_value (center # high) +
        decimal_lsd_value (center # rev low)) mod 11 =
      (2 * center + 10 * ?high +
        double_reverse_center_sign11 ?h * ?low) mod 11"
  proof -
    have replacement:
      "(2 * center + 10 * ?high +
          10 * decimal_lsd_value (rev low)) mod 11 =
        (2 * center + 10 * ?high +
          double_reverse_center_sign11 ?h * ?low) mod 11"
      by (rule mod_add_cong[OF refl sign_low_reflected])
    show ?thesis by (simp only: left_expansion replacement)
  qed
  have right_cong:
    "(center + double_reverse_center_sign11 ?h *
        decimal_lsd_value (low @ [center] @ high)) mod 11 =
      (2 * center + 10 * ?high +
        double_reverse_center_sign11 ?h * ?low) mod 11"
  proof -
    have center_term:
      "(center + double_reverse_center_sign11 ?h *
          (10 ^ ?h * center)) mod 11 = (2 * center) mod 11"
    proof -
      have add:
        "(center + double_reverse_center_sign11 ?h *
            (10 ^ ?h * center)) mod 11 = (center + center) mod 11"
        by (rule mod_add_cong[OF refl sign_center])
      have twice: "2 * center = center + center"
        by (simp add: mult_2)
      have twice_mod: "(center + center) mod 11 = (2 * center) mod 11"
        by (simp only: twice[symmetric])
      show ?thesis by (rule trans[OF add twice_mod])
    qed
    have low_high:
      "(double_reverse_center_sign11 ?h * ?low +
          double_reverse_center_sign11 ?h * (10 ^ Suc ?h * ?high)) mod 11 =
        (double_reverse_center_sign11 ?h * ?low + 10 * ?high) mod 11"
      by (rule mod_add_cong[OF refl sign_high])
    have grouped:
      "(center + double_reverse_center_sign11 ?h *
          (10 ^ ?h * center) +
        (double_reverse_center_sign11 ?h * ?low +
          double_reverse_center_sign11 ?h * (10 ^ Suc ?h * ?high))) mod 11 =
        (2 * center + (double_reverse_center_sign11 ?h * ?low +
          10 * ?high)) mod 11"
      by (rule mod_add_cong[OF center_term low_high])
    have rearranged:
      "center + double_reverse_center_sign11 ?h * ?low +
          double_reverse_center_sign11 ?h * (10 ^ ?h * center) +
          double_reverse_center_sign11 ?h * (10 ^ Suc ?h * ?high) =
        center + double_reverse_center_sign11 ?h * (10 ^ ?h * center) +
          (double_reverse_center_sign11 ?h * ?low +
            double_reverse_center_sign11 ?h * (10 ^ Suc ?h * ?high))"
      by (simp add: algebra_simps add.commute)
    have target_order:
      "(2 * center + (double_reverse_center_sign11 ?h * ?low +
          10 * ?high)) mod 11 =
        (2 * center + 10 * ?high +
          double_reverse_center_sign11 ?h * ?low) mod 11"
      by (simp add: algebra_simps add.commute)
    show ?thesis
      by (simp only: right_expansion rearranged grouped target_order)
  qed
  show ?thesis by (rule trans[OF left_cong sym[OF right_cong]])
qed

theorem double_reverse_centered_half_mod11_uses_only_mod99:
  "double_reverse_centered_half_mod11 width center (global mod 99) =
    double_reverse_centered_half_mod11 width center global"
proof -
  have mod_projection: "(global mod 99) mod 11 = global mod 11"
    by (rule mod_mod_cancel) simp
  show ?thesis
    using mod_projection
    by (simp add: double_reverse_centered_half_mod11_def)
qed

theorem double_reverse_centered_even_half_word_projection:
  assumes lengths: "length low = length high"
  shows "double_reverse_centered_half_mod11 (2 * length low) 0
      (decimal_lsd_value (low @ high) mod 99) =
    (decimal_lsd_value high +
      10 * decimal_lsd_value (rev low)) mod 11"
proof -
  have half_split: "(double_reverse_center_sign11 (length low) *
      decimal_lsd_value (low @ high)) mod 11 =
    (decimal_lsd_value high +
      10 * decimal_lsd_value (rev low)) mod 11"
    by (rule double_reverse_decimal_even_half_split[OF lengths])
  have global:
    "(decimal_lsd_value (low @ high) mod 99) mod 11 =
      decimal_lsd_value (low @ high) mod 11"
    by (rule mod_mod_cancel) simp
  have factor:
    "((decimal_lsd_value (low @ high) mod 99) mod 11) mod 11 =
      decimal_lsd_value (low @ high) mod 11"
    using global by simp
  have signed:
    "(double_reverse_center_sign11 (length low) *
        (decimal_lsd_value (low @ high) mod 99 mod 11)) mod 11 =
      (double_reverse_center_sign11 (length low) *
        decimal_lsd_value (low @ high)) mod 11"
    by (rule mod_mult_cong[OF refl factor])
  have projected:
    "(double_reverse_center_sign11 (length low) *
        (decimal_lsd_value (low @ high) mod 99 mod 11)) mod 11 =
      (decimal_lsd_value high +
        10 * decimal_lsd_value (rev low)) mod 11"
    using signed half_split by simp
  show ?thesis
    using projected
    by (simp add: double_reverse_centered_half_mod11_def
        double_reverse_center_sign11_def add.commute)
qed

theorem double_reverse_centered_odd_half_word_projection:
  assumes lengths: "length low = length high"
  shows "double_reverse_centered_half_mod11 (2 * length low + 1) center
      (decimal_lsd_value (low @ [center] @ high) mod 99) =
    (decimal_lsd_value (center # high) +
      decimal_lsd_value (center # rev low)) mod 11"
proof -
  have half_split:
    "(decimal_lsd_value (center # high) +
        decimal_lsd_value (center # rev low)) mod 11 =
      (center + double_reverse_center_sign11 (length low) *
        decimal_lsd_value (low @ [center] @ high)) mod 11"
    by (rule double_reverse_decimal_odd_half_split[OF lengths])
  have global:
    "(decimal_lsd_value (low @ [center] @ high) mod 99) mod 11 =
      decimal_lsd_value (low @ [center] @ high) mod 11"
    by (rule mod_mod_cancel) simp
  have factor:
    "((decimal_lsd_value (low @ [center] @ high) mod 99) mod 11) mod 11 =
      decimal_lsd_value (low @ [center] @ high) mod 11"
    using global by simp
  have signed:
    "(double_reverse_center_sign11 (length low) *
        (decimal_lsd_value (low @ [center] @ high) mod 99 mod 11)) mod 11 =
      (double_reverse_center_sign11 (length low) *
        decimal_lsd_value (low @ [center] @ high)) mod 11"
    by (rule mod_mult_cong[OF refl factor])
  have centered:
    "(center + double_reverse_center_sign11 (length low) *
        (decimal_lsd_value (low @ [center] @ high) mod 99 mod 11)) mod 11 =
      (center + double_reverse_center_sign11 (length low) *
        decimal_lsd_value (low @ [center] @ high)) mod 11"
    by (rule mod_add_cong[OF refl signed])
  have projected:
    "(center + double_reverse_center_sign11 (length low) *
        (decimal_lsd_value (low @ [center] @ high) mod 99 mod 11)) mod 11 =
      (decimal_lsd_value (center # high) +
        decimal_lsd_value (center # rev low)) mod 11"
    using centered half_split by simp
  show ?thesis
    using projected
    by (simp add: double_reverse_centered_half_mod11_def
        double_reverse_center_sign11_def add.commute)
qed

theorem double_reverse_mod99_action_centered_half_projection:
  "(double_reverse_mod99_clock_action width steps skew residue) mod 11 =
    (residue * 2 ^ steps *
      10 ^ double_reverse_mod99_clock_exponent width steps skew) mod 11"
  unfolding double_reverse_mod99_clock_action_def
  by (rule mod_mod_cancel) simp

ML \<open>
  val checked = @{thms double_reverse_centered_half_mod11_uses_only_mod99
    double_reverse_centered_even_half_word_projection
    double_reverse_centered_odd_half_word_projection
    double_reverse_mod99_action_centered_half_projection};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse centered-half projection depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse centered-half proof" else ();
\<close>

end
