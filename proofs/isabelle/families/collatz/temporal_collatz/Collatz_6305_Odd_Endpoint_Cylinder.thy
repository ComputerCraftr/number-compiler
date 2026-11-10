theory Collatz_6305_Odd_Endpoint_Cylinder
  imports Collatz_Skew_Cylinder_Temporal_Squaring
    Collatz_Border_Return_Refinement
begin

text \<open>The extra odd-endpoint bit is derived from the exact powered affine
return.  The primitive defect is multiplied by an odd geometric weight under
repetition; it is not identified with the defect of the repeated word.\<close>

fun collatz_6305_repeat_weight :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_6305_repeat_weight j 0 = 0"
| "collatz_6305_repeat_weight j (Suc r) =
    9^r + 2^(j+2) * collatz_6305_repeat_weight j r"

lemma collatz_6305_repeat_weight_odd:
  "odd (collatz_6305_repeat_weight j (Suc r))"
proof -
  have odd_gain: "odd (9^r)" by simp
  have even_scale: "even (2^(j+2) * collatz_6305_repeat_weight j r)"
    by simp
  show ?thesis
    using odd_gain even_scale
    by (simp add: collatz_6305_repeat_weight.simps)
qed

lemma collatz_6305_repeat_weight_geometric_identity:
  "((2::int)^(j+2) - 9) * int (collatz_6305_repeat_weight j r) =
    (2::int)^(r*(j+2)) - 9^r"
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have exponent: "Suc r * (j+2) = r*(j+2) + (j+2)"
    by simp
  show ?case
    using Suc.IH
    by (simp add: collatz_6305_repeat_weight.simps exponent
        power_add algebra_simps)
qed

lemma collatz_power_of_two_coprime_if_odd:
  fixes n :: nat and z :: int
  assumes odd_z: "odd z"
  shows "coprime ((2::int)^n) z"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  have base: "coprime (2::int) z"
    using odd_z by simp
  have "coprime ((2::int)^(Suc k)) z"
    using base by (simp only: coprime_power_left_iff; simp)
  then show ?thesis using Suc by simp
qed

lemma collatz_6305_repeated_action_fields:
  shows "joint_dyadic_steps
      (collatz_joint_dyadic_word
        (concat (replicate repeats (collatz_6305_return_word j)))) =
        repeats*(j+2) \<and>
    joint_dyadic_gain
      (collatz_joint_dyadic_word
        (concat (replicate repeats (collatz_6305_return_word j)))) =
        9^repeats \<and>
    joint_dyadic_offset
      (collatz_joint_dyadic_word
        (concat (replicate repeats (collatz_6305_return_word j)))) =
        (3+2^(j+1))*collatz_6305_repeat_weight j repeats"
proof (induction repeats)
  case 0
  then show ?case
    by (simp add: collatz_6305_return_word_def
        collatz_joint_dyadic_identity_def collatz_6305_repeat_weight.simps)
next
  case (Suc repeats)
  let ?word = "collatz_6305_return_word j"
  let ?tail = "concat (replicate repeats ?word)"
  have split: "concat (replicate (Suc repeats) ?word) = ?word @ ?tail"
    by simp
  have action:
    "collatz_joint_dyadic_word (concat (replicate (Suc repeats) ?word)) =
      collatz_joint_dyadic_then (collatz_joint_dyadic_word ?word)
        (collatz_joint_dyadic_word ?tail)"
    by (simp only: split collatz_joint_dyadic_word_append)
  have primitive_action:
    "collatz_joint_dyadic_word ?word =
      \<lparr>joint_dyadic_steps = j+2, joint_dyadic_gain = 9,
        joint_dyadic_offset = 3+2^(j+1),
        joint_dyadic_sum_gain = 3*2^(j+2)+3,
        joint_dyadic_sum_offset = 3*2^(j+1)+1\<rparr>"
    by (rule collatz_6305_return_action_exact)
  show ?case
    using action primitive_action Suc.IH
    by (simp add: collatz_joint_dyadic_then_def power_Suc
        collatz_6305_repeat_weight.simps algebra_simps)
qed

lemma collatz_6305_repeated_defect_factor:
  "collatz_temporal_word_defect
      (concat (replicate repeats (collatz_6305_return_word j))) x =
    int (collatz_6305_repeat_weight j repeats) *
      collatz_temporal_word_defect (collatz_6305_return_word j) x"
proof -
  have repeated_length:
    "length (concat (replicate repeats (collatz_6305_return_word j))) =
      repeats*(j+2)"
    by (induction repeats) (simp_all add: collatz_6305_return_word_def)
  have steps:
    "joint_dyadic_steps (collatz_joint_dyadic_word
      (concat (replicate repeats (collatz_6305_return_word j)))) = repeats*(j+2)"
    using collatz_6305_repeated_action_fields
      [where repeats = repeats and j = j] by blast
  have gain:
    "joint_dyadic_gain (collatz_joint_dyadic_word
      (concat (replicate repeats (collatz_6305_return_word j)))) = 9^repeats"
    using collatz_6305_repeated_action_fields
      [where repeats = repeats and j = j] by blast
  have offset:
    "joint_dyadic_offset (collatz_joint_dyadic_word
      (concat (replicate repeats (collatz_6305_return_word j)))) =
       (3+2^(j+1))*collatz_6305_repeat_weight j repeats"
    using collatz_6305_repeated_action_fields
      [where repeats = repeats and j = j] by blast
  note geometric = collatz_6305_repeat_weight_geometric_identity
    [where j = j and r = repeats]
  have primitive_length:
    "length (collatz_6305_return_word j) = j+2"
    by (simp add: collatz_6305_return_word_def)
  have primitive_gain:
    "joint_dyadic_gain (collatz_joint_dyadic_word
        (collatz_6305_return_word j)) = 9"
    using collatz_6305_return_action_exact[where j = j] by simp
  have primitive_offset:
    "joint_dyadic_offset (collatz_joint_dyadic_word
        (collatz_6305_return_word j)) = 3+2^(j+1)"
    using collatz_6305_return_action_exact[where j = j] by simp
  have repeated_explicit:
    "collatz_temporal_word_defect
        (concat (replicate repeats (collatz_6305_return_word j))) x =
      ((2::int)^(repeats*(j+2))-9^repeats)*int x -
        int ((3+2^(j+1))*collatz_6305_repeat_weight j repeats)"
    by (simp only: collatz_temporal_word_defect_def steps gain offset
        repeated_length; simp)
  have primitive_explicit:
    "collatz_temporal_word_defect (collatz_6305_return_word j) x =
      ((2::int)^(j+2)-9)*int x-int (3+2^(j+1))"
    unfolding collatz_temporal_word_defect_def
    by (simp only: primitive_length primitive_gain primitive_offset; simp)
  have geometric_x:
    "((2::int)^(repeats*(j+2))-9^repeats)*int x =
      ((2::int)^(j+2)-9) *
        int (collatz_6305_repeat_weight j repeats) * int x"
  proof -
    have product:
      "(((2::int)^(j+2)-9) *
          int (collatz_6305_repeat_weight j repeats)) * int x =
        ((2::int)^(repeats*(j+2))-9^repeats)*int x"
      using arg_cong[OF geometric,
        where f="\<lambda>v::int. v * int x"] .
    show ?thesis using product by (simp add: algebra_simps)
  qed
  have offset_product:
    "int ((3+2^(j+1))*collatz_6305_repeat_weight j repeats) =
      int (3+2^(j+1)) * int (collatz_6305_repeat_weight j repeats)"
    by simp
  have repeated_scaled:
    "collatz_temporal_word_defect
        (concat (replicate repeats (collatz_6305_return_word j))) x =
      ((2::int)^(j+2)-9) *
          int (collatz_6305_repeat_weight j repeats) * int x -
        int (3+2^(j+1)) * int (collatz_6305_repeat_weight j repeats)"
    using repeated_explicit geometric_x offset_product
    by (simp only: repeated_explicit geometric_x offset_product;
        simp add: algebra_simps)
  have primitive_scaled:
    "collatz_temporal_word_defect (collatz_6305_return_word j) x *
        int (collatz_6305_repeat_weight j repeats) =
      ((2::int)^(j+2)-9) *
          int (collatz_6305_repeat_weight j repeats) * int x -
        int (3+2^(j+1)) * int (collatz_6305_repeat_weight j repeats)"
  proof -
    have product:
      "collatz_temporal_word_defect (collatz_6305_return_word j) x *
          int (collatz_6305_repeat_weight j repeats) =
        (((2::int)^(j+2)-9)*int x-int (3+2^(j+1))) *
          int (collatz_6305_repeat_weight j repeats)"
      using arg_cong[OF primitive_explicit,
        where f="\<lambda>v::int. v * int (collatz_6305_repeat_weight j repeats)"] .
    show ?thesis using product by (simp add: algebra_simps)
  qed
  show ?thesis
    using repeated_scaled primitive_scaled by (simp add: mult.commute)
qed

lemma collatz_int_pow2_increment_dvd_scaled_iff:
  "(2::int)^(Suc n) dvd (2::int)^n * z \<longleftrightarrow> even z"
proof
  assume divides: "(2::int)^(Suc n) dvd (2::int)^n * z"
  then obtain k where equation:
    "(2::int)^n * z = (2::int)^(Suc n) * k"
    by (elim dvdE)
  have scaled: "(2::int)^n * z = (2::int)^n * (2*k)"
    using equation by (simp add: power_Suc algebra_simps)
  have nonzero: "(2::int)^n \<noteq> 0" by simp
  have z: "z = 2*k"
    using scaled nonzero by (metis mult_left_cancel)
  show "even z" using z by simp
next
  assume even_z: "even z"
  then obtain k where z: "z = 2*k" by (elim evenE)
  have equation: "(2::int)^n * z = (2::int)^(Suc n) * k"
    using z by (simp add: power_Suc algebra_simps)
  show "(2::int)^(Suc n) dvd (2::int)^n * z"
    using equation by (rule dvdI[where k=k]; simp)
qed

theorem collatz_6305_return_powered_odd_endpoint_cylinder:
  fixes j x repeats :: nat
  assumes source: "collatz_guarded_normalized_word_admitted
      (collatz_6305_return_word j) x"
  defines "bits \<equiv> concat (replicate repeats (collatz_6305_return_word j))"
      and "endpoint \<equiv> collatz_guarded_normalized_word_endpoint
        (concat (replicate repeats (collatz_6305_return_word j))) x"
      and "steps \<equiv> repeats*(j+2)"
      and "primitive_defect \<equiv>
        collatz_temporal_word_defect (collatz_6305_return_word j) x"
      and "repeated_defect \<equiv> collatz_temporal_word_defect
        (concat (replicate repeats (collatz_6305_return_word j))) x"
  shows "(collatz_guarded_normalized_word_admitted bits x \<and> odd endpoint)
      \<longleftrightarrow> (2::int)^(steps+1) dvd repeated_defect"
proof (cases repeats)
  case 0
  have odd_source: "odd x"
    using source by (simp add: collatz_6305_return_word_def)
  show ?thesis
    using odd_source 0
    by (simp add: bits_def endpoint_def steps_def repeated_defect_def
        collatz_temporal_word_defect_def collatz_joint_dyadic_identity_def)
next
  case (Suc r)
  let ?bits = "concat (replicate (Suc r) (collatz_6305_return_word j))"
  let ?steps = "Suc r*(j+2)"
  let ?weight = "collatz_6305_repeat_weight j (Suc r)"
  have source_odd: "odd x"
    using source by (simp add: collatz_6305_return_word_def)
  have length_exact: "length ?bits = ?steps"
  proof -
    have repeated_length:
      "length ?bits = Suc r * length (collatz_6305_return_word j)"
      by (induction r) simp_all
    show ?thesis using repeated_length
      by (simp add: collatz_6305_return_word_def)
  qed
  have primitive_length: "length (collatz_6305_return_word j) = j+2"
    by (simp add: collatz_6305_return_word_def)
  have repeat_cylinder:
    "collatz_guarded_normalized_word_admitted ?bits x \<longleftrightarrow>
       (2::int)^?steps dvd primitive_defect"
    using collatz_guarded_word_repetition_dyadic_cylinder
      [OF source, where repeats = "Suc r"]
    by (simp only: bits_def primitive_defect_def Suc;
        simp add: primitive_length power_mult)
  have defect_factor: "repeated_defect = int ?weight * primitive_defect"
    using collatz_6305_repeated_defect_factor
      [where j = j and repeats = "Suc r" and x = x]
    by (simp add: bits_def repeated_defect_def primitive_defect_def Suc)
  have weight_odd: "odd (int ?weight)"
    using collatz_6305_repeat_weight_odd[where j = j and r = r] by simp
  have coprime: "coprime ((2::int)^(?steps+1)) (int ?weight)"
    by (rule collatz_power_of_two_coprime_if_odd[OF weight_odd])
  have divide_factor_iff:
    "(2::int)^(?steps+1) dvd int ?weight * primitive_defect \<longleftrightarrow>
       (2::int)^(?steps+1) dvd primitive_defect"
    using coprime by (rule coprime_dvd_mult_right_iff)
  have source_factor:
    "repeated_defect = (2::int)^?steps * (int x-int endpoint)"
    if admitted: "collatz_guarded_normalized_word_admitted ?bits x"
  proof -
    note exact = collatz_temporal_word_defect_source_factor[OF admitted]
    show ?thesis using exact length_exact Suc
      by (simp only: exact repeated_defect_def endpoint_def Suc length_exact)
  qed
  show ?thesis
  proof
    assume left:
      "collatz_guarded_normalized_word_admitted bits x \<and> odd endpoint"
    have admitted: "collatz_guarded_normalized_word_admitted ?bits x"
      using left Suc by (simp add: bits_def)
    have endpoint_odd: "odd endpoint" using left by blast
    have difference_even: "even (int x-int endpoint)"
      using source_odd endpoint_odd by simp
    obtain k where difference: "int x-int endpoint = 2*k"
      using difference_even by (elim evenE)
    have factor: "repeated_defect = (2::int)^(?steps+1)*k"
      using source_factor[OF admitted] difference length_exact Suc
      by (simp add: power_Suc repeated_defect_def steps_def
          endpoint_def bits_def Suc algebra_simps)
    have extra: "(2::int)^(?steps+1) dvd repeated_defect"
      using factor by (rule dvdI[where k=k]; simp)
    show "(2::int)^(steps+1) dvd repeated_defect"
      using extra Suc by (simp add: steps_def)
  next
    assume extra: "(2::int)^(steps+1) dvd repeated_defect"
    have extra_local: "(2::int)^(?steps+1) dvd repeated_defect"
      using extra Suc by (simp add: steps_def)
    have primitive_extra:
      "(2::int)^(?steps+1) dvd primitive_defect"
      using extra_local defect_factor divide_factor_iff by blast
    have lower_power:
      "(2::int)^?steps dvd (2::int)^(?steps+1)"
      by (rule dvdI[where k=2]) (simp add: power_Suc)
    have primitive_base: "(2::int)^?steps dvd primitive_defect"
      using dvd_trans[OF lower_power primitive_extra] .
    have admitted: "collatz_guarded_normalized_word_admitted ?bits x"
      using repeat_cylinder primitive_base by blast
    note factor = source_factor[OF admitted]
    have scaled:
      "(2::int)^(?steps+1) dvd
         (2::int)^?steps * (int x-int endpoint)"
      using extra_local factor by simp
    have exponent: "?steps+1 = Suc ?steps" by simp
    have scaled_suc:
      "(2::int)^(Suc ?steps) dvd
         (2::int)^?steps * (int x-int endpoint)"
      using scaled by (simp only: exponent)
    have even_difference:
      "even (int x-int endpoint)"
      using collatz_int_pow2_increment_dvd_scaled_iff
        [where n = ?steps and z = "int x-int endpoint"] scaled_suc by blast
    have endpoint_odd: "odd endpoint"
      using source_odd even_difference by simp
    show "collatz_guarded_normalized_word_admitted bits x \<and> odd endpoint"
      using admitted endpoint_odd Suc by (simp add: bits_def)
  qed
qed

corollary collatz_6305_return_powered_odd_endpoint_primitive_cylinder:
  fixes j x repeats :: nat
  assumes source: "collatz_guarded_normalized_word_admitted
      (collatz_6305_return_word j) x"
  shows "(collatz_guarded_normalized_word_admitted
        (concat (replicate repeats (collatz_6305_return_word j))) x \<and>
      odd (collatz_guarded_normalized_word_endpoint
        (concat (replicate repeats (collatz_6305_return_word j))) x))
    \<longleftrightarrow>
      (2::int)^(repeats*(j+2)+1) dvd
        collatz_temporal_word_defect (collatz_6305_return_word j) x"
proof (cases repeats)
  case 0
  let ?word = "collatz_6305_return_word j"
  let ?endpoint = "collatz_guarded_normalized_word_endpoint ?word x"
  let ?defect = "collatz_temporal_word_defect ?word x"
  have odd_source: "odd x"
    using source by (simp add: collatz_6305_return_word_def)
  have source_factor:
    "?defect = (2::int)^(j+2) * (int x-int ?endpoint)"
    using collatz_temporal_word_defect_source_factor[OF source]
    by (simp add: collatz_6305_return_word_def)
  have factor_two:
    "?defect = 2 * ((2::int)^(j+1) * (int x-int ?endpoint))"
    using source_factor by (simp add: power_Suc algebra_simps)
  have defect_divisible: "(2::int) dvd ?defect"
    unfolding factor_two by (rule dvdI[where k="(2::int)^(j+1) *
      (int x-int ?endpoint)"]; simp)
  have left:
    "collatz_guarded_normalized_word_admitted
        (concat (replicate 0 ?word)) x \<and>
      odd (collatz_guarded_normalized_word_endpoint
        (concat (replicate 0 ?word)) x)"
    using odd_source by simp
  have right:
    "(2::int)^(0*(j+2)+1) dvd ?defect"
    using defect_divisible by simp
  show ?thesis using left right 0 by simp
next
  case (Suc r)
  let ?word = "collatz_6305_return_word j"
  let ?bits = "concat (replicate (Suc r) ?word)"
  let ?steps = "Suc r*(j+2)"
  let ?weight = "collatz_6305_repeat_weight j (Suc r)"
  let ?primitive = "collatz_temporal_word_defect ?word x"
  let ?repeated = "collatz_temporal_word_defect ?bits x"
  have powered:
    "(collatz_guarded_normalized_word_admitted ?bits x \<and>
      odd (collatz_guarded_normalized_word_endpoint ?bits x))
       \<longleftrightarrow> (2::int)^(?steps+1) dvd ?repeated"
    using collatz_6305_return_powered_odd_endpoint_cylinder
      [OF source, where repeats = "Suc r"]
    by simp
  have defect_factor: "?repeated = int ?weight * ?primitive"
    by (rule collatz_6305_repeated_defect_factor
      [where j = j and repeats = "Suc r" and x = x])
  have weight_odd: "odd (int ?weight)"
    using collatz_6305_repeat_weight_odd[where j = j and r = r] by simp
  have coprime: "coprime ((2::int)^(?steps+1)) (int ?weight)"
    by (rule collatz_power_of_two_coprime_if_odd[OF weight_odd])
  have cancellation:
    "((2::int)^(?steps+1) dvd int ?weight * ?primitive) \<longleftrightarrow>
      ((2::int)^(?steps+1) dvd ?primitive)"
    using coprime by (rule coprime_dvd_mult_right_iff)
  show ?thesis
    using powered defect_factor cancellation Suc
    by (simp add: algebra_simps)
qed

lemma collatz_6305_return_preserves_mod_five:
  fixes j x :: nat
  assumes admitted: "collatz_guarded_normalized_word_admitted
      (collatz_6305_return_word j) x"
      and residue: "x mod 5 = 3"
  shows "collatz_guarded_normalized_word_endpoint
      (collatz_6305_return_word j) x mod 5 = 3"
proof -
  let ?y = "collatz_guarded_normalized_word_endpoint
      (collatz_6305_return_word j) x"
  have affine_nat:
    "9*x + (3+2^(j+1)) = 2^(j+2) * ?y"
  proof -
    have action:
      "collatz_joint_dyadic_word (collatz_6305_return_word j) =
        \<lparr>joint_dyadic_steps = j+2, joint_dyadic_gain = 9,
          joint_dyadic_offset = 3+2^(j+1),
          joint_dyadic_sum_gain = 3*2^(j+2)+3,
          joint_dyadic_sum_offset = 3*2^(j+1)+1\<rparr>"
      by (rule collatz_6305_return_action_exact)
    have general:
      "joint_dyadic_gain (collatz_joint_dyadic_word
          (collatz_6305_return_word j)) * x +
        joint_dyadic_offset (collatz_joint_dyadic_word
          (collatz_6305_return_word j)) =
        2^(joint_dyadic_steps (collatz_joint_dyadic_word
          (collatz_6305_return_word j))) * ?y"
      using collatz_guarded_word_affine_endpoint[OF admitted] by simp
    have gain:
      "joint_dyadic_gain (collatz_joint_dyadic_word
          (collatz_6305_return_word j)) = 9"
      using action by simp
    have offset:
      "joint_dyadic_offset (collatz_joint_dyadic_word
          (collatz_6305_return_word j)) = 3+2^(j+1)"
      using action by simp
    have steps:
      "joint_dyadic_steps (collatz_joint_dyadic_word
          (collatz_6305_return_word j)) = j+2"
      using action by simp
    show ?thesis using general gain offset steps by simp
  qed
  have affine_int:
    "9*int x + (3+(2::int)^(j+1)) = 2^(j+2)*int ?y"
    using collatz_nat_affine_cast[OF affine_nat] by simp
  have division: "(x div 5)*5 + x mod 5 = x"
    by (rule div_mult_mod_eq)
  have x_nat_decomposition: "x = 5*(x div 5)+3"
    using division residue by arith
  have x_decomposition: "int x = 5*int (x div 5)+3"
    using x_nat_decomposition by simp
  have numerator_multiple: "(5::int) dvd 9*int x+3"
  proof -
    have "9*int x+3 = 5*(9*int (x div 5)+6)"
      using x_decomposition by (simp add: algebra_simps)
    then show ?thesis
      by (rule dvdI[where k="9*int (x div 5)+6"]; simp)
  qed
  have scaled:
    "(2::int)^(j+1) * (2*int ?y-1) = 9*int x+3"
  proof -
    let ?scale = "(2::int)^(j+1)"
    have affine_rearranged:
      "?scale*(2*int ?y) = 9*int x+3+?scale"
      using affine_int by (simp add: power_Suc algebra_simps)
    have subtracted:
      "?scale*(2*int ?y)-?scale = 9*int x+3"
      using affine_rearranged by arith
    show ?thesis using subtracted by (simp add: algebra_simps)
  qed
  have power_coprime: "coprime (5::int) ((2::int)^(j+1))"
    by simp
  have factor_multiple: "(5::int) dvd (2::int)^(j+1) * (2*int ?y-1)"
    using numerator_multiple scaled by simp
  have doubled_minus_one_multiple: "(5::int) dvd 2*int ?y-1"
    using coprime_dvd_mult_right_iff[OF power_coprime] factor_multiple
    by blast
  have doubled_residue_mod:
    "(2*int ?y) mod 5 = (1::int) mod 5"
    using doubled_minus_one_multiple
    by (rule iffD2[OF mod_eq_dvd_iff[of "2*int ?y" 5 "1::int"]])
  have doubled_residue: "(2*int ?y) mod 5 = 1"
    using doubled_residue_mod by simp
  have triple_residue: "(6*int ?y) mod 5 = 3"
  proof -
    have reduction:
      "(3*((2*int ?y) mod 5)) mod 5 = (3*(2*int ?y)) mod 5"
      by (rule mod_mult_right_eq)
    have reduced_residue:
      "(3*((2*int ?y) mod 5)) mod 5 = 3"
      using doubled_residue by simp
    show ?thesis using reduction reduced_residue
      by (simp add: algebra_simps)
  qed
  have target_mod_transport:
    "(6*int ?y) mod 5 = ((6 mod 5)*int ?y) mod 5"
    by (rule mod_mult_left_eq[symmetric])
  have target_residue: "int ?y mod 5 = 3"
    using triple_residue target_mod_transport by simp
  have target_cast: "int (?y mod 5) = int (3::nat)"
    using target_residue by (simp add: of_nat_mod)
  show ?thesis using target_cast by (simp only: of_nat_eq_iff)
qed

theorem collatz_6305_source_selects_admitted_return:
  fixes x :: nat
  assumes source_border: "x mod 10 = 3"
  obtains q j u where
    "x = 10*q+3"
    and "collatz_source_valuation x = Suc j"
    and "collatz_accelerated_target x = 5*u"
    and "3*q+1 = 2^j*u"
    and "odd u"
    and "collatz_guarded_normalized_word_admitted
      (collatz_6305_return_word j) x"
    and "collatz_guarded_normalized_word_endpoint
      (collatz_6305_return_word j) x = (15*u+1) div 2"
proof -
  let ?q = "(x-3) div 10"
  let ?j = "collatz_source_valuation x - 1"
  let ?t = "collatz_accelerated_target x"
  let ?u = "?t div 5"
  have source_division: "(x div 10)*10 + x mod 10 = x"
    by (rule div_mult_mod_eq)
  have x_decomposition: "x = 10*(x div 10)+3"
    using source_division source_border by arith
  have q_decomposition: "?q = x div 10"
  proof -
    have "x-3 = 10*(x div 10)"
      using x_decomposition by arith
    then show ?thesis by simp
  qed
  have source: "x = 10*?q+3"
    using x_decomposition q_decomposition by (simp add: algebra_simps)
  have mod_two: "(x mod 10) mod 2 = x mod 2"
    by (rule mod_mod_cancel) simp
  have residue_two: "x mod 2 = 1"
    using source_border mod_two by simp
  have odd_source: "odd x"
    using residue_two by (simp only: odd_iff_mod_2_eq_one)
  have positive: "0 < collatz_source_valuation x"
    by (rule odd_source_has_positive_valuation[OF odd_source])
  have valuation: "collatz_source_valuation x = Suc ?j"
    using positive by simp
  have split:
    "3*x+1 = 2^(collatz_source_valuation x)*?t"
    by (rule collatz_source_split_exact)
  have source_equation: "3*x+1 = 2*(5*(3*?q+1))"
    using source by (simp add: algebra_simps)
  have split_equation: "3*x+1 = 2^(Suc ?j)*?t"
    using split valuation by simp
  have doubled:
    "2*(5*(3*?q+1)) = 2*(2^?j*?t)"
  proof -
    have "2*(5*(3*?q+1)) = 2^(Suc ?j)*?t"
      by (rule trans[OF source_equation[symmetric] split_equation])
    then show ?thesis by (simp add: power_Suc algebra_simps)
  qed
  have two_nonzero: "(2::nat) \<noteq> 0" by simp
  have scaled_factor: "5*(3*?q+1) = 2^?j*?t"
    using doubled two_nonzero by (metis mult_left_cancel)
  have five_divides_product: "5 dvd 2^?j*?t"
  proof -
    have factor: "2^?j*?t = 5*(3*?q+1)"
      using scaled_factor by (rule sym)
    show ?thesis using factor by (rule dvdI[where k="3*?q+1"])
  qed
  have power_coprime: "coprime (5::nat) ((2::nat)^?j)"
    by simp
  have five_divides_target: "5 dvd ?t"
    using coprime_dvd_mult_right_iff[OF power_coprime]
      five_divides_product by blast
  have target_division: "(?t div 5)*5 + ?t mod 5 = ?t"
    by (rule div_mult_mod_eq)
  have target_remainder: "?t mod 5 = 0"
    using five_divides_target by (simp add: dvd_eq_mod_eq_0)
  have target: "?t = 5*?u"
    using target_division target_remainder by arith
  have factor_five:
    "5*(3*?q+1) = 5*(2^?j*?u)"
  proof -
    have "5*(3*?q+1) = 2^?j*?t"
      by (rule scaled_factor)
    also have "... = 2^?j*(5*?u)"
      using target by simp
    also have "... = 5*(2^?j*?u)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have five_nonzero: "(5::nat) \<noteq> 0" by simp
  have selected_factor: "3*?q+1 = 2^?j*?u"
    using factor_five five_nonzero by (metis mult_left_cancel)
  have target_odd: "odd ?t"
    by (rule collatz_accelerated_target_odd)
  have odd_u: "odd ?u"
  proof -
    have odd_product: "odd (5*?u)"
      by (subst target[symmetric]) (rule target_odd)
    show ?thesis using odd_product by simp
  qed
  have selected:
    "collatz_guarded_normalized_word_admitted
       (collatz_6305_return_word ?j) (10*?q+3) \<and>
     collatz_guarded_normalized_word_endpoint
       (collatz_6305_return_word ?j) (10*?q+3) = (15*?u+1) div 2"
    using collatz_border_return_normalized_word[OF selected_factor odd_u]
    by (simp add: collatz_6305_return_word_def)
  have selected_admitted:
    "collatz_guarded_normalized_word_admitted
       (collatz_6305_return_word ?j) (10*?q+3)"
    using selected by blast
  have selected_endpoint:
    "collatz_guarded_normalized_word_endpoint
       (collatz_6305_return_word ?j) (10*?q+3) = (15*?u+1) div 2"
    using selected by blast
  show thesis
  proof (rule that[where q = ?q and j = ?j and u = ?u])
    show "x = 10*?q+3" by (rule source)
    show "collatz_source_valuation x = Suc ?j" by (rule valuation)
    show "collatz_accelerated_target x = 5*?u" by (rule target)
    show "3*?q+1 = 2^?j*?u" by (rule selected_factor)
    show "odd ?u" by (rule odd_u)
    have admitted_rebase:
      "collatz_guarded_normalized_word_admitted
          (collatz_6305_return_word ?j) (10*?q+3) \<longleftrightarrow>
        collatz_guarded_normalized_word_admitted
          (collatz_6305_return_word ?j) x"
      by (rule arg_cong[OF source[symmetric],
        where f="\<lambda>z. collatz_guarded_normalized_word_admitted
          (collatz_6305_return_word ?j) z"])
    show "collatz_guarded_normalized_word_admitted
        (collatz_6305_return_word ?j) x"
      by (rule iffD1[OF admitted_rebase selected_admitted])
    have endpoint_rebase:
      "(collatz_guarded_normalized_word_endpoint
          (collatz_6305_return_word ?j) (10*?q+3) = (15*?u+1) div 2) \<longleftrightarrow>
        (collatz_guarded_normalized_word_endpoint
          (collatz_6305_return_word ?j) x = (15*?u+1) div 2)"
      by (rule arg_cong[OF source[symmetric],
        where f="\<lambda>z. collatz_guarded_normalized_word_endpoint
          (collatz_6305_return_word ?j) z = (15*?u+1) div 2"])
    show "collatz_guarded_normalized_word_endpoint
        (collatz_6305_return_word ?j) x = (15*?u+1) div 2"
      by (rule iffD1[OF endpoint_rebase selected_endpoint])
  qed
qed

theorem collatz_6305_repeated_return_preserves_mod_five:
  fixes j x repeats :: nat
  assumes admitted: "collatz_guarded_normalized_word_admitted
      (concat (replicate repeats (collatz_6305_return_word j))) x"
      and residue: "x mod 5 = 3"
  shows "collatz_guarded_normalized_word_endpoint
      (concat (replicate repeats (collatz_6305_return_word j))) x mod 5 = 3"
  using admitted residue
proof (induction repeats arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc repeats)
  let ?word = "collatz_6305_return_word j"
  let ?tail = "concat (replicate repeats ?word)"
  let ?middle = "collatz_guarded_normalized_word_endpoint ?word x"
  have split: "concat (replicate (Suc repeats) ?word) = ?word @ ?tail"
    by simp
  have parts:
    "collatz_guarded_normalized_word_admitted ?word x \<and>
      collatz_guarded_normalized_word_admitted ?tail ?middle"
    using Suc.prems(1) by (simp only: split
      collatz_guarded_normalized_word_admitted_append)
  have middle_residue: "?middle mod 5 = 3"
    using collatz_6305_return_preserves_mod_five[OF parts[THEN conjunct1]
      Suc.prems(2)] .
  have tail_residue:
    "collatz_guarded_normalized_word_endpoint ?tail ?middle mod 5 = 3"
    using Suc.IH parts[THEN conjunct2] middle_residue by blast
  show ?case using tail_residue
    by (simp only: split collatz_guarded_normalized_word_endpoint_append)
qed

lemma collatz_nat_residue_three_from_mod_five_and_odd:
  fixes n :: nat
  assumes residue: "n mod 5 = 3" and odd_n: "odd n"
  shows "n mod 10 = 3"
proof -
  have division: "(n div 5)*5 + n mod 5 = n"
    by (rule div_mult_mod_eq)
  have decomposition: "n = 5*(n div 5)+3"
    using division residue by arith
  have odd_rebase:
    "odd (5*(n div 5)+3) = odd n"
    by (rule arg_cong[OF decomposition[symmetric],
      where f="\<lambda>k. odd k"])
  have odd_explicit: "odd (5*(n div 5)+3)"
    using odd_rebase odd_n by blast
  have quotient_even: "even (n div 5)"
    using odd_explicit by simp
  obtain k where quotient: "n div 5 = 2*k"
    using quotient_even by (elim evenE)
  have n_as_even_quotient: "n = 5*(2*k)+3"
    using decomposition quotient by arith
  have projected:
    "n mod 10 = (5*(2*k)+3) mod 10"
    by (rule arg_cong[OF n_as_even_quotient, where f="\<lambda>v. v mod 10"])
  show ?thesis using projected by simp
qed

corollary collatz_6305_repeated_return_preserves_3_border:
  fixes j x repeats :: nat
  assumes admitted: "collatz_guarded_normalized_word_admitted
      (concat (replicate repeats (collatz_6305_return_word j))) x"
      and source_border: "x mod 10 = 3"
      and target_odd: "odd (collatz_guarded_normalized_word_endpoint
        (concat (replicate repeats (collatz_6305_return_word j))) x)"
  shows "collatz_guarded_normalized_word_endpoint
      (concat (replicate repeats (collatz_6305_return_word j))) x mod 10 = 3"
proof -
  have source_residue: "x mod 5 = 3"
  proof -
    have reduce: "(x mod 10) mod 5 = x mod 5"
      by (rule mod_mod_cancel) simp
    show ?thesis using source_border reduce by simp
  qed
  have target_residue:
    "collatz_guarded_normalized_word_endpoint
      (concat (replicate repeats (collatz_6305_return_word j))) x mod 5 = 3"
    by (rule collatz_6305_repeated_return_preserves_mod_five[OF admitted
      source_residue])
  show ?thesis
    by (rule collatz_nat_residue_three_from_mod_five_and_odd
      [OF target_residue target_odd])
qed

text \<open>The zero-tail carry matrix uses the shifted source modulo 25,
not merely the decimal border modulo 5. This is a conditional clock law for
an admitted return; it does not authorize a future word from its residue.\<close>

lemma collatz_6305_zero_tail_shifted_endpoint:
  assumes admitted: "collatz_guarded_normalized_word_admitted
    (collatz_6305_return_word 0) x"
  shows "4 * (collatz_guarded_normalized_word_endpoint
    (collatz_6305_return_word 0) x + 1) = 9 * (x + 1)"
proof -
  note affine = collatz_guarded_word_affine_endpoint[OF admitted]
  note fields = collatz_6305_return_action_exact[of 0]
  have "9*x + 5 = 4 * collatz_guarded_normalized_word_endpoint
      (collatz_6305_return_word 0) x"
    using affine fields by simp
  then show ?thesis by arith
qed

lemma collatz_6305_zero_tail_mod25:
  assumes admitted: "collatz_guarded_normalized_word_admitted
    (collatz_6305_return_word 0) x"
  shows "(collatz_guarded_normalized_word_endpoint
    (collatz_6305_return_word 0) x + 1) mod 25 = (21*(x+1)) mod 25"
proof -
  let ?y = "collatz_guarded_normalized_word_endpoint
    (collatz_6305_return_word 0) x"
  have equation: "4*(?y+1) = 9*(x+1)"
    by (rule collatz_6305_zero_tail_shifted_endpoint[OF admitted])
  have scaled: "76*(?y+1) = 171*(x+1)"
    using arg_cong[OF equation, where f="\<lambda>z. 19*z"]
    by (simp only: algebra_simps)
  have residue: "(76*(?y+1)) mod 25 = (171*(x+1)) mod 25"
    by (rule arg_cong[OF scaled])
  have left: "(76*(?y+1)) mod 25 = ((76 mod 25)*(?y+1)) mod 25"
    by (rule mod_mult_left_eq[symmetric])
  have right: "(171*(x+1)) mod 25 = ((171 mod 25)*(x+1)) mod 25"
    by (rule mod_mult_left_eq[symmetric])
  show ?thesis using residue left right by simp
qed

text \<open>The same admitted two-odd return induces multiplication by four on
the centered mod-7 phase. This establishes the three-step return of that
projection; it does not make the phase period a physical repetition guard.\<close>

lemma collatz_6305_zero_tail_mod7:
  assumes admitted: "collatz_guarded_normalized_word_admitted
    (collatz_6305_return_word 0) x"
  shows "(collatz_guarded_normalized_word_endpoint
    (collatz_6305_return_word 0) x + 1) mod 7 = (4*(x+1)) mod 7"
proof -
  let ?y = "collatz_guarded_normalized_word_endpoint
    (collatz_6305_return_word 0) x"
  have equation: "4*(?y+1) = 9*(x+1)"
    by (rule collatz_6305_zero_tail_shifted_endpoint[OF admitted])
  have scaled: "8*(?y+1) = 18*(x+1)"
  proof -
    have "2*(4*(?y+1)) = 2*(9*(x+1))"
      by (rule arg_cong[OF equation, where f="\<lambda>z. 2*z"])
    then show ?thesis by (simp add: algebra_simps)
  qed
  have residue: "(8*(?y+1)) mod 7 = (18*(x+1)) mod 7"
    by (rule arg_cong[OF scaled])
  have left:
    "(8*(?y+1)) mod 7 = ((8 mod 7)*(?y+1)) mod 7"
    by (rule mod_mult_left_eq[symmetric])
  have right:
    "(18*(x+1)) mod 7 = ((18 mod 7)*(x+1)) mod 7"
    by (rule mod_mult_left_eq[symmetric])
  show ?thesis using residue left right by simp
qed

lemma collatz_6305_shifted_mod7_clock:
  "((4::nat)^(k+3)*z) mod 7 = (4^k*z) mod 7"
proof -
  have period: "(4::nat)^3 mod 7 = 1" by simp
  have "(4^(k+3)*z) mod 7 = (4^3*(4^k*z)) mod 7"
    by (simp add: power_add mult.commute mult.left_commute mult.assoc)
  also have "... = ((4^3 mod 7)*(4^k*z)) mod 7"
    by (rule mod_mult_left_eq[symmetric])
  finally have "(4^(k+3)*z) mod 7 = ((4^3 mod 7)*(4^k*z)) mod 7" .
  then show ?thesis using period by simp
qed

lemma collatz_6305_shifted_mod25_clock:
  "((21::nat)^(k+5)*z) mod 25 = (21^k*z) mod 25"
proof -
  have period: "(21::nat)^5 mod 25 = 1" by simp
  have "(21^(k+5)*z) mod 25 = (21^5*(21^k*z)) mod 25"
    by (simp add: power_add mult.commute mult.left_commute mult.assoc)
  also have "... = ((21^5 mod 25)*(21^k*z)) mod 25"
    by (rule mod_mult_left_eq[symmetric])
  finally have "(21^(k+5)*z) mod 25 = ((21^5 mod 25)*(21^k*z)) mod 25" .
  then show ?thesis using period by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_6305_repeat_weight_geometric_identity
      collatz_power_of_two_coprime_if_odd
      collatz_6305_repeated_action_fields
      collatz_6305_repeated_defect_factor
      collatz_int_pow2_increment_dvd_scaled_iff
      collatz_6305_return_powered_odd_endpoint_cylinder
      collatz_6305_return_powered_odd_endpoint_primitive_cylinder
      collatz_6305_return_preserves_mod_five
      collatz_6305_source_selects_admitted_return
      collatz_6305_repeated_return_preserves_mod_five
      collatz_nat_residue_three_from_mod_five_and_odd
      collatz_6305_repeated_return_preserves_3_border
      collatz_6305_zero_tail_shifted_endpoint
      collatz_6305_zero_tail_mod25
      collatz_6305_zero_tail_mod7
      collatz_6305_shifted_mod7_clock
      collatz_6305_shifted_mod25_clock}) then ()
    else error "The powered 6305 endpoint cylinder depends on an oracle";
\<close>

end
