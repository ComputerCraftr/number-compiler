theory Collatz_Skew_Cylinder_Temporal_Squaring
  imports Collatz_Physical_Cylinder_Lift
    "Shared_Growth_Arithmetic.Affine_High_Digits"
begin

text \<open>This theory adds a source-cylinder law for repeating one already
admitted normalized parity word.  The word remains fixed throughout each
statement.  The results do not authorize a changed named-family selector,
discover a future word, or establish a finite quotient for all Collatz
orbits.\<close>

definition collatz_temporal_source_step :: "nat \<Rightarrow> nat" where
  "collatz_temporal_source_step x =
    (if odd x then (3*x+1) div 2 else x div 2)"

definition collatz_temporal_gain :: "bool \<Rightarrow> nat" where
  "collatz_temporal_gain branch = (if branch then 3 else 1)"

lemma collatz_temporal_source_step_translation:
  "collatz_temporal_source_step (source + 2*lift_amount) =
    collatz_temporal_source_step source +
      collatz_temporal_gain (odd source) * lift_amount"
proof (cases "odd source")
  case True
  then obtain q where source: "source = 2*q+1" by (rule oddE)
  show ?thesis
    unfolding collatz_temporal_source_step_def collatz_temporal_gain_def
    using source by simp
next
  case False
  then have even: "even source" by simp
  then obtain q where source: "source = 2*q" by (rule evenE)
  show ?thesis
    unfolding collatz_temporal_source_step_def collatz_temporal_gain_def
    using source by simp
qed

interpretation collatz_temporal_dyadic_source: dyadic_source_action
    collatz_temporal_source_step odd collatz_temporal_gain
proof
  show "\<And>source lift_amount.
      odd (source + 2*lift_amount) = odd source"
    by simp
  show "\<And>source lift_amount.
      collatz_temporal_source_step (source + 2*lift_amount) =
        collatz_temporal_source_step source +
          collatz_temporal_gain (odd source) * lift_amount"
    by (rule collatz_temporal_source_step_translation)
qed

lemma collatz_guarded_temporal_step_matches:
  "collatz_temporal_source_step source =
    collatz_guarded_normalized_source_step (odd source) source"
proof (cases "odd source")
  case True
  have first_tick: "physical_collatz source = 3*source+1"
    using True by (simp add: physical_collatz_def)
  have even_after: "even (3*source+1)"
    using True by simp
  have second_tick:
    "physical_collatz (3*source+1) = (3*source+1) div 2"
    using even_after by (simp add: physical_collatz_def)
  have two: "2 = Suc (Suc 0)" by simp
  have iterate_two:
    "(physical_collatz ^^ 2) source =
      physical_collatz (physical_collatz source)"
    by (simp only: two funpow.simps comp_apply id_apply)
  have exact:
    "collatz_guarded_normalized_source_step True source =
      (3*source+1) div 2"
    unfolding collatz_guarded_normalized_source_step_def
    using iterate_two first_tick second_tick by simp
  then show ?thesis
    using True by (simp add: collatz_temporal_source_step_def)
next
  case False
  then have even: "even source" by simp
  have exact:
    "collatz_guarded_normalized_source_step False source = source div 2"
    using even by (simp add: collatz_guarded_normalized_source_step_def
        physical_collatz_def)
  then show ?thesis
    using False by (simp add: collatz_temporal_source_step_def)
qed

lemma collatz_guarded_word_admitted_iff_temporal_word:
  "collatz_guarded_normalized_word_admitted bits source \<longleftrightarrow>
    bits = dyadic_source_word collatz_temporal_source_step odd source
      (length bits)"
proof (induction bits arbitrary: source)
  case Nil
  then show ?case by simp
next
  case (Cons branch tail)
  show ?case
  proof (cases "branch = odd source")
    case False
    then show ?thesis by simp
  next
    case True
    have step:
      "collatz_guarded_normalized_source_step (odd source) source =
        collatz_temporal_source_step source"
      using collatz_guarded_temporal_step_matches[of source] by simp
    show ?thesis
      using Cons.IH[of "collatz_temporal_source_step source"]
      by (simp add: True step)
  qed
qed

lemma collatz_temporal_word_same_residue:
  assumes residue: "source mod 2^n = target mod 2^n"
  shows "dyadic_source_word collatz_temporal_source_step odd source n =
    dyadic_source_word collatz_temporal_source_step odd target n"
proof -
  have source_lift:
    "dyadic_source_word collatz_temporal_source_step odd source n =
      dyadic_source_word collatz_temporal_source_step odd
        (source mod 2^n) n"
    using collatz_temporal_dyadic_source.source_residue_lift[of source n]
    by blast
  have target_lift:
    "dyadic_source_word collatz_temporal_source_step odd target n =
      dyadic_source_word collatz_temporal_source_step odd
        (target mod 2^n) n"
    using collatz_temporal_dyadic_source.source_residue_lift[of target n]
    by blast
  show ?thesis using source_lift target_lift residue by simp
qed

lemma collatz_joint_dyadic_word_steps:
  "joint_dyadic_steps (collatz_joint_dyadic_word bits) = length bits"
  by (induction bits)
    (simp_all add: collatz_joint_dyadic_then_def
      collatz_joint_dyadic_atom_def collatz_joint_dyadic_identity_def)

theorem collatz_guarded_word_same_residue_cylinder:
  assumes residue: "source mod 2^(length bits) =
      target mod 2^(length bits)"
  shows "collatz_guarded_normalized_word_admitted bits source \<longleftrightarrow>
    collatz_guarded_normalized_word_admitted bits target"
  using collatz_guarded_word_admitted_iff_temporal_word[of bits source]
    collatz_guarded_word_admitted_iff_temporal_word[of bits target]
    collatz_temporal_word_same_residue[OF residue]
  by simp

lemma collatz_affine_defect_recurrence:
  fixes a b x y m :: int
  assumes positive: "0 < m"
      and endpoint: "a*x + b = m*y"
  shows "(m-a)*y-b = a * (((m-a)*x-b) div m)"
proof -
  have initial_defect: "(m-a)*x-b = m*(x-y)"
    using endpoint by (simp only: algebra_simps; linarith)
  have quotient: "((m-a)*x-b) div m = x-y"
    using initial_defect positive by simp
  have target_defect: "(m-a)*y-b = a*(x-y)"
    using endpoint by (simp only: algebra_simps; linarith)
  show ?thesis
    using target_defect quotient by simp
qed

lemma collatz_guarded_word_affine_endpoint:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
      and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
  shows "joint_dyadic_gain action * source + joint_dyadic_offset action =
    2^(joint_dyadic_steps action) * target"
proof -
  have endpoint:
    "collatz_joint_dyadic_endpoint action (of_nat source) = of_nat target"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by (simp add: action_def target_def)
  have denominator: "(2::rat)^joint_dyadic_steps action \<noteq> 0" by simp
  have rational_equation:
    "of_nat (joint_dyadic_gain action) * of_nat source +
        of_nat (joint_dyadic_offset action) =
      (2::rat)^joint_dyadic_steps action * of_nat target"
    using endpoint denominator
    by (simp add: collatz_joint_dyadic_endpoint_def
        nonzero_divide_eq_eq mult.commute)
  have cast_equation:
    "(of_nat (joint_dyadic_gain action * source + joint_dyadic_offset action)::rat) =
      of_nat (2^(joint_dyadic_steps action) * target)"
    using rational_equation by simp
  have natural_equation:
    "joint_dyadic_gain action * source + joint_dyadic_offset action =
      2^(joint_dyadic_steps action) * target"
    using cast_equation by (simp only: of_nat_eq_iff)
  show ?thesis using natural_equation .
qed

lemma collatz_nat_affine_cast:
  assumes endpoint: "gain * source + bias = 2^steps * target"
  shows "int gain * int source + int bias =
    (2::int)^steps * int target"
proof -
  have cast:
    "int (gain * source + bias) = int (2^steps * target)"
    using endpoint by (rule arg_cong[where f="\<lambda>n::nat. int n"])
  show ?thesis using cast by simp
qed

theorem collatz_guarded_word_affine_high_digits:
  fixes bits :: "bool list" and source i width cut_bit :: nat
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
      and position: "i < width"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
      and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
      and "before \<equiv> affine_corrected_endpoint
        (int (collatz_guarded_normalized_word_endpoint bits source))
        (int (joint_dyadic_offset (collatz_joint_dyadic_word bits)))
        (joint_dyadic_steps (collatz_joint_dyadic_word bits))"
  shows "before =
      (int (joint_dyadic_gain action) * int source) div
        (2::int)^joint_dyadic_steps action"
    and "affine_signed_high_carry (int target) before cut_bit =
      int target div (2::int)^cut_bit -
        ((int (joint_dyadic_gain action) * int source) div
          (2::int)^joint_dyadic_steps action) div (2::int)^cut_bit"
    and "affine_high_xor_mask (nat (int target)) (nat before) cut_bit width ! i =
      (affine_binary_digit (nat (int target)) (cut_bit+i) \<noteq>
        affine_binary_digit
          (nat ((int (joint_dyadic_gain action) * int source) div
            (2::int)^joint_dyadic_steps action)) (cut_bit+i))"
proof -
  have endpoint_nat:
    "joint_dyadic_gain action * source + joint_dyadic_offset action =
      2^(joint_dyadic_steps action) * target"
    using collatz_guarded_word_affine_endpoint[OF admitted]
    by (simp add: action_def target_def)
  have endpoint_int_forward:
    "int (joint_dyadic_gain action) * int source +
      int (joint_dyadic_offset action) =
      (2::int)^joint_dyadic_steps action * int target"
    by (rule collatz_nat_affine_cast[OF endpoint_nat])
  have endpoint_int:
    "(2::int)^joint_dyadic_steps action * int target =
      int (joint_dyadic_gain action) * int source +
        int (joint_dyadic_offset action)"
    by (rule endpoint_int_forward[symmetric])
  have after_nonnegative: "0 \<le> int target" by simp
  have before_equation:
    "before =
      (int (joint_dyadic_gain action) * int source) div
        (2::int)^joint_dyadic_steps action"
    using affine_endpoint_floor_correction[OF endpoint_int]
    by (simp add: before_def affine_corrected_endpoint_def
        affine_ceiling_shift_def action_def target_def)
  have before_nonnegative: "0 \<le> before"
  proof -
    have numerator_nonnegative:
      "0 \<le> int (joint_dyadic_gain action) * int source"
      by simp
    have denominator_positive:
      "0 < (2::int)^joint_dyadic_steps action"
      by simp
    show ?thesis
      using before_equation numerator_nonnegative denominator_positive
      by (simp add: pos_imp_zdiv_nonneg_iff)
  qed
  have before_nonnegative_raw:
    "0 \<le> affine_corrected_endpoint (int target)
      (int (joint_dyadic_offset action)) (joint_dyadic_steps action)"
    using before_nonnegative by (simp add: before_def action_def target_def)
  show before:
    "before =
      (int (joint_dyadic_gain action) * int source) div
        (2::int)^joint_dyadic_steps action"
    by (rule before_equation)
  show "affine_signed_high_carry (int target) before cut_bit =
      int target div (2::int)^cut_bit -
        ((int (joint_dyadic_gain action) * int source) div
          (2::int)^joint_dyadic_steps action) div (2::int)^cut_bit"
    using affine_high_digit_transport(2)[OF endpoint_int after_nonnegative
        before_nonnegative_raw position]
    by (simp add: before_def action_def target_def)
  show "affine_high_xor_mask (nat (int target)) (nat before) cut_bit width ! i =
      (affine_binary_digit (nat (int target)) (cut_bit+i) \<noteq>
        affine_binary_digit
          (nat ((int (joint_dyadic_gain action) * int source) div
            (2::int)^joint_dyadic_steps action)) (cut_bit+i))"
    using affine_high_digit_transport(3)[OF endpoint_int after_nonnegative
        before_nonnegative_raw position]
    by (simp add: before_def action_def target_def)
qed

theorem collatz_guarded_word_defect_recurrence:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
      and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
  shows "((2::int)^joint_dyadic_steps action -
        int (joint_dyadic_gain action)) * int target -
        int (joint_dyadic_offset action) =
      int (joint_dyadic_gain action) *
        ((((2::int)^joint_dyadic_steps action -
          int (joint_dyadic_gain action)) * int source -
          int (joint_dyadic_offset action)) div
          (2::int)^joint_dyadic_steps action)"
proof -
  have affine_nat:
    "joint_dyadic_gain action * source + joint_dyadic_offset action =
      2^(joint_dyadic_steps action) * target"
    using collatz_guarded_word_affine_endpoint[OF admitted]
    by (simp add: action_def target_def)
  have affine_int:
    "int (joint_dyadic_gain action) * int source +
        int (joint_dyadic_offset action) =
      (2::int)^joint_dyadic_steps action * int target"
    by (rule collatz_nat_affine_cast[OF affine_nat])
  show ?thesis
    by (rule collatz_affine_defect_recurrence[
      where a="int (joint_dyadic_gain action)"
        and b="int (joint_dyadic_offset action)"
        and x="int source" and y="int target"
        and m="(2::int)^joint_dyadic_steps action"])
      (simp_all add: affine_int)
qed

lemma collatz_joint_dyadic_word_gain_odd:
  "odd (joint_dyadic_gain (collatz_joint_dyadic_word bits))"
  by (induction bits)
    (simp_all add: collatz_joint_dyadic_then_def
      collatz_joint_dyadic_atom_def collatz_joint_dyadic_identity_def)

lemma collatz_nat_residue_iff_int_divisibility:
  "source mod modulus = target mod modulus \<longleftrightarrow>
    (int modulus :: int) dvd int source - int target"
proof -
  have nat_to_int:
    "source mod modulus = target mod modulus \<longleftrightarrow>
      int (source mod modulus) = int (target mod modulus)"
    by simp
  have int_residues:
    "int (source mod modulus) = int (target mod modulus) \<longleftrightarrow>
      (int modulus :: int) dvd int source - int target"
    by (simp only: of_nat_mod mod_eq_dvd_iff)
  show ?thesis using nat_to_int int_residues by blast
qed

definition collatz_temporal_word_defect :: "bool list \<Rightarrow> nat \<Rightarrow> int" where
  "collatz_temporal_word_defect bits source =
    ((2::int)^length bits -
      int (joint_dyadic_gain (collatz_joint_dyadic_word bits))) *
        int source -
      int (joint_dyadic_offset (collatz_joint_dyadic_word bits))"

theorem collatz_guarded_word_square_cylinder:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
      and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
      and "modulus \<equiv> (2::int)^length bits"
      and "defect \<equiv> collatz_temporal_word_defect bits source"
  shows "collatz_guarded_normalized_word_admitted bits target \<longleftrightarrow>
    (2::int)^(2*length bits) dvd defect"
proof -
  have affine_source:
    "joint_dyadic_gain action * source + joint_dyadic_offset action =
      2^(joint_dyadic_steps action) * target"
    using collatz_guarded_word_affine_endpoint[OF admitted]
    by (simp add: action_def target_def)
  have affine_target:
    "joint_dyadic_gain action * target + joint_dyadic_offset action =
      2^(joint_dyadic_steps action) *
        collatz_guarded_normalized_word_endpoint bits target"
    if target_admitted: "collatz_guarded_normalized_word_admitted bits target"
    using collatz_guarded_word_affine_endpoint[OF target_admitted]
    by (simp add: action_def target_def)
  have affine_source_int:
    "int (joint_dyadic_gain action) * int source +
      int (joint_dyadic_offset action) = modulus * int target"
  proof -
    have cast:
      "int (joint_dyadic_gain action) * int source +
        int (joint_dyadic_offset action) =
        (2::int)^(joint_dyadic_steps action) * int target"
      by (rule collatz_nat_affine_cast[OF affine_source])
    show ?thesis using cast
      by (simp add: modulus_def action_def collatz_joint_dyadic_word_steps)
  qed
  have source_defect_factor:
    "defect = modulus * (int source - int target)"
    using affine_source_int
    by (simp only: defect_def collatz_temporal_word_defect_def
        modulus_def action_def algebra_simps; linarith)
  have source_residue_iff:
    "source mod 2^(length bits) = target mod 2^(length bits) \<longleftrightarrow>
      modulus dvd int source - int target"
    using collatz_nat_residue_iff_int_divisibility[
      where source=source and modulus="2^(length bits)" and target=target]
    by (simp add: modulus_def)
  have residue_admission:
    "source mod 2^(length bits) = target mod 2^(length bits) \<Longrightarrow>
      collatz_guarded_normalized_word_admitted bits target"
    using collatz_guarded_word_same_residue_cylinder[
      where source=source and bits=bits and target=target]
      admitted by blast
  have modulus_positive: "0 < modulus"
    by (simp add: modulus_def)
  have gain_odd: "odd (int (joint_dyadic_gain action))"
    using collatz_joint_dyadic_word_gain_odd[of bits]
    by (simp add: action_def)
  have coprime: "coprime modulus (int (joint_dyadic_gain action))"
    using gain_odd by (simp add: modulus_def coprime_power_left_iff)
  have target_residue_implies_divisibility:
    "collatz_guarded_normalized_word_admitted bits target \<Longrightarrow>
      modulus dvd int source - int target"
  proof -
    assume target_admitted:
      "collatz_guarded_normalized_word_admitted bits target"
    have affine_target_int:
      "int (joint_dyadic_gain action) * int target +
        int (joint_dyadic_offset action) = modulus *
          int (collatz_guarded_normalized_word_endpoint bits target)"
    proof -
      have cast:
        "int (joint_dyadic_gain action) * int target +
          int (joint_dyadic_offset action) =
          (2::int)^(joint_dyadic_steps action) *
            int (collatz_guarded_normalized_word_endpoint bits target)"
        by (rule collatz_nat_affine_cast[OF affine_target[OF target_admitted]])
      show ?thesis using cast
        by (simp add: modulus_def action_def collatz_joint_dyadic_word_steps)
    qed
    have multiple_eq:
      "int (joint_dyadic_gain action) * (int source - int target) =
        modulus * (int target -
          int (collatz_guarded_normalized_word_endpoint bits target))"
      using affine_source_int affine_target_int
      by (simp only: algebra_simps; linarith)
    have multiple:
      "modulus dvd int (joint_dyadic_gain action) *
        (int source - int target)"
      using multiple_eq by (auto simp: dvd_def)
    show "modulus dvd int source - int target"
      using coprime_dvd_mult_right_iff[OF coprime, of "int source-int target"]
        multiple by simp
  qed
  have defect_criterion:
    "(2::int)^(2*length bits) dvd defect \<longleftrightarrow>
      modulus dvd int source - int target"
  proof -
    have power: "(2::int)^(2*length bits) = modulus * modulus"
      by (simp add: modulus_def power_mult power2_eq_square mult.commute)
    show ?thesis
      using source_defect_factor modulus_positive
      by (simp add: power source_defect_factor)
  qed
  show ?thesis
  proof
    assume target_admitted:
      "collatz_guarded_normalized_word_admitted bits target"
    have divides: "modulus dvd int source - int target"
      by (rule target_residue_implies_divisibility[OF target_admitted])
    show "(2::int)^(2*length bits) dvd defect"
      using divides defect_criterion by blast
  next
    assume "(2::int)^(2*length bits) dvd defect"
    then have divides: "modulus dvd int source - int target"
      using defect_criterion by blast
    have residue:
      "source mod 2^(length bits) = target mod 2^(length bits)"
      using source_residue_iff divides by blast
    show "collatz_guarded_normalized_word_admitted bits target"
      by (rule residue_admission[OF residue])
  qed
qed

lemma collatz_temporal_word_defect_divides_modulus:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "((2::int)^length bits) dvd
      collatz_temporal_word_defect bits source"
proof -
  have affine:
    "joint_dyadic_gain (collatz_joint_dyadic_word bits) * source +
      joint_dyadic_offset (collatz_joint_dyadic_word bits) =
        2^(joint_dyadic_steps (collatz_joint_dyadic_word bits)) *
          collatz_guarded_normalized_word_endpoint bits source"
    using collatz_guarded_word_affine_endpoint[OF admitted] by simp
  have affine_int:
    "int (joint_dyadic_gain (collatz_joint_dyadic_word bits)) * int source +
      int (joint_dyadic_offset (collatz_joint_dyadic_word bits)) =
        (2::int)^(joint_dyadic_steps (collatz_joint_dyadic_word bits)) *
          int (collatz_guarded_normalized_word_endpoint bits source)"
    by (rule collatz_nat_affine_cast[OF affine])
  have same_steps:
    "joint_dyadic_steps (collatz_joint_dyadic_word bits) = length bits"
    by (rule collatz_joint_dyadic_word_steps)
  have exact:
    "collatz_temporal_word_defect bits source =
      (2::int)^length bits *
        (int source - int (collatz_guarded_normalized_word_endpoint bits source))"
    using affine_int
    by (simp only: collatz_temporal_word_defect_def same_steps
        algebra_simps; linarith)
  show ?thesis using exact by (auto simp: dvd_def)
qed

lemma collatz_temporal_word_defect_source_factor:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_temporal_word_defect bits source =
    (2::int)^length bits *
      (int source - int (collatz_guarded_normalized_word_endpoint bits source))"
proof -
  have affine:
    "joint_dyadic_gain (collatz_joint_dyadic_word bits) * source +
      joint_dyadic_offset (collatz_joint_dyadic_word bits) =
        2^(joint_dyadic_steps (collatz_joint_dyadic_word bits)) *
          collatz_guarded_normalized_word_endpoint bits source"
    using collatz_guarded_word_affine_endpoint[OF admitted] by simp
  have affine_int:
    "int (joint_dyadic_gain (collatz_joint_dyadic_word bits)) * int source +
      int (joint_dyadic_offset (collatz_joint_dyadic_word bits)) =
        (2::int)^(joint_dyadic_steps (collatz_joint_dyadic_word bits)) *
          int (collatz_guarded_normalized_word_endpoint bits source)"
    by (rule collatz_nat_affine_cast[OF affine])
  have same_steps:
    "joint_dyadic_steps (collatz_joint_dyadic_word bits) = length bits"
    by (rule collatz_joint_dyadic_word_steps)
  show ?thesis using affine_int
    by (simp only: collatz_temporal_word_defect_def same_steps
        algebra_simps; linarith)
qed

lemma collatz_temporal_word_defect_endpoint:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
      and "modulus \<equiv> (2::int)^length bits"
  shows "collatz_temporal_word_defect bits target =
      int (joint_dyadic_gain (collatz_joint_dyadic_word bits)) *
        (collatz_temporal_word_defect bits source div modulus)"
proof -
  have same_steps:
    "joint_dyadic_steps (collatz_joint_dyadic_word bits) = length bits"
    by (rule collatz_joint_dyadic_word_steps)
  have source_factor:
    "collatz_temporal_word_defect bits source =
      modulus * (int source - int target)"
    using collatz_temporal_word_defect_source_factor[OF admitted]
    by (simp add: target_def modulus_def)
  have quotient:
    "collatz_temporal_word_defect bits source div modulus =
      int source - int target"
    using source_factor
    by (simp add: div_mult_self1 mult.commute modulus_def)
  have recurrence:
    "collatz_temporal_word_defect bits target =
      int (joint_dyadic_gain (collatz_joint_dyadic_word bits)) *
        (collatz_temporal_word_defect bits source div modulus)"
    using collatz_guarded_word_defect_recurrence[OF admitted]
    by (simp add: collatz_temporal_word_defect_def target_def modulus_def
        same_steps)
  show ?thesis using recurrence .
qed

lemma collatz_int_power_dvd_cancel_mult_left:
  fixes m q :: int
  assumes nonzero: "m \<noteq> 0"
  shows "m^(Suc k) dvd m*q \<longleftrightarrow> m^k dvd q"
proof
  assume divides: "m^(Suc k) dvd m*q"
  then obtain c where equation: "m*q = m^(Suc k)*c"
    by (elim dvdE)
  have factor: "m*q = m*(m^k*c)"
    using equation by (simp add: power_Suc algebra_simps)
  have quotient: "q = m^k*c"
    using factor nonzero by (metis mult_left_cancel)
  show "m^k dvd q" using quotient by (auto simp: dvd_def)
next
  assume divides: "m^k dvd q"
  then obtain c where equation: "q = m^k*c" by (elim dvdE)
  have "m*q = m^(Suc k)*c"
    using equation by (simp add: power_Suc algebra_simps)
  then show "m^(Suc k) dvd m*q" by (auto simp: dvd_def)
qed

lemma collatz_temporal_word_defect_power_shift:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
      and "modulus \<equiv> (2::int)^length bits"
  shows "modulus^k dvd collatz_temporal_word_defect bits target \<longleftrightarrow>
      modulus^(Suc k) dvd collatz_temporal_word_defect bits source"
proof -
  have source_factor:
    "collatz_temporal_word_defect bits source =
      modulus * (int source - int target)"
    using collatz_temporal_word_defect_source_factor[OF admitted]
    by (simp add: target_def modulus_def)
  have endpoint_factor:
    "collatz_temporal_word_defect bits target =
      int (joint_dyadic_gain (collatz_joint_dyadic_word bits)) *
        (int source - int target)"
    using collatz_temporal_word_defect_endpoint[OF admitted]
      source_factor
    by (simp add: target_def modulus_def)
  have gain_coprime: "coprime modulus
      (int (joint_dyadic_gain (collatz_joint_dyadic_word bits)))"
    using collatz_joint_dyadic_word_gain_odd[of bits]
    by (simp add: modulus_def coprime_power_left_iff)
  have power_coprime:
    "coprime (modulus^k)
      (int (joint_dyadic_gain (collatz_joint_dyadic_word bits)))"
    using gain_coprime by (simp add: coprime_power_left_iff)
  have source_divisibility:
    "modulus^(Suc k) dvd collatz_temporal_word_defect bits source \<longleftrightarrow>
      modulus^k dvd int source - int target"
    using collatz_int_power_dvd_cancel_mult_left[
        where m=modulus and q="int source - int target" and k=k]
      modulus_def source_factor by simp
  have endpoint_divisibility:
    "modulus^k dvd collatz_temporal_word_defect bits target \<longleftrightarrow>
      modulus^k dvd int source - int target"
    using endpoint_factor
      coprime_dvd_mult_right_iff[OF power_coprime,
        of "int source - int target"]
    by simp
  show ?thesis using source_divisibility endpoint_divisibility by blast
qed

theorem collatz_guarded_word_repetition_cylinder:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_guarded_normalized_word_admitted
      (concat (replicate (Suc repeats) bits)) source \<longleftrightarrow>
    ((2::int)^length bits)^(Suc repeats) dvd
      collatz_temporal_word_defect bits source"
  using admitted
proof (induction repeats arbitrary: source)
  case "0"
  have divides: "((2::int)^length bits) dvd
      collatz_temporal_word_defect bits source"
    by (rule collatz_temporal_word_defect_divides_modulus[OF "0.prems"])
  show ?case using "0.prems" divides by simp
next
  case (Suc repeats)
  let ?modulus = "(2::int)^length bits"
  let ?target = "collatz_guarded_normalized_word_endpoint bits source"
  let ?tail = "concat (replicate (Suc repeats) bits)"
  have append:
    "collatz_guarded_normalized_word_admitted
        (concat (replicate (Suc (Suc repeats)) bits)) source \<longleftrightarrow>
      collatz_guarded_normalized_word_admitted bits source \<and>
      collatz_guarded_normalized_word_admitted ?tail ?target"
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  have tail_decomposition:
    "collatz_guarded_normalized_word_admitted ?tail ?target \<longleftrightarrow>
      collatz_guarded_normalized_word_admitted bits ?target \<and>
      collatz_guarded_normalized_word_admitted
        (concat (replicate repeats bits))
          (collatz_guarded_normalized_word_endpoint bits ?target)"
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show ?case
  proof
    assume full:
      "collatz_guarded_normalized_word_admitted
        (concat (replicate (Suc (Suc repeats)) bits)) source"
    then have tail:
      "collatz_guarded_normalized_word_admitted ?tail ?target"
      using append Suc.prems by blast
    have first_target:
      "collatz_guarded_normalized_word_admitted bits ?target"
      using tail tail_decomposition by blast
    have tail_criterion:
      "?modulus^(Suc repeats) dvd collatz_temporal_word_defect bits ?target"
      using Suc.IH[OF first_target] tail by blast
    have shift:
      "?modulus^(Suc (Suc repeats)) dvd
        collatz_temporal_word_defect bits source \<longleftrightarrow>
        ?modulus^(Suc repeats) dvd collatz_temporal_word_defect bits ?target"
      using collatz_temporal_word_defect_power_shift[OF Suc.prems] by blast
    show "?modulus^(Suc (Suc repeats)) dvd
        collatz_temporal_word_defect bits source"
      using tail_criterion shift by blast
  next
    assume criterion:
      "?modulus^(Suc (Suc repeats)) dvd
        collatz_temporal_word_defect bits source"
    have power_factor:
      "?modulus^(Suc (Suc repeats)) =
        (2::int)^(2*length bits) * ?modulus^repeats"
    proof -
      have split:
        "?modulus^(Suc (Suc repeats)) =
          ?modulus^2 * ?modulus^repeats"
        by (simp only: power_Suc power2_eq_square mult.assoc)
      have square: "(2::int)^(2*length bits) = ?modulus^2"
        by (simp add: power_mult power2_eq_square mult.commute)
      show ?thesis using split square by simp
    qed
    have power_divides:
      "(2::int)^(2*length bits) dvd ?modulus^(Suc (Suc repeats))"
      using power_factor
      by (rule dvdI[where k="?modulus^repeats"])
    have square_divides:
      "(2::int)^(2*length bits) dvd
        collatz_temporal_word_defect bits source"
      using dvd_trans[OF power_divides criterion] .
    have square_equivalence:
      "collatz_guarded_normalized_word_admitted bits ?target \<longleftrightarrow>
        (2::int)^(2*length bits) dvd
          collatz_temporal_word_defect bits source"
      using collatz_guarded_word_square_cylinder[OF Suc.prems]
      by simp
    have first_target:
      "collatz_guarded_normalized_word_admitted bits ?target"
      using square_equivalence square_divides by blast
    have shift:
      "?modulus^(Suc (Suc repeats)) dvd
        collatz_temporal_word_defect bits source \<longleftrightarrow>
        ?modulus^(Suc repeats) dvd collatz_temporal_word_defect bits ?target"
      using collatz_temporal_word_defect_power_shift[OF Suc.prems] by blast
    have tail_criterion:
      "?modulus^(Suc repeats) dvd collatz_temporal_word_defect bits ?target"
      using criterion shift by blast
    have tail:
      "collatz_guarded_normalized_word_admitted ?tail ?target"
      using Suc.IH[OF first_target] tail_criterion by blast
    show "collatz_guarded_normalized_word_admitted
        (concat (replicate (Suc (Suc repeats)) bits)) source"
      using append Suc.prems tail by blast
  qed
qed

theorem collatz_guarded_word_repetition_dyadic_cylinder:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_guarded_normalized_word_admitted
      (concat (replicate repeats bits)) source \<longleftrightarrow>
    (2::int)^(repeats * length bits) dvd
      collatz_temporal_word_defect bits source"
proof (cases repeats)
  case "0"
  then show ?thesis by simp
next
  case (Suc r)
  have criterion:
    "collatz_guarded_normalized_word_admitted
        (concat (replicate (Suc r) bits)) source \<longleftrightarrow>
      ((2::int)^length bits)^(Suc r) dvd
        collatz_temporal_word_defect bits source"
    using collatz_guarded_word_repetition_cylinder[OF admitted,
      where repeats=r] .
  have exponent: "length bits * Suc r = Suc r * length bits"
    by (rule mult.commute)
  have power_identity:
    "((2::int)^length bits)^(Suc r) =
      (2::int)^(Suc r * length bits)"
  proof -
    have "((2::int)^length bits)^(Suc r) =
        (2::int)^(length bits * Suc r)"
      by (simp only: power_mult[symmetric])
    also have "... = (2::int)^(Suc r * length bits)"
      using exponent by simp
    finally show ?thesis .
  qed
  show ?thesis using criterion Suc power_identity by simp
qed

text \<open>The runtime's global Sturmian exponents are additive across a
source-guarded repeated block: `count_list bits True` is the 3-exponent,
`length bits` is the normalized division exponent, and each odd normalized
symbol contributes one additional physical tick.  This is a clock-composition
law only; the cylinder theorem above remains the authority for reusing the
same word at a later source.\<close>

definition collatz_normalized_clock :: "bool list \<Rightarrow> nat \<times> nat" where
  "collatz_normalized_clock bits = (count_list bits True, length bits)"

definition collatz_physical_ticks :: "bool list \<Rightarrow> nat" where
  "collatz_physical_ticks bits = length bits + count_list bits True"

lemma collatz_repeated_word_clock:
  "collatz_normalized_clock (concat (replicate repetitions bits)) =
      (repetitions * count_list bits True, repetitions * length bits)"
  "collatz_physical_ticks (concat (replicate repetitions bits)) =
      repetitions * collatz_physical_ticks bits"
proof -
  have length_repeat:
    "length (concat (replicate repetitions bits)) = repetitions * length bits"
    by (induction repetitions) simp_all
  have count_repeat:
    "count_list (concat (replicate repetitions bits)) True =
      repetitions * count_list bits True"
    by (induction repetitions) (simp_all add: count_list_append)
  show "collatz_normalized_clock (concat (replicate repetitions bits)) =
      (repetitions * count_list bits True, repetitions * length bits)"
    using length_repeat count_repeat
    by (simp add: collatz_normalized_clock_def)
  show "collatz_physical_ticks (concat (replicate repetitions bits)) =
      repetitions * collatz_physical_ticks bits"
    using length_repeat count_repeat
    by (simp add: collatz_physical_ticks_def algebra_simps)
qed

text \<open>The residue-cylinder theorem is the induction principle used when a
fixed word is considered again at a later endpoint.  The defect recurrence
tracks its exact affine displacement.  A caller may combine these facts with
its own source-issued repeat budget; this theory does not convert a parity
continuation into a named-family transition.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_temporal_source_step_translation
      collatz_guarded_word_admitted_iff_temporal_word
      collatz_guarded_word_same_residue_cylinder
      collatz_affine_defect_recurrence
      collatz_guarded_word_affine_endpoint
      collatz_guarded_word_affine_high_digits
      collatz_guarded_word_defect_recurrence
      collatz_guarded_word_square_cylinder
      collatz_temporal_word_defect_source_factor
      collatz_temporal_word_defect_endpoint
      collatz_temporal_word_defect_power_shift
      collatz_guarded_word_repetition_cylinder
      collatz_guarded_word_repetition_dyadic_cylinder
      collatz_repeated_word_clock}) then ()
    else error "Temporal Collatz squaring depends on an oracle";
\<close>

end
