theory Reverse_Mod7_Controlled_Action
  imports Reverse_Punctured_T2_Coefficients "HOL-Number_Theory.Cong"
begin

text \<open>This theory certifies the finite affine action on an already supplied
physical carry port. It does not prove that any port word repeats along the
reverse/add orbit, and therefore does not authorize source evolution by
powering alone.\<close>

record reverse_mod7_action =
  reverse_mod7_multiplier :: nat
  reverse_mod7_correction :: nat

definition reverse_mod7_apply ::
    "reverse_mod7_action \<Rightarrow> nat \<Rightarrow> nat" where
  "reverse_mod7_apply action x =
    (reverse_mod7_multiplier action * x +
      reverse_mod7_correction action) mod 7"

definition reverse_mod7_compose ::
    "reverse_mod7_action \<Rightarrow> reverse_mod7_action \<Rightarrow>
      reverse_mod7_action" where
  "reverse_mod7_compose earlier later =
    \<lparr>reverse_mod7_multiplier =
        (reverse_mod7_multiplier later * reverse_mod7_multiplier earlier) mod 7,
      reverse_mod7_correction =
        (reverse_mod7_multiplier later * reverse_mod7_correction earlier +
          reverse_mod7_correction later) mod 7\<rparr>"

definition reverse_mod7_port_action ::
    "nat \<Rightarrow> nat \<Rightarrow> reverse_mod7_action" where
  "reverse_mod7_port_action defect growth =
    \<lparr>reverse_mod7_multiplier = (1 + 3^growth) mod 7,
      reverse_mod7_correction =
        (growth + 7 - (3^growth * defect mod 7)) mod 7\<rparr>"

definition reverse_mod7_canonical ::
    "reverse_mod7_action \<Rightarrow> bool" where
  "reverse_mod7_canonical action =
    (reverse_mod7_multiplier action \<in> {1,2,4} \<and>
      reverse_mod7_correction action < 7)"

definition reverse_mod7_identity :: reverse_mod7_action where
  "reverse_mod7_identity = \<lparr>reverse_mod7_multiplier = 1,
    reverse_mod7_correction = 0\<rparr>"

definition reverse_mod7_letters :: "reverse_mod7_action list" where
  "reverse_mod7_letters = concat
    (map (\<lambda>growth. map (\<lambda>defect.
      reverse_mod7_port_action defect growth) [0..<7]) [0,1])"

definition reverse_mod7_actions_up_to_two_letters ::
    "reverse_mod7_action list" where
  "reverse_mod7_actions_up_to_two_letters =
    reverse_mod7_identity # reverse_mod7_letters @
      concat (map (\<lambda>earlier. map (\<lambda>later.
        reverse_mod7_compose earlier later) reverse_mod7_letters)
        reverse_mod7_letters)"

definition reverse_mod7_canonical_actions ::
    "reverse_mod7_action list" where
  "reverse_mod7_canonical_actions = concat
    (map (\<lambda>multiplier. map (\<lambda>correction.
      \<lparr>reverse_mod7_multiplier = multiplier,
        reverse_mod7_correction = correction\<rparr>) [0..<7]) [1,2,4])"

lemma reverse_mod7_port_action_canonical:
  assumes growth: "growth \<le> 1"
      and defect: "defect < 7"
  shows "reverse_mod7_canonical (reverse_mod7_port_action defect growth)"
  using growth
  by (cases growth; simp add: reverse_mod7_canonical_def
      reverse_mod7_port_action_def)

lemma reverse_mod7_compose_canonical:
  assumes earlier: "reverse_mod7_canonical earlier"
      and later: "reverse_mod7_canonical later"
  shows "reverse_mod7_canonical (reverse_mod7_compose earlier later)"
proof -
  have multiplier_closed:
    "(a::nat) \<in> {1,2,4} \<Longrightarrow> (b::nat) \<in> {1,2,4} \<Longrightarrow>
      (a * b) mod 7 \<in> {1,2,4}"
    by auto
  show ?thesis using earlier later
    unfolding reverse_mod7_canonical_def reverse_mod7_compose_def
    by (auto intro: multiplier_closed)
qed

lemma reverse_mod7_affine_mod_congruence:
  fixes a b c d x :: nat
  shows "((b * a mod 7 * x + (b * c + d) mod 7) mod 7) =
    ((b * ((a * x + c) mod 7) + d) mod 7)"
proof -
  have first_product:
    "(b * a mod 7 * x) mod 7 = (b * a * x) mod 7"
  proof (rule mod_mult_cong)
    show "(b * a mod 7) mod 7 = (b * a) mod 7" by simp
    show "x mod 7 = x mod 7" by simp
  qed
  have left_normalized:
    "((b * a mod 7 * x + (b * c + d) mod 7) mod 7) =
      ((b * a * x + (b * c + d)) mod 7)"
    using mod_add_cong[OF first_product] by simp
  have inner_product:
    "(b * ((a * x + c) mod 7)) mod 7 =
      (b * (a * x + c)) mod 7"
  proof (rule mod_mult_cong)
    show "b mod 7 = b mod 7" by simp
    show "((a * x + c) mod 7) mod 7 = (a * x + c) mod 7" by simp
  qed
  have right_normalized:
    "((b * ((a * x + c) mod 7) + d) mod 7) =
      ((b * (a * x + c) + d) mod 7)"
    using mod_add_cong[OF inner_product refl] .
  show ?thesis
    using left_normalized right_normalized
    by (simp add: algebra_simps)
qed

lemma reverse_mod7_compose_apply:
  "reverse_mod7_apply (reverse_mod7_compose earlier later) x =
    reverse_mod7_apply later (reverse_mod7_apply earlier x)"
  by (cases earlier; cases later;
      simp add: reverse_mod7_apply_def reverse_mod7_compose_def
        reverse_mod7_affine_mod_congruence)

lemma reverse_mod7_two_letter_reachability:
  "set reverse_mod7_actions_up_to_two_letters =
    set reverse_mod7_canonical_actions"
  by code_simp

lemma reverse_mod7_canonical_action_count:
  "length reverse_mod7_canonical_actions = 21 \<and>
    distinct reverse_mod7_canonical_actions"
  by code_simp

lemma reverse_mod7_action_semantics_determined:
  assumes left: "reverse_mod7_canonical earlier"
      and right: "reverse_mod7_canonical later"
      and at_zero: "reverse_mod7_apply earlier 0 = reverse_mod7_apply later 0"
      and at_one: "reverse_mod7_apply earlier 1 = reverse_mod7_apply later 1"
  shows "earlier = later"
proof -
  obtain a c where earlier_record:
    "earlier = \<lparr>reverse_mod7_multiplier = a,
      reverse_mod7_correction = c\<rparr>"
    by (cases earlier) auto
  obtain b d where later_record:
    "later = \<lparr>reverse_mod7_multiplier = b,
      reverse_mod7_correction = d\<rparr>"
    by (cases later) auto
  have a_class: "a \<in> {1,2,4}"
    using left by (simp add: reverse_mod7_canonical_def earlier_record)
  have b_class: "b \<in> {1,2,4}"
    using right by (simp add: reverse_mod7_canonical_def later_record)
  have c_bound: "c < 7"
    using left by (simp add: reverse_mod7_canonical_def earlier_record)
  have d_bound: "d < 7"
    using right by (simp add: reverse_mod7_canonical_def later_record)
  have correction_residues: "c mod 7 = d mod 7"
    using at_zero by (simp add: reverse_mod7_apply_def earlier_record later_record)
  have correction_equal: "c = d"
    using correction_residues c_bound d_bound by simp
  have successor_residues: "(a + c) mod 7 = (b + d) mod 7"
    using at_one by (simp add: reverse_mod7_apply_def earlier_record later_record)
  have multiplier_congruence: "[a = b] (mod 7)"
  proof -
    have translated: "[a + c = b + c] (mod 7)"
      using successor_residues correction_equal by (simp add: cong_def)
    show ?thesis using translated by (metis cong_add_rcancel_nat)
  qed
  have multiplier_equal: "a = b"
    using multiplier_congruence a_class b_class
    by (auto simp: cong_def)
  show ?thesis
    using earlier_record later_record correction_equal multiplier_equal
    by simp
qed

lemma reverse_mod7_port_equation:
  assumes growth: "growth \<le> 1"
      and defect: "defect < 7"
      and input: "input < 7"
  shows "reverse_mod7_apply (reverse_mod7_port_action defect growth) input =
    ((1 + 3^growth) * input + growth + 7 -
      (3^growth * defect mod 7)) mod 7"
proof -
  let ?coefficient = "1 + 3^growth"
  let ?carry = "3^growth * defect mod 7"
  have carry_lt: "?carry < 7" by simp
  have carry_bound: "?carry \<le> growth + 7"
  proof (rule le_trans)
    show "?carry \<le> 7" using carry_lt by (rule less_imp_le)
    show "7 \<le> growth + 7" by simp
  qed
  have product_mod:
    "((?coefficient mod 7) * input) mod 7 =
      (?coefficient * input) mod 7"
    by (rule mod_mult_left_eq)
  have correction_mod:
    "((growth + 7 - ?carry) mod 7) mod 7 =
      (growth + 7 - ?carry) mod 7"
    by simp
  have combined_mod:
    "((?coefficient mod 7) * input +
        (growth + 7 - ?carry) mod 7) mod 7 =
      (?coefficient * input + growth + 7 - ?carry) mod 7"
    using mod_add_cong[OF product_mod correction_mod] carry_bound
    by (simp add: add_diff_assoc algebra_simps)
  have action_value:
    "reverse_mod7_apply (reverse_mod7_port_action defect growth) input =
      ((?coefficient mod 7) * input +
        (growth + 7 - ?carry) mod 7) mod 7"
    by (simp add: reverse_mod7_apply_def reverse_mod7_port_action_def)
  show ?thesis
  proof -
    have first:
      "reverse_mod7_apply (reverse_mod7_port_action defect growth) input =
        ((?coefficient mod 7) * input +
          (growth + 7 - ?carry) mod 7) mod 7"
      by (rule action_value)
    also have "... = (?coefficient * input + growth + 7 - ?carry) mod 7"
      by (rule combined_mod)
    finally show ?thesis by (simp add: algebra_simps)
  qed
qed

text \<open>Because 10 is 3 modulo seven, this is the scalar form of the paired
radix-3/radix-5 temporal port action. The input is the successor integer
residue; the (defect,growth) letter belongs to the completed preceding
physical step.\<close>

lemma reverse_mod7_port_multiplier:
  assumes "growth \<le> 1"
  shows "reverse_mod7_multiplier (reverse_mod7_port_action defect growth)
      \<in> {2,4}"
  using assms by (cases growth) (simp_all add: reverse_mod7_port_action_def)

ML \<open>
  val checked = @{thms reverse_mod7_port_action_canonical
    reverse_mod7_compose_canonical reverse_mod7_compose_apply
    reverse_mod7_two_letter_reachability reverse_mod7_canonical_action_count
    reverse_mod7_action_semantics_determined reverse_mod7_port_equation
    reverse_mod7_port_multiplier};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Controlled reverse mod-7 action theorem depends on an oracle";
\<close>

end

