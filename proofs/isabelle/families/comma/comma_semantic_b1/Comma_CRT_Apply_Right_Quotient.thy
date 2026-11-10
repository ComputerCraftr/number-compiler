theory Comma_CRT_Apply_Right_Quotient
  imports Comma_CRT_Apply
begin

lemma comma_crt_apply_shifted_from_shift_equiv:
  assumes depth_bound: "depth \<le> 4"
    and zero_branch: "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
    and suffix_residues:
      "\<forall>level. 4-depth \<le> level \<longrightarrow> level < 4 \<longrightarrow>
        shift mod comma_crt_period level = shift' mod comma_crt_period level"
  shows "comma_crt_apply_shifted_from depth shift operation left right =
    comma_crt_apply_shifted_from depth shift' operation left right"
  using assms
proof (induction depth arbitrary: shift shift' operation left right)
  case 0
  then show ?case
    by (simp add: comma_crt_apply_shifted_from.simps
        comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)
next
  case (Suc depth)
  let ?level = "4 - Suc depth"
  have level_lt: "?level < 4" by arith
  have shift_residue:
    "shift mod comma_crt_period ?level = shift' mod comma_crt_period ?level"
    using Suc.prems(3) level_lt by blast
  have shifted_index:
    "(digit + shift) mod comma_crt_period ?level =
      (digit + shift') mod comma_crt_period ?level" for digit
    by (rule mod_add_cong[OF refl shift_residue])
  have child_residues:
    "\<forall>level. 4-depth \<le> level \<longrightarrow> level < 4 \<longrightarrow>
      shift mod comma_crt_period level = shift' mod comma_crt_period level"
  proof (intro allI impI)
    fix level
    assume lower: "4-depth \<le> level" and upper: "level < 4"
    have parent_lower: "4 - Suc depth \<le> level" using lower by arith
    show "shift mod comma_crt_period level = shift' mod comma_crt_period level"
      using Suc.prems(3) parent_lower upper by blast
  qed
  have child_depth_bound: "depth \<le> 4" using Suc.prems(1) by arith
  have child_apply:
    "\<And>digit. comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right) =
      comma_crt_apply_shifted_from depth shift' operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift' right)"
  proof -
    fix digit
    have right_alignment:
      "comma_crt_apply_shifted_from depth shift' operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift' right) =
        comma_crt_apply_shifted_from depth shift' operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
      by (simp only: comma_crt_shifted_cofactor_or_false_as_cofactor shifted_index)
    have induction_result:
      "comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right) =
        comma_crt_apply_shifted_from depth shift' operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
    proof (rule Suc.IH)
      show "depth \<le> 4" by (rule child_depth_bound)
      show "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
        by (rule Suc.prems(2))
      show "\<forall>level. 4-depth \<le> level \<longrightarrow> level < 4 \<longrightarrow>
        shift mod comma_crt_period level = shift' mod comma_crt_period level"
        by (rule child_residues)
    qed
    show "comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right) =
      comma_crt_apply_shifted_from depth shift' operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift' right)"
      using induction_result right_alignment by simp
  qed
  have children_equal:
    "map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right))
      [0..<comma_crt_period ?level] =
     map (\<lambda>digit. comma_crt_apply_shifted_from depth shift' operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift' right))
      [0..<comma_crt_period ?level]"
    by (rule map_cong[OF refl]) (rule child_apply)
  have shortcut_equal:
    "comma_crt_shifted_apply_shortcut operation shift left right =
      comma_crt_shifted_apply_shortcut operation shift' left right"
    using Suc.prems(2)
    by (simp add: comma_crt_shifted_apply_shortcut_def)
  show ?case
  proof (cases "comma_crt_shifted_apply_shortcut operation shift left right")
    case None
    have other_none:
      "comma_crt_shifted_apply_shortcut operation shift' left right = None"
      using shortcut_equal None by simp
    show ?thesis
      by (simp only: comma_crt_apply_shifted_from.simps None other_none
          option.case Let_def level_lt if_True children_equal)
  next
    case (Some result)
    have other_some:
      "comma_crt_shifted_apply_shortcut operation shift' left right = Some result"
      using shortcut_equal Some by simp
    show ?thesis
      by (simp only: comma_crt_apply_shifted_from.simps Some other_some option.case)
  qed
qed

definition comma_crt_apply_suffix_period :: "nat \<Rightarrow> nat" where
  "comma_crt_apply_suffix_period depth =
    (if depth = 0 then 1 else if depth = 1 then 11 else
      if depth = 2 then 77 else if depth = 3 then 231 else 924)"

lemma comma_crt_apply_period_divides_suffix:
  assumes depth_bound: "depth \<le> 4"
    and lower: "4-depth \<le> level"
    and upper: "level < 4"
  shows "comma_crt_period level dvd comma_crt_apply_suffix_period depth"
proof -
  have depth_cases: "depth = 0 \<or> depth = 1 \<or> depth = 2 \<or>
      depth = 3 \<or> depth = 4" using depth_bound by arith
  have level_cases: "level = 0 \<or> level = 1 \<or> level = 2 \<or> level = 3"
    using upper by arith
  show ?thesis
    using depth_cases level_cases lower
    by (elim disjE; simp_all add: comma_crt_apply_suffix_period_def
        comma_crt_period_def dvd_eq_mod_eq_0)
qed

lemma comma_crt_apply_shifted_from_suffix_equiv:
  assumes depth_bound: "depth \<le> 4"
    and zero_branch: "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
    and suffix_residue:
      "shift mod comma_crt_apply_suffix_period depth =
        shift' mod comma_crt_apply_suffix_period depth"
  shows "comma_crt_apply_shifted_from depth shift operation left right =
    comma_crt_apply_shifted_from depth shift' operation left right"
proof (rule comma_crt_apply_shifted_from_shift_equiv[OF depth_bound zero_branch])
  show "\<forall>level. 4-depth \<le> level \<longrightarrow> level < 4 \<longrightarrow>
      shift mod comma_crt_period level = shift' mod comma_crt_period level"
  proof (intro allI impI)
    fix level
    assume lower: "4-depth \<le> level" and upper: "level < 4"
    have divides: "comma_crt_period level dvd
        comma_crt_apply_suffix_period depth"
      by (rule comma_crt_apply_period_divides_suffix[OF depth_bound lower upper])
    have shift_cancel:
      "(shift mod comma_crt_apply_suffix_period depth) mod comma_crt_period level =
        shift mod comma_crt_period level"
      by (rule mod_mod_cancel[OF divides])
    have shift'_cancel:
      "(shift' mod comma_crt_apply_suffix_period depth) mod comma_crt_period level =
        shift' mod comma_crt_period level"
      by (rule mod_mod_cancel[OF divides])
    show "shift mod comma_crt_period level = shift' mod comma_crt_period level"
      using suffix_residue shift_cancel shift'_cancel by metis
  qed
qed

lemma comma_crt_shifted_cofactor_equal_at_level:
  assumes residue:
      "shift mod comma_crt_period level = shift' mod comma_crt_period level"
  shows "comma_crt_shifted_cofactor_or_false level digit shift column =
    comma_crt_shifted_cofactor_or_false level digit shift' column"
proof -
  have index_eq:
    "(digit + shift) mod comma_crt_period level =
     (digit + shift') mod comma_crt_period level"
    by (rule mod_add_cong[OF refl residue])
  show ?thesis using index_eq
    by (simp only: comma_crt_shifted_cofactor_or_false_as_cofactor index_eq)
qed

lemma comma_crt_shifted_cofactor_admitted_from_lower:
  assumes admitted: "comma_crt_admitted lower column"
    and lower: "lower \<le> level"
    and level: "level < 4"
  shows "comma_crt_admitted (Suc level)
    (comma_crt_shifted_cofactor_or_false level digit shift column)"
proof (cases column)
  case (Comma_CRT_Bool payload)
  then show ?thesis
    by (simp add: comma_crt_shifted_cofactor_or_false_def
        comma_crt_cofactor_or_false_def)
next
  case (Comma_CRT_Node node_level children)
  have node_facts: "lower \<le> node_level" "node_level < 4"
      "length children = comma_crt_period node_level"
      "list_all (comma_crt_admitted (Suc node_level)) children"
    using admitted Comma_CRT_Node by (auto simp: list_all_iff)
  show ?thesis
  proof (cases "node_level < level")
    case True
    then show ?thesis using Comma_CRT_Node
      by (simp add: comma_crt_shifted_cofactor_or_false_def
          comma_crt_cofactor_or_false_def)
  next
    case False
    then have level_le_node: "level \<le> node_level" by simp
    show ?thesis
    proof (cases "node_level = level")
      case True
      have width: "length children = comma_crt_period level"
        using node_facts(3) True by simp
      have index_bound:
        "(digit + shift) mod comma_crt_period level < length children"
      proof -
        have "(digit + shift) mod comma_crt_period level <
            comma_crt_period level"
          by (rule mod_less_divisor;
              rule comma_crt_period_positive[OF level])
        then show ?thesis using width by simp
      qed
      have child_admitted:
        "comma_crt_admitted (Suc level)
          (children ! ((digit + shift) mod comma_crt_period level))"
        using node_facts(4) True index_bound by (simp add: list_all_iff)
      show ?thesis using Comma_CRT_Node True child_admitted
        by (simp add: comma_crt_shifted_cofactor_or_false_def
            comma_crt_cofactor_or_false_def)
    next
      case False
      have level_lt_node: "level < node_level"
        using level_le_node False by simp
      have node_order: "Suc level \<le> node_level"
        using level_lt_node by simp
      show ?thesis using Comma_CRT_Node node_facts(2,3)
          node_facts(4) node_order
        by (simp add: comma_crt_shifted_cofactor_or_false_def
            comma_crt_cofactor_or_false_def)
    qed
  qed
qed

lemma comma_crt_apply_shifted_from_right_suffix_equiv:
  assumes depth_bound: "depth \<le> 4"
    and zero_branch:
      "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
    and right_admitted: "comma_crt_admitted lower right"
    and right_suffix_residues:
      "\<forall>level. lower \<le> level \<longrightarrow> level < 4 \<longrightarrow>
        shift mod comma_crt_period level = shift' mod comma_crt_period level"
  shows "comma_crt_apply_shifted_from depth shift operation left right =
    comma_crt_apply_shifted_from depth shift' operation left right"
  using assms
proof (induction depth arbitrary: lower shift shift' operation left right)
  case 0
  then show ?case
    by (simp add: comma_crt_apply_shifted_from.simps
        comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)
next
  case (Suc depth)
  let ?level = "4 - Suc depth"
  let ?next_lower = "if ?level < lower then lower else Suc ?level"
  have level_lt: "?level < 4" using Suc.prems(1) by arith
  have shortcut_equal:
    "comma_crt_shifted_apply_shortcut operation shift left right =
      comma_crt_shifted_apply_shortcut operation shift' left right"
    using Suc.prems(2)
    by (simp add: comma_crt_shifted_apply_shortcut_def)

  have right_alignment:
    "comma_crt_shifted_cofactor_or_false ?level digit shift right =
      comma_crt_shifted_cofactor_or_false ?level digit shift' right"
    for digit
  proof (cases "?level < lower")
    case True
    have level_admitted: "comma_crt_admitted (Suc ?level) right"
      by (rule comma_crt_admitted_mono[OF _ Suc.prems(3)])
         (use True in simp)
    have left_cofactor:
      "comma_crt_cofactor ?level ((digit + shift) mod
          comma_crt_period ?level) right = Some right"
      by (rule comma_crt_apply_cofactor_skip_from_admission[OF level_admitted])
    have right_cofactor:
      "comma_crt_cofactor ?level ((digit + shift') mod
          comma_crt_period ?level) right = Some right"
      by (rule comma_crt_apply_cofactor_skip_from_admission[OF level_admitted])
    show ?thesis using left_cofactor right_cofactor
      by (simp add: comma_crt_shifted_cofactor_or_false_def
          comma_crt_cofactor_or_false_def)
  next
    case False
    have lower_level: "lower \<le> ?level" using False by simp
    have residue:
      "shift mod comma_crt_period ?level = shift' mod comma_crt_period ?level"
      using Suc.prems(4) lower_level level_lt by blast
    show ?thesis
      by (rule comma_crt_shifted_cofactor_equal_at_level
          [OF residue])
  qed

  have right_child_admitted:
    "comma_crt_admitted ?next_lower
      (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
    for digit
  proof (cases "?level < lower")
    case True
    have level_admitted: "comma_crt_admitted (Suc ?level) right"
      by (rule comma_crt_admitted_mono[OF _ Suc.prems(3)])
         (use True in simp)
    have cofactor:
      "comma_crt_cofactor ?level ((digit + shift) mod
          comma_crt_period ?level) right = Some right"
      by (rule comma_crt_apply_cofactor_skip_from_admission[OF level_admitted])
    show ?thesis using True cofactor Suc.prems(3)
      by (simp add: comma_crt_shifted_cofactor_or_false_def
          comma_crt_cofactor_or_false_def)
  next
    case False
    have lower_level: "lower \<le> ?level" using False by simp
    have admitted:
      "comma_crt_admitted (Suc ?level)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
      by (rule comma_crt_shifted_cofactor_admitted_from_lower
          [OF Suc.prems(3) lower_level level_lt])
    show ?thesis using False admitted by simp
  qed

  have next_residues:
    "\<forall>level. ?next_lower \<le> level \<longrightarrow> level < 4 \<longrightarrow>
      shift mod comma_crt_period level = shift' mod comma_crt_period level"
  proof (intro allI impI)
    fix level
    assume next_lower: "?next_lower \<le> level"
      and level_bound: "level < 4"
    have lower_bound: "lower \<le> level"
    proof (cases "?level < lower")
      case True
      then show ?thesis using next_lower by simp
    next
      case False
      have lower_current: "lower \<le> ?level" using False by simp
      have current_next: "Suc ?level \<le> level"
        using False next_lower by simp
      show ?thesis using lower_current current_next by arith
    qed
    show "shift mod comma_crt_period level = shift' mod comma_crt_period level"
      using Suc.prems(4) lower_bound level_bound by blast
  qed

  have child_apply:
    "comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right) =
      comma_crt_apply_shifted_from depth shift' operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift' right)"
    for digit
  proof -
    have induction_result:
      "comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right) =
        comma_crt_apply_shifted_from depth shift' operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
    proof (rule Suc.IH)
      show "depth \<le> 4" using Suc.prems(1) by arith
      show "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
        by (rule Suc.prems(2))
      show "comma_crt_admitted ?next_lower
          (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
        by (rule right_child_admitted)
      show "\<forall>level. ?next_lower \<le> level \<longrightarrow> level < 4 \<longrightarrow>
          shift mod comma_crt_period level = shift' mod comma_crt_period level"
        by (rule next_residues)
    qed
    show ?thesis using induction_result right_alignment by simp
  qed

  have children_equal:
    "map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right))
      [0..<comma_crt_period ?level] =
     map (\<lambda>digit. comma_crt_apply_shifted_from depth shift' operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift' right))
      [0..<comma_crt_period ?level]"
    by (rule map_cong[OF refl]) (rule child_apply)

  show ?case
  proof (cases "comma_crt_shifted_apply_shortcut operation shift left right")
    case None
    have other_none:
      "comma_crt_shifted_apply_shortcut operation shift' left right = None"
      using shortcut_equal None by simp
    show ?thesis
      by (simp only: comma_crt_apply_shifted_from.simps None other_none
          option.case Let_def level_lt if_True children_equal)
  next
    case (Some result)
    have other_some:
      "comma_crt_shifted_apply_shortcut operation shift' left right = Some result"
      using shortcut_equal Some by simp
    show ?thesis
      by (simp only: comma_crt_apply_shifted_from.simps Some other_some option.case)
  qed
qed

corollary comma_crt_apply_shifted_from_right_suffix_period_equiv:
  assumes depth_bound: "depth \<le> 4"
    and support_bound: "lower \<le> 4"
    and zero_branch:
      "(shift mod 924 = 0) \<longleftrightarrow> (shift' mod 924 = 0)"
    and right_admitted: "comma_crt_admitted lower right"
    and suffix_residue:
      "shift mod comma_crt_apply_suffix_period (4-lower) =
       shift' mod comma_crt_apply_suffix_period (4-lower)"
  shows "comma_crt_apply_shifted_from depth shift operation left right =
    comma_crt_apply_shifted_from depth shift' operation left right"
proof (rule comma_crt_apply_shifted_from_right_suffix_equiv
    [OF depth_bound zero_branch right_admitted])
  show "\<forall>level. lower \<le> level \<longrightarrow> level < 4 \<longrightarrow>
      shift mod comma_crt_period level = shift' mod comma_crt_period level"
  proof (intro allI impI)
    fix level
    assume lower: "lower \<le> level" and upper: "level < 4"
    have apply_depth_bound: "4-lower \<le> 4"
      using support_bound by arith
    have apply_lower_bound: "4-(4-lower) \<le> level"
      using support_bound lower by arith
    have divides: "comma_crt_period level dvd
        comma_crt_apply_suffix_period (4-lower)"
      by (rule comma_crt_apply_period_divides_suffix
          [OF apply_depth_bound apply_lower_bound upper])
    have shift_cancel:
      "(shift mod comma_crt_apply_suffix_period (4-lower)) mod
          comma_crt_period level = shift mod comma_crt_period level"
      by (rule mod_mod_cancel[OF divides])
    have shift'_cancel:
      "(shift' mod comma_crt_apply_suffix_period (4-lower)) mod
          comma_crt_period level = shift' mod comma_crt_period level"
      by (rule mod_mod_cancel[OF divides])
    show "shift mod comma_crt_period level = shift' mod comma_crt_period level"
      using suffix_residue shift_cancel shift'_cancel by metis
  qed
qed

ML \<open>
  val checked = @{thms comma_crt_shifted_cofactor_equal_at_level
    comma_crt_shifted_cofactor_admitted_from_lower
    comma_crt_apply_shifted_from_right_suffix_equiv
    comma_crt_apply_shifted_from_right_suffix_period_equiv
    comma_crt_apply_shifted_from_shift_equiv
    comma_crt_apply_period_divides_suffix
    comma_crt_apply_shifted_from_suffix_equiv};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Right-column clock quotient" checked;
\<close>

end
