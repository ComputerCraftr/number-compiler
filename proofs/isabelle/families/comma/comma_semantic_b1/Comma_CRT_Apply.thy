theory Comma_CRT_Apply
  imports Comma_CRT_Columns
begin
ML \<open>Comma_Proof_Profile.report "CRT apply stage=entered"\<close>

text \<open>
Matched-cofactor Boolean apply for the four CRT clock dimensions.  Recursion
is over the remaining spatial dimensions, not over elapsed time or clock
phases.  The smart node constructor removes constant and identical branches.
\<close>

datatype comma_crt_boolean_operation = Comma_CRT_And | Comma_CRT_Or

definition comma_crt_boolean_value ::
    "comma_crt_boolean_operation \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "comma_crt_boolean_value operation left right =
    (case operation of Comma_CRT_And \<Rightarrow> left \<and> right
     | Comma_CRT_Or \<Rightarrow> left \<or> right)"

definition comma_crt_apply_shortcut ::
    "comma_crt_boolean_operation \<Rightarrow> comma_crt_column \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column option" where
  "comma_crt_apply_shortcut operation left right =
    (if left=right then Some left else
      case operation of
        Comma_CRT_And \<Rightarrow>
          (if left=Comma_CRT_Bool False \<or> right=Comma_CRT_Bool False
           then Some (Comma_CRT_Bool False)
           else if left=Comma_CRT_Bool True then Some right
           else if right=Comma_CRT_Bool True then Some left else None)
      | Comma_CRT_Or \<Rightarrow>
          (if left=Comma_CRT_Bool True \<or> right=Comma_CRT_Bool True
           then Some (Comma_CRT_Bool True)
           else if left=Comma_CRT_Bool False then Some right
           else if right=Comma_CRT_Bool False then Some left else None))"

definition comma_crt_cofactor_or_false ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_cofactor_or_false level digit column =
    (case comma_crt_cofactor level digit column of
       Some child \<Rightarrow> child | None \<Rightarrow> Comma_CRT_Bool False)"

definition comma_crt_shifted_apply_shortcut ::
    "comma_crt_boolean_operation \<Rightarrow> nat \<Rightarrow> comma_crt_column \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column option" where
  "comma_crt_shifted_apply_shortcut operation shift left right =
    (if shift mod 924=0 then comma_crt_apply_shortcut operation left right
     else case operation of
       Comma_CRT_And \<Rightarrow>
         (if left=Comma_CRT_Bool False \<or> right=Comma_CRT_Bool False
          then Some (Comma_CRT_Bool False)
          else if right=Comma_CRT_Bool True then Some left
          else case (left,right) of
            (Comma_CRT_Bool x,Comma_CRT_Bool y) \<Rightarrow>
              Some (Comma_CRT_Bool (x \<and> y))
          | _ \<Rightarrow> None)
     | Comma_CRT_Or \<Rightarrow>
         (if left=Comma_CRT_Bool True \<or> right=Comma_CRT_Bool True
          then Some (Comma_CRT_Bool True)
          else if right=Comma_CRT_Bool False then Some left
          else case (left,right) of
            (Comma_CRT_Bool x,Comma_CRT_Bool y) \<Rightarrow>
              Some (Comma_CRT_Bool (x \<or> y))
          | _ \<Rightarrow> None))"

definition comma_crt_shifted_cofactor_or_false ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_shifted_cofactor_or_false level digit shift column =
    (case comma_crt_cofactor level
      ((digit+shift) mod comma_crt_period level) column of
       Some child \<Rightarrow> child | None \<Rightarrow> Comma_CRT_Bool False)"

fun comma_crt_apply_shifted_from ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_boolean_operation \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_apply_shifted_from 0 shift operation left right =
    (case comma_crt_shifted_apply_shortcut operation shift left right of
       Some result \<Rightarrow> result
     | None \<Rightarrow>
       (case (left,right) of
          (Comma_CRT_Bool x, Comma_CRT_Bool y) \<Rightarrow>
            Comma_CRT_Bool (comma_crt_boolean_value operation x y)
        | _ \<Rightarrow> Comma_CRT_Bool False))"
| "comma_crt_apply_shifted_from (Suc remaining) shift operation left right =
    (case comma_crt_shifted_apply_shortcut operation shift left right of
       Some result \<Rightarrow> result
     | None \<Rightarrow>
       (let level = 4 - Suc remaining in
        if level < 4 then
          comma_crt_node level
            (map (\<lambda>digit. comma_crt_apply_shifted_from remaining shift operation
              (comma_crt_cofactor_or_false level digit left)
              (comma_crt_shifted_cofactor_or_false level digit shift right))
              [0..<comma_crt_period level])
        else Comma_CRT_Bool False))"

lemma comma_crt_shifted_cofactor_or_false_as_cofactor:
  "comma_crt_shifted_cofactor_or_false level digit shift column =
    comma_crt_cofactor_or_false level
      ((digit + shift) mod comma_crt_period level) column"
  by (simp add: comma_crt_shifted_cofactor_or_false_def
      comma_crt_cofactor_or_false_def)

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

lemma comma_crt_node_constant_map:
  assumes nonempty: "columns \<noteq> []"
  shows "comma_crt_node level (map (\<lambda>_. column) columns) = column"
  using nonempty
proof (cases columns)
  case Nil
  then show ?thesis using nonempty by simp
next
  case (Cons first rest)
  then show ?thesis
    by (simp add: comma_crt_node_def list_all_iff)
qed

lemma comma_crt_apply_cofactor_skip_from_admission:
  assumes admitted: "comma_crt_admitted (Suc level) column"
  shows "comma_crt_cofactor level digit column = Some column"
proof (cases column)
  case (Comma_CRT_Bool payload)
  then show ?thesis by simp
next
  case (Comma_CRT_Node node_level children)
  have "Suc level \<le> node_level"
    using admitted Comma_CRT_Node by simp
  then have "level < node_level" by simp
  then show ?thesis using Comma_CRT_Node by simp
qed

lemma comma_crt_apply_shifted_from_shortcut_result:
  assumes shortcut:
    "comma_crt_shifted_apply_shortcut operation shift left right = Some result"
  shows "comma_crt_apply_shifted_from depth shift operation left right = result"
  using shortcut
proof (induction depth arbitrary: left right)
  case 0
  then show ?case by (simp add: comma_crt_apply_shifted_from.simps)
next
  case (Suc depth)
  then show ?case by (simp add: comma_crt_apply_shifted_from.simps)
qed

lemma comma_crt_apply_shifted_from_skip_unused_level:
  assumes depth: "depth < 4"
    and left: "comma_crt_admitted (4-depth) left"
    and right: "comma_crt_admitted (4-depth) right"
  shows "comma_crt_apply_shifted_from (Suc depth) shift operation left right =
    comma_crt_apply_shifted_from depth shift operation left right"
proof (cases "comma_crt_shifted_apply_shortcut operation shift left right")
  case (Some result)
  have parent_result:
    "comma_crt_apply_shifted_from (Suc depth) shift operation left right = result"
    by (rule comma_crt_apply_shifted_from_shortcut_result[OF Some])
  have child_result:
    "comma_crt_apply_shifted_from depth shift operation left right = result"
    by (rule comma_crt_apply_shifted_from_shortcut_result[OF Some])
  show ?thesis using parent_result child_result by simp
next
  case None
  let ?level = "4 - Suc depth"
  have level_bound: "?level < 4" using depth by arith
  have successor_level: "Suc ?level = 4-depth" using depth by arith
  have left_admitted: "comma_crt_admitted (Suc ?level) left"
    using left successor_level by simp
  have right_admitted: "comma_crt_admitted (Suc ?level) right"
    using right successor_level by simp
  have left_cofactor:
    "comma_crt_cofactor_or_false ?level digit left = left" for digit
  proof -
    have "comma_crt_cofactor ?level digit left = Some left"
      by (rule comma_crt_apply_cofactor_skip_from_admission[OF left_admitted])
    then show ?thesis by (simp add: comma_crt_cofactor_or_false_def)
  qed
  have right_cofactor:
    "comma_crt_shifted_cofactor_or_false ?level digit shift right = right" for digit
  proof -
    have "comma_crt_cofactor ?level
        ((digit+shift) mod comma_crt_period ?level) right = Some right"
      by (rule comma_crt_apply_cofactor_skip_from_admission[OF right_admitted])
    then show ?thesis
      by (simp add: comma_crt_shifted_cofactor_or_false_def)
  qed
  have period_positive: "0 < comma_crt_period ?level"
    by (rule comma_crt_period_positive[OF level_bound])
  have digits_nonempty: "[0..<comma_crt_period ?level] \<noteq> []"
    using period_positive by auto
  let ?child = "comma_crt_apply_shifted_from depth shift operation left right"
  have children:
    "map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
        (comma_crt_cofactor_or_false ?level digit left)
        (comma_crt_shifted_cofactor_or_false ?level digit shift right))
      [0..<comma_crt_period ?level] =
      map (\<lambda>_. ?child) [0..<comma_crt_period ?level]"
    by (rule map_cong[OF refl]) (simp only: left_cofactor right_cofactor)
  have parent:
    "comma_crt_apply_shifted_from (Suc depth) shift operation left right =
      comma_crt_node ?level
        (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right))
          [0..<comma_crt_period ?level])"
    using None level_bound by (simp add: comma_crt_apply_shifted_from.simps Let_def)
  have collapse:
    "comma_crt_node ?level (map (\<lambda>_. ?child) [0..<comma_crt_period ?level]) = ?child"
    by (rule comma_crt_node_constant_map[OF digits_nonempty])
  show ?thesis by (simp only: parent children collapse)
qed

text \<open>
These equations expose the Boolean cases that the proof-producing apply
driver may discharge after it has authenticated both operands.  They are
uniform in depth and shift; the two left-neutral cases below deliberately
require zero shift because the left operand is not shifted.
\<close>

lemma comma_crt_apply_shifted_from_and_false_left:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_And
      (Comma_CRT_Bool False) right = Comma_CRT_Bool False"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_and_false_right:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_And
      left (Comma_CRT_Bool False) = Comma_CRT_Bool False"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_or_true_left:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_Or
      (Comma_CRT_Bool True) right = Comma_CRT_Bool True"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_or_true_right:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_Or
      left (Comma_CRT_Bool True) = Comma_CRT_Bool True"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_and_true_right:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_And
      left (Comma_CRT_Bool True) = left"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_or_false_right:
  "comma_crt_apply_shifted_from depth shift Comma_CRT_Or
      left (Comma_CRT_Bool False) = left"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_zero_and_true_left:
  "comma_crt_apply_shifted_from depth 0 Comma_CRT_And
      (Comma_CRT_Bool True) right = right"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_zero_or_false_left:
  "comma_crt_apply_shifted_from depth 0 Comma_CRT_Or
      (Comma_CRT_Bool False) right = right"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

lemma comma_crt_apply_shifted_from_zero_equal:
  "comma_crt_apply_shifted_from depth 0 operation column column = column"
  by (cases depth)
     (simp_all add: comma_crt_apply_shifted_from.simps
       comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def)

definition comma_crt_apply_from ::
    "nat \<Rightarrow> comma_crt_boolean_operation \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_apply_from depth operation left right =
    comma_crt_apply_shifted_from depth 0 operation left right"

definition comma_crt_apply_shifted ::
    "comma_crt_boolean_operation \<Rightarrow> nat \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_apply_shifted operation shift left right =
    comma_crt_apply_shifted_from 4 shift operation left right"

definition comma_crt_apply ::
    "comma_crt_boolean_operation \<Rightarrow>
      comma_crt_column \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_apply operation left right = comma_crt_apply_from 4 operation left right"

lemma comma_crt_cofactor_admitted_digit:
  assumes valid: "comma_crt_admitted level column"
    and level: "level < 4"
    and digit: "digit < comma_crt_period level"
  obtains child where
    "comma_crt_cofactor level digit column = Some child"
    "comma_crt_admitted (Suc level) child"
proof -
  have residue: "digit = digit mod comma_crt_period level"
    using digit comma_crt_period_positive[OF level] by simp
  obtain child where cofactor:
      "comma_crt_cofactor level digit column = Some child"
    and child_admitted: "comma_crt_admitted (Suc level) child"
    and "comma_crt_eval digit child = comma_crt_eval digit column"
    by (rule comma_crt_cofactor_exact[OF valid level residue])
  show thesis by (rule that[OF cofactor child_admitted])
qed

lemma comma_crt_shifted_cofactor_admitted_digit:
  assumes valid: "comma_crt_admitted level column"
    and level: "level < 4"
    and digit: "digit < comma_crt_period level"
  obtains child where
    "comma_crt_cofactor level ((digit+shift) mod comma_crt_period level) column =
      Some child"
    "comma_crt_admitted (Suc level) child"
proof -
  have shifted_digit: "(digit+shift) mod comma_crt_period level <
      comma_crt_period level"
    by (rule mod_less_divisor; rule comma_crt_period_positive[OF level])
  obtain child where cofactor:
      "comma_crt_cofactor level ((digit+shift) mod comma_crt_period level) column =
        Some child"
    and child_admitted: "comma_crt_admitted (Suc level) child"
    by (rule comma_crt_cofactor_admitted_digit[OF valid level shifted_digit])
  show thesis by (rule that[OF cofactor child_admitted])
qed

lemma comma_crt_shifted_apply_shortcut_admitted:
  assumes left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
    and shortcut:
      "comma_crt_shifted_apply_shortcut operation shift left right=Some result"
  shows "comma_crt_admitted lower result"
proof (cases "shift mod 924=0")
  case True
  have ordinary: "comma_crt_apply_shortcut operation left right=Some result"
    using shortcut True by (simp add: comma_crt_shifted_apply_shortcut_def)
  show ?thesis
    using left right ordinary
    by (cases operation)
       (auto simp: comma_crt_apply_shortcut_def split: if_splits)
  next
    case False
  show ?thesis
    using left right shortcut False
    by (cases operation)
       (auto simp: comma_crt_shifted_apply_shortcut_def
         split: if_splits comma_crt_column.splits)
qed
ML \<open>Thm.consolidate [@{thm comma_crt_shifted_apply_shortcut_admitted}]; Comma_Proof_Profile.report "CRT apply claim=shifted-shortcut-admitted checked"\<close>

lemma comma_crt_apply_shifted_from_admitted:
  assumes bound: "depth \<le> 4"
    and lower: "lower = 4 - depth"
    and left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
  shows "comma_crt_admitted lower
    (comma_crt_apply_shifted_from depth shift operation left right)"
  using bound lower left right
proof (induction depth arbitrary: lower left right)
  case 0
  then show ?case
    by (cases left; cases right; cases operation)
       (auto simp: comma_crt_shifted_apply_shortcut_def comma_crt_apply_shortcut_def
         comma_crt_boolean_value_def split: if_splits)
next
  case (Suc depth)
  let ?level = "4 - Suc depth"
  have depth_bound: "depth \<le> 4" using Suc.prems(1) by arith
  have lower_eq: "lower = ?level" using Suc.prems(2) by simp
  have level: "?level < 4" using Suc.prems(1) by arith
  have left_valid: "comma_crt_admitted ?level left" using Suc.prems(3) lower_eq by simp
  have right_valid: "comma_crt_admitted ?level right" using Suc.prems(4) lower_eq by simp
  show ?case
  proof (cases "comma_crt_shifted_apply_shortcut operation shift left right")
    case (Some result)
    have result_valid: "comma_crt_admitted lower result"
      using comma_crt_shifted_apply_shortcut_admitted
        [OF left_valid right_valid Some] lower_eq by simp
    show ?thesis using Some result_valid lower_eq
      by (simp add: Let_def comma_crt_apply_shifted_from.simps)
  next
    case None
    have children_valid:
        "list_all (comma_crt_admitted (Suc ?level))
          (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
            (comma_crt_cofactor_or_false ?level digit left)
            (comma_crt_shifted_cofactor_or_false ?level digit shift right))
            [0..<comma_crt_period ?level])"
      unfolding list_all_iff
    proof (intro ballI)
      fix child
      assume child_mem:
        "child \<in> set (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right))
          [0..<comma_crt_period ?level])"
      then obtain digit where digit:
          "digit \<in> set [0..<comma_crt_period ?level]"
        and child_eq:
          "child = comma_crt_apply_shifted_from depth shift operation
            (comma_crt_cofactor_or_false ?level digit left)
            (comma_crt_shifted_cofactor_or_false ?level digit shift right)"
        by auto
      have digit_bound: "digit < comma_crt_period ?level" using digit by simp
      obtain left_child where left_cofactor:
          "comma_crt_cofactor ?level digit left = Some left_child"
        and left_child_valid: "comma_crt_admitted (Suc ?level) left_child"
        by (rule comma_crt_cofactor_admitted_digit[OF left_valid level digit_bound])
      obtain right_child where right_cofactor:
          "comma_crt_cofactor ?level ((digit+shift) mod comma_crt_period ?level)
            right = Some right_child"
        and right_child_valid: "comma_crt_admitted (Suc ?level) right_child"
        by (rule comma_crt_shifted_cofactor_admitted_digit
          [OF right_valid level digit_bound])
      have lower_child: "Suc ?level = 4 - depth" using Suc.prems(1) by arith
      have result_valid:
        "comma_crt_admitted (Suc ?level)
          (comma_crt_apply_shifted_from depth shift operation left_child right_child)"
        by (rule Suc.IH[OF depth_bound lower_child left_child_valid right_child_valid])
      show "comma_crt_admitted (Suc ?level) child"
        using result_valid left_cofactor right_cofactor child_eq
        by (simp add: comma_crt_cofactor_or_false_def
          comma_crt_shifted_cofactor_or_false_def)
    qed
    have mapped_width:
        "length (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right))
          [0..<comma_crt_period ?level]) = comma_crt_period ?level"
      by simp
    have node_valid:
      "comma_crt_admitted ?level
        (comma_crt_node ?level
          (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
            (comma_crt_cofactor_or_false ?level digit left)
            (comma_crt_shifted_cofactor_or_false ?level digit shift right))
            [0..<comma_crt_period ?level]))"
      by (rule comma_crt_node_admitted[OF order_refl level mapped_width children_valid])
    show ?thesis using None node_valid lower_eq level
      by (simp add: Let_def comma_crt_apply_shifted_from.simps)
  qed
qed
ML \<open>Thm.consolidate [@{thm comma_crt_apply_shifted_from_admitted}]; Comma_Proof_Profile.report "CRT apply claim=shifted-from-admitted checked"\<close>

lemma comma_crt_apply_shortcut_admitted:
  assumes left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
    and shortcut: "comma_crt_apply_shortcut operation left right = Some result"
  shows "comma_crt_admitted lower result"
  using left right shortcut
  by (cases operation)
     (auto simp: comma_crt_apply_shortcut_def split: if_splits)

lemma comma_crt_apply_shortcut_eval:
  assumes shortcut: "comma_crt_apply_shortcut operation left right = Some result"
  shows "comma_crt_eval phase result =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval phase right)"
  using shortcut
proof (cases "left=right")
  case True
  have result_left: "result=left"
    using shortcut True by (cases operation) (simp_all add: comma_crt_apply_shortcut_def)
  show ?thesis using result_left True
    by (cases operation) (simp_all add: comma_crt_boolean_value_def)
next
  case False
  then show ?thesis using shortcut
    by (cases operation; cases left; cases right)
       (auto simp: comma_crt_apply_shortcut_def comma_crt_boolean_value_def
         split: if_splits)
qed

lemma comma_crt_shifted_apply_shortcut_eval:
  assumes right: "comma_crt_admitted lower right"
    and shortcut:
      "comma_crt_shifted_apply_shortcut operation shift left right=Some result"
  shows "comma_crt_eval phase result =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval (phase+shift) right)"
proof (cases "shift mod 924=0")
  case True
  have same_clock:
      "comma_crt_eval phase right=comma_crt_eval (phase+shift) right"
  proof -
    have phase_periodic:
      "comma_crt_eval (phase mod 924) right=comma_crt_eval phase right"
      by (rule comma_crt_eval_periodic[OF right])
    have shifted_periodic:
      "comma_crt_eval ((phase+shift) mod 924) right=
        comma_crt_eval (phase+shift) right"
      by (rule comma_crt_eval_periodic[OF right])
    have residue: "(phase+shift) mod 924=phase mod 924"
    proof -
      have "(phase+shift) mod 924 =
          ((phase mod 924)+(shift mod 924)) mod 924"
        by (rule mod_add_eq[symmetric])
      also have "... = phase mod 924" using True by simp
      finally show ?thesis .
    qed
    show ?thesis using phase_periodic shifted_periodic residue by simp
  qed
  have ordinary: "comma_crt_apply_shortcut operation left right=Some result"
    using shortcut True by (simp add: comma_crt_shifted_apply_shortcut_def)
  show ?thesis
    using comma_crt_apply_shortcut_eval[OF ordinary] same_clock by simp
next
  case False
  then show ?thesis
    using shortcut
    by (cases operation; cases left; cases right)
       (auto simp: comma_crt_shifted_apply_shortcut_def
         comma_crt_boolean_value_def split: if_splits)
qed

lemma comma_crt_apply_shifted_from_eval:
  assumes bound: "depth \<le> 4"
    and lower: "lower = 4 - depth"
    and left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
  shows "comma_crt_eval phase
      (comma_crt_apply_shifted_from depth shift operation left right) =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval (phase+shift) right)"
  using bound lower left right
proof (induction depth arbitrary: lower left right)
  case 0
  then show ?case
    by (cases left; cases right; cases operation)
       (auto simp: comma_crt_apply_shifted_from.simps
         comma_crt_boolean_value_def comma_crt_shifted_apply_shortcut_def
         comma_crt_apply_shortcut_def split: if_splits)
next
  case (Suc depth)
  let ?level = "4 - Suc depth"
  have depth_bound: "depth \<le> 4" using Suc.prems(1) by arith
  have lower_eq: "lower = ?level" using Suc.prems(2) by simp
  have level: "?level < 4" using Suc.prems(1) by arith
  have left_valid: "comma_crt_admitted ?level left"
    using Suc.prems(3) lower_eq by simp
  have right_valid: "comma_crt_admitted ?level right"
    using Suc.prems(4) lower_eq by simp
  show ?case
  proof (cases "comma_crt_shifted_apply_shortcut operation shift left right")
    case (Some result)
    have apply_eq:
      "comma_crt_apply_shifted_from (Suc depth) shift operation left right=result"
      using Some by (simp add: comma_crt_apply_shifted_from.simps Let_def)
    show ?thesis
      using apply_eq
        comma_crt_shifted_apply_shortcut_eval[OF right_valid Some]
      by simp
  next
    case None
    have width:
      "length (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right))
          [0..<comma_crt_period ?level])=comma_crt_period ?level"
      by simp
    have index: "phase mod comma_crt_period ?level < comma_crt_period ?level"
      using comma_crt_period_positive[OF level] by simp
    have right_residue:
      "(phase mod comma_crt_period ?level + shift) mod comma_crt_period ?level =
        (phase+shift) mod comma_crt_period ?level"
      by (simp add: mod_add_left_eq)
    obtain left_child where left_cofactor:
        "comma_crt_cofactor ?level (phase mod comma_crt_period ?level) left =
          Some left_child"
      and left_child_valid: "comma_crt_admitted (Suc ?level) left_child"
      and left_eval:
        "comma_crt_eval phase left_child=comma_crt_eval phase left"
      by (rule comma_crt_cofactor_exact[OF left_valid level refl])
    obtain right_child where right_cofactor:
        "comma_crt_cofactor ?level ((phase+shift) mod comma_crt_period ?level) right =
          Some right_child"
      and right_child_valid: "comma_crt_admitted (Suc ?level) right_child"
      and right_eval:
        "comma_crt_eval (phase+shift) right_child=
          comma_crt_eval (phase+shift) right"
      by (rule comma_crt_cofactor_exact[OF right_valid level refl])
    have lower_child: "Suc ?level=4-depth" using Suc.prems(1) by arith
    have child_eval:
      "comma_crt_eval phase
          (comma_crt_apply_shifted_from depth shift operation left_child right_child) =
        comma_crt_boolean_value operation
          (comma_crt_eval phase left_child)
          (comma_crt_eval (phase+shift) right_child)"
      by (rule Suc.IH[OF depth_bound lower_child left_child_valid right_child_valid])
    have selected_left:
      "comma_crt_cofactor_or_false ?level (phase mod comma_crt_period ?level) left =
        left_child"
      using left_cofactor by (simp add: comma_crt_cofactor_or_false_def)
    have selected_right:
      "comma_crt_shifted_cofactor_or_false ?level
          (phase mod comma_crt_period ?level) shift right = right_child"
      using right_cofactor right_residue
      by (simp add: comma_crt_shifted_cofactor_or_false_def)
    have branch_eval:
      "comma_crt_eval phase
        (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
          (comma_crt_cofactor_or_false ?level digit left)
          (comma_crt_shifted_cofactor_or_false ?level digit shift right))
          [0..<comma_crt_period ?level] ! (phase mod comma_crt_period ?level)) =
        comma_crt_eval phase
          (comma_crt_apply_shifted_from depth shift operation left_child right_child)"
      using index selected_left selected_right
      by (simp add: nth_map)
    have node_eval:
      "comma_crt_eval phase
        (comma_crt_node ?level
          (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
            (comma_crt_cofactor_or_false ?level digit left)
            (comma_crt_shifted_cofactor_or_false ?level digit shift right))
            [0..<comma_crt_period ?level])) =
        comma_crt_eval phase
          (comma_crt_apply_shifted_from depth shift operation left_child right_child)"
      using comma_crt_node_eval[OF level width] branch_eval
        comma_crt_period_positive[OF level] level by simp
    have apply_eq:
      "comma_crt_apply_shifted_from (Suc depth) shift operation left right =
        comma_crt_node ?level
          (map (\<lambda>digit. comma_crt_apply_shifted_from depth shift operation
            (comma_crt_cofactor_or_false ?level digit left)
            (comma_crt_shifted_cofactor_or_false ?level digit shift right))
            [0..<comma_crt_period ?level])"
      using None level by (simp add: Let_def comma_crt_apply_shifted_from.simps)
    show ?thesis
      using node_eval child_eval left_eval right_eval apply_eq
      by (simp add: comma_crt_boolean_value_def)
  qed
qed
ML \<open>Thm.consolidate [@{thm comma_crt_apply_shifted_from_eval}]; Comma_Proof_Profile.report "CRT apply claim=shifted-from-eval checked"\<close>

lemma comma_crt_apply_from_admitted:
  assumes bound: "depth \<le> 4"
    and lower: "lower = 4 - depth"
    and left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
  shows "comma_crt_admitted lower (comma_crt_apply_from depth operation left right)"
  unfolding comma_crt_apply_from_def
  by (rule comma_crt_apply_shifted_from_admitted[OF bound lower left right])

lemma comma_crt_apply_from_eval:
  assumes bound: "depth \<le> 4"
    and lower: "lower = 4 - depth"
    and left: "comma_crt_admitted lower left"
    and right: "comma_crt_admitted lower right"
  shows "comma_crt_eval phase (comma_crt_apply_from depth operation left right) =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval phase right)"
  unfolding comma_crt_apply_from_def
  using comma_crt_apply_shifted_from_eval[OF bound lower left right, where shift=0]
  by simp

lemma comma_crt_apply_shifted_admitted:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_admitted 0 (comma_crt_apply_shifted operation shift left right)"
  unfolding comma_crt_apply_shifted_def
  by (rule comma_crt_apply_shifted_from_admitted[where depth=4 and lower=0])
     (simp_all add: left right)

lemma comma_crt_apply_shifted_refines_boolean:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_eval phase (comma_crt_apply_shifted operation shift left right) =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval (phase+shift) right)"
  unfolding comma_crt_apply_shifted_def
  by (rule comma_crt_apply_shifted_from_eval[where depth=4 and lower=0])
     (simp_all add: left right)

lemma comma_crt_apply_admitted:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_admitted 0 (comma_crt_apply operation left right)"
  unfolding comma_crt_apply_def
  by (rule comma_crt_apply_from_admitted[where depth=4 and lower=0])
     (simp_all add: left right)

lemma comma_crt_apply_refines_boolean:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_eval phase (comma_crt_apply operation left right) =
    comma_crt_boolean_value operation (comma_crt_eval phase left)
      (comma_crt_eval phase right)"
  unfolding comma_crt_apply_def
  by (rule comma_crt_apply_from_eval[where depth=4 and lower=0])
     (simp_all add: left right)

lemma comma_crt_apply_and_set:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_set (comma_crt_apply Comma_CRT_And left right) =
    comma_crt_set left \<inter> comma_crt_set right"
  using comma_crt_apply_refines_boolean[OF left right, where operation=Comma_CRT_And]
  by (auto simp: comma_crt_set_def comma_crt_boolean_value_def)

lemma comma_crt_apply_or_set:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_set (comma_crt_apply Comma_CRT_Or left right) =
    comma_crt_set left \<union> comma_crt_set right"
  using comma_crt_apply_refines_boolean[OF left right, where operation=Comma_CRT_Or]
  by (auto simp: comma_crt_set_def comma_crt_boolean_value_def)

lemma comma_crt_power_intersection_refines:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_set
      (comma_crt_apply Comma_CRT_And left (comma_crt_shift span right)) =
    comma_crt_set left \<inter>
      comma_semantic_b1_column_advance span (comma_crt_set right)"
proof -
  have shifted: "comma_crt_admitted 0 (comma_crt_shift span right)"
    by (rule comma_crt_shift_admitted[OF right])
  show ?thesis
    using comma_crt_apply_and_set[OF left shifted]
      comma_crt_shift_is_power_advance[OF right, where shift=span]
    by simp
qed

lemma comma_crt_fused_power_intersection_refines:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_set
      (comma_crt_apply_shifted Comma_CRT_And span left right) =
    comma_crt_set left \<inter>
      comma_semantic_b1_column_advance span (comma_crt_set right)"
proof -
  have fused:
      "comma_crt_set (comma_crt_apply_shifted Comma_CRT_And span left right) =
        comma_crt_set left \<inter> comma_crt_set (comma_crt_shift span right)"
  proof (unfold comma_crt_set_def, rule set_eqI)
    fix phase
    show "phase \<in> {phase. phase<924 \<and>
          comma_crt_eval phase
            (comma_crt_apply_shifted Comma_CRT_And span left right)} \<longleftrightarrow>
        phase \<in> ({phase. phase<924 \<and> comma_crt_eval phase left} \<inter>
          {phase. phase<924 \<and>
            comma_crt_eval phase (comma_crt_shift span right)})"
      using comma_crt_apply_shifted_refines_boolean[OF left right,
          where operation=Comma_CRT_And and shift=span]
        comma_crt_shift_refines[OF right, where shift=span]
      by (auto simp: comma_crt_boolean_value_def)
  qed
  show ?thesis
    using fused comma_crt_shift_is_power_advance[OF right, where shift=span]
    by simp
qed

ML \<open>
  val checked = @{thms comma_crt_apply_admitted comma_crt_apply_refines_boolean
    comma_crt_apply_and_set comma_crt_apply_or_set
    comma_crt_power_intersection_refines comma_crt_apply_shifted_admitted
    comma_crt_apply_shifted_refines_boolean
    comma_crt_fused_power_intersection_refines
    comma_crt_shifted_cofactor_or_false_as_cofactor
    comma_crt_apply_shifted_from_shift_equiv
    comma_crt_apply_period_divides_suffix
    comma_crt_apply_shifted_from_suffix_equiv
    comma_crt_apply_shifted_from_skip_unused_level};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report "CRT apply claims consolidated";
  val _ = Comma_Proof_Profile.report "CRT apply audit=native entered";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Structural matched-cofactor CRT Boolean apply" checked;
  val _ = Comma_Proof_Profile.report "CRT apply audit=native checked";
\<close>

end
