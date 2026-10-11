theory Comma_CRT_Columns
  imports Comma_Semantic_B1_Power
begin
ML \<open>Comma_Proof_Profile.report "CRT columns stage=entered"\<close>

text \<open>
Executable Boolean columns for the four external cyclotomic characters.
This is the tree denotation of the reduced nodes used by return_mdd.py and
the ML template constructor; sharing changes storage, not interpretation.
Neither the clock origin nor a temporal Stop weight belongs to this node.
Malformed child vectors evaluate to False and are excluded by admission.
\<close>

datatype comma_crt_column =
    Comma_CRT_Bool bool
  | Comma_CRT_Node nat "comma_crt_column list"

definition comma_crt_period :: "nat \<Rightarrow> nat" where
  "comma_crt_period level = (if level<4 then [4,3,7,11]!level else 0)"

lemma comma_crt_period_positive:
  assumes "level<4"
  shows "0<comma_crt_period level"
proof -
  have "level=0 \<or> level=1 \<or> level=2 \<or> level=3" using assms by arith
  then show ?thesis by (auto simp: comma_crt_period_def)
qed

lemma comma_crt_period_divides:
  assumes "level<4"
  shows "comma_crt_period level dvd 924"
proof -
  have "level=0 \<or> level=1 \<or> level=2 \<or> level=3" using assms by arith
  then show ?thesis by (auto simp: comma_crt_period_def)
qed

primrec comma_crt_eval :: "nat \<Rightarrow> comma_crt_column \<Rightarrow> bool" where
  "comma_crt_eval phase (Comma_CRT_Bool value) = value"
| "comma_crt_eval phase (Comma_CRT_Node level children) =
    (if level<4 \<and> length children=comma_crt_period level then
      map (comma_crt_eval phase) children ! (phase mod comma_crt_period level)
     else False)"

text \<open>
The logical primitive equation above remains the reference semantics.  For
code evaluation, select the demanded child before recursively evaluating it:
evaluating \<^term>\<open>map (comma_crt_eval phase) children\<close> first needlessly
visits every branch of the CRT node.  The guard is unchanged, so malformed
nodes retain their original total behavior.
\<close>

declare comma_crt_eval.simps(2)[code del]

lemma comma_crt_eval_node_selected[code]:
  "comma_crt_eval phase (Comma_CRT_Node level children) =
    (if level<4 \<and> length children=comma_crt_period level then
       comma_crt_eval phase (children!(phase mod comma_crt_period level))
     else False)"
proof (cases "level<4 \<and> length children=comma_crt_period level")
  case True
  then have level: "level<4"
    and width: "length children=comma_crt_period level" by auto
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have selected_bound:
    "phase mod comma_crt_period level<length children"
    using positive width by simp
  have selected:
    "map (comma_crt_eval phase) children !
        (phase mod comma_crt_period level) =
      comma_crt_eval phase
        (children!(phase mod comma_crt_period level))"
    by (rule nth_map[OF selected_bound])
  show ?thesis using True selected
    by (simp add: comma_crt_eval.simps)
next
  case False
  then show ?thesis by (simp only: comma_crt_eval.simps if_False)
qed

lemma comma_crt_eval_node_selected_malformed:
  assumes malformed:
    "\<not> (level<4 \<and> length children=comma_crt_period level)"
  shows "comma_crt_eval phase (Comma_CRT_Node level children)=False"
  using malformed
  by (simp only: comma_crt_eval_node_selected if_False)

primrec comma_crt_admitted :: "nat \<Rightarrow> comma_crt_column \<Rightarrow> bool" where
  "comma_crt_admitted lower (Comma_CRT_Bool value) = True"
| "comma_crt_admitted lower (Comma_CRT_Node level children) =
    (lower\<le>level \<and> level<4 \<and> length children=comma_crt_period level \<and>
      list_all (comma_crt_admitted (Suc level)) children)"

definition comma_crt_set :: "comma_crt_column \<Rightarrow> nat set" where
  "comma_crt_set column = {phase. phase<924 \<and> comma_crt_eval phase column}"

definition comma_crt_node :: "nat \<Rightarrow> comma_crt_column list \<Rightarrow> comma_crt_column" where
  "comma_crt_node level children =
    (if children=[] then Comma_CRT_Bool False
     else if list_all (\<lambda>child. child=hd children) children
       then hd children else Comma_CRT_Node level children)"

lemma comma_crt_node_cons:
  "comma_crt_node level (first # rest) =
    (if list_all (\<lambda>child. child = first) (first # rest)
     then first else Comma_CRT_Node level (first # rest))"
  by (simp add: comma_crt_node_def)

lemma comma_crt_admitted_mono:
  "lower\<le>upper \<Longrightarrow> comma_crt_admitted upper column \<Longrightarrow>
    comma_crt_admitted lower column"
  by (cases column) auto

lemma comma_crt_node_admitted:
  assumes order: "lower\<le>level" and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children: "list_all (comma_crt_admitted (Suc level)) children"
  shows "comma_crt_admitted lower (comma_crt_node level children)"
proof (cases children)
  case Nil
  then show ?thesis by (simp add: comma_crt_node_def)
next
  case (Cons first rest)
  have first_valid: "comma_crt_admitted (Suc level) first"
    using children Cons by simp
  have lower_bound: "lower\<le>Suc level" using order by arith
  have reduced_valid: "comma_crt_admitted lower first"
    by (rule comma_crt_admitted_mono[OF lower_bound first_valid])
  show ?thesis
    using order level width children Cons reduced_valid
    by (simp add: comma_crt_node_def)
qed

lemma comma_crt_node_eval:
  assumes level: "level<4" and width: "length children=comma_crt_period level"
  shows "comma_crt_eval phase (comma_crt_node level children) =
    comma_crt_eval phase (Comma_CRT_Node level children)"
proof -
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have nonempty: "children\<noteq>[]" using positive width by auto
  have index: "phase mod comma_crt_period level<length children"
    using positive width by simp
  show ?thesis
  proof (cases "list_all (\<lambda>child. child=hd children) children")
    case True
    have selected: "children!(phase mod comma_crt_period level)=hd children"
      using True nth_mem[OF index] by (simp add: list_all_iff)
    show ?thesis
      using True nonempty level width index selected
      by (simp add: comma_crt_node_def nth_map)
  next
    case False
    then show ?thesis using nonempty by (simp add: comma_crt_node_def)
  qed
qed

primrec comma_crt_shift :: "nat \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_shift shift (Comma_CRT_Bool value) = Comma_CRT_Bool value"
| "comma_crt_shift shift (Comma_CRT_Node level children) =
    Comma_CRT_Node level (rotate shift (map (comma_crt_shift shift) children))"

lemma comma_crt_shift_zero [simp]:
  "comma_crt_shift 0 column = column"
  by (induction column) (simp_all cong: map_cong)

lemma comma_crt_shift_refines:
  assumes valid: "comma_crt_admitted lower column"
  shows "comma_crt_eval phase (comma_crt_shift shift column) =
    comma_crt_eval (phase+shift) column"
  using valid
proof (induction column arbitrary: lower phase)
  case (Comma_CRT_Bool payload)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  have level: "level<4" and width: "length children=comma_crt_period level"
    and children_valid: "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems by (auto simp: list_all_iff)
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have index: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have rotated_index: "(shift+phase mod comma_crt_period level) mod comma_crt_period level =
      (phase+shift) mod comma_crt_period level"
    using width by (simp add: mod_add_right_eq add.commute)
  have target_index: "(phase+shift) mod comma_crt_period level<length children"
    using positive width by simp
  have child_valid: "comma_crt_admitted (Suc level)
      (children!((phase+shift) mod comma_crt_period level))"
    using children_valid nth_mem[OF target_index] by blast
  have child_eq:
      "comma_crt_eval phase
        (comma_crt_shift shift (children!((phase+shift) mod comma_crt_period level))) =
       comma_crt_eval (phase+shift) (children!((phase+shift) mod comma_crt_period level))"
    by (rule Comma_CRT_Node.IH[OF nth_mem[OF target_index] child_valid])
  show ?case
    using level width index target_index child_eq
    by (simp add: nth_rotate nth_map rotated_index)
qed

ML \<open>Thm.consolidate [@{thm comma_crt_shift_refines}]; Comma_Proof_Profile.report "CRT columns claim=shift-refines checked"\<close>

lemma comma_crt_shift_admitted:
  "comma_crt_admitted lower column \<Longrightarrow>
    comma_crt_admitted lower (comma_crt_shift shift column)"
  by (induction column arbitrary: lower) (auto simp: list_all_iff)

lemma comma_crt_eval_periodic:
  assumes valid: "comma_crt_admitted lower column"
  shows "comma_crt_eval (phase mod 924) column = comma_crt_eval phase column"
  using valid
proof (induction column arbitrary: lower)
  case (Comma_CRT_Bool payload)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  have level: "level<4" and width: "length children=comma_crt_period level"
    and children_valid: "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems by (auto simp: list_all_iff)
  have divides: "comma_crt_period level dvd 924"
    by (rule comma_crt_period_divides[OF level])
  have residue: "(phase mod 924) mod comma_crt_period level=phase mod comma_crt_period level"
    by (rule mod_mod_cancel[OF divides])
  have index: "phase mod comma_crt_period level<length children"
    using comma_crt_period_positive[OF level] width by simp
  have child_valid: "comma_crt_admitted (Suc level) (children!(phase mod comma_crt_period level))"
    using children_valid nth_mem[OF index] by blast
  have child_eq: "comma_crt_eval (phase mod 924) (children!(phase mod comma_crt_period level)) =
      comma_crt_eval phase (children!(phase mod comma_crt_period level))"
    by (rule Comma_CRT_Node.IH[OF nth_mem[OF index] child_valid])
  show ?case using level width index child_eq by (simp add: residue nth_map)
qed

lemma comma_crt_shift_column_exact:
  assumes valid: "comma_crt_admitted lower column"
  shows "comma_crt_set (comma_crt_shift shift column) =
    {phase. phase<924 \<and> (phase+shift) mod 924\<in>comma_crt_set column}"
  using comma_crt_shift_refines[OF valid, of _ shift]
    comma_crt_eval_periodic[OF valid]
  by (auto simp: comma_crt_set_def)

corollary comma_crt_shift_is_power_advance:
  "comma_crt_admitted lower column \<Longrightarrow>
    comma_crt_set (comma_crt_shift shift column) =
      comma_semantic_b1_column_advance shift (comma_crt_set column)"
  using comma_crt_shift_column_exact
  by (simp add: comma_semantic_b1_column_advance_def)

fun comma_crt_cofactor ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column \<Rightarrow> comma_crt_column option" where
  "comma_crt_cofactor level digit (Comma_CRT_Bool payload) = Some (Comma_CRT_Bool payload)"
| "comma_crt_cofactor level digit (Comma_CRT_Node node_level children) =
    (if node_level<level then None
     else if level<node_level then Some (Comma_CRT_Node node_level children)
     else if digit<length children then Some (children!digit) else None)"

lemma comma_crt_cofactor_exact:
  assumes valid: "comma_crt_admitted level column"
    and level: "level<4"
    and digit: "digit=phase mod comma_crt_period level"
  obtains child where
    "comma_crt_cofactor level digit column=Some child"
    "comma_crt_admitted (Suc level) child"
    "comma_crt_eval phase child=comma_crt_eval phase column"
proof (cases column)
  case (Comma_CRT_Bool payload)
  show thesis
    by (rule that[of column]) (simp_all add: Comma_CRT_Bool)
next
  case (Comma_CRT_Node node_level children)
  have order: "level\<le>node_level" and node_bound: "node_level<4"
    and width: "length children=comma_crt_period node_level"
    and child_admitted:
      "\<forall>child\<in>set children. comma_crt_admitted (Suc node_level) child"
    using valid Comma_CRT_Node by (auto simp: list_all_iff)
  show thesis
  proof (cases "node_level=level")
    case True
    have bound: "digit<length children"
      using digit width True comma_crt_period_positive[OF level] by simp
    have selected_valid: "comma_crt_admitted (Suc level) (children!digit)"
      using child_admitted nth_mem[OF bound] True by blast
    show thesis
      by (rule that[of "children!digit"])
        (use Comma_CRT_Node True bound selected_valid digit level width in
          \<open>simp_all add: nth_map\<close>)
  next
    case False
    have later: "level<node_level" using order False by arith
    have admitted: "comma_crt_admitted (Suc level) column"
      using valid Comma_CRT_Node later by simp
    show thesis
      by (rule that[of column])
        (use Comma_CRT_Node later admitted in simp_all)
  qed
qed

ML \<open>Thm.consolidate [@{thm comma_crt_cofactor_exact}]; Comma_Proof_Profile.report "CRT columns claim=cofactor-exact checked"\<close>

ML \<open>
  val checked = @{thms comma_crt_admitted_mono comma_crt_node_admitted
    comma_crt_node_eval comma_crt_shift_refines
    comma_crt_shift_admitted comma_crt_eval_periodic comma_crt_shift_column_exact
    comma_crt_shift_is_power_advance comma_crt_cofactor_exact};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report "CRT columns claims consolidated";
  val _ = Comma_Proof_Profile.report "CRT columns audit=native entered";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Concrete CRT column interpretation and clock transport" checked;
  val _ = Comma_Proof_Profile.report "CRT columns audit=native checked";
\<close>

end
