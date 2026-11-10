theory Comma_Weighted_CRT_Guard
  imports Comma_Semantic_B1.Comma_Semantic_Graph_Weighted_CRT_DAG
    Comma_Semantic_B1.Comma_CRT_Columns
    Comma_Semantic_B1.Comma_Phase_Class_Rank
begin

text \<open>
A Boolean observation of a weighted CRT tree is lowered directly to the
existing CRT-column representation.  The projection keeps CRT axes and child
order, and drops only edge weights.  It does not create an intermediate
Boolean weighted tree or evaluate a phase list.
\<close>

lemma comma_crt_period_axis_radix:
  assumes "axis<4"
  shows "comma_crt_period axis=comma_crt_axis_radix axis"
  using comma_crt_axis_cases[OF assms]
  by (auto simp: comma_crt_period_def comma_crt_axis_radix_def)

fun comma_weighted_crt_project_bool ::
    "('a \<Rightarrow> bool) \<Rightarrow> 'a comma_semantic_weighted_crt_dag
      \<Rightarrow> comma_crt_column" where
  "comma_weighted_crt_project_bool observe (Comma_Weighted_CRT_Leaf control) =
    Comma_CRT_Bool (observe control)"
| "comma_weighted_crt_project_bool observe
      (Comma_Weighted_CRT_Branch axis rows) =
    comma_crt_node axis
      (map (\<lambda>(weight,child). comma_weighted_crt_project_bool observe child) rows)"

lemma comma_weighted_crt_project_bool_admitted:
  assumes shape: "comma_weighted_crt_shape lower tree"
  shows "comma_crt_admitted lower (comma_weighted_crt_project_bool observe tree)"
  using shape
proof (induction tree arbitrary: lower)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have order: "lower \<le> axis"
    and axis_lt: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
    and children_shape:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_shape (Suc axis) child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  have children_admitted:
      "list_all (\<lambda>column. comma_crt_admitted (Suc axis) column)
        (map (\<lambda>(weight,child). comma_weighted_crt_project_bool observe child) rows)"
  proof -
    have each: "\<And>weight child. (weight,child)\<in>set rows \<Longrightarrow>
        comma_crt_admitted (Suc axis)
          (comma_weighted_crt_project_bool observe child)"
    proof -
      fix weight child
      assume member: "(weight,child)\<in>set rows"
      have child_shape: "comma_weighted_crt_shape (Suc axis) child"
        using children_shape member by (auto simp: list_all_iff prod_set_defs)
      show "comma_crt_admitted (Suc axis)
          (comma_weighted_crt_project_bool observe child)"
        by (rule Comma_Weighted_CRT_Branch.IH[OF member _ child_shape])
          (simp add: prod_set_defs)
    qed
    show ?thesis using each by (auto simp: list_all_iff)
  qed
  show ?case
    unfolding comma_weighted_crt_project_bool.simps
    by (rule comma_crt_node_admitted[OF order axis_lt _ children_admitted])
      (simp add: extent comma_crt_period_axis_radix[OF axis_lt])
qed

lemma comma_weighted_crt_project_bool_eval:
  assumes shape: "comma_weighted_crt_shape lower tree"
  shows "comma_crt_eval phase (comma_weighted_crt_project_bool observe tree) =
    (case comma_weighted_crt_eval tree phase of
      Some (control,elapsed) \<Rightarrow> observe control | None \<Rightarrow> False)"
  using shape
proof (induction tree arbitrary: lower phase)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis_lt: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
    and children_shape:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_shape (Suc axis) child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  have period_eq: "comma_crt_period axis=comma_crt_axis_radix axis"
    by (rule comma_crt_period_axis_radix[OF axis_lt])
  let ?i = "phase mod comma_crt_axis_radix axis"
  have index: "?i<length rows"
    using axis_lt extent comma_weighted_crt_axis_positive[OF axis_lt] by simp
  obtain weight child where selected: "rows!?i=(weight,child)"
    by (cases "rows!?i") auto
  have member: "(weight,child)\<in>set rows"
    using nth_mem[OF index] selected by simp
  have child_shape: "comma_weighted_crt_shape (Suc axis) child"
    using children_shape member by (auto simp: list_all_iff prod_set_defs)
  have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
    by (simp add: prod_set_defs)
  have child_eval:
    "comma_crt_eval phase (comma_weighted_crt_project_bool observe child) =
      (case comma_weighted_crt_eval child phase of
        Some (control,elapsed) \<Rightarrow> observe control | None \<Rightarrow> False)"
    by (rule Comma_Weighted_CRT_Branch.IH[OF member child_member child_shape])
  have column_eval:
    "comma_crt_eval phase (comma_weighted_crt_project_bool observe
        (Comma_Weighted_CRT_Branch axis rows)) =
      comma_crt_eval phase (comma_weighted_crt_project_bool observe child)"
  proof -
    have node:
      "comma_crt_eval phase
          (comma_crt_node axis
            (map (\<lambda>(edge,subtree).
              comma_weighted_crt_project_bool observe subtree) rows)) =
       comma_crt_eval phase
          (Comma_CRT_Node axis
            (map (\<lambda>(edge,subtree).
              comma_weighted_crt_project_bool observe subtree) rows))"
      by (rule comma_crt_node_eval[OF axis_lt])
        (simp add: extent comma_crt_period_axis_radix[OF axis_lt])
    show ?thesis using node selected index period_eq axis_lt extent
      by (simp add: comma_weighted_crt_project_bool.simps
        comma_crt_eval_node_selected nth_map)
  qed
  have weighted_eval:
    "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
      map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
        (comma_weighted_crt_eval child phase)"
    using comma_weighted_crt_eval_branch[OF axis_lt extent, of phase]
      selected by (simp add: nth_map)
  show ?case using column_eval child_eval weighted_eval
    by (simp add: comma_weighted_crt_project_bool.simps
      split: option.splits prod.splits)
qed

fun comma_phase_class_action_continues_to ::
    "'c \<Rightarrow> 'c comma_phase_class_action \<Rightarrow> bool" where
  "comma_phase_class_action_continues_to target
      (Comma_Phase_Class_Continue next_phase next_class) =
    (next_class=target)"
| "comma_phase_class_action_continues_to target Comma_Phase_Class_Invalid = False"
| "comma_phase_class_action_continues_to target (Comma_Phase_Class_Fork a d) = False"
| "comma_phase_class_action_continues_to target (Comma_Phase_Class_Landmine d) = False"

definition comma_weighted_crt_continue_column ::
    "'c \<Rightarrow> 'c comma_phase_class_action comma_semantic_weighted_crt_dag
      \<Rightarrow> comma_crt_column" where
  "comma_weighted_crt_continue_column target tree =
    comma_weighted_crt_project_bool
      (comma_phase_class_action_continues_to target) tree"

lemma comma_weighted_crt_continue_column_admitted:
  assumes shape: "comma_weighted_crt_shape 0 tree"
  shows "comma_crt_admitted 0
    (comma_weighted_crt_continue_column target tree)"
  unfolding comma_weighted_crt_continue_column_def
  by (rule comma_weighted_crt_project_bool_admitted[OF shape])

lemma comma_weighted_crt_continue_column_eval:
  assumes shape: "comma_weighted_crt_shape 0 tree"
  shows "comma_crt_eval phase
      (comma_weighted_crt_continue_column target tree) =
    (case comma_weighted_crt_eval tree phase of
      Some (action,elapsed) \<Rightarrow>
        comma_phase_class_action_continues_to target action
    | None \<Rightarrow> False)"
  unfolding comma_weighted_crt_continue_column_def
  by (rule comma_weighted_crt_project_bool_eval[OF shape])

lemma comma_weighted_crt_continue_column_true_iff:
  assumes shape: "comma_weighted_crt_shape 0 tree"
  shows "comma_crt_eval phase
      (comma_weighted_crt_continue_column target tree) = True
    \<longleftrightarrow> (\<exists>next_phase elapsed.
      comma_weighted_crt_eval tree phase =
        Some (Comma_Phase_Class_Continue next_phase target,elapsed))"
proof (cases "comma_weighted_crt_eval tree phase")
  case None
  show ?thesis
    using comma_weighted_crt_continue_column_eval
      [OF shape, where phase=phase and target=target] None by simp
next
  case (Some payload)
  obtain control weight where payload_eq: "payload=(control,weight)"
    by (cases payload) auto
  have exact: "comma_weighted_crt_eval tree phase=Some (control,weight)"
    using Some payload_eq by simp
  have projected:
      "comma_crt_eval phase (comma_weighted_crt_continue_column target tree) =
        comma_phase_class_action_continues_to target control"
    using comma_weighted_crt_continue_column_eval
      [OF shape, where phase=phase and target=target] exact by simp
  show ?thesis
    using exact projected by (cases control) simp_all
qed

text \<open>
The target class is retained in the guard.  The transition theorem supplies
that a Continue advances phase by one; shift is applied to the recursive
successor column, not folded into or erased from this label.
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT control guards preserve exact target classes"
    @{thms comma_weighted_crt_project_bool_admitted
      comma_weighted_crt_project_bool_eval
      comma_weighted_crt_continue_column_true_iff};
\<close>

end
