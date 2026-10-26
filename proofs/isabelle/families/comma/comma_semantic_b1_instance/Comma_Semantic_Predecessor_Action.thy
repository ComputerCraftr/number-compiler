theory Comma_Semantic_Predecessor_Action
  imports Comma_Semantic_Graph_CRT_Local_Node_Compilation
    Comma_Semantic_B1.Comma_Weighted_CRT_Cofactor
begin

text \<open>
The weighted graph publisher stores terminal control separately from its
complete-decade payload.  A terminal label is the within-decade sector J;
height is carried only by normalized edge/root weights in the generic CRT
diagram, never in the control identity.
\<close>

definition comma_semantic_b1_crt_add_stop ::
    "nat \<Rightarrow> nat \<times> comma_semantic_b1_crt_dag \<Rightarrow>
      nat \<times> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_add_stop amount action =
    comma_weighted_crt_bind (snd action) (\<lambda>control.
      case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow>
          (0, comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
          (fst action + amount, comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
          (0, comma_semantic_b1_crt_leaf control))"

lemma comma_semantic_b1_crt_add_stop_exact:
  assumes applied:
      "comma_weighted_crt_apply action phase = Some (control,height)"
    and nonterminal_zero:
      "(\<exists>root. control=Comma_Semantic_B1_CRT_Continue root) \<or>
        control=Comma_Semantic_B1_CRT_Invalid \<Longrightarrow> height=0"
  shows "comma_weighted_crt_apply
      (comma_semantic_b1_crt_add_stop amount action) phase =
    Some (control,
      (case control of
         Comma_Semantic_B1_CRT_Stop _ \<Rightarrow> height+amount
       | _ \<Rightarrow> 0))"
proof -
  obtain elapsed where evaluated:
      "comma_weighted_crt_eval (snd action) phase=Some (control,elapsed)"
    and height: "fst action+elapsed=height"
    using applied by (auto simp: comma_weighted_crt_apply_def
      split: option.splits prod.splits)
  have bind_application:
    "comma_weighted_crt_apply
        (comma_semantic_b1_crt_add_stop amount action) phase =
      Option.bind (comma_weighted_crt_eval (snd action) phase)
        (\<lambda>(selected,spent). map_option
          (\<lambda>(result,more). (result,spent+more))
          (comma_weighted_crt_apply
            (case selected of
               Comma_Semantic_B1_CRT_Continue root \<Rightarrow>
                 (0,comma_semantic_b1_crt_leaf selected)
             | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
                 (fst action+amount,comma_semantic_b1_crt_leaf selected)
             | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
                 (0,comma_semantic_b1_crt_leaf selected)) phase))"
    by (simp only: comma_semantic_b1_crt_add_stop_def
      comma_weighted_crt_bind_exact)
  show ?thesis
  proof (cases control)
    case (Comma_Semantic_B1_CRT_Continue root)
    have zero: "height=0"
      using nonterminal_zero Comma_Semantic_B1_CRT_Continue by blast
    have elapsed_zero: "elapsed=0"
      using height zero by simp
    have leaf_applied:
      "comma_weighted_crt_apply
          (0,comma_semantic_b1_crt_leaf
            (Comma_Semantic_B1_CRT_Continue root)) phase =
        Some (Comma_Semantic_B1_CRT_Continue root,0)"
      by (simp add: comma_semantic_b1_crt_leaf_def comma_weighted_crt_apply_def)
    show ?thesis
      using bind_application evaluated elapsed_zero
        Comma_Semantic_B1_CRT_Continue leaf_applied
      by (simp only: Option.bind_lunit prod.case case_prod_Pair option.map
        option.map_id
        comma_semantic_b1_crt_control.case
        add_0_left bind_application evaluated elapsed_zero
        Comma_Semantic_B1_CRT_Continue leaf_applied)
  next
    case (Comma_Semantic_B1_CRT_Stop terminal)
    have accumulated_height:
      "elapsed+(fst action+amount)=height+amount"
      using height by (simp add: algebra_simps)
    have leaf_applied:
      "comma_weighted_crt_apply
          (fst action+amount,comma_semantic_b1_crt_leaf
            (Comma_Semantic_B1_CRT_Stop terminal)) phase =
        Some (Comma_Semantic_B1_CRT_Stop terminal,fst action+amount)"
      by (simp add: comma_semantic_b1_crt_leaf_def comma_weighted_crt_apply_def)
    show ?thesis
      using bind_application evaluated height
        Comma_Semantic_B1_CRT_Stop leaf_applied accumulated_height
      by (simp only: Option.bind_lunit prod.case case_prod_Pair option.map
        option.map_id
        comma_semantic_b1_crt_control.case
        bind_application evaluated height Comma_Semantic_B1_CRT_Stop
        leaf_applied accumulated_height)
  next
    case Comma_Semantic_B1_CRT_Invalid
    have zero: "height=0"
      using nonterminal_zero Comma_Semantic_B1_CRT_Invalid by blast
    have elapsed_zero: "elapsed=0"
      using height zero by simp
    have leaf_applied:
      "comma_weighted_crt_apply
          (0,comma_semantic_b1_crt_leaf Comma_Semantic_B1_CRT_Invalid) phase =
        Some (Comma_Semantic_B1_CRT_Invalid,0)"
      by (simp add: comma_semantic_b1_crt_leaf_def comma_weighted_crt_apply_def)
    show ?thesis
      using bind_application evaluated elapsed_zero
        Comma_Semantic_B1_CRT_Invalid leaf_applied
      by (simp only: Option.bind_lunit prod.case case_prod_Pair option.map
        option.map_id
        comma_semantic_b1_crt_control.case
        add_0_left bind_application evaluated elapsed_zero
        Comma_Semantic_B1_CRT_Invalid leaf_applied)
  qed
qed

definition comma_semantic_b1_crt_compose ::
    "nat \<Rightarrow> (nat \<times> comma_semantic_b1_crt_dag) \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      nat \<times> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_compose span left children =
    (if length children=46 then
      comma_weighted_crt_bind (snd left) (\<lambda>control.
        case control of
          Comma_Semantic_B1_CRT_Continue child \<Rightarrow>
            if child<length children then
              comma_semantic_b1_crt_add_stop span
                (fst (children!child),
                  comma_weighted_crt_shift span (snd (children!child)))
            else comma_semantic_b1_crt_invalid_action
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
            (fst left, comma_semantic_b1_crt_leaf control)
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
            (fst left, comma_semantic_b1_crt_leaf control))
     else comma_semantic_b1_crt_invalid_action)"

fun comma_semantic_b1_crt_power ::
    "nat \<Rightarrow> (nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list" where
  "comma_semantic_b1_crt_power 0 roots = roots"
| "comma_semantic_b1_crt_power (Suc k) roots =
    map (\<lambda>left.
      comma_semantic_b1_crt_compose (2^k) left
        (comma_semantic_b1_crt_power k roots))
      (comma_semantic_b1_crt_power k roots)"

fun comma_semantic_b1_crt_decode ::
    "comma_semantic_b1_crt_control \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_crt_decode
      (Comma_Semantic_B1_CRT_Continue root) height =
        (if root<46 \<and> height=0 then Comma_Semantic_B1_Continue root
         else Comma_Semantic_B1_Weighted_Invalid)"
| "comma_semantic_b1_crt_decode
      (Comma_Semantic_B1_CRT_Stop terminal) height =
        (if terminal<9 then Comma_Semantic_B1_Stop_At terminal height
         else Comma_Semantic_B1_Weighted_Invalid)"
| "comma_semantic_b1_crt_decode
      Comma_Semantic_B1_CRT_Invalid height =
        Comma_Semantic_B1_Weighted_Invalid"

definition comma_semantic_b1_crt_action_at ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_crt_action_at roots phase root =
    (if phase<924 \<and> length roots=46 \<and> root<length roots \<and>
        comma_weighted_crt_shape 0 (snd (roots!root)) then
       (case comma_weighted_crt_apply (roots!root) phase of
          None \<Rightarrow> Comma_Semantic_B1_Weighted_Invalid
        | Some (control,height) \<Rightarrow>
            comma_semantic_b1_crt_decode control height)
     else Comma_Semantic_B1_Weighted_Invalid)"

definition comma_semantic_b1_crt_action_eval ::
    "nat \<times> comma_semantic_b1_crt_dag \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_crt_action_eval action phase =
    (case comma_weighted_crt_apply action phase of
       None \<Rightarrow> Comma_Semantic_B1_Weighted_Invalid
     | Some (control,height) \<Rightarrow>
         comma_semantic_b1_crt_decode control height)"

definition comma_semantic_b1_crt_roots_action ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_crt_roots_action roots phase root =
    (if root<length roots then
       comma_semantic_b1_crt_action_eval (roots!root) phase
     else Comma_Semantic_B1_Weighted_Invalid)"

definition comma_semantic_b1_crt_roots_wellformed ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_roots_wellformed roots \<longleftrightarrow>
    length roots=46 \<and> (\<forall>root<46.
      comma_weighted_crt_wellformed (snd (roots!root)))"

definition comma_semantic_b1_crt_action_nonterminal_zero ::
    "(nat \<times> comma_semantic_b1_crt_dag) \<Rightarrow> bool" where
  "comma_semantic_b1_crt_action_nonterminal_zero action \<longleftrightarrow>
    (\<forall>phase control height.
      comma_weighted_crt_apply action phase=Some (control,height) \<longrightarrow>
        (case control of
           Comma_Semantic_B1_CRT_Continue root \<Rightarrow> height=0
         | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> height=0
         | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True))"

lemma comma_semantic_b1_crt_wellformed_eval_total:
  assumes wellformed: "comma_weighted_crt_wellformed tree"
  shows "\<exists>control elapsed.
    comma_weighted_crt_eval tree phase=Some (control,elapsed)"
  using wellformed
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
    and children: "list_all (\<lambda>(weight,child).
      comma_weighted_crt_wellformed child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  have index: "phase mod comma_crt_axis_radix axis<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain weight child where selected:
      "rows!(phase mod comma_crt_axis_radix axis)=(weight,child)"
    by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
  have member: "(weight,child)\<in>set rows"
    using nth_mem[OF index] selected by simp
  have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
    by (simp add: prod_set_defs)
  have child_wellformed: "comma_weighted_crt_wellformed child"
    using children member by (auto simp: list_all_iff prod_set_defs)
  obtain result elapsed where child_eval:
      "comma_weighted_crt_eval child phase=Some (result,elapsed)"
    using Comma_Weighted_CRT_Branch.IH[OF member child_member child_wellformed]
    by blast
  show ?case
    using axis extent selected child_eval
    by (auto simp: comma_weighted_crt_eval_branch)
qed

lemma comma_semantic_b1_crt_action_eval_total:
  assumes wellformed: "comma_weighted_crt_wellformed (snd action)"
  obtains control height where
    "comma_weighted_crt_apply action phase=Some (control,height)"
proof -
  obtain control elapsed where
      "comma_weighted_crt_eval (snd action) phase=Some (control,elapsed)"
    using comma_semantic_b1_crt_wellformed_eval_total[OF wellformed] by blast
  then have applied:
      "comma_weighted_crt_apply action phase=
        Some (control,fst action+elapsed)"
    by (simp add: comma_weighted_crt_apply_def)
  then show thesis by (rule that)
qed

lemma comma_semantic_b1_crt_action_admitted_zero:
  assumes wellformed: "comma_weighted_crt_wellformed (snd action)"
    and admitted: "\<forall>phase<924. comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_crt_action_eval action phase)"
  shows "comma_semantic_b1_crt_action_nonterminal_zero action"
proof -
  have periodic: "\<And>phase. comma_weighted_crt_apply action (phase mod 924)=
      comma_weighted_crt_apply action phase"
    using comma_weighted_crt_eval_mod_924[OF wellformed]
    by (auto simp: comma_weighted_crt_apply_def)
  have admitted_apply:
    "\<And>phase control height. comma_weighted_crt_apply action phase=
      Some (control,height) \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_decode control height)"
  proof -
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    have reduced_phase: "phase mod 924<924" by simp
    have reduced_apply:
      "comma_weighted_crt_apply action (phase mod 924)=
        Some (control,height)"
      using periodic[of phase] applied by simp
    have decoded:
      "comma_semantic_b1_crt_action_eval action (phase mod 924)=
        comma_semantic_b1_crt_decode control height"
      using reduced_apply
      by (simp add: comma_semantic_b1_crt_action_eval_def)
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_decode control height)"
    proof -
      have reduced_admitted:
        "comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_crt_action_eval action (phase mod 924))"
        using admitted[rule_format, OF reduced_phase] .
      show ?thesis using reduced_admitted decoded by simp
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_action_nonterminal_zero_def
  proof (intro allI impI)
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    have decoded_admitted:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_decode control height)"
      by (rule admitted_apply[OF applied])
    show "case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
      using decoded_admitted
    proof (cases control)
      case (Comma_Semantic_B1_CRT_Continue root)
      have "root<46 \<and> height=0"
        using decoded_admitted Comma_Semantic_B1_CRT_Continue
        by (simp add: comma_semantic_b1_crt_decode.simps
          comma_semantic_b1_weighted_result_admitted.simps
          split: if_splits)
      then show ?thesis using Comma_Semantic_B1_CRT_Continue by simp
    next
      case Comma_Semantic_B1_CRT_Invalid
      then show ?thesis using decoded_admitted
        by (simp add: comma_semantic_b1_crt_decode.simps
          comma_semantic_b1_weighted_result_admitted.simps)
    next
      case (Comma_Semantic_B1_CRT_Stop terminal)
      then show ?thesis by simp
    qed
  qed
qed

lemma comma_semantic_b1_crt_nonterminal_zero_of_graph_refinement:
  assumes refinement:
    "(\<forall>phase. comma_weighted_crt_apply action phase =
      map_option comma_semantic_b1_crt_graph_result
        (comma_semantic_b1_graph_eval nodes cid phase))"
  shows "comma_semantic_b1_crt_action_nonterminal_zero action"
proof -
  have zero:
    "\<And>phase control height.
      comma_weighted_crt_apply action phase=Some (control,height) \<Longrightarrow>
      height=0"
  proof -
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    have phase_refinement:
      "comma_weighted_crt_apply action phase =
        map_option comma_semantic_b1_crt_graph_result
          (comma_semantic_b1_graph_eval nodes cid phase)"
      using spec[OF refinement] .
    have mapped:
      "map_option comma_semantic_b1_crt_graph_result
        (comma_semantic_b1_graph_eval nodes cid phase)=Some (control,height)"
      using phase_refinement applied by simp
    then obtain returned where
      returned_exact: "comma_semantic_b1_graph_eval nodes cid phase=Some returned"
      and pair:
        "comma_semantic_b1_crt_graph_result returned=(control,height)"
      by (cases "comma_semantic_b1_graph_eval nodes cid phase") auto
    show "height=0" using pair by (cases returned) simp_all
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_action_nonterminal_zero_def
  proof (intro allI impI)
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    have height_zero: "height=0" by (rule zero[OF applied])
    show "case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
      using height_zero by (cases control) simp_all
  qed
qed

lemma comma_semantic_b1_crt_nonterminal_zero_of_bounded_stops:
  assumes terminal:
    "\<forall>phase. \<exists>J H. comma_weighted_crt_apply action phase=
      Some (Comma_Semantic_B1_CRT_Stop J,H)"
  shows "comma_semantic_b1_crt_action_nonterminal_zero action"
proof -
  have stop_control:
    "\<And>phase control height.
      comma_weighted_crt_apply action phase=Some (control,height) \<Longrightarrow>
      (\<exists>J. control=Comma_Semantic_B1_CRT_Stop J)"
  proof -
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    have stop_exists: "\<exists>J H. comma_weighted_crt_apply action phase=
        Some (Comma_Semantic_B1_CRT_Stop J,H)"
      using terminal by blast
    obtain J H where stop:
      "comma_weighted_crt_apply action phase=
        Some (Comma_Semantic_B1_CRT_Stop J,H)"
      using stop_exists by blast
    have "(control,height)=(Comma_Semantic_B1_CRT_Stop J,H)"
      using applied stop by simp
    then show "\<exists>J. control=Comma_Semantic_B1_CRT_Stop J" by blast
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_action_nonterminal_zero_def
  proof (intro allI impI)
    fix phase control height
    assume applied:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    obtain terminal where control_stop:
      "control=Comma_Semantic_B1_CRT_Stop terminal"
      using stop_control[OF applied] by blast
    show "case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> height=0
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
      using control_stop by simp
  qed
qed

lemma comma_semantic_b1_crt_action_eval_decode:
  assumes result:
      "comma_weighted_crt_apply action phase=Some (control,height)"
  shows "comma_semantic_b1_crt_action_eval action phase=
      comma_semantic_b1_crt_decode control height"
  using result by (simp add: comma_semantic_b1_crt_action_eval_def)

lemma comma_semantic_b1_graph_eval_result_admitted:
  assumes result:
    "comma_semantic_b1_graph_eval nodes cid phase=Some returned"
  shows "case returned of
      Comma_Semantic_B1_Live root \<Rightarrow> root<46
    | Comma_Semantic_B1_Stop terminal \<Rightarrow> terminal<9
    | Comma_Semantic_B1_Invalid \<Rightarrow> True"
  using result
proof (induction cid arbitrary: nodes phase returned rule: less_induct)
  case (less cid)
  then show ?case
    by (cases "comma_semantic_b1_graph_apply nodes cid phase")
      (auto simp: comma_semantic_b1_graph_eval.simps
        split: option.splits comma_semantic_b1_edge.splits if_splits
        dest: less.IH)
qed

lemma comma_semantic_b1_crt_decode_graph_root:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_crt_decode
      (fst (comma_semantic_b1_crt_graph_result
        (comma_semantic_graph_root_action phase root)))
      (snd (comma_semantic_b1_crt_graph_result
        (comma_semantic_graph_root_action phase root))) =
    comma_semantic_graph_root_weighted_action phase root"
proof -
  let ?evaluation = "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
    (comma_semantic_graph_root_ids!root) phase"
  show ?thesis
  proof (cases ?evaluation)
    case None
    then show ?thesis
      by (simp add: comma_semantic_graph_root_action_def
        comma_semantic_graph_root_weighted_action_def)
  next
    case (Some returned)
    have admitted:
      "case returned of
          Comma_Semantic_B1_Live next_root \<Rightarrow> next_root<46
        | Comma_Semantic_B1_Stop terminal \<Rightarrow> terminal<9
        | Comma_Semantic_B1_Invalid \<Rightarrow> True"
      by (rule comma_semantic_b1_graph_eval_result_admitted[OF Some])
    show ?thesis
      using Some admitted
      by (cases returned)
        (auto simp: comma_semantic_graph_root_action_def
          comma_semantic_graph_root_weighted_action_def
          comma_semantic_b1_crt_graph_result.simps
          comma_semantic_b1_crt_decode.simps)
  qed
qed

lemma comma_semantic_b1_crt_compile_root_weighted_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root)) phase =
    comma_semantic_graph_root_weighted_action phase root"
proof -
  have applied:
    "comma_weighted_crt_apply
       (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
         (comma_semantic_graph_root_ids!root)) phase =
     Some (comma_semantic_b1_crt_graph_result
       (comma_semantic_b1 phase root))"
    by (rule comma_semantic_b1_crt_compile_published_root_exact
      [OF comma_semantic_graph_valid_checked phase root])
  have root_action:
    "comma_semantic_graph_root_action phase root=comma_semantic_b1 phase root"
    by (rule comma_semantic_graph_root_action_exact
      [OF comma_semantic_graph_valid_checked phase root])
  have decoded:
    "comma_semantic_b1_crt_decode
       (fst (comma_semantic_b1_crt_graph_result (comma_semantic_b1 phase root)))
       (snd (comma_semantic_b1_crt_graph_result (comma_semantic_b1 phase root))) =
     comma_semantic_graph_root_weighted_action phase root"
    using comma_semantic_b1_crt_decode_graph_root[OF phase root]
      root_action by simp
  have applied_pair:
    "comma_weighted_crt_apply
       (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
         (comma_semantic_graph_root_ids!root)) phase =
     Some (fst (comma_semantic_b1_crt_graph_result
       (comma_semantic_b1 phase root)),
       snd (comma_semantic_b1_crt_graph_result
         (comma_semantic_b1 phase root)))"
    using applied by simp
  have action_value:
    "comma_semantic_b1_crt_action_eval
       (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
         (comma_semantic_graph_root_ids!root)) phase =
     comma_semantic_b1_crt_decode
       (fst (comma_semantic_b1_crt_graph_result (comma_semantic_b1 phase root)))
       (snd (comma_semantic_b1_crt_graph_result (comma_semantic_b1 phase root)))"
    by (rule comma_semantic_b1_crt_action_eval_decode[OF applied_pair])
  show ?thesis using action_value decoded by simp
qed

lemma comma_semantic_b1_crt_add_stop_wellformed:
  assumes wellformed: "comma_weighted_crt_wellformed (snd action)"
  shows "comma_weighted_crt_wellformed
      (snd (comma_semantic_b1_crt_add_stop amount action))"
proof -
  have callback: "\<And>control. comma_weighted_crt_wellformed
      (snd (case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow>
          (0,comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
          (fst action+amount,comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
          (0,comma_semantic_b1_crt_leaf control)))"
  proof -
    fix control
    show "comma_weighted_crt_wellformed
      (snd (case control of
        Comma_Semantic_B1_CRT_Continue root \<Rightarrow>
          (0,comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
          (fst action+amount,comma_semantic_b1_crt_leaf control)
      | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
          (0,comma_semantic_b1_crt_leaf control)))"
      by (cases control) (simp_all add: comma_semantic_b1_crt_leaf_def)
  qed
  have bound:
    "comma_weighted_crt_wellformed
      (snd (comma_weighted_crt_bind (snd action)
        (\<lambda>control. case control of
          Comma_Semantic_B1_CRT_Continue root \<Rightarrow>
            (0,comma_semantic_b1_crt_leaf control)
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
            (fst action+amount,comma_semantic_b1_crt_leaf control)
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
            (0,comma_semantic_b1_crt_leaf control))))"
    by (rule comma_weighted_crt_wellformed_bind[OF wellformed callback])
  show ?thesis using bound
    by (simp add: comma_semantic_b1_crt_add_stop_def)
qed

lemma comma_semantic_b1_crt_compose_wellformed:
  assumes length: "length children=46"
    and left: "comma_weighted_crt_wellformed (snd left)"
    and right: "\<And>child. child<46 \<Longrightarrow>
      comma_weighted_crt_wellformed (snd (children!child))"
  shows "comma_weighted_crt_wellformed
      (snd (comma_semantic_b1_crt_compose span left children))"
proof (cases "length children=46")
  case False
  then show ?thesis
    by (simp add: comma_semantic_b1_crt_compose_def
      comma_semantic_b1_crt_invalid_action_def comma_semantic_b1_crt_leaf_def)
next
  case True
  have callback:
      "\<And>control. comma_weighted_crt_wellformed
        (snd (case control of
          Comma_Semantic_B1_CRT_Continue child \<Rightarrow>
            if child<length children then
              comma_semantic_b1_crt_add_stop span
                (fst (children!child),
                  comma_weighted_crt_shift span (snd (children!child)))
            else comma_semantic_b1_crt_invalid_action
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
            (fst left,comma_semantic_b1_crt_leaf control)
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
            (fst left,comma_semantic_b1_crt_leaf control)))"
  proof -
    fix control
    show "comma_weighted_crt_wellformed
        (snd (case control of
          Comma_Semantic_B1_CRT_Continue child \<Rightarrow>
            if child<length children then
              comma_semantic_b1_crt_add_stop span
                (fst (children!child),
                  comma_weighted_crt_shift span (snd (children!child)))
            else comma_semantic_b1_crt_invalid_action
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
            (fst left,comma_semantic_b1_crt_leaf control)
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
            (fst left,comma_semantic_b1_crt_leaf control)))"
    proof (cases control)
      case (Comma_Semantic_B1_CRT_Continue child)
      then show ?thesis
      proof (cases "child<length children")
        case True
        then have child: "child<46" using length by simp
        have child_wf: "comma_weighted_crt_wellformed (snd (children!child))"
          by (rule right[OF child])
        have shifted_wf:
          "comma_weighted_crt_wellformed
            (comma_weighted_crt_shift span (snd (children!child)))"
          using child_wf by (simp only: comma_weighted_crt_shift_wellformed)
        have shifted_pair_wf:
          "comma_weighted_crt_wellformed
            (snd (fst (children!child),
              comma_weighted_crt_shift span (snd (children!child))))"
          using shifted_wf by simp
        have added_wf:
          "comma_weighted_crt_wellformed
            (snd (comma_semantic_b1_crt_add_stop span
              (fst (children!child),
                comma_weighted_crt_shift span (snd (children!child)))))"
          by (rule comma_semantic_b1_crt_add_stop_wellformed
            [where action="(fst (children!child),
              comma_weighted_crt_shift span (snd (children!child)))",
              OF shifted_pair_wf])
        show ?thesis using added_wf True Comma_Semantic_B1_CRT_Continue
          by simp
      next
        case False
        then show ?thesis using Comma_Semantic_B1_CRT_Continue
          by (simp add: comma_semantic_b1_crt_invalid_action_def
            comma_semantic_b1_crt_leaf_def)
      qed
    next
      case (Comma_Semantic_B1_CRT_Stop terminal)
      then show ?thesis by (simp add: comma_semantic_b1_crt_leaf_def)
    next
      case Comma_Semantic_B1_CRT_Invalid
      then show ?thesis by (simp add: comma_semantic_b1_crt_leaf_def)
    qed
  qed
  have bound:
      "comma_weighted_crt_wellformed
        (snd (comma_weighted_crt_bind (snd left)
          (\<lambda>control. case control of
            Comma_Semantic_B1_CRT_Continue child \<Rightarrow>
              if child<length children then
                comma_semantic_b1_crt_add_stop span
                  (fst (children!child),
                    comma_weighted_crt_shift span (snd (children!child)))
              else comma_semantic_b1_crt_invalid_action
          | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
              (fst left,comma_semantic_b1_crt_leaf control)
          | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
              (fst left,comma_semantic_b1_crt_leaf control))))"
    by (rule comma_weighted_crt_wellformed_bind[OF left callback])
  show ?thesis using True bound
    by (simp add: comma_semantic_b1_crt_compose_def)
qed

lemma comma_semantic_b1_crt_power_length:
  "length (comma_semantic_b1_crt_power k roots)=length roots"
  by (induction k) simp_all

lemma comma_semantic_b1_weighted_action_power_admitted_all:
  assumes base: "\<forall>phase root. root<46 \<longrightarrow>
      comma_semantic_b1_weighted_result_admitted (action phase root)"
  shows "\<forall>phase root. root<46 \<longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power k action phase root)"
  using base
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (intro allI impI)
    fix phase root :: nat
    assume root: "root<46"
    have prior_admitted:
      "\<forall>phase root. root<46 \<longrightarrow>
        comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_weighted_action_power k action phase root)"
      by (rule Suc.IH[OF Suc.prems])
    have first:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power k action phase root)"
      using prior_admitted[rule_format, OF root] .
    have second:
      "\<And>child. child<46 \<Longrightarrow>
        comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_weighted_action_power k action
            ((phase+2^k) mod 924) child)"
    proof -
      fix child :: nat
      assume child: "child<46"
      show "comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_weighted_action_power k action
            ((phase+2^k) mod 924) child)"
        using prior_admitted[rule_format, OF child] .
    qed
    have then_admitted:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_word_then (2^k)
          (\<lambda>p i. comma_semantic_b1_weighted_action_power k action p i)
          (\<lambda>p i. comma_semantic_b1_weighted_action_power k action p i)
          phase root)"
      by (rule comma_semantic_b1_weighted_word_then_admitted
        [where A="\<lambda>p i. comma_semantic_b1_weighted_action_power k action p i"
          and B="\<lambda>p i. comma_semantic_b1_weighted_action_power k action p i"
          and n="2^k" and phase=phase and root=root, OF first second])
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power (Suc k) action phase root)"
      using then_admitted
      by (simp only: comma_semantic_b1_weighted_action_power.simps)
  qed
qed

lemma comma_semantic_b1_crt_power_wellformed:
  assumes roots: "comma_semantic_b1_crt_roots_wellformed roots"
  shows "comma_semantic_b1_crt_roots_wellformed
      (comma_semantic_b1_crt_power k roots)"
  using roots
proof (induction k)
  case 0
  then show ?case by (simp add: comma_semantic_b1_crt_roots_wellformed_def)
next
  case (Suc k)
  let ?current = "comma_semantic_b1_crt_power k roots"
  have current: "comma_semantic_b1_crt_roots_wellformed ?current"
    by (rule Suc.IH[OF roots])
  have count: "length ?current=46"
    using current by (simp add: comma_semantic_b1_crt_roots_wellformed_def)
  have length_result:
      "length (comma_semantic_b1_crt_power (Suc k) roots)=46"
    using current by (simp add: comma_semantic_b1_crt_roots_wellformed_def)
  have children:
      "\<And>root. root<46 \<Longrightarrow>
        comma_weighted_crt_wellformed (snd (?current!root))"
    using current by (auto simp: comma_semantic_b1_crt_roots_wellformed_def)
  show ?case
    unfolding comma_semantic_b1_crt_roots_wellformed_def
  proof (intro conjI allI impI)
    show "length (comma_semantic_b1_crt_power (Suc k) roots)=46"
      by (rule length_result)
  next
    fix root :: nat assume root: "root<46"
    have left: "comma_weighted_crt_wellformed (snd (?current!root))"
      by (rule children[OF root])
    have result:
      "comma_weighted_crt_wellformed
        (snd (comma_semantic_b1_crt_compose (2^k) (?current!root) ?current))"
      by (rule comma_semantic_b1_crt_compose_wellformed[OF count left children])
    show "comma_weighted_crt_wellformed
        (snd (comma_semantic_b1_crt_power (Suc k) roots!root))"
      using root count result by (simp add: comma_semantic_b1_crt_power.simps)
  qed
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_add_stop_exact
    comma_semantic_b1_crt_wellformed_eval_total
    comma_semantic_b1_crt_action_eval_total
    comma_semantic_b1_crt_action_admitted_zero
    comma_semantic_b1_crt_nonterminal_zero_of_graph_refinement
    comma_semantic_b1_crt_nonterminal_zero_of_bounded_stops
    comma_semantic_b1_crt_add_stop_wellformed
    comma_semantic_b1_crt_compose_wellformed
    comma_semantic_b1_crt_power_length
    comma_semantic_b1_weighted_action_power_admitted_all
    comma_semantic_b1_crt_power_wellformed};
  Thm.consolidate checked;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT composition, power, wellformedness, and admission laws" checked;
  if null (Thm_Deps.all_oracles checked) then ()
  else error "Weighted CRT action laws depend on an oracle"
\<close>

end
