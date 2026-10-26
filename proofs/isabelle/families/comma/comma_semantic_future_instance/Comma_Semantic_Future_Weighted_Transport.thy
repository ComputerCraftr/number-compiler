theory Comma_Semantic_Future_Weighted_Transport
  imports Comma_Semantic_B1_Instance.Comma_Semantic_Summary_Instance
begin

text \<open>
An authenticated source-family action has a quotient key and an occurrence
payload.  The key contains the future control (including the terminal label)
and the exact ordered child class IDs.  The local transition displacement and
the complete-decade weight stay in the payload.  In particular, the Stop
weight is reconstructed as @{term "9 * H + J"}; neither it nor the completed
displacement is a semantic class ID.  The receiver phase is an argument to
application and is transported by the two distinct guarded phase equations
below.
\<close>

record comma_semantic_future_weighted_action =
  comma_semantic_future_action_control :: comma_future_control
  comma_semantic_future_action_local_delta :: nat
  comma_semantic_future_action_complete_decades :: nat
  comma_semantic_future_action_ordered_children :: "nat list"

fun comma_semantic_future_action_terminal_position ::
    "comma_future_control \<Rightarrow> nat" where
  "comma_semantic_future_action_terminal_position (Comma_Future_Fork a) = a - 2"
| "comma_semantic_future_action_terminal_position Comma_Future_Landmine = 8"

fun comma_semantic_future_action_terminal ::
    "comma_future_control \<Rightarrow> comma_decade_terminal" where
  "comma_semantic_future_action_terminal (Comma_Future_Fork a) =
    Comma_Terminal_Fork a"
| "comma_semantic_future_action_terminal Comma_Future_Landmine =
    Comma_Terminal_Landmine"

definition comma_semantic_future_control_of_terminal_position ::
    "nat \<Rightarrow> comma_future_control" where
  "comma_semantic_future_control_of_terminal_position J =
    (if J=8 then Comma_Future_Landmine else Comma_Future_Fork (J+2))"

definition comma_semantic_future_action_key ::
    "comma_semantic_future_weighted_action \<Rightarrow>
      comma_future_control \<times> nat list" where
  "comma_semantic_future_action_key action =
    (comma_semantic_future_action_control action,
     comma_semantic_future_action_ordered_children action)"

definition comma_semantic_future_action_stop_weight ::
    "comma_semantic_future_weighted_action \<Rightarrow> nat" where
  "comma_semantic_future_action_stop_weight action =
    9 * comma_semantic_future_action_complete_decades action +
      comma_semantic_future_action_terminal_position
        (comma_semantic_future_action_control action)"

definition comma_semantic_future_action_completed_delta ::
    "comma_semantic_future_weighted_action \<Rightarrow> nat" where
  "comma_semantic_future_action_completed_delta action =
    comma_semantic_future_action_local_delta action +
      comma_semantic_future_action_complete_decades action"

definition comma_semantic_future_action_provider_phase ::
    "nat \<Rightarrow> comma_semantic_future_weighted_action \<Rightarrow> nat" where
  "comma_semantic_future_action_provider_phase r action =
    (r + comma_semantic_future_action_local_delta action) mod 924"

definition comma_semantic_future_action_successor_phase ::
    "nat \<Rightarrow> comma_semantic_future_weighted_action \<Rightarrow> nat" where
  "comma_semantic_future_action_successor_phase r action =
    (r + comma_semantic_future_action_completed_delta action) mod 924"

definition comma_semantic_future_action_control_admitted ::
    "comma_future_control \<Rightarrow> bool" where
  "comma_semantic_future_action_control_admitted control =
    (case control of
       Comma_Future_Fork a \<Rightarrow> 2 \<le> a \<and> a \<le> 9
     | Comma_Future_Landmine \<Rightarrow> True)"

fun comma_semantic_future_action_children_shape ::
    "comma_future_control \<Rightarrow> nat list \<Rightarrow> bool" where
  "comma_semantic_future_action_children_shape (Comma_Future_Fork a) children =
    (length children=2)"
| "comma_semantic_future_action_children_shape Comma_Future_Landmine children =
    (children=[])"

definition comma_semantic_future_action_of_weighted_stop ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
      comma_semantic_b1_weighted_result \<Rightarrow>
      comma_semantic_future_weighted_action option" where
  "comma_semantic_future_action_of_weighted_stop d children result =
    (case result of
       Comma_Semantic_B1_Stop_At J H \<Rightarrow>
         if J<9 \<and> H\<le>26 \<and>
             comma_semantic_future_action_children_shape
               (comma_semantic_future_control_of_terminal_position J) children
         then Some
           \<lparr>comma_semantic_future_action_control =
              comma_semantic_future_control_of_terminal_position J,
            comma_semantic_future_action_local_delta = d,
            comma_semantic_future_action_complete_decades = H,
            comma_semantic_future_action_ordered_children = children\<rparr>
         else None
     | _ \<Rightarrow> None)"

definition comma_semantic_future_action_of_direct_control ::
    "nat \<Rightarrow> nat list \<Rightarrow> comma_future_control \<Rightarrow>
      comma_semantic_future_weighted_action option" where
  "comma_semantic_future_action_of_direct_control d children control =
    (if comma_semantic_future_action_control_admitted control \<and>
        comma_semantic_future_action_children_shape control children then
       Some \<lparr>comma_semantic_future_action_control = control,
         comma_semantic_future_action_local_delta = d,
         comma_semantic_future_action_complete_decades = 0,
         comma_semantic_future_action_ordered_children = children\<rparr>
     else None)"

lemma comma_semantic_future_control_of_terminal_position_exact:
  assumes "J<9"
  shows "comma_semantic_future_action_terminal_position
      (comma_semantic_future_control_of_terminal_position J) = J"
    "comma_semantic_future_action_control_admitted
      (comma_semantic_future_control_of_terminal_position J)"
proof (cases "J=8")
  case True
  then show ?thesis
    by (simp_all add: comma_semantic_future_control_of_terminal_position_def
      comma_semantic_future_action_control_admitted_def
      comma_semantic_future_action_terminal_position.simps)
next
  case False
  have "J\<le>7" using assms False by arith
  then show ?thesis
    using False
    by (simp_all add: comma_semantic_future_control_of_terminal_position_def
      comma_semantic_future_action_control_admitted_def
      comma_semantic_future_action_terminal_position.simps; arith)
qed

lemma comma_semantic_future_action_of_weighted_stop_exact:
  assumes stop: "result=Comma_Semantic_B1_Stop_At J H"
    and position: "J<9"
    and height: "H\<le>26"
    and children_shape:
      "comma_semantic_future_action_children_shape
        (comma_semantic_future_control_of_terminal_position J) children"
  obtains action where
    "comma_semantic_future_action_of_weighted_stop d children result =
      Some action"
    "comma_semantic_future_action_control action =
      comma_semantic_future_control_of_terminal_position J"
    "comma_semantic_future_action_local_delta action = d"
    "comma_semantic_future_action_complete_decades action = H"
    "comma_semantic_future_action_ordered_children action = children"
    "comma_semantic_future_action_stop_weight action = 9*H+J"
    "comma_semantic_future_action_completed_delta action = d+H"
proof -
  let ?action = "\<lparr>comma_semantic_future_action_control =
      comma_semantic_future_control_of_terminal_position J,
    comma_semantic_future_action_local_delta = d,
    comma_semantic_future_action_complete_decades = H,
    comma_semantic_future_action_ordered_children = children\<rparr>"
  have control_position:
    "comma_semantic_future_action_terminal_position
      (comma_semantic_future_control_of_terminal_position J) = J"
    and control_admitted:
    "comma_semantic_future_action_control_admitted
      (comma_semantic_future_control_of_terminal_position J)"
    by (rule comma_semantic_future_control_of_terminal_position_exact[OF position])
  have selected:
    "comma_semantic_future_action_of_weighted_stop d children result =
      Some ?action"
    using stop position height children_shape
    by (simp add: comma_semantic_future_action_of_weighted_stop_def)
  show thesis
    by (rule that[OF selected])
      (simp_all add: comma_semantic_future_action_stop_weight_def
        comma_semantic_future_action_completed_delta_def control_position)
qed

lemma comma_semantic_future_action_of_direct_control_exact:
  assumes admitted: "comma_semantic_future_action_control_admitted control"
    and children_shape:
      "comma_semantic_future_action_children_shape control children"
  obtains action where
    "comma_semantic_future_action_of_direct_control d children control =
      Some action"
    "comma_semantic_future_action_control action = control"
    "comma_semantic_future_action_local_delta action = d"
    "comma_semantic_future_action_complete_decades action = 0"
    "comma_semantic_future_action_ordered_children action = children"
    "comma_semantic_future_action_stop_weight action =
      comma_semantic_future_action_terminal_position control"
    "comma_semantic_future_action_completed_delta action = d"
proof -
  let ?action = "\<lparr>comma_semantic_future_action_control = control,
      comma_semantic_future_action_local_delta = d,
      comma_semantic_future_action_complete_decades = 0,
      comma_semantic_future_action_ordered_children = children\<rparr>"
  have selected:
    "comma_semantic_future_action_of_direct_control d children control =
      Some ?action"
    using admitted children_shape
    by (simp add: comma_semantic_future_action_of_direct_control_def)
  show thesis
    by (rule that[OF selected])
      (simp_all add: comma_semantic_future_action_stop_weight_def
        comma_semantic_future_action_completed_delta_def)
qed

text \<open>This decoder binds only the graph-derived Stop control and complete
decade weight.  Its local displacement and ordered children are explicit
occurrence inputs; no source-prefix or candidate-class authority follows from
this adapter alone.\<close>

definition comma_semantic_future_action_of_graph_power ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_future_weighted_action option" where
  "comma_semantic_future_action_of_graph_power d children phase root =
    (if phase<924 \<and> root<46 then
       comma_semantic_future_action_of_weighted_stop d children
         (comma_semantic_b1_weighted_action_power 5
           comma_semantic_graph_root_weighted_action phase root)
     else None)"

lemma comma_semantic_future_action_of_weighted_stop_rejects_large_height:
  assumes stop: "result=Comma_Semantic_B1_Stop_At J H"
    and height: "26 < H"
  shows "comma_semantic_future_action_of_weighted_stop d children result=None"
  using stop height
  by (simp add: comma_semantic_future_action_of_weighted_stop_def)

lemma comma_semantic_future_exact_summary_control_transport:
  assumes controls: "comma_decade_control source = comma_decade_control target"
    and summary: "comma_decade_exact_summary source H terminal"
  shows "comma_decade_exact_summary target H terminal"
  using summary controls
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have target_control:
    "comma_decade_control target = Comma_Decade_Fork a 0"
    using fork.hyps fork.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.fork[OF target_control])
next
  case (landmine s)
  have target_control:
    "comma_decade_control target = Comma_Decade_Landmine 0"
    using landmine.hyps landmine.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.landmine[OF target_control])
next
  case (crossing s t n terminal)
  have target_control:
    "comma_decade_control target = Comma_Decade_Continue t"
    using crossing.hyps(1) crossing.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.crossing
      [OF target_control crossing.hyps(2)])
qed

lemma comma_semantic_future_exact_summary_orbit_transport:
  assumes phase: "phase<924"
    and x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
    and summary:
      "comma_decade_exact_summary (Comma_Decade phase x) H terminal"
  shows "comma_decade_exact_summary (Comma_Decade phase y) H terminal"
proof -
  have controls:
    "comma_decade_control (Comma_Decade phase x) =
      comma_decade_control (Comma_Decade phase y)"
    by (rule comma_decade_control_orbit_congruent[OF x y same])
  show ?thesis
    by (rule comma_semantic_future_exact_summary_control_transport
      [OF controls summary])
qed

lemma comma_semantic_future_graph_power_weighted_stop:
  assumes phase: "phase<924"
    and offset: "offset\<le>90"
    and summary:
      "comma_decade_exact_summary (Comma_Decade phase offset) H terminal"
    and height: "H\<le>26"
    and children_shape:
      "comma_semantic_future_action_children_shape
        (comma_semantic_future_control_of_terminal_position
          (comma_terminal_weight_digit terminal)) children"
  obtains action where
    "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action phase
        (comma_offset_orbit offset) =
      Comma_Semantic_B1_Stop_At (comma_terminal_weight_digit terminal) H"
    "comma_semantic_future_action_of_graph_power d children phase
        (comma_offset_orbit offset) = Some action"
    "comma_semantic_future_action_control action =
      comma_semantic_future_control_of_terminal_position
        (comma_terminal_weight_digit terminal)"
    "comma_semantic_future_action_local_delta action = d"
    "comma_semantic_future_action_complete_decades action = H"
    "comma_semantic_future_action_ordered_children action = children"
    "comma_semantic_future_action_stop_weight action =
      comma_terminal_weight_encode H terminal"
    "comma_semantic_future_action_completed_delta action = d+H"
proof -
  let ?root = "comma_offset_orbit offset"
  let ?representative = "comma_offset_representative offset"
  let ?result = "comma_semantic_b1_weighted_action_power 5
      comma_semantic_graph_root_weighted_action phase ?root"
  have root: "?root<46"
    by (rule comma_offset_orbit_bound)
  have representative_bound: "?representative\<le>90"
    by (rule comma_offset_representative_admitted(1))
  have same:
    "comma_offset_orbit offset=comma_offset_orbit ?representative"
    by (rule comma_offset_representative_admitted(2))
  have representative_summary:
    "comma_decade_exact_summary
      (Comma_Decade phase ?representative) H terminal"
    by (rule comma_semantic_future_exact_summary_orbit_transport
      [OF phase offset representative_bound same summary])
  have graph_stop:
    "comma_semantic_graph_action_power 5 phase ?root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode H terminal)"
    using comma_semantic_graph_stop_from_exact_summary
      [OF phase root representative_summary height] by blast
  have encoded:
    "comma_semantic_b1_weighted_encode ?result =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode H terminal)"
    using comma_semantic_graph_weighted_power_exact[of 5 phase ?root]
      graph_stop by simp
  have admitted: "comma_semantic_b1_weighted_result_admitted ?result"
  proof (rule comma_semantic_b1_weighted_action_power_admitted)
    show "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
        comma_semantic_b1_weighted_result_admitted
          (comma_semantic_graph_root_weighted_action phase root)"
      by (rule comma_semantic_graph_root_weighted_action_admitted)
    show "phase<924" by (rule phase)
    show "?root<46" by (rule root)
  qed
  have stop: "\<exists>J. \<exists>K. ?result=Comma_Semantic_B1_Stop_At J K"
    using encoded admitted
    by (cases ?result)
      (auto simp: comma_semantic_b1_weighted_result_admitted.simps)
  obtain J K where result:
      "?result=Comma_Semantic_B1_Stop_At J K"
    using stop by blast
  have J_bound: "J<9"
    using admitted result
    by (simp add: comma_semantic_b1_weighted_result_admitted.simps)
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound
      [OF comma_decade_exact_summary_terminal_admitted[OF summary]])
  have components:
    "J=comma_terminal_weight_digit terminal" "K=H"
    using encoded result J_bound digit_bound
    by (auto simp: comma_semantic_b1_weighted_encode.simps
        comma_terminal_weight_encode_def; presburger)
  have selected:
    "comma_semantic_future_action_of_graph_power d children phase ?root =
      Some \<lparr>comma_semantic_future_action_control =
          comma_semantic_future_control_of_terminal_position
            (comma_terminal_weight_digit terminal),
        comma_semantic_future_action_local_delta=d,
        comma_semantic_future_action_complete_decades=H,
        comma_semantic_future_action_ordered_children=children\<rparr>"
    using result components digit_bound height children_shape phase root
    by (simp add: comma_semantic_future_action_of_graph_power_def
        comma_semantic_future_action_of_weighted_stop_def)
  have weighted_result:
    "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action phase ?root =
      Comma_Semantic_B1_Stop_At (comma_terminal_weight_digit terminal) H"
    using result components by simp
  have position:
    "comma_semantic_future_action_terminal_position
      (comma_semantic_future_control_of_terminal_position
        (comma_terminal_weight_digit terminal)) =
      comma_terminal_weight_digit terminal"
    and control_admitted:
    "comma_semantic_future_action_control_admitted
      (comma_semantic_future_control_of_terminal_position
        (comma_terminal_weight_digit terminal))"
    by (rule comma_semantic_future_control_of_terminal_position_exact
      [OF digit_bound])+
  show thesis
    by (rule that[OF weighted_result selected])
      (simp_all add: comma_semantic_future_action_stop_weight_def
        comma_semantic_future_action_completed_delta_def
        comma_terminal_weight_encode_def position)
qed

lemma comma_semantic_future_action_position_bound:
  assumes "comma_semantic_future_action_control_admitted control"
  shows "comma_semantic_future_action_terminal_position control < 9"
  using assms
  by (cases control)
    (auto simp: comma_semantic_future_action_control_admitted_def)

lemma comma_semantic_future_action_terminal_weight_decode:
  assumes admitted: "comma_semantic_future_action_control_admitted
      (comma_semantic_future_action_control action)"
  shows "comma_terminal_weight_decode
      (comma_semantic_future_action_stop_weight action) =
    (comma_semantic_future_action_complete_decades action,
     comma_semantic_future_action_terminal
       (comma_semantic_future_action_control action))"
proof -
  let ?H = "comma_semantic_future_action_complete_decades action"
  let ?control = "comma_semantic_future_action_control action"
  let ?J = "comma_semantic_future_action_terminal_position ?control"
  have J: "?J < 9"
    by (rule comma_semantic_future_action_position_bound[OF admitted])
  have quotient: "(9*?H+?J) div 9 = ?H"
    and residue: "(9*?H+?J) mod 9 = ?J"
    using J by presburger
  show ?thesis
    using admitted quotient residue
    by (cases ?control)
      (auto simp: comma_terminal_weight_decode_def
        comma_terminal_weight_terminal_def
        comma_semantic_future_action_stop_weight_def
        comma_semantic_future_action_terminal_position.simps
        comma_semantic_future_action_terminal.simps
        comma_semantic_future_action_control_admitted_def; arith)
qed

lemma comma_semantic_future_action_phase_transport:
  "comma_semantic_future_action_provider_phase r action =
      (r + comma_semantic_future_action_local_delta action) mod 924"
  "comma_semantic_future_action_successor_phase r action =
      (r + comma_semantic_future_action_local_delta action +
        comma_semantic_future_action_complete_decades action) mod 924"
  by (simp_all add: comma_semantic_future_action_provider_phase_def
    comma_semantic_future_action_successor_phase_def
    comma_semantic_future_action_completed_delta_def)

lemma comma_semantic_future_action_phase_transport_guarded:
  assumes receiver: "r < 924"
  shows "comma_semantic_future_action_provider_phase r action < 924"
    "comma_semantic_future_action_successor_phase r action < 924"
  using receiver
  by (simp_all add: comma_semantic_future_action_provider_phase_def
    comma_semantic_future_action_successor_phase_def
    comma_semantic_future_action_completed_delta_def)

lemma comma_semantic_future_action_key_ignores_occurrence_payload:
  assumes control:
      "comma_semantic_future_action_control left =
        comma_semantic_future_action_control right"
    and children:
      "comma_semantic_future_action_ordered_children left =
        comma_semantic_future_action_ordered_children right"
  shows "comma_semantic_future_action_key left =
    comma_semantic_future_action_key right"
  using control children by (simp add: comma_semantic_future_action_key_def)

lemma comma_semantic_future_action_key_eq_iff:
  "comma_semantic_future_action_key left =
      comma_semantic_future_action_key right \<longleftrightarrow>
    comma_semantic_future_action_control left =
      comma_semantic_future_action_control right \<and>
    comma_semantic_future_action_ordered_children left =
      comma_semantic_future_action_ordered_children right"
  by (simp add: comma_semantic_future_action_key_def)

lemma comma_semantic_future_weighted_crt_eval_periodic_924:
  "comma_weighted_crt_eval tree phase =
    comma_weighted_crt_eval tree (phase mod 924)"
proof (induction tree arbitrary: phase)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  show ?case
  proof (cases "axis<4 \<and> length rows=comma_crt_axis_radix axis")
    case False
    then show ?thesis by simp
  next
    case True
    then have axis: "axis<4" and extent:
        "length rows=comma_crt_axis_radix axis" by auto
  have radix_divides: "comma_crt_axis_radix axis dvd 924"
    by (rule comma_crt_axis_radices_divide_924[OF axis])
  have same_slot:
    "phase mod comma_crt_axis_radix axis =
      (phase mod 924) mod comma_crt_axis_radix axis"
  proof -
    have "(phase mod 924) mod comma_crt_axis_radix axis =
        phase mod comma_crt_axis_radix axis"
      by (rule mod_mod_cancel[OF radix_divides])
    then show ?thesis by (rule sym)
  qed
  have selected_index:
    "phase mod comma_crt_axis_radix axis<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain edge_weight child where selected:
      "rows!(phase mod comma_crt_axis_radix axis)=(edge_weight,child)"
    by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
  have member: "(edge_weight,child)\<in>set rows"
    using nth_mem[OF selected_index] selected by simp
  have child_member: "child\<in>Basic_BNFs.snds (edge_weight,child)"
    by (simp add: prod_set_defs)
  have child_periodic:
    "comma_weighted_crt_eval child phase =
      comma_weighted_crt_eval child (phase mod 924)"
    using Comma_Weighted_CRT_Branch.IH[OF member child_member, of phase]
    by blast
  show ?thesis
    using comma_weighted_crt_eval_branch[OF axis extent, of phase]
      comma_weighted_crt_eval_branch[OF axis extent, of "phase mod 924"]
      selected same_slot child_periodic
    by simp
  qed
qed

text \<open>
The candidate binding for a weighted semantic action must query its receiver
at the phase after the accumulated edge/root weight.  A control-only bind
would query at the original phase and is therefore unsound for future child
IDs.  The following generic phase bind keeps the source control and the
receiver lookup result together while retaining the source weight as the
single additive output payload.
\<close>

fun comma_semantic_future_crt_map_control ::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      'b comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_map_control f (Comma_Weighted_CRT_Leaf control) =
    Comma_Weighted_CRT_Leaf (f control)"
| "comma_semantic_future_crt_map_control f
      (Comma_Weighted_CRT_Branch axis rows) =
    Comma_Weighted_CRT_Branch axis
      (map (\<lambda>(weight,child).
        (weight,comma_semantic_future_crt_map_control f child)) rows)"

lemma comma_semantic_future_crt_map_control_shape:
  "comma_weighted_crt_shape lower
      (comma_semantic_future_crt_map_control f tree) =
    comma_weighted_crt_shape lower tree"
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_semantic_future_crt_map_control_eval:
  "comma_weighted_crt_eval (comma_semantic_future_crt_map_control f tree) phase =
    map_option (\<lambda>(control,weight). (f control,weight))
      (comma_weighted_crt_eval tree phase)"
  by (induction tree)
    (auto simp: comma_weighted_crt_eval_branch nth_map
      split: option.splits prod.splits)

definition comma_semantic_future_crt_map_action_control ::
    "('a \<Rightarrow> 'b) \<Rightarrow>
      nat \<times> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      nat \<times> 'b comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_map_action_control f action =
    (fst action,comma_semantic_future_crt_map_control f (snd action))"

definition comma_semantic_future_crt_key_apply ::
    "nat \<times> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      nat \<Rightarrow> 'a option" where
  "comma_semantic_future_crt_key_apply action phase =
    map_option fst (comma_weighted_crt_apply action phase)"

text \<open>
The future key is observed from three independent projections.  In
particular, an ordered child pair is never a selector leaf: the North and
South class IDs remain separate actions and are joined only by this checked
point query.  The query rejects absent components, unequal accumulated
weights, and a control/arity mismatch.
\<close>

type_synonym comma_semantic_future_projected_key_action =
  "(nat \<times> comma_future_control option comma_semantic_weighted_crt_dag) \<times>
   ((nat \<times> nat comma_semantic_weighted_crt_dag) \<times>
    (nat \<times> nat comma_semantic_weighted_crt_dag))"

definition comma_semantic_future_projected_control_action ::
    "comma_semantic_future_projected_key_action \<Rightarrow>
      nat \<times> comma_future_control option comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_projected_control_action action = fst action"

definition comma_semantic_future_projected_north_action ::
    "comma_semantic_future_projected_key_action \<Rightarrow>
      nat \<times> nat comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_projected_north_action action = fst (snd action)"

definition comma_semantic_future_projected_south_action ::
    "comma_semantic_future_projected_key_action \<Rightarrow>
      nat \<times> nat comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_projected_south_action action = snd (snd action)"

definition comma_semantic_future_projected_key_apply ::
    "comma_semantic_future_projected_key_action \<Rightarrow> nat \<Rightarrow>
      (comma_future_control option \<times> nat list) option" where
  "comma_semantic_future_projected_key_apply action phase =
    (case comma_weighted_crt_apply
        (comma_semantic_future_projected_control_action action) phase of
       Some (Some (Comma_Future_Fork target),control_weight) \<Rightarrow>
         (case (comma_weighted_crt_apply
                  (comma_semantic_future_projected_north_action action) phase,
                comma_weighted_crt_apply
                  (comma_semantic_future_projected_south_action action) phase) of
            (Some (north,north_weight),Some (south,south_weight)) \<Rightarrow>
              if control_weight=north_weight \<and> control_weight=south_weight \<and>
                  2 \<le> target \<and> target \<le> 9 \<and>
                  comma_semantic_future_action_children_shape
                    (Comma_Future_Fork target) [north,south]
              then Some (Some (Comma_Future_Fork target),[north,south]) else None
          | _ \<Rightarrow> None)
     | Some (Some Comma_Future_Landmine,_) \<Rightarrow>
         if comma_semantic_future_action_control_admitted Comma_Future_Landmine \<and>
             comma_semantic_future_action_children_shape Comma_Future_Landmine []
         then Some (Some Comma_Future_Landmine,[]) else None
     | _ \<Rightarrow> None)"

lemma comma_semantic_future_projected_key_apply_exact:
  assumes control:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_control_action action) phase =
        Some (Some (Comma_Future_Fork target),weight)"
    and north:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_north_action action) phase =
        Some (north_id,weight)"
    and south:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_south_action action) phase =
        Some (south_id,weight)"
    and target: "2 \<le> target" "target \<le> 9"
    and shape:
      "comma_semantic_future_action_children_shape
        (Comma_Future_Fork target) [north_id,south_id]"
  shows "comma_semantic_future_projected_key_apply action phase =
    Some (Some (Comma_Future_Fork target),[north_id,south_id])"
  using control north south target shape
  by (simp add: comma_semantic_future_projected_key_apply_def)

lemma comma_semantic_future_projected_key_apply_landmine:
  assumes control:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_control_action action) phase =
        Some (Some Comma_Future_Landmine,weight)"
  shows "comma_semantic_future_projected_key_apply action phase =
    Some (Some Comma_Future_Landmine,[])"
  using control
  by (simp add: comma_semantic_future_projected_key_apply_def
    comma_semantic_future_action_control_admitted.simps
    comma_semantic_future_action_children_shape.simps)

lemma comma_semantic_future_crt_map_action_control_exact:
  "comma_semantic_future_crt_key_apply
      (comma_semantic_future_crt_map_action_control f action) phase =
    map_option f (comma_semantic_future_crt_key_apply action phase)"
  by (cases action)
    (simp add: comma_semantic_future_crt_key_apply_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval
      comma_weighted_crt_apply_def)

lemma comma_semantic_future_crt_key_apply_periodic_924:
  "comma_semantic_future_crt_key_apply action phase =
    comma_semantic_future_crt_key_apply action (phase mod 924)"
  by (cases action)
    (simp add: comma_semantic_future_crt_key_apply_def
      comma_weighted_crt_apply_def
      comma_semantic_future_weighted_crt_eval_periodic_924)

lemma comma_semantic_future_crt_key_apply_extensional_924:
  assumes equal:
    "\<And>phase. phase<924 \<Longrightarrow>
      comma_semantic_future_crt_key_apply left phase =
      comma_semantic_future_crt_key_apply right phase"
  shows "comma_semantic_future_crt_key_apply left phase =
    comma_semantic_future_crt_key_apply right phase"
proof -
  have residue: "phase mod 924<924" by simp
  have selected:
    "comma_semantic_future_crt_key_apply left (phase mod 924) =
      comma_semantic_future_crt_key_apply right (phase mod 924)"
    by (rule equal[OF residue])
  show ?thesis
    using selected
    by (simp only: comma_semantic_future_crt_key_apply_periodic_924)
qed

lemma comma_semantic_future_weighted_crt_shape_mono:
  assumes shape: "comma_weighted_crt_shape high tree"
    and bound: "low\<le>high"
  shows "comma_weighted_crt_shape low tree"
  using shape bound
  by (induction tree arbitrary: low high)
    (auto simp: list_all_iff prod_set_defs)

fun comma_semantic_future_crt_phase_bind_aux ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      ('a \<Rightarrow> 'b comma_semantic_weighted_crt_dag) \<Rightarrow>
      ('a \<times> 'b) comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_phase_bind_aux prefix
      (Comma_Weighted_CRT_Leaf control) receiver =
    comma_weighted_crt_shift prefix
      (comma_semantic_future_crt_map_control (Pair control)
        (receiver control))"
| "comma_semantic_future_crt_phase_bind_aux prefix
      (Comma_Weighted_CRT_Branch axis rows) receiver =
    Comma_Weighted_CRT_Branch axis
      (map (\<lambda>(weight,child).
        (weight,comma_semantic_future_crt_phase_bind_aux (prefix+weight)
          child receiver)) rows)"

lemma comma_semantic_future_crt_phase_bind_aux_shape:
  "comma_weighted_crt_shape lower
      (comma_semantic_future_crt_phase_bind_aux prefix tree receiver) =
    (comma_weighted_crt_shape lower tree \<and>
      (\<forall>control. comma_weighted_crt_shape 0 (receiver control)))"
proof (induction tree arbitrary: lower prefix)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case
    by (simp add: comma_weighted_crt_shift_shape
        comma_semantic_future_crt_map_control_shape)
next
  case (Comma_Weighted_CRT_Branch axis rows)
  then show ?case
    by (auto simp: list_all_iff prod_set_defs)
qed

lemma comma_semantic_future_crt_phase_bind_aux_eval:
  assumes shape: "comma_weighted_crt_shape 0 tree"
    and receivers:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_eval tree phase = Some (control,height)"
    and target:
      "comma_weighted_crt_eval (receiver control) (phase+prefix+height) =
        Some (child,child_weight)"
  shows "comma_weighted_crt_eval
      (comma_semantic_future_crt_phase_bind_aux prefix tree receiver) phase =
    Some ((control,child),height+child_weight)"
  using shape receivers source target
proof (induction tree arbitrary: prefix phase control height)
  case (Comma_Weighted_CRT_Leaf selected)
  then show ?case
    by (simp add: comma_semantic_future_crt_map_control_eval
        comma_weighted_crt_shift_exact)
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
    using Comma_Weighted_CRT_Branch.prems(1) by simp_all
  have index: "phase mod comma_crt_axis_radix axis<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain edge_weight child_tree where selected:
      "rows!(phase mod comma_crt_axis_radix axis)=(edge_weight,child_tree)"
    by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
  have member: "(edge_weight,child_tree)\<in>set rows"
    using nth_mem[OF index] selected by simp
  have tree_shape:
      "comma_weighted_crt_shape (Suc axis) child_tree"
    using Comma_Weighted_CRT_Branch.prems(1) member
    by (auto simp: list_all_iff)
  have tree_shape_zero: "comma_weighted_crt_shape 0 child_tree"
    by (rule comma_semantic_future_weighted_crt_shape_mono[OF tree_shape])
      simp
  have selected_eval:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch axis rows) phase =
        map_option (\<lambda>(value,elapsed). (value,edge_weight+elapsed))
          (comma_weighted_crt_eval child_tree phase)"
    using comma_weighted_crt_eval_branch[OF axis extent, of phase] selected
    by simp
  obtain child_height where child_eval_original:
      "comma_weighted_crt_eval child_tree phase =
        Some (control,child_height)"
    and height_decomposition: "height=edge_weight+child_height"
    using Comma_Weighted_CRT_Branch.prems(3) selected_eval
    by (cases "comma_weighted_crt_eval child_tree phase")
      (auto split: prod.splits)
  have child_eval:
      "comma_weighted_crt_eval child_tree phase =
        Some (control,height-edge_weight)"
    using child_eval_original height_decomposition by simp
  have weight_eq: "height=edge_weight+(height-edge_weight)"
    using height_decomposition by simp
  have child_target:
      "comma_weighted_crt_eval (receiver control)
        (phase+(prefix+edge_weight)+(height-edge_weight)) =
          Some (child,child_weight)"
    using Comma_Weighted_CRT_Branch.prems(4) weight_eq
    by (simp add: algebra_simps)
  have receiver_shape:
      "\<And>value. comma_weighted_crt_shape 0 (receiver value)"
    using Comma_Weighted_CRT_Branch.prems(2) by blast
  have bound_child:
      "comma_weighted_crt_eval
        (comma_semantic_future_crt_phase_bind_aux (prefix+edge_weight)
          child_tree receiver) phase =
        Some ((control,child),height-edge_weight+child_weight)"
    using Comma_Weighted_CRT_Branch.IH
      [OF member child_member tree_shape_zero,
        of "prefix+edge_weight" phase control "height-edge_weight"]
      receiver_shape child_eval child_target
    by blast
  show ?case
    using axis extent selected bound_child weight_eq
    by (simp add: comma_weighted_crt_eval_branch)
qed

definition comma_semantic_future_crt_phase_bind ::
    "nat \<times> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      ('a \<Rightarrow> 'b comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<times> ('a \<times> 'b) comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_phase_bind action receiver =
    (fst action,comma_semantic_future_crt_phase_bind_aux (fst action)
      (snd action) receiver)"

lemma comma_semantic_future_crt_phase_bind_apply:
  assumes shape: "comma_weighted_crt_shape 0 (snd action)"
    and receivers:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    and target:
      "comma_weighted_crt_eval (receiver control) (phase+height) =
        Some (child,child_weight)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action receiver) phase =
    Some ((control,child),height+child_weight)"
proof -
  obtain offset where action: "action=(offset,snd action)"
    by (cases action) auto
  obtain elapsed where evaluated:
      "comma_weighted_crt_eval (snd action) phase=Some (control,elapsed)"
    and height: "offset+elapsed=height"
    using source by (auto simp: comma_weighted_crt_apply_def
      split: option.splits prod.splits)
  have target_shifted:
      "comma_weighted_crt_eval (receiver control) (phase+offset+elapsed) =
        Some (child,child_weight)"
    using target height by (simp add: algebra_simps)
  have evaluated_bind:
      "comma_weighted_crt_eval
        (comma_semantic_future_crt_phase_bind_aux offset (snd action) receiver)
        phase = Some ((control,child),elapsed+child_weight)"
    by (rule comma_semantic_future_crt_phase_bind_aux_eval
      [OF shape receivers evaluated target_shifted])
  show ?thesis
    using evaluated_bind height action
    by (simp add: comma_semantic_future_crt_phase_bind_def
        comma_weighted_crt_apply_def)
qed

lemma comma_semantic_future_crt_phase_bind_apply_mod924:
  assumes shape: "comma_weighted_crt_shape 0 (snd action)"
    and receivers:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action phase=Some (control,height)"
    and target:
      "comma_weighted_crt_eval (receiver control)
        ((phase+height) mod 924) = Some (child,child_weight)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action receiver) phase =
    Some ((control,child),height+child_weight)"
proof -
  have raw_target:
      "comma_weighted_crt_eval (receiver control) (phase+height) =
        Some (child,child_weight)"
  proof -
    have periodic:
      "comma_weighted_crt_eval (receiver control) (phase+height) =
        comma_weighted_crt_eval (receiver control)
          ((phase+height) mod 924)"
      by (rule comma_semantic_future_weighted_crt_eval_periodic_924)
    show ?thesis using periodic target by simp
  qed
  show ?thesis
    by (rule comma_semantic_future_crt_phase_bind_apply
      [OF shape receivers source raw_target])
qed

lemma comma_semantic_future_crt_phase_bind_apply_local_delta:
  assumes phase: "r<924"
    and shape: "comma_weighted_crt_shape 0 (snd action)"
    and receivers:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action ((r+d) mod 924) =
        Some (control,height)"
    and target:
      "comma_weighted_crt_eval (receiver control)
        ((r+d+height) mod 924) = Some (child,child_weight)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action receiver)
        ((r+d) mod 924) =
    Some ((control,child),height+child_weight)"
proof -
  have receiver_target:
      "comma_weighted_crt_eval (receiver control)
        (((r+d) mod 924+height) mod 924) =
          Some (child,child_weight)"
    using target by (simp add: mod_add_eq algebra_simps)
  show ?thesis
    by (rule comma_semantic_future_crt_phase_bind_apply_mod924
      [OF shape receivers source receiver_target])
qed

lemma comma_semantic_future_crt_phase_bind_apply_selected_delta:
  fixes action :: "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag)"
    and receiver :: "'a \<Rightarrow> 'b comma_semantic_weighted_crt_dag"
  assumes phase: "r<924"
    and shape: "comma_weighted_crt_shape 0 (snd action)"
    and receivers:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action r=Some ((control,d),height)"
    and target:
      "comma_weighted_crt_eval (receiver control)
        ((r+d+height) mod 924)=Some (child,child_weight)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action
        (\<lambda>(selected,delta).
          comma_weighted_crt_shift delta (receiver selected))) r =
    Some (((control,d),child),height+child_weight)"
proof -
  let ?skew_receiver = "\<lambda>(selected,delta).
    comma_weighted_crt_shift delta (receiver selected)"
  have receiver_shape:
      "\<And>selection. comma_weighted_crt_shape 0
        (?skew_receiver selection)"
    using receivers
    by (cases selection) (simp add: comma_weighted_crt_shift_shape)
  have target_plain:
      "comma_weighted_crt_eval (receiver control) (r+d+height) =
        Some (child,child_weight)"
  proof -
    have periodic:
        "comma_weighted_crt_eval (receiver control) (r+d+height) =
          comma_weighted_crt_eval (receiver control)
            ((r+d+height) mod 924)"
      by (rule comma_semantic_future_weighted_crt_eval_periodic_924)
    show ?thesis using periodic target by simp
  qed
  have shifted_target:
      "comma_weighted_crt_eval
        (comma_weighted_crt_shift d (receiver control)) (r+height) =
          Some (child,child_weight)"
    using comma_weighted_crt_shift_exact[OF receivers[of control],
        of d "r+height"] target_plain
    by (simp add: algebra_simps)
  show ?thesis
    by (rule comma_semantic_future_crt_phase_bind_apply
      [OF shape receiver_shape source shifted_target])
qed

ML \<open>
  val published = @{thms
    comma_semantic_future_action_terminal_position.simps
    comma_semantic_future_action_terminal.simps
    comma_semantic_future_control_of_terminal_position_def
    comma_semantic_future_action_key_def
    comma_semantic_future_action_stop_weight_def
    comma_semantic_future_action_completed_delta_def
    comma_semantic_future_action_provider_phase_def
    comma_semantic_future_action_successor_phase_def
    comma_semantic_future_action_control_admitted_def
    comma_semantic_future_action_children_shape.simps
    comma_semantic_future_action_of_weighted_stop_def
    comma_semantic_future_action_of_direct_control_def
    comma_semantic_future_action_of_graph_power_def
    comma_semantic_future_control_of_terminal_position_exact
    comma_semantic_future_action_of_weighted_stop_exact
    comma_semantic_future_action_of_direct_control_exact
    comma_semantic_future_action_of_weighted_stop_rejects_large_height
    comma_semantic_future_exact_summary_control_transport
    comma_semantic_future_exact_summary_orbit_transport
    comma_semantic_future_graph_power_weighted_stop
    comma_semantic_future_action_position_bound
    comma_semantic_future_action_terminal_weight_decode
    comma_semantic_future_action_phase_transport
    comma_semantic_future_action_phase_transport_guarded
    comma_semantic_future_action_key_ignores_occurrence_payload
    comma_semantic_future_action_key_eq_iff
    comma_semantic_future_weighted_crt_eval_periodic_924
    comma_semantic_future_crt_map_control_shape
    comma_semantic_future_crt_map_control_eval
    comma_semantic_future_crt_map_action_control_def
    comma_semantic_future_crt_map_action_control_exact
    comma_semantic_future_crt_key_apply_def
    comma_semantic_future_crt_key_apply_periodic_924
    comma_semantic_future_crt_key_apply_extensional_924
    comma_semantic_future_weighted_crt_shape_mono
    comma_semantic_future_crt_phase_bind_aux_shape
    comma_semantic_future_crt_phase_bind_aux_eval
    comma_semantic_future_crt_phase_bind_def
    comma_semantic_future_crt_phase_bind_apply
    comma_semantic_future_crt_phase_bind_apply_mod924
    comma_semantic_future_crt_phase_bind_apply_local_delta
    comma_semantic_future_crt_phase_bind_apply_selected_delta}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future weighted action and guarded phase transport laws" published
\<close>

end
