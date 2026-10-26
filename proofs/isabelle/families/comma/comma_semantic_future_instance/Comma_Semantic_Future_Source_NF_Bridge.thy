theory Comma_Semantic_Future_Source_NF_Bridge
  imports Comma_Semantic_Future_Prefix_Boundary
    Comma_Semantic_Future_Candidate_Provider_NF
begin

lemma comma_semantic_future_initial_round_output_from_close:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,terminal_position,event)"
  shows "comma_semantic_b1_round_output (snd (snd q))
      (comma_finite_initial q) =
    (case event of
       Comma_Round_Fork a d \<Rightarrow>
         if d=0 then Comma_Semantic_B1_Stop (a-2)
         else Comma_Semantic_B1_Invalid
     | Comma_Round_Landmine d \<Rightarrow>
         if d=0 then Comma_Semantic_B1_Stop 8
         else Comma_Semantic_B1_Invalid
     | Comma_Round_Cross (Comma_Entry f d x) \<Rightarrow>
         if f=1 \<and> d=1 \<and> x\<le>90
         then Comma_Semantic_B1_Live (comma_offset_orbit x)
         else Comma_Semantic_B1_Invalid
     | _ \<Rightarrow> Comma_Semantic_B1_Invalid)"
proof -
  have admitted: "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have round:
    "comma_decisive_endpoint_round (snd (snd q)) (comma_finite_initial q) =
      event"
    using comma_decisive_endpoint_round_refines_close[OF admitted] close by simp
  show ?thesis
    using round
    by (cases event)
      (auto simp: comma_semantic_b1_round_output_def
        comma_sector_base_project.simps comma_semantic_b1_of_word.simps
        comma_terminal_weight_encode_def split: comma_finite_position.splits)
qed

lemma comma_semantic_future_initial_round_fork_target_bounds:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,terminal,Comma_Round_Fork a d)"
  shows "2\<le>a \<and> a\<le>9"
proof -
  have source_admitted: "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have terminal_admitted: "comma_round_admitted terminal"
    by (rule comma_round_close_admitted(1)[OF close source_admitted])
  have terminal_step:
    "comma_finite_step (snd (snd q) mod 924) terminal = Comma_Fork a d"
    using comma_round_close_refines_trace[OF close] by simp
  show ?thesis
    using terminal_admitted terminal_step
    by (cases terminal)
      (auto simp: comma_round_admitted.simps comma_finite_step_def
        comma_weighted_step_def comma_weighted_step_with_headroom_def
        Let_def split: if_splits)
qed

lemma comma_semantic_future_initial_crossing_stop:
  fixes q :: comma_boundary_state and x d n terminal_position :: nat
  assumes valid: "comma_boundary_valid q"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 d x))"
  obtains J H where
    "comma_semantic_b1_weighted_action_power 5
      comma_semantic_graph_root_weighted_action
      ((snd (snd q)+d) mod 924) (comma_offset_orbit x) =
        Comma_Semantic_B1_Stop_At J H"
proof -
  have admitted: "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  obtain x' where x_bound: "x'\<le>90"
    and target_shape:
      "Comma_Entry 1 d x = Comma_Entry 1
        (Suc (comma_round_delta (comma_finite_initial q))) x'"
    using comma_round_close_crossing_phase[OF close admitted] by blast
  have initial_delta: "comma_round_delta (comma_finite_initial q)=0"
    by (cases q) (auto simp: comma_finite_initial_def)
  have d_eq: "d=1" using target_shape initial_delta by simp
  have x_eq: "x=x'" using target_shape by simp
  have offset: "x\<le>90" using x_bound x_eq by simp
  let ?phase = "(snd (snd q)+d) mod 924"
  let ?root = "comma_offset_orbit x"
  let ?state = "Comma_Decade ?phase x"
  have phase_bound: "?phase<924" by simp
  have root_bound: "?root<46" by (rule comma_offset_orbit_bound)
  have state_admitted: "comma_decade_admitted ?state"
    using phase_bound offset by simp
  obtain H terminal where height: "H\<le>26"
    and summary: "comma_decade_exact_summary ?state H terminal"
    using comma_semantic_decade_summary_total_exact[OF state_admitted] by blast
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound
      [OF comma_decade_exact_summary_terminal_admitted[OF summary]])
  let ?children =
    "case terminal of Comma_Terminal_Fork a \<Rightarrow> [0,0]
     | Comma_Terminal_Landmine \<Rightarrow> []"
  have children_shape:
    "comma_semantic_future_action_children_shape
      (comma_semantic_future_control_of_terminal_position
        (comma_terminal_weight_digit terminal)) ?children"
    using digit_bound
    by (cases terminal)
      (auto simp: comma_semantic_future_action_children_shape.simps
        comma_semantic_future_control_of_terminal_position_def
        comma_terminal_weight_digit.simps)
  obtain action where weighted:
      "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action ?phase ?root =
          Comma_Semantic_B1_Stop_At
            (comma_terminal_weight_digit terminal) H"
    by (rule comma_semantic_future_graph_power_weighted_stop
      [OF phase_bound offset summary height children_shape])
  show thesis using weighted by (rule that)
qed

lemma comma_semantic_future_initial_source_graph_eval_exact:
  fixes q :: comma_boundary_state and phase :: nat
  assumes valid: "comma_boundary_valid q"
    and phase: "phase<924"
  shows "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
      (comma_semantic_graph_initial_source_ids !
        comma_semantic_future_initial_source_index q) phase =
    Some (comma_semantic_b1_round_output phase (comma_finite_initial q))"
proof -
  have selected_lookup:
    "comma_semantic_b1_binding_cid_of comma_semantic_graph_bindings
        (comma_finite_initial q) =
      Some (comma_semantic_graph_initial_source_ids !
        comma_semantic_future_initial_source_index q)"
    by (rule comma_semantic_future_initial_source_cid_exact(2)[OF valid])
  obtain binding where member: "binding\<in>set comma_semantic_graph_bindings"
    and source: "comma_semantic_b1_binding_source binding=comma_finite_initial q"
    and cid:
      "comma_semantic_b1_binding_cid binding =
        comma_semantic_graph_initial_source_ids !
          comma_semantic_future_initial_source_index q"
    using comma_semantic_b1_binding_cid_of_sound[OF selected_lookup] by blast
  have all_bindings:
    "\<forall>cid. comma_semantic_b1_graph_correct_at
      comma_semantic_graph_bindings comma_semantic_graph_nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint
      [OF comma_semantic_graph_valid_checked])
  have evaluation:
    "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_b1_binding_cid binding) phase =
      Some (comma_semantic_b1_round_output phase
        (comma_semantic_b1_binding_source binding))"
    using all_bindings member
    by (simp add: comma_semantic_b1_graph_correct_at_def)
  show ?thesis using evaluation source cid by simp
qed

lemma comma_semantic_future_initial_source_action_eval_exact:
  fixes q :: comma_boundary_state and phase :: nat
  assumes valid: "comma_boundary_valid q"
    and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_graph_initial_source_actions !
        comma_semantic_future_initial_source_index q) phase =
    (case comma_semantic_b1_round_output phase (comma_finite_initial q) of
       Comma_Semantic_B1_Live root \<Rightarrow>
         Comma_Semantic_B1_Continue root
     | Comma_Semantic_B1_Stop J \<Rightarrow>
         Comma_Semantic_B1_Stop_At J 0
     | Comma_Semantic_B1_Invalid \<Rightarrow>
         Comma_Semantic_B1_Weighted_Invalid)"
proof -
  have index_facts:
    "comma_semantic_future_initial_source_index q<16"
    "comma_semantic_future_initial_sources !
      comma_semantic_future_initial_source_index q = comma_finite_initial q"
    by (rule comma_semantic_future_initial_source_index_exact[OF valid])+
  have apply_exact:
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_source_actions !
        comma_semantic_future_initial_source_index q) phase =
      map_option comma_semantic_b1_crt_graph_result
        (comma_semantic_b1_graph_eval comma_semantic_graph_nodes
          (comma_semantic_graph_initial_source_ids !
            comma_semantic_future_initial_source_index q) phase)"
    by (rule comma_semantic_graph_initial_source_actions_refine
      [OF index_facts(1)])
  have graph_eval:
    "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
      (comma_semantic_graph_initial_source_ids !
        comma_semantic_future_initial_source_index q) phase =
      Some (comma_semantic_b1_round_output phase (comma_finite_initial q))"
    by (rule comma_semantic_future_initial_source_graph_eval_exact[OF valid phase])
  show ?thesis
    using apply_exact graph_eval
    by (cases "comma_semantic_b1_round_output phase (comma_finite_initial q)")
      (simp_all add: comma_semantic_b1_crt_action_eval_def
        comma_semantic_b1_crt_decode.simps
        comma_semantic_b1_crt_graph_result.simps)
qed

lemma comma_semantic_future_initial_nf_action_eval_exact:
  fixes slot phase :: nat
  assumes slot: "slot<16" and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_graph_initial_nf_actions!slot) phase =
    comma_semantic_b1_weighted_word_then 1
      (\<lambda>p i. comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_source_actions!i) p)
      (\<lambda>p i. comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_b32_weighted_actions!i) p)
      phase slot"
proof -
  have source_length:
    "length comma_semantic_graph_initial_source_actions=16"
    by (rule comma_semantic_graph_initial_source_actions_length)
  have b32_length:
    "length comma_semantic_graph_b32_weighted_actions=46"
    by (rule comma_semantic_graph_b32_weighted_actions_length)
  have source_slot_bound:
    "slot<length comma_semantic_graph_initial_source_actions"
    using slot source_length by simp
  have source_member:
    "comma_semantic_graph_initial_source_actions!slot \<in>
      set comma_semantic_graph_initial_source_actions"
    by (rule nth_mem[OF source_slot_bound])
  have source_wf:
    "comma_weighted_crt_wellformed
      (snd (comma_semantic_graph_initial_source_actions!slot))"
    using comma_semantic_graph_initial_source_actions_wellformed source_member
    by (simp add: list_all_iff)
  have source_zero:
    "comma_semantic_b1_crt_action_nonterminal_zero
      (comma_semantic_graph_initial_source_actions!slot)"
    using comma_semantic_graph_initial_source_actions_nonterminal_zero
      source_member by (simp add: list_all_iff)
  have b32_wf:
    "\<And>root. root<46 \<Longrightarrow>
      comma_weighted_crt_wellformed
        (snd (comma_semantic_graph_b32_weighted_actions!root))"
  proof -
    fix root assume root: "root<46"
    have root_bound:
      "root<length comma_semantic_graph_b32_weighted_actions"
      using root b32_length by simp
    have member:
      "comma_semantic_graph_b32_weighted_actions!root \<in>
        set comma_semantic_graph_b32_weighted_actions"
      by (rule nth_mem[OF root_bound])
    show "comma_weighted_crt_wellformed
        (snd (comma_semantic_graph_b32_weighted_actions!root))"
      using comma_semantic_graph_b32_weighted_actions_wellformed member
      by (simp add: list_all_iff)
  qed
  have b32_zero:
    "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero
        (comma_semantic_graph_b32_weighted_actions!root)"
  proof -
    fix root assume root: "root<46"
    have root_bound:
      "root<length comma_semantic_graph_b32_weighted_actions"
      using root b32_length by simp
    have member:
      "comma_semantic_graph_b32_weighted_actions!root \<in>
        set comma_semantic_graph_b32_weighted_actions"
      by (rule nth_mem[OF root_bound])
    show "comma_semantic_b1_crt_action_nonterminal_zero
        (comma_semantic_graph_b32_weighted_actions!root)"
      using comma_semantic_graph_b32_weighted_actions_nonterminal_zero member
      by (simp add: list_all_iff)
  qed
  have family_spec:
    "comma_semantic_future_initial_nf_action_at phase slot =
      comma_semantic_future_family_nf_spec_of_dags
        comma_semantic_graph_initial_source_actions
        comma_semantic_graph_b32_weighted_actions phase slot"
    by (rule comma_semantic_future_initial_nf_action_at_exact
      [OF phase slot source_length b32_length source_wf source_zero b32_wf b32_zero])
  have compiled_action:
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_nf_actions!slot) phase =
      comma_weighted_crt_apply
        (comma_semantic_b1_crt_compose 1
          (comma_semantic_graph_initial_source_actions!slot)
          comma_semantic_graph_b32_weighted_actions) phase"
    using comma_semantic_graph_initial_nf_actions_refine slot
    by (simp add: list_all_iff)
  have actual:
    "comma_semantic_b1_crt_action_eval
      (comma_semantic_graph_initial_nf_actions!slot) phase =
      comma_semantic_future_initial_nf_action_at phase slot"
    using compiled_action
    by (simp add: comma_semantic_b1_crt_action_eval_def
      comma_semantic_future_initial_nf_action_at_def
      comma_semantic_future_family_nf_action_at_def
      comma_semantic_future_family_nf_dags_def)
  show ?thesis
    using actual family_spec
    by (simp add: comma_semantic_future_family_nf_spec_of_dags_def)
qed

lemma comma_semantic_future_b32_action_eval_exact:
  fixes root phase :: nat
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_graph_b32_weighted_actions!root) phase =
    comma_semantic_b1_weighted_action_power 5
      comma_semantic_graph_root_weighted_action phase root"
  by (rule comma_semantic_graph_b32_weighted_actions_refine[OF root phase])

text \<open>
The published initial normal form is tied back to the same source's first
boundary event.  Its displacement remains occurrence data, and candidate
children are selected only after that displacement has rebased the clock.
\<close>

theorem comma_semantic_future_initial_nf_action_boundary_exact:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains J delta control ordered_children where
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_nf_actions!
        (comma_semantic_future_initial_source_index q)) (snd (snd q)) =
      Some (Comma_Semantic_B1_CRT_Stop J delta)"
    "J<9" "delta\<le>27"
    "comma_semantic_boundary_control_step
      comma_semantic_decade_summary q = Some control"
    "control=comma_semantic_future_control_of_terminal_position J"
    "comma_semantic_boundary_children comma_semantic_decade_summary q control =
      (case control of
         Comma_Future_Fork a \<Rightarrow>
           [(Comma_N,a,(snd (snd q)+delta) mod 924),
            (Comma_Z,a,(snd (snd q)+delta) mod 924)]
       | Comma_Future_Landmine \<Rightarrow> [])"
    "comma_semantic_future_candidate_child_ids_at (Some control)
      ((snd (snd q)+delta) mod 924) = Some ordered_children"
    "ordered_children =
      (case control of
         Comma_Future_Fork a \<Rightarrow>
           [comma_semantic_future_candidate_class_ids!
              (924*(a-2)+((snd (snd q)+delta) mod 924)),
            comma_semantic_future_candidate_class_ids!
              (924*(8+(a-2))+((snd (snd q)+delta) mod 924))]
       | Comma_Future_Landmine \<Rightarrow> [])"
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action
        (comma_semantic_future_initial_source_index q)) (snd (snd q)) =
      Some (Some control,ordered_children)"
proof -
  let ?slot = "comma_semantic_future_initial_source_index q"
  let ?phase = "snd (snd q)"
  have slot_bound: "?slot<16"
    by (rule comma_semantic_future_initial_source_index_exact[OF valid])
  have phase_bound: "?phase<924"
    using valid by (cases q) (auto simp: comma_boundary_valid_def)
  have source_exact:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_source_actions!?slot) ?phase =
      (case comma_semantic_b1_round_output ?phase (comma_finite_initial q) of
         Comma_Semantic_B1_Live root \<Rightarrow>
           Comma_Semantic_B1_Continue root
       | Comma_Semantic_B1_Stop J \<Rightarrow>
           Comma_Semantic_B1_Stop_At J 0
       | Comma_Semantic_B1_Invalid \<Rightarrow>
           Comma_Semantic_B1_Weighted_Invalid)"
    by (rule comma_semantic_future_initial_source_action_eval_exact
      [OF valid phase_bound])
  obtain actual_J actual_delta actual_children where actual_apply:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!?slot) ?phase =
          Some (Comma_Semantic_B1_CRT_Stop actual_J actual_delta)"
    and actual_j_bound: "actual_J<9"
    and actual_delta_bound: "actual_delta\<le>27"
    and actual_receiver:
      "comma_semantic_future_candidate_child_ids_at
        (Some (comma_semantic_future_control_of_terminal_position actual_J))
        ((?phase+actual_delta) mod 924) = Some actual_children"
    and actual_key:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action ?slot) ?phase =
          Some (Some (comma_semantic_future_control_of_terminal_position actual_J),
            actual_children)"
    by (rule comma_semantic_future_initial_nf_source_key_action_result
      [OF slot_bound phase_bound])
  have actual_eval:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!?slot) ?phase =
      Comma_Semantic_B1_Stop_At actual_J actual_delta"
    using actual_apply actual_j_bound
    by (simp add: comma_semantic_b1_crt_action_eval_def
        comma_semantic_b1_crt_decode.simps)
  have crossing_stop:
      "\<And>n final d x.
        comma_round_close ?phase (comma_finite_initial q) =
          (n,final,Comma_Round_Cross (Comma_Entry 1 d x)) \<Longrightarrow>
        \<exists>J H. comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action
          ((?phase+d) mod 924) (comma_offset_orbit x) =
            Comma_Semantic_B1_Stop_At J H"
    using comma_semantic_future_initial_crossing_stop[OF valid] by blast
  obtain calls steps final event where close:
      "comma_round_close ?phase (comma_finite_initial q) =
        (steps,final,event)"
    and boundary:
      "(\<exists>a d. event=Comma_Round_Fork a d \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (Comma_Future_Fork a) \<and>
          comma_semantic_boundary_children comma_semantic_decade_summary q
            (Comma_Future_Fork a) =
              [(Comma_N,a,(?phase+d) mod 924),
               (Comma_Z,a,(?phase+d) mod 924)]) \<or>
       (\<exists>d. event=Comma_Round_Landmine d \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some Comma_Future_Landmine \<and>
          comma_semantic_boundary_children comma_semantic_decade_summary q
            Comma_Future_Landmine = []) \<or>
       (\<exists>x J H terminal. x\<le>90 \<and>
          event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
          comma_semantic_b1_weighted_action_power 5
            comma_semantic_graph_root_weighted_action
            ((?phase+1) mod 924) (comma_offset_orbit x) =
              Comma_Semantic_B1_Stop_At J H \<and>
          J=comma_terminal_weight_digit terminal \<and> H\<le>26 \<and>
          comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x)
            H terminal \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (comma_semantic_boundary_control_of
              (comma_summary_outcome (H+1) terminal)) \<and>
          comma_semantic_boundary_children comma_semantic_decade_summary q
            (comma_semantic_boundary_control_of
              (comma_summary_outcome (H+1) terminal)) =
            (case terminal of
               Comma_Terminal_Fork a \<Rightarrow>
                 [(Comma_N,a,(?phase+1+H) mod 924),
                  (Comma_Z,a,(?phase+1+H) mod 924)]
             | Comma_Terminal_Landmine \<Rightarrow> []))"
    using comma_semantic_future_initial_prefix_boundary_result
      [OF valid crossing_stop]
    by blast
  have nf_eval:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!?slot) ?phase =
      comma_semantic_b1_weighted_word_then 1
        (\<lambda>p i. comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_initial_source_actions!i) p)
        (\<lambda>p i. comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_b32_weighted_actions!i) p)
        ?phase ?slot"
    by (rule comma_semantic_future_initial_nf_action_eval_exact
      [OF slot_bound phase_bound])
  have event_relation:
    "(\<exists>a. actual_J=a-2 \<and> actual_delta=0 \<and>
        2\<le>a \<and> a\<le>9 \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (Comma_Future_Fork a)) \<or>
     (actual_J=8 \<and> actual_delta=0 \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some Comma_Future_Landmine) \<or>
     (\<exists>x H terminal. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        actual_J=comma_terminal_weight_digit terminal \<and>
        actual_delta=1+H \<and> H\<le>26 \<and>
        (case terminal of Comma_Terminal_Fork a \<Rightarrow>
           2\<le>a \<and> a\<le>9
         | Comma_Terminal_Landmine \<Rightarrow> True) \<and>
        comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x)
          H terminal \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)))"
  proof -
    have fork_event_bounds:
      "\<And>a d. event=Comma_Round_Fork a d \<Longrightarrow> 2\<le>a \<and> a\<le>9"
    proof -
      fix a d
      assume event_eq: "event=Comma_Round_Fork a d"
      have fork_close:
        "comma_round_close ?phase (comma_finite_initial q) =
          (steps,final,Comma_Round_Fork a d)"
        using close event_eq by simp
      show "2\<le>a \<and> a\<le>9"
        by (rule comma_semantic_future_initial_round_fork_target_bounds
          [OF valid fork_close])
    qed
    have terminal_event_bounds:
      "\<And>s h terminal. comma_decade_exact_summary s h terminal \<Longrightarrow>
        (case terminal of Comma_Terminal_Fork a \<Rightarrow>
           2\<le>a \<and> a\<le>9
         | Comma_Terminal_Landmine \<Rightarrow> True)"
    proof -
      fix s h terminal
      assume exact: "comma_decade_exact_summary s h terminal"
      have admitted: "comma_terminal_weight_admitted terminal"
        by (rule comma_decade_exact_summary_terminal_admitted[OF exact])
      show "(case terminal of Comma_Terminal_Fork a \<Rightarrow>
               2\<le>a \<and> a\<le>9
             | Comma_Terminal_Landmine \<Rightarrow> True)"
        using admitted
        by (cases terminal)
          (auto simp: comma_terminal_weight_admitted_def)
    qed
    have direct_cases:
      "(\<exists>a d. event=Comma_Round_Fork a d \<and>
          2\<le>a \<and> a\<le>9 \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (Comma_Future_Fork a)) \<or>
       (\<exists>d. event=Comma_Round_Landmine d \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some Comma_Future_Landmine) \<or>
       (\<exists>x J H terminal. x\<le>90 \<and>
          event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
          comma_semantic_b1_weighted_action_power 5
            comma_semantic_graph_root_weighted_action
            ((?phase+1) mod 924) (comma_offset_orbit x) =
              Comma_Semantic_B1_Stop_At J H \<and>
          J=comma_terminal_weight_digit terminal \<and> H\<le>26 \<and>
          (case terminal of Comma_Terminal_Fork a \<Rightarrow>
             2\<le>a \<and> a\<le>9
           | Comma_Terminal_Landmine \<Rightarrow> True) \<and>
          comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x)
            H terminal \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (comma_semantic_boundary_control_of
              (comma_summary_outcome (H+1) terminal)))"
      using boundary fork_event_bounds terminal_event_bounds by blast
    then show ?thesis
    proof (elim disjE)
      assume "(\<exists>a d. event=Comma_Round_Fork a d \<and>
          2\<le>a \<and> a\<le>9 \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (Comma_Future_Fork a))"
      then obtain a d where fork:
          "event=Comma_Round_Fork a d"
        and a_lower: "2\<le>a"
        and a_upper: "a\<le>9"
        and control:
          "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (Comma_Future_Fork a)"
        by blast
      have round:
        "comma_semantic_b1_round_output ?phase (comma_finite_initial q) =
          (if d=0 then Comma_Semantic_B1_Stop (a-2)
           else Comma_Semantic_B1_Invalid)"
        using comma_semantic_future_initial_round_output_from_close
          [OF valid] close fork by simp
      have fork_bounds: "2\<le>a \<and> a\<le>9"
        using comma_semantic_future_initial_round_fork_target_bounds
          [OF valid close] by blast
      have src:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_initial_source_actions!?slot) ?phase =
          (if d=0 then Comma_Semantic_B1_Stop_At (a-2) 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using source_exact round by simp
      have composed:
        "comma_semantic_b1_weighted_word_then 1
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_initial_source_actions!i) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_b32_weighted_actions!i) p)
          ?phase ?slot =
          (if d=0 then Comma_Semantic_B1_Stop_At (a-2) 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using src by (cases "d=0") simp_all
      have eq:
        "Comma_Semantic_B1_Stop_At actual_J actual_delta =
          (if d=0 then Comma_Semantic_B1_Stop_At (a-2) 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using actual_eval nf_eval composed by simp
      have d_zero: "d=0" using eq by (cases "d=0") simp_all
      have j_eq: "actual_J=a-2" and delta_eq: "actual_delta=0"
        using eq d_zero by simp_all
      show ?thesis using control j_eq delta_eq fork_bounds by blast
    next
      assume landmine:
        "\<exists>d. event=Comma_Round_Landmine d \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some Comma_Future_Landmine"
      then obtain d where event_eq: "event=Comma_Round_Landmine d"
        and control:
          "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some Comma_Future_Landmine"
        by blast
      have round:
        "comma_semantic_b1_round_output ?phase (comma_finite_initial q) =
          (if d=0 then Comma_Semantic_B1_Stop 8
           else Comma_Semantic_B1_Invalid)"
        using comma_semantic_future_initial_round_output_from_close
          [OF valid] close event_eq by simp
      have src:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_initial_source_actions!?slot) ?phase =
          (if d=0 then Comma_Semantic_B1_Stop_At 8 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using source_exact round by simp
      have composed:
        "comma_semantic_b1_weighted_word_then 1
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_initial_source_actions!i) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_b32_weighted_actions!i) p)
          ?phase ?slot =
          (if d=0 then Comma_Semantic_B1_Stop_At 8 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using src by (cases "d=0") simp_all
      have eq:
        "Comma_Semantic_B1_Stop_At actual_J actual_delta =
          (if d=0 then Comma_Semantic_B1_Stop_At 8 0
           else Comma_Semantic_B1_Weighted_Invalid)"
        using actual_eval nf_eval composed by simp
      have d_zero: "d=0" using eq by (cases "d=0") simp_all
      have j_eq: "actual_J=8" and delta_eq: "actual_delta=0"
        using eq d_zero by simp_all
      show ?thesis using control j_eq delta_eq by blast
    next
      assume cross:
        "\<exists>x J H terminal. x\<le>90 \<and>
          event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
          comma_semantic_b1_weighted_action_power 5
            comma_semantic_graph_root_weighted_action
            ((?phase+1) mod 924) (comma_offset_orbit x) =
              Comma_Semantic_B1_Stop_At J H \<and>
          J=comma_terminal_weight_digit terminal \<and> H\<le>26 \<and>
          comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x)
            H terminal \<and>
          comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (comma_semantic_boundary_control_of
              (comma_summary_outcome (H+1) terminal))"
      then obtain x J H terminal where x_bound: "x\<le>90"
        and event_eq:
          "event=Comma_Round_Cross (Comma_Entry 1 1 x)"
        and stop:
          "comma_semantic_b1_weighted_action_power 5
            comma_semantic_graph_root_weighted_action
            ((?phase+1) mod 924) (comma_offset_orbit x) =
              Comma_Semantic_B1_Stop_At J H"
        and j_terminal: "J=comma_terminal_weight_digit terminal"
        and height: "H\<le>26"
        and terminal_bounds:
          "(case terminal of Comma_Terminal_Fork a \<Rightarrow>
              2\<le>a \<and> a\<le>9
            | Comma_Terminal_Landmine \<Rightarrow> True)"
        and exact:
          "comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x)
            H terminal"
        and control:
          "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
            Some (comma_semantic_boundary_control_of
              (comma_summary_outcome (H+1) terminal))"
        by blast
      have round:
        "comma_semantic_b1_round_output ?phase (comma_finite_initial q) =
          Comma_Semantic_B1_Live (comma_offset_orbit x)"
        using comma_semantic_future_initial_round_output_from_close
          [OF valid] close event_eq x_bound by simp
      have src:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_initial_source_actions!?slot) ?phase =
          Comma_Semantic_B1_Continue (comma_offset_orbit x)"
        using source_exact round by simp
      have root_bound: "comma_offset_orbit x<46"
        by (rule comma_offset_orbit_bound)
      have b32:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_b32_weighted_actions!comma_offset_orbit x)
          ((?phase+1) mod 924) = Comma_Semantic_B1_Stop_At J H"
        using comma_semantic_future_b32_action_eval_exact[OF root_bound] stop
        by simp
      have composed:
        "comma_semantic_b1_weighted_word_then 1
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_initial_source_actions!i) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_b32_weighted_actions!i) p)
          ?phase ?slot = Comma_Semantic_B1_Stop_At J (1+H)"
        using src b32
        by (simp add: comma_semantic_b1_weighted_word_then.simps)
      have eq: "actual_J=J" "actual_delta=1+H"
        using actual_eval nf_eval composed by auto
      show ?thesis using control j_terminal height exact terminal_bounds eq by blast
    qed
  qed
  then obtain control where control_eq:
      "control=comma_semantic_future_control_of_terminal_position actual_J"
    and control_step:
      "comma_semantic_boundary_control_step
        comma_semantic_decade_summary q = Some control"
    and semantic_children:
      "(case control of
          Comma_Future_Fork a \<Rightarrow>
            comma_semantic_boundary_children comma_semantic_decade_summary q control =
              [(Comma_N,a,(?phase+actual_delta) mod 924),
               (Comma_Z,a,(?phase+actual_delta) mod 924)]
        | Comma_Future_Landmine \<Rightarrow>
            comma_semantic_boundary_children comma_semantic_decade_summary q control = [])"
    by (elim disjE)
      (auto simp: comma_semantic_future_control_of_terminal_position_def
        comma_semantic_boundary_children_def comma_summary_outcome.simps
        comma_terminal_weight_digit.simps algebra_simps
        split: comma_decade_terminal.splits)
  have boundary_children:
    "comma_semantic_boundary_children comma_semantic_decade_summary q control =
      (case control of
         Comma_Future_Fork a \<Rightarrow>
           [(Comma_N,a,(?phase+actual_delta) mod 924),
            (Comma_Z,a,(?phase+actual_delta) mod 924)]
       | Comma_Future_Landmine \<Rightarrow> [])"
    using semantic_children control_eq by simp
  have receiver:
    "comma_semantic_future_candidate_child_ids_at (Some control)
      ((?phase+actual_delta) mod 924) = Some actual_children"
    using actual_receiver control_eq by simp
  have key:
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action ?slot) ?phase =
        Some (Some control,actual_children)"
    using actual_key control_eq by simp
  have receiver_shape:
    "actual_children =
      (case control of
         Comma_Future_Fork a \<Rightarrow>
           [comma_semantic_future_candidate_class_ids!
              (924*(a-2)+((?phase+actual_delta) mod 924)),
            comma_semantic_future_candidate_class_ids!
              (924*(8+(a-2))+((?phase+actual_delta) mod 924))]
       | Comma_Future_Landmine \<Rightarrow> [])"
    using receiver control_eq actual_j_bound
    by (cases control)
      (auto simp: comma_semantic_future_candidate_child_ids_fork_exact
        comma_semantic_future_candidate_child_ids_landmine)
  show thesis
    by (rule that[OF actual_apply actual_j_bound actual_delta_bound control_step
        control_eq boundary_children receiver receiver_shape key])
qed

ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_future_initial_prefix_boundary_result
      comma_semantic_future_initial_round_fork_target_bounds
      comma_semantic_future_initial_nf_action_boundary_exact})
  then ()
  else error "Comma_Semantic_Future_Source_NF_Bridge oracle audit failed"
\<close>

end
