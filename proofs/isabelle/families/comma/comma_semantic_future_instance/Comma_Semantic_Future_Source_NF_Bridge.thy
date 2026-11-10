theory Comma_Semantic_Future_Source_NF_Bridge
  imports Comma_Semantic_Future_Source_Action
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
      comma_semantic_future_rank_round_action
        ((snd (snd q)+d) mod 924) (comma_offset_orbit x) =
      Comma_Semantic_B1_Stop_At J H"
proof -
  let ?phase = "(snd (snd q)+d) mod 924"
  let ?root = "comma_offset_orbit x"
  have phase_bound: "?phase<924" by simp
  have root_bound: "?root<46" by (rule comma_offset_orbit_bound)
  have image24:
      "\<And>p cid terminal. p<924 \<Longrightarrow> cid<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (p,cid)=Some terminal
        \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
    by (rule comma_semantic_phase_continue24_image_checked)
  obtain H terminal where height: "H\<le>26"
    and summary:
      "comma_decade_exact_summary
        (Comma_Decade ?phase
          (comma_offset_representatives!?root)) H terminal"
    and weighted_power:
      "comma_semantic_b1_weighted_action_power 5
        comma_semantic_future_rank_round_action ?phase ?root =
          Comma_Semantic_B1_Stop_At
            (comma_terminal_weight_digit terminal) H"
    by (rule comma_semantic_future_rank_b32_source_free_exact
      [OF image24 phase_bound root_bound])
  show thesis by (rule that[OF weighted_power])
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

lemma comma_semantic_future_initial_round_output_cases:
  fixes q :: comma_boundary_state and phase :: nat
  assumes valid: "comma_boundary_valid q"
  obtains J where
      "comma_semantic_b1_round_output phase (comma_finite_initial q) =
        Comma_Semantic_B1_Stop J" "J<9"
    | root where
      "comma_semantic_b1_round_output phase (comma_finite_initial q) =
        Comma_Semantic_B1_Live root" "root<46"
proof -
  let ?source = "comma_finite_initial q"
  have source_admitted: "comma_round_admitted ?source"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have source_delta: "comma_round_delta ?source=0"
    using valid by (cases q) (simp add: comma_finite_initial_def comma_boundary_valid_def)
  obtain steps terminal event where close:
      "comma_round_close phase ?source=(steps,terminal,event)"
    by (cases "comma_round_close phase ?source") auto
  have terminal_admitted: "comma_round_admitted terminal"
    by (rule comma_round_close_admitted(1)[OF close source_admitted])
  have event_not_invalid: "event\<noteq>Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close source_admitted])
  have terminal_delta: "comma_round_delta terminal=0"
    using comma_round_close_delta[OF close source_admitted] source_delta by simp
  have trace:
      "case event of
         Comma_Round_Fork a d \<Rightarrow>
           comma_finite_step (phase mod 924) terminal=Comma_Fork a d
       | Comma_Round_Landmine d \<Rightarrow>
           comma_finite_step (phase mod 924) terminal=Comma_Landmine d
       | Comma_Round_Cross target \<Rightarrow>
           comma_finite_step (phase mod 924) terminal=Comma_Next target \<and>
             comma_round_crossing terminal target
       | Comma_Round_Invalid \<Rightarrow>
           comma_finite_step (phase mod 924) terminal=Comma_Invalid"
    using comma_round_close_refines_trace[OF close] by simp
  have output_exact:
      "comma_semantic_b1_round_output phase ?source =
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
    by (rule comma_semantic_future_initial_round_output_from_close[OF valid close])
  show thesis
  proof (cases event)
    case (Comma_Round_Fork a d)
    have finite_fork:
      "comma_finite_step (phase mod 924) terminal=Comma_Fork a d"
      using trace Comma_Round_Fork by simp
    have digit_bounds: "2\<le>a" "a\<le>9"
      using comma_finite_fork_digit_bounds[OF finite_fork] by auto
    have delta_zero: "d=0"
      using finite_fork terminal_delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    have output:
      "comma_semantic_b1_round_output phase ?source=
        Comma_Semantic_B1_Stop (a-2)"
      using output_exact Comma_Round_Fork delta_zero by simp
    have bound: "a-2<9" using digit_bounds by arith
    show thesis by (rule that(1)[OF output bound])
  next
    case (Comma_Round_Landmine d)
    have finite_landmine:
      "comma_finite_step (phase mod 924) terminal=Comma_Landmine d"
      using trace Comma_Round_Landmine by simp
    have delta_zero: "d=0"
      using finite_landmine terminal_delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    have output:
      "comma_semantic_b1_round_output phase ?source=
        Comma_Semantic_B1_Stop 8"
      using output_exact Comma_Round_Landmine delta_zero by simp
    have bound: "8<9" by simp
    show thesis by (rule that(1)[OF output bound])
  next
    case (Comma_Round_Cross target)
    obtain d h x where terminal_shape:
        "terminal=Comma_Near 9 d h"
      and target_shape: "target=Comma_Entry 1 (Suc d) x"
      and offset_bound: "x\<le>90"
      using comma_round_close_crossing_shape[OF close] by blast
    have delta_zero: "d=0"
      using terminal_delta terminal_shape by simp
    have output:
      "comma_semantic_b1_round_output phase ?source=
        Comma_Semantic_B1_Live (comma_offset_orbit x)"
      using output_exact Comma_Round_Cross target_shape offset_bound delta_zero
      by simp
    have root_bound: "comma_offset_orbit x<46"
      by (rule comma_offset_orbit_bound)
    show thesis by (rule that(2)[OF output root_bound])
  next
    case Comma_Round_Invalid
    show thesis using event_not_invalid Comma_Round_Invalid by simp
  qed
qed

lemma comma_semantic_future_b32_action_eval_exact:
  fixes root phase :: nat
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_future_rank_b32_weighted_actions!root) phase =
    comma_semantic_b1_weighted_action_power 5
      comma_semantic_future_rank_round_action phase root"
  by (rule comma_semantic_future_rank_b32_action_eval_exact[OF root phase])

lemma comma_semantic_future_action_eval_stop_apply:
  assumes eval:
    "comma_semantic_b1_crt_action_eval action phase=
      Comma_Semantic_B1_Stop_At J H"
  shows "comma_weighted_crt_apply action phase=
    Some (Comma_Semantic_B1_CRT_Stop J,H)"
  using eval
  by (cases "comma_weighted_crt_apply action phase")
    (auto simp: comma_semantic_b1_crt_action_eval_def
      comma_semantic_b1_crt_decode.simps split: prod.splits
        comma_semantic_b1_crt_control.splits)

lemma comma_semantic_future_initial_nf_slot_stopped:
  fixes slot phase :: nat
  assumes slot: "slot<16" and phase: "phase<924"
  obtains J H where
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_nf_actions!slot) phase =
      Some (Comma_Semantic_B1_CRT_Stop J,H)"
    "J<9" "H\<le>27"
proof -
  let ?kind = "if slot<8 then Comma_N else Comma_Z"
  let ?digit = "if slot<8 then slot+2 else slot-6"
  let ?source_state = "(?kind,?digit,0)"
  have source_valid: "comma_boundary_valid ?source_state"
    using slot by (auto simp: comma_boundary_valid_def; arith)
  have source_index:
      "comma_semantic_future_initial_source_index ?source_state=slot"
    using slot by (auto simp: comma_semantic_future_initial_source_index_def;
      arith)
  have source_position:
      "comma_semantic_future_initial_sources!slot=
        comma_finite_initial ?source_state"
  proof -
    have exact:
      "comma_semantic_future_initial_sources!
        comma_semantic_future_initial_source_index ?source_state=
        comma_finite_initial ?source_state"
      by (rule comma_semantic_future_initial_source_index_exact(2)[OF source_valid])
    show ?thesis using exact source_index by simp
  qed
  have classified:
      "(\<exists>J<9. comma_semantic_b1_round_output phase
          (comma_finite_initial ?source_state)=Comma_Semantic_B1_Stop J) \<or>
       (\<exists>root<46. comma_semantic_b1_round_output phase
          (comma_finite_initial ?source_state)=Comma_Semantic_B1_Live root)"
    using comma_semantic_future_initial_round_output_cases[OF source_valid]
    by blast
  have source_exact:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_source_actions!slot) phase =
       (case comma_semantic_b1_round_output phase (comma_finite_initial ?source_state) of
          Comma_Semantic_B1_Live root \<Rightarrow> Comma_Semantic_B1_Continue root
        | Comma_Semantic_B1_Stop J \<Rightarrow> Comma_Semantic_B1_Stop_At J 0
        | Comma_Semantic_B1_Invalid \<Rightarrow> Comma_Semantic_B1_Weighted_Invalid)"
    using comma_semantic_future_initial_source_action_eval_exact
      [OF source_valid phase] source_index source_position by simp
  have nf_exact:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!slot) phase =
       comma_semantic_b1_weighted_word_then 1
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_graph_initial_source_actions!i) p)
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_future_rank_b32_weighted_actions!i) p)
         phase slot"
    using comma_semantic_future_initial_nf_action_eval_exact[OF slot phase]
    by (simp add: comma_semantic_future_initial_nf_dags_def)
  show thesis
  proof (cases "comma_semantic_b1_round_output phase
      (comma_finite_initial ?source_state)")
    case (Comma_Semantic_B1_Stop first_J)
    have first_stop_bound: "first_J<9"
      using classified Comma_Semantic_B1_Stop by blast
    have word_stop:
      "comma_semantic_b1_weighted_word_then 1
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_graph_initial_source_actions!i) p)
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_future_rank_b32_weighted_actions!i) p)
         phase slot = Comma_Semantic_B1_Stop_At first_J 0"
      using source_exact Comma_Semantic_B1_Stop
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
    have action_eval:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!slot) phase =
        Comma_Semantic_B1_Stop_At first_J 0"
      using nf_exact word_stop by simp
    have applied:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!slot) phase =
        Some (Comma_Semantic_B1_CRT_Stop first_J,0)"
      by (rule comma_semantic_future_action_eval_stop_apply[OF action_eval])
    have height_bound: "0\<le>27" by simp
    show thesis
      by (rule that(1)[OF applied first_stop_bound height_bound])
  next
    case (Comma_Semantic_B1_Live root)
    have root_bound: "root<46"
      using classified Comma_Semantic_B1_Live by blast
    let ?next_phase = "(phase+1) mod 924"
    have next_phase_bound: "?next_phase<924" by simp
    obtain H terminal where height: "H\<le>26"
      and summary:
        "comma_decade_exact_summary
          (Comma_Decade ?next_phase (comma_offset_representatives!root)) H terminal"
      and power:
        "comma_semantic_b1_weighted_action_power 5
          comma_semantic_future_rank_round_action ?next_phase root =
          Comma_Semantic_B1_Stop_At
            (comma_terminal_weight_digit terminal) H"
      and rank_eval:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_future_rank_b32_weighted_actions!root) ?next_phase =
          Comma_Semantic_B1_Stop_At
            (comma_terminal_weight_digit terminal) H"
      by (rule comma_semantic_future_rank_b32_action_stop_exact
        [OF next_phase_bound root_bound])
    have terminal_admitted:
        "comma_terminal_weight_admitted terminal"
      by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
    have digit_bound:
        "comma_terminal_weight_digit terminal<9"
      by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
    have word_stop:
      "comma_semantic_b1_weighted_word_then 1
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_graph_initial_source_actions!i) p)
         (\<lambda>p i. comma_semantic_b1_crt_action_eval
           (comma_semantic_future_rank_b32_weighted_actions!i) p)
         phase slot = Comma_Semantic_B1_Stop_At
           (comma_terminal_weight_digit terminal) (1+H)"
      using source_exact Comma_Semantic_B1_Live rank_eval
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
    have action_eval:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!slot) phase =
        Comma_Semantic_B1_Stop_At
          (comma_terminal_weight_digit terminal) (1+H)"
      using nf_exact word_stop by simp
    have applied:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!slot) phase =
        Some (Comma_Semantic_B1_CRT_Stop
          (comma_terminal_weight_digit terminal),1+H)"
      by (rule comma_semantic_future_action_eval_stop_apply[OF action_eval])
    have height_bound: "1+H\<le>27" using height by arith
    show thesis
      by (rule that(1)[OF applied digit_bound height_bound])
  next
    case Comma_Semantic_B1_Invalid
    then show thesis using classified by blast
  qed
qed

lemma comma_semantic_graph_initial_nf_actions_stopped:
  "list_all
    (\<lambda>action. \<forall>phase. \<exists>J delta.
      comma_weighted_crt_apply action phase =
        Some (Comma_Semantic_B1_CRT_Stop J,delta) \<and>
      J<9 \<and> delta\<le>27)
    comma_semantic_graph_initial_nf_actions"
proof -
  have actions_length: "length comma_semantic_graph_initial_nf_actions=16"
    by (rule comma_semantic_graph_initial_nf_actions_length)
  have all_slots:
      "\<forall>slot<length comma_semantic_graph_initial_nf_actions.
        (\<forall>phase. \<exists>J delta.
          comma_weighted_crt_apply
            (comma_semantic_graph_initial_nf_actions!slot) phase =
              Some (Comma_Semantic_B1_CRT_Stop J,delta) \<and>
          J<9 \<and> delta\<le>27)"
  proof (intro allI impI)
    fix slot :: nat
    assume slot: "slot<length comma_semantic_graph_initial_nf_actions"
    have slot_bound: "slot<16" using slot actions_length by simp
    have action_member:
        "comma_semantic_graph_initial_nf_actions!slot \<in>
          set comma_semantic_graph_initial_nf_actions"
      using slot by (rule nth_mem)
    have action_wf:
        "comma_weighted_crt_wellformed
          (snd (comma_semantic_graph_initial_nf_actions!slot))"
      using comma_semantic_graph_initial_nf_actions_wellformed action_member
      by (simp add: list_all_iff)
    show "\<forall>phase. \<exists>J delta.
        comma_weighted_crt_apply
          (comma_semantic_graph_initial_nf_actions!slot) phase =
            Some (Comma_Semantic_B1_CRT_Stop J,delta) \<and>
        J<9 \<and> delta\<le>27"
    proof (intro allI)
      fix phase :: nat
      have reduced_phase: "phase mod 924<924" by simp
      obtain J delta where stopped:
          "comma_weighted_crt_apply
            (comma_semantic_graph_initial_nf_actions!slot) (phase mod 924) =
              Some (Comma_Semantic_B1_CRT_Stop J,delta)"
        and digit: "J<9" and height: "delta\<le>27"
        by (rule comma_semantic_future_initial_nf_slot_stopped
          [OF slot_bound reduced_phase])
      have periodic:
          "comma_weighted_crt_apply
            (comma_semantic_graph_initial_nf_actions!slot) phase =
           comma_weighted_crt_apply
            (comma_semantic_graph_initial_nf_actions!slot) (phase mod 924)"
        using comma_weighted_crt_eval_mod_924[OF action_wf, of phase]
        by (simp add: comma_weighted_crt_apply_def)
      show "\<exists>J delta. comma_weighted_crt_apply
          (comma_semantic_graph_initial_nf_actions!slot) phase =
            Some (Comma_Semantic_B1_CRT_Stop J,delta) \<and>
          J<9 \<and> delta\<le>27"
        using stopped digit height periodic by blast
    qed
  qed
  show ?thesis
    using all_slots actions_length
    by (simp add: list_all_iff all_set_conv_all_nth)
qed

text \<open>
The published initial normal form is tied back to the same source's first
boundary event.  Its displacement remains occurrence data, and candidate
children are selected only after that displacement has rebased the clock.
\<close>

theorem comma_semantic_future_initial_nf_direct_boundary_exact:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains J delta control where
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_nf_actions!
        (comma_semantic_future_initial_source_index q)) (snd (snd q)) =
      Some (Comma_Semantic_B1_CRT_Stop J delta)"
    "comma_weighted_crt_apply
      (comma_semantic_future_initial_nf_dags!
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
  have all_stopped:
    "list_all
      (\<lambda>action. \<forall>phase. \<exists>J delta.
        comma_weighted_crt_apply action phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta) \<and>
        J<9 \<and> delta\<le>27)
      comma_semantic_graph_initial_nf_actions"
    by (rule comma_semantic_graph_initial_nf_actions_stopped)
  have actions_length:
    "length comma_semantic_graph_initial_nf_actions=16"
    by (rule comma_semantic_graph_initial_nf_actions_length)
  have selected_mem:
    "comma_semantic_graph_initial_nf_actions!?slot \<in>
      set comma_semantic_graph_initial_nf_actions"
    using slot_bound actions_length by (auto intro: nth_mem)
  have selected_stopped:
    "\<forall>phase. \<exists>J delta.
      comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!?slot) phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta) \<and>
      J<9 \<and> delta\<le>27"
    using all_stopped selected_mem by (simp add: list_all_iff)
  obtain actual_J actual_delta where actual_apply:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!?slot) ?phase =
          Some (Comma_Semantic_B1_CRT_Stop actual_J actual_delta)"
    and actual_j_bound: "actual_J<9"
    and actual_delta_bound: "actual_delta\<le>27"
    using selected_stopped by blast
  have actual_future_apply:
      "comma_weighted_crt_apply
        (comma_semantic_future_initial_nf_dags!?slot) ?phase =
          Some (Comma_Semantic_B1_CRT_Stop actual_J actual_delta)"
    using actual_apply actual_j_bound by simp
  have actual_eval:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_future_initial_nf_dags!?slot) ?phase =
      Comma_Semantic_B1_Stop_At actual_J actual_delta"
    using actual_future_apply actual_j_bound
    by (simp add: comma_semantic_b1_crt_action_eval_def
        comma_semantic_b1_crt_decode.simps)
  have nf_eval:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_future_initial_nf_dags!?slot) ?phase =
      comma_semantic_b1_weighted_word_then 1
        (\<lambda>p i. comma_semantic_b1_crt_action_eval
          (comma_semantic_graph_initial_source_actions!i) p)
        (\<lambda>p i. comma_semantic_b1_crt_action_eval
          (comma_semantic_future_rank_b32_weighted_actions!i) p)
        ?phase ?slot"
    by (rule comma_semantic_future_initial_nf_action_eval_exact
      [OF slot_bound phase_bound])
  have crossing_stop:
      "\<And>n final d x.
        comma_round_close ?phase (comma_finite_initial q) =
          (n,final,Comma_Round_Cross (Comma_Entry 1 d x)) \<Longrightarrow>
        \<exists>J H. comma_semantic_b1_weighted_action_power 5
          comma_semantic_future_rank_round_action
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
            comma_semantic_future_rank_round_action
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
            comma_semantic_future_rank_round_action
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
            (comma_semantic_future_rank_b32_weighted_actions!i) p)
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
            (comma_semantic_future_rank_b32_weighted_actions!i) p)
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
          comma_semantic_b1_crt_action_eval
            (comma_semantic_future_rank_b32_weighted_actions!
              (comma_offset_orbit x)) ((?phase+1) mod 924) =
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
        and weighted_power:
          "comma_semantic_b1_weighted_action_power 5
            comma_semantic_future_rank_round_action
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
      have post_phase_bound: "((?phase+1) mod 924)<924" by simp
      have b32:
        "comma_semantic_b1_crt_action_eval
          (comma_semantic_future_rank_b32_weighted_actions!comma_offset_orbit x)
          ((?phase+1) mod 924) = Comma_Semantic_B1_Stop_At J H"
      proof -
        have exact:
          "comma_semantic_b1_crt_action_eval
            (comma_semantic_future_rank_b32_weighted_actions!comma_offset_orbit x)
            ((?phase+1) mod 924) =
           comma_semantic_b1_weighted_action_power 5
            comma_semantic_future_rank_round_action
            ((?phase+1) mod 924) (comma_offset_orbit x)"
          by (rule comma_semantic_future_b32_action_eval_exact
            [OF root_bound post_phase_bound])
        show ?thesis using exact weighted_power by simp
      qed
      have composed:
        "comma_semantic_b1_weighted_word_then 1
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_graph_initial_source_actions!i) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (comma_semantic_future_rank_b32_weighted_actions!i) p)
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
  show thesis
    by (rule that[OF actual_apply actual_future_apply actual_j_bound
        actual_delta_bound control_step control_eq boundary_children])
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_future_initial_prefix_boundary_result
      comma_semantic_future_initial_crossing_stop
      comma_semantic_future_initial_round_fork_target_bounds
      comma_semantic_future_initial_nf_direct_boundary_exact})
  then ()
  else error "Comma_Semantic_Future_Source_NF_Bridge oracle audit failed"
\<close>

end
