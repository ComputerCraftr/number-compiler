theory Comma_Semantic_Future_Prefix_Transport
  imports Comma_Semantic_Future_Weighted_Transport
begin

text \<open>The family domain is explicit so a source lookup or checked
crossing-prefix bridge has exactly sixteen inputs.  The list itself grants no
source graph authority.  That must come from an authenticated lookup or the
source-independent packet transport.\<close>

definition comma_semantic_future_initial_source_index ::
    "comma_boundary_state \<Rightarrow> nat" where
  "comma_semantic_future_initial_source_index q =
    (case q of (kind,a,r) \<Rightarrow>
      (if kind=Comma_N then 0 else 8) + (a-2))"

lemma comma_semantic_future_initial_source_index_exact:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_future_initial_source_index q<16"
    "comma_semantic_future_initial_sources !
        comma_semantic_future_initial_source_index q =
      comma_finite_initial q"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have a_lower: "2\<le>a" and a_upper: "a\<le>9"
    using valid by (simp_all add: q comma_boundary_valid_def)
  have a_index: "a-2<8" using a_lower a_upper by arith
  show "comma_semantic_future_initial_source_index q<16"
    using a_index by (cases kind)
      (simp_all add: comma_semantic_future_initial_source_index_def q)
  show "comma_semantic_future_initial_sources !
        comma_semantic_future_initial_source_index q =
      comma_finite_initial q"
  proof (cases kind)
    case Comma_N
    have index: "comma_semantic_future_initial_source_index q=a-2"
      using Comma_N by (simp add: comma_semantic_future_initial_source_index_def q)
    have source:
      "comma_semantic_future_initial_sources ! (a-2) =
        Comma_Near (a-1) 0 1"
      using a_index
      by (simp add: comma_semantic_future_initial_sources_def nth_append
          nth_map_upt)
    show ?thesis
      using source index Comma_N
      by (simp add: q comma_finite_initial_def)
  next
    case Comma_Z
    have index: "comma_semantic_future_initial_source_index q=8+(a-2)"
      using Comma_Z by (simp add: comma_semantic_future_initial_source_index_def q)
    have source:
      "comma_semantic_future_initial_sources ! (8+(a-2)) =
        Comma_Entry a 0 0"
      using a_index
      by (simp add: comma_semantic_future_initial_sources_def nth_append
          nth_map_upt)
    show ?thesis
      using source index Comma_Z
      by (simp add: q comma_finite_initial_def)
  qed
qed

definition comma_semantic_future_initial_source_cid ::
    "comma_boundary_state \<Rightarrow> nat option" where
  "comma_semantic_future_initial_source_cid q =
    (if comma_boundary_valid q then
       Some (comma_semantic_graph_initial_source_ids !
         comma_semantic_future_initial_source_index q)
     else None)"

lemma comma_semantic_future_initial_source_cid_exact:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_future_initial_source_cid q =
      Some (comma_semantic_graph_initial_source_ids !
        comma_semantic_future_initial_source_index q)"
    "comma_semantic_b1_binding_cid_of comma_semantic_graph_bindings
        (comma_finite_initial q) =
      comma_semantic_future_initial_source_cid q"
proof -
  have index_facts:
      "comma_semantic_future_initial_source_index q<16"
      "comma_semantic_future_initial_sources !
        comma_semantic_future_initial_source_index q =
          comma_finite_initial q"
    by (rule comma_semantic_future_initial_source_index_exact[OF valid])+
  have source_length:
      "length comma_semantic_future_initial_sources=16"
    by (simp add: comma_semantic_future_initial_sources_def)
  have index_bound:
      "comma_semantic_future_initial_source_index q <
        length comma_semantic_future_initial_sources"
    using index_facts source_length by simp
  have selected_lookup:
      "comma_semantic_b1_binding_cid_of comma_semantic_graph_bindings
        (comma_semantic_future_initial_sources !
          comma_semantic_future_initial_source_index q) =
       Some (comma_semantic_graph_initial_source_ids !
          comma_semantic_future_initial_source_index q)"
    by (rule list_all2_nthD
      [OF comma_semantic_graph_initial_source_binding_exact index_bound])
  show "comma_semantic_future_initial_source_cid q =
      Some (comma_semantic_graph_initial_source_ids !
        comma_semantic_future_initial_source_index q)"
    using valid
    by (simp add: comma_semantic_future_initial_source_cid_def)
  show "comma_semantic_b1_binding_cid_of comma_semantic_graph_bindings
        (comma_finite_initial q) =
      comma_semantic_future_initial_source_cid q"
    using selected_lookup index_facts(2)
    by (simp add: comma_semantic_future_initial_source_cid_def valid)
qed

lemma comma_semantic_future_initial_source_in_family:
  assumes kind: "kind = Comma_N \<or> kind = Comma_Z"
    and digit: "2 \<le> a" "a \<le> 9"
  shows "comma_finite_initial (kind,a,r) \<in>
    set comma_semantic_future_initial_sources"
  using kind digit
  by (cases kind)
    (auto simp: comma_finite_initial_def
      comma_semantic_future_initial_sources_def; arith)

lemma comma_semantic_future_initial_source_admitted:
  assumes valid: "comma_boundary_valid q"
  shows "comma_round_admitted (comma_finite_initial q)"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  show ?thesis
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def; arith)
qed

text \<open>The source-family prefix starts from the exact period-aware packet
for its admitted initial chart.  This is a source action certificate, not an
assumed graph binding.  It does not establish the crossing-prefix phase map
for an Exit; that requires a separate checked bridge before graph transport.\<close>

lemma comma_semantic_future_initial_source_packet_action:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_b1_source_port_action (comma_finite_initial q)
      (snd (snd q)) =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet (snd (snd q))
        (comma_finite_initial q))"
proof -
  have admitted: "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have exact:
    "comma_semantic_b1_source_port_action (comma_finite_initial q)
        (snd (snd q)) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (snd (snd q))
          (comma_source_continuation_base (comma_finite_initial q)))"
    by (rule comma_semantic_b1_source_port_action_packet[OF admitted])
  show ?thesis using exact
    by (cases q) (simp add: comma_finite_initial_def)
qed

definition comma_semantic_future_initial_family_action ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_future_initial_family_action source slot =
    (case source of
       Comma_Near f delta headroom \<Rightarrow>
         if delta=0 \<and> headroom=1 then
           (case comma_decisive_sector_target slot
               (comma_source_continuation_base source) of
              Comma_Near next_f next_delta next_headroom \<Rightarrow>
                comma_semantic_b1_near_control_port_action
                  next_f next_delta next_headroom
            | _ \<Rightarrow> Comma_Continuation_Invalid)
         else Comma_Continuation_Invalid
     | Comma_Entry f delta offset \<Rightarrow>
         if delta=0 \<and> offset=0 then
           comma_c1_b1_entry_core_port_action f offset slot
         else Comma_Continuation_Invalid)"

lemma comma_semantic_future_initial_family_action_exact:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_future_initial_family_action
      (comma_finite_initial q) slot =
    comma_semantic_b1_source_port_action (comma_finite_initial q) slot"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have digit_bounds: "2\<le>a" "a\<le>9"
    using valid q by (auto simp: comma_boundary_valid_def)
  show ?thesis
    using valid digit_bounds q
    by (cases kind)
      (auto simp: comma_semantic_future_initial_family_action_def
        comma_finite_initial_def comma_semantic_b1_source_port_action_def
        comma_c1_b1_entry_core_port_action_source_exact
        split: comma_finite_position.splits)
qed

lemma comma_semantic_future_initial_family_action_packet:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_future_initial_family_action
      (comma_finite_initial q) slot =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet slot (comma_finite_initial q))"
  using comma_semantic_future_initial_family_action_exact[OF valid]
    comma_semantic_future_initial_source_packet_action[OF valid]
  by simp

text \<open>
The family action at the initial chart is usually only the first local
sector packet.  It can be a Goto, so the source-to-boundary bridge follows
the existing strictly ranked sector recursion to its first terminal event.
The terminal crossing is then the only place that enters an authenticated
Entry-1 graph root; no binding for the initial Near/Entry family is assumed.
\<close>

theorem comma_semantic_future_initial_family_prefix_closed:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains calls steps terminal event where
    "comma_round_control_germ_calls (snd (snd q))
      (comma_finite_initial q) calls"
    "calls \<le> 9"
    "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_prefix_steps steps (snd (snd q))
      (comma_finite_initial q) terminal"
    "comma_semantic_future_initial_family_action (comma_finite_initial q)
        (snd (snd q)) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (snd (snd q))
          (comma_finite_initial q))"
    "(\<exists>a d. event = Comma_Round_Fork a d) \<or>
      (\<exists>d. event = Comma_Round_Landmine d) \<or>
      (\<exists>x. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x)"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  let ?initial = "comma_finite_initial q"
  have source_admitted: "comma_round_admitted ?initial"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  obtain calls where calls:
      "comma_round_control_germ_calls r ?initial calls"
    and calls_bound: "calls\<le>9"
    using comma_round_control_germ_at_most_nine_sectors[OF source_admitted]
    by blast
  obtain steps terminal event where close:
      "comma_round_close r ?initial=(steps,terminal,event)"
    by (cases "comma_round_close r ?initial") auto
  have trace:
      "comma_round_prefix_steps steps r ?initial terminal"
    using comma_round_close_refines_trace[OF close] by simp
  have initial_action:
      "comma_semantic_future_initial_family_action ?initial r =
        comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet r ?initial)"
    by (rule comma_semantic_future_initial_family_action_packet[OF valid])
  have germ:
      "comma_round_control_germ r ?initial=(steps,terminal,event)"
    using comma_round_control_germ_refines close by simp
  have close_at_q:
      "comma_round_close (snd (snd q)) ?initial=(steps,terminal,event)"
    using close q by simp
  have event_not_invalid: "event\<noteq>Comma_Round_Invalid"
    using comma_round_close_admitted(2)[OF close source_admitted] by simp
  have source_delta: "comma_round_delta ?initial=0"
    using q by (cases kind) (simp_all add: comma_finite_initial_def)
  have event_shape:
      "(\<exists>a' d'. event = Comma_Round_Fork a' d') \<or>
       (\<exists>d'. event = Comma_Round_Landmine d') \<or>
       (\<exists>x. x\<le>90 \<and>
         event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
         comma_normalize_position r (Comma_Entry 1 1 x) =
           Comma_Entry 1 ((r+1) mod 924) x)"
  proof (cases event)
    case (Comma_Round_Fork fork delta)
    then show ?thesis by blast
  next
    case (Comma_Round_Landmine delta)
    then show ?thesis by blast
  next
    case (Comma_Round_Cross target)
    obtain x where x_bound: "x\<le>90"
      and target: "target=Comma_Entry 1 (Suc (comma_round_delta ?initial)) x"
      and normalized:
        "comma_normalize_position r target =
          Comma_Entry 1 ((r+comma_round_delta ?initial+1) mod 924) x"
      using comma_round_close_crossing_phase[OF close source_admitted]
      by blast
    have target_one: "target=Comma_Entry 1 1 x"
      using target source_delta by simp
    have normalized_one:
        "comma_normalize_position r (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((r+1) mod 924) x"
      using normalized target_one source_delta by simp
    show ?thesis using Comma_Round_Cross x_bound target_one normalized_one
      by blast
  next
    case Comma_Round_Invalid
    then show ?thesis using event_not_invalid by blast
  qed
  show thesis
    using calls calls_bound germ close_at_q trace initial_action event_shape q
    by (intro that[of calls steps terminal event]) simp_all
qed

theorem comma_semantic_future_initial_family_prefix_root_or_terminal:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains calls steps terminal event where
    "comma_round_control_germ_calls (snd (snd q))
      (comma_finite_initial q) calls"
    "calls \<le> 9"
    "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_prefix_steps steps (snd (snd q))
      (comma_finite_initial q) terminal"
    "comma_semantic_future_initial_family_action (comma_finite_initial q)
        (snd (snd q)) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (snd (snd q))
          (comma_finite_initial q))"
    "(\<exists>a d. event = Comma_Round_Fork a d) \<or>
      (\<exists>d. event = Comma_Round_Landmine d) \<or>
      (\<exists>x binding. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x \<and>
        binding\<in>set comma_semantic_graph_bindings \<and>
        comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0
            (comma_offset_representatives ! comma_offset_orbit x) \<and>
        comma_semantic_b1_binding_cid binding =
          comma_semantic_graph_root_ids ! comma_offset_orbit x)"
proof -
  obtain calls steps terminal event where calls:
      "comma_round_control_germ_calls (snd (snd q))
        (comma_finite_initial q) calls"
    and calls_bound: "calls\<le>9"
    and germ:
      "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
        (steps,terminal,event)"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,terminal,event)"
    and trace:
      "comma_round_prefix_steps steps (snd (snd q))
        (comma_finite_initial q) terminal"
    and initial_action:
      "comma_semantic_future_initial_family_action (comma_finite_initial q)
          (snd (snd q)) =
        comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet (snd (snd q))
            (comma_finite_initial q))"
    and shape:
      "(\<exists>a d. event = Comma_Round_Fork a d) \<or>
       (\<exists>d. event = Comma_Round_Landmine d) \<or>
       (\<exists>x. x\<le>90 \<and>
         event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
         comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
           Comma_Entry 1 ((snd (snd q)+1) mod 924) x)"
    by (rule comma_semantic_future_initial_family_prefix_closed[OF valid])
  let ?direct = "(\<exists>a d. event=Comma_Round_Fork a d) \<or>
    (\<exists>d. event=Comma_Round_Landmine d)"
  show thesis
  proof (cases ?direct)
    case True
    show ?thesis
      apply (rule that[OF calls calls_bound germ close trace initial_action])
      using True by blast
  next
    case False
    then obtain x where x_bound: "x\<le>90"
      and crossing:
        "event=Comma_Round_Cross (Comma_Entry 1 1 x)"
      and normalized:
        "comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x"
      using shape by blast
    let ?root = "comma_offset_orbit x"
    have root_bound: "?root<46" by (rule comma_offset_orbit_bound)
    obtain binding where binding:
        "binding\<in>set comma_semantic_graph_bindings"
        "comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0 (comma_offset_representatives ! ?root)"
        "comma_semantic_b1_binding_cid binding =
          comma_semantic_graph_root_ids ! ?root"
      using comma_semantic_graph_root_binding_exists[OF root_bound] by blast
    show ?thesis
      apply (rule that[OF calls calls_bound germ close trace initial_action])
      using crossing normalized x_bound binding by blast
  qed
qed

lemma comma_semantic_future_initial_goto_prefix_graph_eval:
  assumes valid: "comma_boundary_valid q"
    and phase: "phase < 924"
    and goto:
      "comma_semantic_b1_source_port_action (comma_finite_initial q) phase =
        Comma_Continuation_Goto target 0"
    and member: "binding \<in> set comma_semantic_graph_bindings"
    and source: "comma_semantic_b1_binding_source binding = target"
  shows "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
      (comma_semantic_b1_binding_cid binding) phase =
    Some (comma_semantic_b1_round_output phase (comma_finite_initial q))"
proof -
  let ?initial = "comma_finite_initial q"
  let ?period = "comma_decisive_sector_period ?initial"
  let ?slot = "phase mod ?period"
  have admitted: "comma_round_admitted ?initial"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have normalized: "?initial = comma_source_continuation_base ?initial"
    by (cases q) (simp add: comma_finite_initial_def)
  have period_positive: "0 < ?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have slot_bound: "?slot < ?period"
    using period_positive by simp
  have selected: "phase mod ?period = ?slot" by simp
  have packet_period:
    "comma_decisive_endpoint_packet phase ?initial =
      comma_decisive_endpoint_packet ?slot ?initial"
    using comma_decisive_endpoint_packet_period[OF admitted, of phase ?slot]
    by (simp add: normalized)
  have source_packet:
    "comma_semantic_b1_source_port_action ?initial phase =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase ?initial)"
    using comma_semantic_b1_source_port_action_packet[OF admitted, of phase]
    by (simp add: normalized)
  have slot_action:
    "comma_semantic_b1_source_slot_action ?initial ?slot =
      Comma_Continuation_Goto target 0"
    using goto source_packet packet_period
    by (simp add: comma_semantic_b1_source_slot_action_def)
  have returned:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_slot_action ?initial ?slot) =
      comma_semantic_b1_round_output phase ?initial"
    by (rule comma_semantic_b1_source_slot_round_output
      [OF normalized admitted slot_bound selected])
  have output_target:
    "comma_semantic_b1_round_output phase ?initial =
      comma_semantic_b1_round_output phase target"
    using returned slot_action
    by (simp add: comma_semantic_b1_source_slot_output_def)
  have all_bindings:
    "\<forall>cid. comma_semantic_b1_graph_correct_at
      comma_semantic_graph_bindings comma_semantic_graph_nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint
      [OF comma_semantic_graph_valid_checked])
  have target_evaluation:
    "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_b1_binding_cid binding) phase =
      Some (comma_semantic_b1_round_output phase target)"
    using all_bindings member source
    by (simp add: comma_semantic_b1_graph_correct_at_def)
  show ?thesis using target_evaluation output_target by simp
qed

lemma comma_semantic_future_initial_exit_close:
  fixes q :: comma_boundary_state and x d :: nat
  assumes valid: "comma_boundary_valid q"
    and exit:
      "comma_semantic_future_initial_family_action
        (comma_finite_initial q) (snd (snd q)) =
          Comma_Continuation_Exit (Comma_Entry 1 0 x) d"
  obtains n terminal_position where
    "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 d x))"
    "comma_normalize_position (snd (snd q)) (Comma_Entry 1 d x) =
      Comma_Entry 1
        ((snd (snd q)+comma_round_delta (comma_finite_initial q)+1) mod 924) x"
    "d=1" "x\<le>90"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have source_admitted:
    "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  have family_packet:
    "comma_semantic_future_initial_family_action
        (comma_finite_initial q) r =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet r (comma_finite_initial q))"
    by (rule comma_semantic_future_initial_family_action_packet[OF valid])
  have packet_action:
    "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet r (comma_finite_initial q)) =
      Comma_Continuation_Exit (Comma_Entry 1 0 x) d"
    using family_packet exit q by simp
  obtain target move where packet:
    "comma_decisive_endpoint_packet r (comma_finite_initial q)=(target,move)"
    by (cases "comma_decisive_endpoint_packet r (comma_finite_initial q)") auto
  have selected_action:
    "comma_source_continuation_action_of_packet (target,move) =
      Comma_Continuation_Exit (Comma_Entry 1 0 x) d"
    using packet_action packet by simp
  have packet_next:
    "\<exists>next. move=Comma_Next next \<and>
      comma_round_crossing target next \<and>
      comma_source_continuation_base next=Comma_Entry 1 0 x \<and>
      comma_source_continuation_shift next=d"
    using selected_action
    by (cases move)
      (auto simp: comma_source_continuation_action_of_packet.simps
        split: if_splits)
  obtain next where move: "move=Comma_Next next"
    and crossing: "comma_round_crossing target next"
    and next_base:
      "comma_source_continuation_base next=Comma_Entry 1 0 x"
    and next_shift: "comma_source_continuation_shift next=d"
    using packet_next by blast
  have next_shape: "next=Comma_Entry 1 d x"
  proof (cases next)
    case (Comma_Entry f delta offset)
    then show ?thesis using next_base next_shift by simp
  next
    case (Comma_Near f delta headroom)
    then show ?thesis using next_base by simp
  qed
  have endpoint:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      Comma_Round_Cross (Comma_Entry 1 d x)"
    using comma_decisive_endpoint_round_packet[OF source_admitted]
      packet move crossing next_shape by simp
  have endpoint_close:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      snd (snd (comma_round_close r (comma_finite_initial q)))"
    by (rule comma_decisive_endpoint_round_refines_close[OF source_admitted])
  obtain n terminal_position event where close:
    "comma_round_close r (comma_finite_initial q)=(n,terminal_position,event)"
    by (cases "comma_round_close r (comma_finite_initial q)") auto
  have event:
    "event=Comma_Round_Cross (Comma_Entry 1 d x)"
    using endpoint endpoint_close close by simp
  have close_cross:
    "comma_round_close r (comma_finite_initial q)=
      (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 d x))"
    using close event by simp
  obtain x' where x_bound: "x'\<le>90"
    and target_shape:
      "Comma_Entry 1 d x=Comma_Entry 1
        (Suc (comma_round_delta (comma_finite_initial q))) x'"
    and normalized:
      "comma_normalize_position r (Comma_Entry 1 d x) =
        Comma_Entry 1
          ((r+comma_round_delta (comma_finite_initial q)+1) mod 924) x'"
    using comma_round_close_crossing_phase[OF close_cross source_admitted]
    by blast
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    using q by (cases kind)
      (simp_all add: comma_finite_initial_def)
  have d_eq: "d=1" using target_shape source_delta by simp
  have x_eq: "x=x'" using target_shape by simp
  have x_bound_initial: "x\<le>90" using x_bound x_eq by simp
  have normalized_initial:
    "comma_normalize_position (snd (snd q)) (Comma_Entry 1 d x) =
      Comma_Entry 1
        ((snd (snd q)+comma_round_delta (comma_finite_initial q)+1) mod 924) x"
    using normalized q x_eq by simp
  show thesis
    by (rule that[OF close_cross normalized_initial d_eq x_bound_initial])
qed

theorem comma_semantic_future_initial_crossing_weighted_boundary:
  fixes q :: comma_boundary_state and x d J H n terminal_position :: nat
  assumes valid: "comma_boundary_valid q"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 d x))"
    and weighted_stop:
      "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action
        ((snd (snd q)+d) mod 924) (comma_offset_orbit x) =
          Comma_Semantic_B1_Stop_At J H"
  obtains binding terminal where
    "binding \<in> set comma_semantic_graph_bindings"
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0
        (comma_offset_representatives ! comma_offset_orbit x)"
    "comma_semantic_b1_binding_cid binding =
      comma_semantic_graph_root_ids ! comma_offset_orbit x"
    "comma_normalize_position (snd (snd q)) (Comma_Entry 1 d x) =
      Comma_Entry 1
        ((snd (snd q)+comma_round_delta (comma_finite_initial q)+1) mod 924) x"
    "d=1" "x\<le>90" "J=comma_terminal_weight_digit terminal" "H\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade ((snd (snd q)+d) mod 924) x) H terminal"
    "comma_semantic_decade_summary
      (Comma_Decade ((snd (snd q)+d) mod 924) x) = Some (H,terminal)"
    "comma_semantic_boundary_step comma_semantic_decade_summary q =
      Some (comma_summary_outcome (H+d) terminal)"
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_semantic_boundary_control_of
        (comma_summary_outcome (H+d) terminal))"
    "comma_semantic_boundary_children comma_semantic_decade_summary q
        (comma_semantic_boundary_control_of
          (comma_summary_outcome (H+d) terminal)) =
      comma_native_boundary_children q (comma_summary_outcome (H+d) terminal)"
    "comma_native_boundary_children q (comma_summary_outcome (H+d) terminal) =
      (case terminal of
         Comma_Terminal_Fork a \<Rightarrow>
           [(Comma_N,a,(snd (snd q)+d+H) mod 924),
            (Comma_Z,a,(snd (snd q)+d+H) mod 924)]
       | Comma_Terminal_Landmine \<Rightarrow> [])"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have source_admitted:
      "comma_round_admitted (comma_finite_initial q)"
    by (rule comma_semantic_future_initial_source_admitted[OF valid])
  obtain x' where x_bound: "x'\<le>90"
    and target_shape:
      "Comma_Entry 1 d x = Comma_Entry 1
        (Suc (comma_round_delta (comma_finite_initial q))) x'"
    and normalized:
      "comma_normalize_position (snd (snd q)) (Comma_Entry 1 d x) =
        Comma_Entry 1
          ((snd (snd q)+comma_round_delta (comma_finite_initial q)+1) mod 924) x'"
    using comma_round_close_crossing_phase[OF close source_admitted]
    by blast
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    using q by (cases kind) (simp_all add: comma_finite_initial_def)
  have d_eq: "d=1" using target_shape source_delta by simp
  have x_eq: "x=x'" using target_shape by simp
  have x_bound_initial: "x\<le>90" using x_bound x_eq by simp
  have normalized_cross:
      "comma_normalize_position (snd (snd q)) (Comma_Entry 1 d x) =
        Comma_Entry 1
          ((snd (snd q)+comma_round_delta (comma_finite_initial q)+1) mod 924) x"
    using normalized x_eq by simp
  let ?phase = "(snd (snd q)+d) mod 924"
  let ?root = "comma_offset_orbit x"
  let ?state = "Comma_Decade ?phase x"
  have phase_bound: "?phase<924" by simp
  have root_bound: "?root<46" by (rule comma_offset_orbit_bound)
  have root_binding:
    "\<exists>binding\<in>set comma_semantic_graph_bindings.
       comma_semantic_b1_binding_source binding =
         Comma_Entry 1 0 (comma_offset_representatives ! ?root) \<and>
       comma_semantic_b1_binding_cid binding =
         comma_semantic_graph_root_ids ! ?root"
    by (rule comma_semantic_graph_root_binding_exists[OF root_bound])
  obtain binding where binding_member:
      "binding\<in>set comma_semantic_graph_bindings"
    and binding_source:
      "comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives ! ?root)"
    and binding_cid:
      "comma_semantic_b1_binding_cid binding =
        comma_semantic_graph_root_ids ! ?root"
    using root_binding by blast
  have state_admitted: "comma_decade_admitted ?state"
    using phase_bound x_bound_initial by simp
  obtain h terminal where provider_lookup:
      "comma_semantic_decade_summary ?state=Some (h,terminal)"
    and height: "h\<le>26"
    and exact:
      "comma_decade_exact_summary ?state h terminal"
    using comma_semantic_decade_summary_total_exact[OF state_admitted]
    by blast
  have weighted_admitted:
    "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action ?phase ?root)"
  proof (rule comma_semantic_b1_weighted_action_power_admitted)
    show "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
        comma_semantic_b1_weighted_result_admitted
          (comma_semantic_graph_root_weighted_action phase root)"
      by (rule comma_semantic_graph_root_weighted_action_admitted)
    show "?phase<924" by (rule phase_bound)
    show "?root<46" by (rule root_bound)
  qed
  have J_bound: "J<9"
    using weighted_admitted weighted_stop
    by (simp add: comma_semantic_b1_weighted_result_admitted.simps)
  have graph_stop:
    "comma_semantic_graph_action_power 5 ?phase ?root =
      Comma_Semantic_B1_Stop (9*H+J)"
    using comma_semantic_graph_weighted_power_exact[of 5 ?phase ?root]
      weighted_stop by simp
  have decode:
    "comma_terminal_weight_decode (9*H+J) =
      (H,comma_terminal_weight_terminal J)"
    using J_bound
    by (simp add: comma_terminal_weight_decode_def
        comma_terminal_weight_terminal_def div_add1_eq mod_add_left_eq)
  have computed:
    "comma_semantic_decade_summary ?state =
      Some (H,comma_terminal_weight_terminal J)"
    using state_admitted graph_stop decode
    by (simp add: comma_semantic_decade_summary_code)
  have fields:
    "h=H" "terminal=comma_terminal_weight_terminal J"
    using provider_lookup computed by auto
  have digit:
    "comma_terminal_weight_digit (comma_terminal_weight_terminal J)=J"
    using J_bound
    by (cases "J=8")
      (simp_all add: comma_terminal_weight_terminal_def)
  have terminal_digit: "J=comma_terminal_weight_digit terminal"
    using fields digit by simp
  have exact_H:
    "comma_decade_exact_summary ?state H terminal"
    using exact fields by simp
  have lookup_H:
    "comma_semantic_decade_summary ?state=Some (H,terminal)"
    using provider_lookup fields by simp
  have event:
    "comma_semantic_boundary_event_outcome comma_semantic_decade_summary
        (snd (snd q)) (Comma_Round_Cross (Comma_Entry 1 d x)) =
      Some (comma_summary_outcome (H+d) terminal)"
    using lookup_H x_bound_initial by simp
  have boundary:
    "comma_semantic_boundary_step comma_semantic_decade_summary q =
      Some (comma_summary_outcome (H+d) terminal)"
    using valid q close event
    by (simp add: comma_semantic_boundary_step_def)
  have control:
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_semantic_boundary_control_of
        (comma_summary_outcome (H+d) terminal))"
    using boundary
    by (simp add: comma_semantic_boundary_control_step_def)
  have children:
    "comma_semantic_boundary_children comma_semantic_decade_summary q
        (comma_semantic_boundary_control_of
          (comma_summary_outcome (H+d) terminal)) =
      comma_native_boundary_children q (comma_summary_outcome (H+d) terminal)"
    using boundary
    by (simp add: comma_semantic_boundary_children_def)
  have ordered_children:
    "comma_native_boundary_children q (comma_summary_outcome (H+d) terminal) =
      (case terminal of
         Comma_Terminal_Fork a \<Rightarrow>
           [(Comma_N,a,(snd (snd q)+d+H) mod 924),
            (Comma_Z,a,(snd (snd q)+d+H) mod 924)]
       | Comma_Terminal_Landmine \<Rightarrow> [])"
    using d_eq q by (cases terminal)
      (simp_all add: comma_native_boundary_children_def
        comma_summary_outcome.simps algebra_simps)
  show thesis
    by (rule that[OF binding_member binding_source binding_cid normalized_cross
        d_eq x_bound_initial terminal_digit height exact_H lookup_H boundary control
        children ordered_children])
qed

ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_future_initial_source_index_exact
      comma_semantic_future_initial_source_cid_exact
      comma_semantic_future_initial_family_action_exact
      comma_semantic_future_initial_family_prefix_closed
      comma_semantic_future_initial_family_prefix_root_or_terminal
      comma_semantic_future_initial_goto_prefix_graph_eval
      comma_semantic_future_initial_exit_close
      comma_semantic_future_initial_crossing_weighted_boundary})
  then ()
  else error "Comma_Semantic_Future_Prefix_Transport oracle audit failed"
\<close>

end
