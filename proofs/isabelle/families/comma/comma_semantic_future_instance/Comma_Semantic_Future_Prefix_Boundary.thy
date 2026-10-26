theory Comma_Semantic_Future_Prefix_Boundary
  imports Comma_Semantic_Future_Prefix_Transport
begin

text \<open>The following theorem closes the complete initial-family prefix,
including any Goto chain, before choosing its provider.  Direct Fork and
Landmine events are already boundary results.  A crossing is admitted only
when its authenticated Entry-1 root supplies a checked weighted Stop.  Thus
the theorem covers all sixteen initial charts without asserting that any of
them is itself a published graph binding.\<close>

theorem comma_semantic_future_initial_prefix_boundary_result:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and crossing_stop:
      "\<And>n final d x.
        comma_round_close (snd (snd q)) (comma_finite_initial q) =
          (n,final,Comma_Round_Cross (Comma_Entry 1 d x)) \<Longrightarrow>
        \<exists>J H. comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action
          ((snd (snd q)+d) mod 924) (comma_offset_orbit x) =
            Comma_Semantic_B1_Stop_At J H"
  obtains calls steps final event where
    "comma_round_control_germ_calls (snd (snd q))
      (comma_finite_initial q) calls"
    "calls \<le> 9"
    "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
      (steps,final,event)"
    "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,final,event)"
    "comma_round_prefix_steps steps (snd (snd q))
      (comma_finite_initial q) final"
    "comma_semantic_future_initial_family_action (comma_finite_initial q)
        (snd (snd q)) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (snd (snd q))
          (comma_finite_initial q))"
    "(\<exists>a d. event=Comma_Round_Fork a d \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (Comma_Fork_At a d) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (Comma_Future_Fork a) \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          (Comma_Future_Fork a) =
          comma_native_boundary_children q (Comma_Fork_At a d) \<and>
        comma_native_boundary_children q (Comma_Fork_At a d) =
          [(Comma_N,a,(snd (snd q)+d) mod 924),
           (Comma_Z,a,(snd (snd q)+d) mod 924)]) \<or>
      (\<exists>d. event=Comma_Round_Landmine d \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (Comma_Landmine_At d) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some Comma_Future_Landmine \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          Comma_Future_Landmine =
          comma_native_boundary_children q (Comma_Landmine_At d) \<and>
        comma_native_boundary_children q (Comma_Landmine_At d) = []) \<or>
      (\<exists>x J H terminal binding. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action
          ((snd (snd q)+1) mod 924) (comma_offset_orbit x) =
            Comma_Semantic_B1_Stop_At J H \<and>
        binding\<in>set comma_semantic_graph_bindings \<and>
        comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0
            (comma_offset_representatives ! comma_offset_orbit x) \<and>
        comma_semantic_b1_binding_cid binding =
          comma_semantic_graph_root_ids ! comma_offset_orbit x \<and>
        comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x \<and>
        J=comma_terminal_weight_digit terminal \<and> H\<le>26 \<and>
        comma_decade_exact_summary
          (Comma_Decade ((snd (snd q)+1) mod 924) x) H terminal \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (comma_summary_outcome (H+1) terminal) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)) \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)) =
          comma_native_boundary_children q
            (comma_summary_outcome (H+1) terminal) \<and>
        comma_native_boundary_children q (comma_summary_outcome (H+1) terminal) =
          (case terminal of
             Comma_Terminal_Fork a \<Rightarrow>
               [(Comma_N,a,(snd (snd q)+1+H) mod 924),
                (Comma_Z,a,(snd (snd q)+1+H) mod 924)]
           | Comma_Terminal_Landmine \<Rightarrow> []))"
proof -
  obtain calls steps final event where calls:
      "comma_round_control_germ_calls (snd (snd q))
        (comma_finite_initial q) calls"
    and calls_bound: "calls\<le>9"
    and germ:
      "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
        (steps,final,event)"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,final,event)"
    and trace:
      "comma_round_prefix_steps steps (snd (snd q))
        (comma_finite_initial q) final"
    and initial_action:
      "comma_semantic_future_initial_family_action (comma_finite_initial q)
          (snd (snd q)) =
        comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet (snd (snd q))
            (comma_finite_initial q))"
    and event_shape:
      "(\<exists>a d. event=Comma_Round_Fork a d) \<or>
       (\<exists>d. event=Comma_Round_Landmine d) \<or>
       (\<exists>x. x\<le>90 \<and>
         event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
         comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
           Comma_Entry 1 ((snd (snd q)+1) mod 924) x)"
    by (rule comma_semantic_future_initial_family_prefix_closed[OF valid])
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have boundary_result:
    "(\<exists>a d. event=Comma_Round_Fork a d \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (Comma_Fork_At a d) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (Comma_Future_Fork a) \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          (Comma_Future_Fork a) =
          comma_native_boundary_children q (Comma_Fork_At a d) \<and>
        comma_native_boundary_children q (Comma_Fork_At a d) =
          [(Comma_N,a,(snd (snd q)+d) mod 924),
           (Comma_Z,a,(snd (snd q)+d) mod 924)]) \<or>
      (\<exists>d. event=Comma_Round_Landmine d \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (Comma_Landmine_At d) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some Comma_Future_Landmine \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          Comma_Future_Landmine =
          comma_native_boundary_children q (Comma_Landmine_At d) \<and>
        comma_native_boundary_children q (Comma_Landmine_At d) = []) \<or>
      (\<exists>x J H terminal binding. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action
          ((snd (snd q)+1) mod 924) (comma_offset_orbit x) =
            Comma_Semantic_B1_Stop_At J H \<and>
        binding\<in>set comma_semantic_graph_bindings \<and>
        comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0
            (comma_offset_representatives ! comma_offset_orbit x) \<and>
        comma_semantic_b1_binding_cid binding =
          comma_semantic_graph_root_ids ! comma_offset_orbit x \<and>
        comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x \<and>
        J=comma_terminal_weight_digit terminal \<and> H\<le>26 \<and>
        comma_decade_exact_summary
          (Comma_Decade ((snd (snd q)+1) mod 924) x) H terminal \<and>
        comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (comma_summary_outcome (H+1) terminal) \<and>
        comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)) \<and>
        comma_semantic_boundary_children comma_semantic_decade_summary q
          (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)) =
          comma_native_boundary_children q
            (comma_summary_outcome (H+1) terminal) \<and>
        comma_native_boundary_children q (comma_summary_outcome (H+1) terminal) =
          (case terminal of
             Comma_Terminal_Fork a \<Rightarrow>
               [(Comma_N,a,(snd (snd q)+1+H) mod 924),
                (Comma_Z,a,(snd (snd q)+1+H) mod 924)]
           | Comma_Terminal_Landmine \<Rightarrow> []))"
  proof (cases event)
    case (Comma_Round_Fork fork delta)
    have step:
      "comma_semantic_boundary_step comma_semantic_decade_summary q =
        Some (Comma_Fork_At fork delta)"
      using valid close Comma_Round_Fork
      by (simp add: comma_semantic_boundary_step_def q)
    have control:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some (Comma_Future_Fork fork)"
      using step by (simp add: comma_semantic_boundary_control_step_def)
    have children:
      "comma_semantic_boundary_children comma_semantic_decade_summary q
        (Comma_Future_Fork fork) = comma_native_boundary_children q
          (Comma_Fork_At fork delta)"
      using step control by (simp add: comma_semantic_boundary_children_def)
    have ordered:
      "comma_native_boundary_children q (Comma_Fork_At fork delta) =
        [(Comma_N,fork,(snd (snd q)+delta) mod 924),
         (Comma_Z,fork,(snd (snd q)+delta) mod 924)]"
      using q by (simp add: comma_native_boundary_children_def)
    show ?thesis using Comma_Round_Fork step control children ordered by blast
  next
    case (Comma_Round_Landmine delta)
    have step:
      "comma_semantic_boundary_step comma_semantic_decade_summary q =
        Some (Comma_Landmine_At delta)"
      using valid close Comma_Round_Landmine
      by (simp add: comma_semantic_boundary_step_def q)
    have control:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some Comma_Future_Landmine"
      using step by (simp add: comma_semantic_boundary_control_step_def)
    have children:
      "comma_semantic_boundary_children comma_semantic_decade_summary q
        Comma_Future_Landmine = comma_native_boundary_children q
          (Comma_Landmine_At delta)"
      using step control by (simp add: comma_semantic_boundary_children_def)
    have ordered:
      "comma_native_boundary_children q (Comma_Landmine_At delta) = []"
      by (simp add: comma_native_boundary_children_def)
    show ?thesis using Comma_Round_Landmine step control children ordered by blast
  next
    case (Comma_Round_Cross target)
    obtain x where x_bound: "x\<le>90"
      and crossing: "event=Comma_Round_Cross (Comma_Entry 1 1 x)"
      and normalized:
        "comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x"
      using event_shape Comma_Round_Cross by blast
    have close_cross:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,final,Comma_Round_Cross (Comma_Entry 1 1 x))"
      using close crossing by simp
    obtain J H where stop:
      "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action
        ((snd (snd q)+1) mod 924) (comma_offset_orbit x) =
          Comma_Semantic_B1_Stop_At J H"
      using crossing_stop[OF close_cross] by blast
    obtain binding terminal where binding:
        "binding\<in>set comma_semantic_graph_bindings"
      and binding_source:
        "comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0
            (comma_offset_representatives ! comma_offset_orbit x)"
      and binding_cid:
        "comma_semantic_b1_binding_cid binding =
          comma_semantic_graph_root_ids ! comma_offset_orbit x"
      and phase:
        "comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x"
      and delta: "1=1"
      and x_admitted: "x\<le>90"
      and terminal_position: "J=comma_terminal_weight_digit terminal"
      and height: "H\<le>26"
      and exact:
        "comma_decade_exact_summary
          (Comma_Decade ((snd (snd q)+1) mod 924) x) H terminal"
      and boundary:
        "comma_semantic_boundary_step comma_semantic_decade_summary q =
          Some (comma_summary_outcome (H+1) terminal)"
      and control:
        "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal))"
      and children:
        "comma_semantic_boundary_children comma_semantic_decade_summary q
          (comma_semantic_boundary_control_of
            (comma_summary_outcome (H+1) terminal)) =
          comma_native_boundary_children q
            (comma_summary_outcome (H+1) terminal)"
      and ordered:
        "comma_native_boundary_children q (comma_summary_outcome (H+1) terminal) =
          (case terminal of
             Comma_Terminal_Fork a \<Rightarrow>
               [(Comma_N,a,(snd (snd q)+1+H) mod 924),
                (Comma_Z,a,(snd (snd q)+1+H) mod 924)]
           | Comma_Terminal_Landmine \<Rightarrow> [])"
      using comma_semantic_future_initial_crossing_weighted_boundary
        [OF valid close_cross stop] by blast
    show ?thesis
      using crossing stop binding binding_source binding_cid phase
        x_admitted terminal_position height exact boundary control children ordered
      by blast
  next
    case Comma_Round_Invalid
    then show ?thesis using event_shape by blast
  qed
  show thesis
    by (rule that[OF calls calls_bound germ close trace initial_action
      boundary_result])
qed

corollary comma_semantic_future_initial_exit_weighted_boundary:
  fixes q :: comma_boundary_state and x d J H :: nat
  assumes valid: "comma_boundary_valid q"
    and exit:
      "comma_semantic_future_initial_family_action
        (comma_finite_initial q) (snd (snd q)) =
          Comma_Continuation_Exit (Comma_Entry 1 0 x) d"
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
  obtain n terminal_position where close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 d x))"
    and d_eq: "d=1" and x_bound: "x\<le>90"
    by (rule comma_semantic_future_initial_exit_close[OF valid exit])
  have selected:
      "comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action
        ((snd (snd q)+d) mod 924) (comma_offset_orbit x) =
          Comma_Semantic_B1_Stop_At J H"
    by (rule weighted_stop)
  show thesis
    by (rule comma_semantic_future_initial_crossing_weighted_boundary
      [OF valid close selected])
qed

ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_future_initial_prefix_boundary_result
      comma_semantic_future_initial_exit_weighted_boundary})
  then ()
  else error "Comma_Semantic_Future_Prefix_Boundary oracle audit failed"
\<close>

end
