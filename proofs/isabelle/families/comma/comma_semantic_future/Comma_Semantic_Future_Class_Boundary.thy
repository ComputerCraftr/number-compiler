theory Comma_Semantic_Future_Class_Boundary
  imports Comma_Semantic_Future.Comma_Semantic_Initial_Prefix
    Comma_Decade_Orbit.Comma_Decade_Orbit_Summary
    Comma_Semantic_B1.Comma_Targeted_Continue_Certificate
begin

text \<open>
This bridge transports the source-free class B32 result into the concrete
boundary provider.  The source segment is still obtained from the exact
closed-germ theorem, and its physical seam is retained.  Only the continued
decade summary is supplied by the normalized phase/class certificate; no
candidate ID or occurrence-indexed weighted action table is used here.
The native Continue24 publisher is registered upstream in the B1 instance;
this bridge keeps its image condition explicit for the downstream consumer.
\<close>

theorem comma_semantic_future_initial_crossing_class_boundary:
  fixes q :: comma_boundary_state
  assumes image24:
      "\<And>phase cid terminal. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (phase,cid) =
          Some terminal \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
    and valid: "comma_boundary_valid q"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q) =
        (steps,final,Comma_Round_Cross (Comma_Entry 1 1 x))"
  obtains height terminal where
    "x\<le>90"
    "height\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade ((snd (snd q)+1) mod 924) x) height terminal"
    "comma_semantic_future_action_terminal_position
      (comma_semantic_boundary_control_of
        (comma_summary_outcome (height+1) terminal)) =
      comma_terminal_weight_digit terminal"
    "comma_semantic_decade_summary
      (Comma_Decade ((snd (snd q)+1) mod 924) x) = Some (height,terminal)"
    "comma_semantic_boundary_step comma_semantic_decade_summary q =
      Some (comma_summary_outcome (height+1) terminal)"
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_semantic_boundary_control_of
        (comma_summary_outcome (height+1) terminal))"
    "comma_semantic_boundary_children comma_semantic_decade_summary q
        (comma_semantic_boundary_control_of
          (comma_summary_outcome (height+1) terminal)) =
      comma_native_boundary_children q (comma_summary_outcome (height+1) terminal)"
    "comma_native_boundary_children q (comma_summary_outcome (height+1) terminal) =
      (case terminal of
         Comma_Terminal_Fork a \<Rightarrow>
           [(Comma_N,a,(snd (snd q)+1+height) mod 924),
            (Comma_Z,a,(snd (snd q)+1+height) mod 924)]
       | Comma_Terminal_Landmine \<Rightarrow> [])"
proof -
  obtain kind a phase where q: "q=(kind,a,phase)"
    by (cases q) auto
  have phase: "phase<924"
    using valid q by (simp add: comma_boundary_valid_def)
  have source_admitted: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases q)
      (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  obtain x' where x_bound: "x'\<le>90"
    and target_shape:
      "Comma_Entry 1 1 x = Comma_Entry 1
        (Suc (comma_round_delta (comma_finite_initial q))) x'"
    using comma_round_close_crossing_phase[OF close source_admitted]
    by blast
  have x_eq: "x=x'" using target_shape by simp
  have x_bound: "x\<le>90" using x_bound x_eq by simp
  let ?next_phase = "(phase+1) mod 924"
  let ?cid = "comma_offset_orbit x"
  have next_phase: "?next_phase<924" by simp
  have cid: "?cid<46" by (rule comma_offset_orbit_bound)
  obtain height terminal where height: "height\<le>26"
    and representative_summary:
      "comma_decade_exact_summary
        (Comma_Decade ?next_phase
          (comma_offset_representatives!?cid)) height terminal"
    and action:
      "comma_semantic_b1_action_power 5 ?next_phase ?cid =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    and encoded_bound:
      "comma_terminal_weight_encode height terminal\<le>242"
    by (rule comma_semantic_phase_class_B32_exact_output_if_continue24_image
      [OF image24 next_phase cid])
  have representative:
    "comma_offset_representatives!?cid = comma_offset_representative x"
    by (simp add: comma_offset_representative_def)
  have representative_bound:
      "comma_offset_representative x\<le>90"
    by (rule comma_offset_representative_admitted(1))
  have same_orbit:
      "comma_offset_orbit (comma_offset_representative x)=?cid"
    using comma_offset_representative_admitted(2)[of x] by simp
  have exact_summary:
      "comma_decade_exact_summary (Comma_Decade ?next_phase x)
        height terminal"
    using comma_semantic_future_exact_summary_orbit_transport
      [OF next_phase representative_bound x_bound same_orbit]
      representative_summary representative by simp
  have terminal_position:
      "comma_semantic_future_action_terminal_position
        (comma_semantic_boundary_control_of
          (comma_summary_outcome (height+1) terminal)) =
        comma_terminal_weight_digit terminal"
    by (cases terminal)
      (simp_all add: comma_summary_outcome.simps
        comma_semantic_boundary_control_of.simps
        comma_semantic_future_action_terminal_position.simps)
  have terminal_admitted:
      "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF exact_summary])
  have decoded:
      "comma_terminal_weight_decode
          (comma_terminal_weight_encode height terminal) = (height,terminal)"
    by (rule comma_terminal_weight_decode_encode[OF terminal_admitted])
  have state_admitted:
      "comma_decade_admitted (Comma_Decade ?next_phase x)"
    using next_phase x_bound by simp
  have lookup:
      "comma_semantic_decade_summary (Comma_Decade ?next_phase x) =
        Some (height,terminal)"
    using action decoded state_admitted
    by (simp add: comma_semantic_decade_summary_def)
  have event_outcome:
      "comma_semantic_boundary_event_outcome comma_semantic_decade_summary
          phase (Comma_Round_Cross (Comma_Entry 1 1 x)) =
        Some (comma_summary_outcome (height+1) terminal)"
    using lookup x_bound by simp
  have boundary:
      "comma_semantic_boundary_step comma_semantic_decade_summary q =
        Some (comma_summary_outcome (height+1) terminal)"
    using valid close event_outcome q
    by (simp add: comma_semantic_boundary_step_def)
  have control:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some (comma_semantic_boundary_control_of
          (comma_summary_outcome (height+1) terminal))"
    using boundary
    by (simp add: comma_semantic_boundary_control_step_def)
  have children:
      "comma_semantic_boundary_children comma_semantic_decade_summary q
          (comma_semantic_boundary_control_of
            (comma_summary_outcome (height+1) terminal)) =
        comma_native_boundary_children q (comma_summary_outcome (height+1) terminal)"
    using boundary
    by (simp add: comma_semantic_boundary_children_def)
  have ordered:
      "comma_native_boundary_children q (comma_summary_outcome (height+1) terminal) =
        (case terminal of
           Comma_Terminal_Fork digit \<Rightarrow>
             [(Comma_N,digit,(phase+1+height) mod 924),
              (Comma_Z,digit,(phase+1+height) mod 924)]
         | Comma_Terminal_Landmine \<Rightarrow> [])"
    using q by (cases terminal)
      (simp_all add: comma_native_boundary_children_def
        comma_summary_outcome.simps algebra_simps)
  have exact_summary_q:
      "comma_decade_exact_summary
        (Comma_Decade ((snd (snd q)+1) mod 924) x) height terminal"
    using exact_summary q by simp
  have lookup_q:
      "comma_semantic_decade_summary
        (Comma_Decade ((snd (snd q)+1) mod 924) x) = Some (height,terminal)"
    using lookup q by simp
  have ordered_q:
      "comma_native_boundary_children q (comma_summary_outcome (height+1) terminal) =
        (case terminal of
           Comma_Terminal_Fork digit \<Rightarrow>
             [(Comma_N,digit,(snd (snd q)+1+height) mod 924),
              (Comma_Z,digit,(snd (snd q)+1+height) mod 924)]
         | Comma_Terminal_Landmine \<Rightarrow> [])"
    using ordered q by (simp only: q snd_conv)
  show thesis
    by (rule that[OF x_bound height exact_summary_q terminal_position lookup_q
        boundary control children ordered_q])
qed

ML \<open>
val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
  "source-free class-to-boundary exact summary bridge"
  @{thms comma_semantic_future_initial_crossing_class_boundary};
\<close>

end
