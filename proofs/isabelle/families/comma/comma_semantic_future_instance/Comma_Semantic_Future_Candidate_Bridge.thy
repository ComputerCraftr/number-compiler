theory Comma_Semantic_Future_Candidate_Bridge
  imports Comma_Semantic_Future_Source_NF_Bridge
    Comma_Semantic_Future_Candidate_Provider_NF
begin

theorem comma_semantic_future_initial_nf_action_boundary_exact:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains J delta control ordered_children where
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
  obtain J delta control where graph_apply:
      "comma_weighted_crt_apply (comma_semantic_graph_initial_nf_actions!?slot)
        ?phase = Some (Comma_Semantic_B1_CRT_Stop J delta)"
    and future_apply:
      "comma_weighted_crt_apply (comma_semantic_future_initial_nf_dags!?slot)
        ?phase = Some (Comma_Semantic_B1_CRT_Stop J delta)"
    and J: "J<9"
    and delta: "delta\<le>27"
    and control_step:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some control"
    and control_exact:
      "control=comma_semantic_future_control_of_terminal_position J"
    and children:
      "comma_semantic_boundary_children comma_semantic_decade_summary q control =
        (case control of
           Comma_Future_Fork a \<Rightarrow>
             [(Comma_N,a,(?phase+delta) mod 924),
              (Comma_Z,a,(?phase+delta) mod 924)]
         | Comma_Future_Landmine \<Rightarrow> [])"
    by (rule comma_semantic_future_initial_nf_direct_boundary_exact[OF valid])
  obtain source_J source_delta ordered_children where source_apply:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!?slot) ?phase =
          Some (Comma_Semantic_B1_CRT_Stop source_J source_delta)"
    and source_J_bound: "source_J<9"
    and source_delta_bound: "source_delta\<le>27"
    and receiver:
      "comma_semantic_future_candidate_child_ids_at
        (Some (comma_semantic_future_control_of_terminal_position source_J))
        ((?phase+source_delta) mod 924) = Some ordered_children"
    and key:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action ?slot) ?phase =
          Some (Some (comma_semantic_future_control_of_terminal_position source_J),
            ordered_children)"
    by (rule comma_semantic_future_initial_nf_source_key_action_result
      [OF slot_bound phase_bound])
  have source_eq: "source_J=J" "source_delta=delta"
    using graph_apply source_apply by auto
  have receiver_exact:
    "comma_semantic_future_candidate_child_ids_at
      (Some control) ((?phase+delta) mod 924) = Some ordered_children"
    using receiver control_exact source_eq by simp
  have ordered_shape:
    "ordered_children =
      (case control of
         Comma_Future_Fork a \<Rightarrow>
           [comma_semantic_future_candidate_class_ids!
              (924*(a-2)+((?phase+delta) mod 924)),
            comma_semantic_future_candidate_class_ids!
              (924*(8+(a-2))+((?phase+delta) mod 924))]
       | Comma_Future_Landmine \<Rightarrow> [])"
    using receiver_exact control_exact J
    by (cases control)
      (auto simp: comma_semantic_future_candidate_child_ids_fork_exact
        comma_semantic_future_candidate_child_ids_landmine)
  have key_exact:
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action ?slot) ?phase =
        Some (Some control,ordered_children)"
    using key control_exact source_eq by simp
  show thesis
    by (rule that[OF future_apply J delta control_step control_exact children
        receiver_exact ordered_shape key_exact])
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_future_initial_nf_direct_boundary_exact
      comma_semantic_future_initial_nf_action_boundary_exact})
  then ()
  else error "Comma_Semantic_Future_Candidate_Bridge oracle audit failed"
\<close>

end
