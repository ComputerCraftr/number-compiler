theory Comma_Semantic_Future_Candidate_Provider_Closure
  imports Comma_Semantic_Future_Instance
    Comma_Semantic_Future_Candidate_Bridge
begin

text \<open>
The source normal form is compared with the checked candidate class output
once per family.  Its source-to-boundary theorem selects child IDs only
after the accumulated displacement has advanced the phase; this closure
then lifts that action comparison to the finite boundary-state provider.
\<close>

lemma comma_semantic_future_candidate_index_source_slot_exact:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_class_index q =
    924 * comma_semantic_future_initial_source_index q +
      (case q of (kind,a,phase) \<Rightarrow> phase)"
proof -
  obtain kind a phase where q: "q=(kind,a,phase)"
    by (cases q) auto
  show ?thesis
    using q
    by (cases kind)
      (simp_all add: comma_semantic_future_candidate_class_index_def
        comma_semantic_future_initial_source_index_def algebra_simps)
qed

lemma comma_semantic_future_candidate_provider_row_of_source_key:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_boundary_valid q"
    and source:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action
          (comma_semantic_future_initial_source_index q))
        (case q of (kind,a,phase) \<Rightarrow> phase) =
          Some (Some control,children)"
    and boundary_control:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some control"
    and boundary_children:
      "map comma_semantic_future_candidate_class_of
        (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
          children"
  shows "comma_semantic_future_candidate_provider_row q"
proof -
  obtain kind a phase where q: "q=(kind,a,phase)"
    by (cases q) auto
  have source_index: "comma_semantic_future_initial_source_index q<16"
    by (rule comma_semantic_future_initial_source_index_exact(1)[OF valid])
  have phase_bound: "phase<924"
    using valid q by (simp add: comma_boundary_valid_def)
  have candidate_index:
    "comma_semantic_future_candidate_class_index q =
      924*comma_semantic_future_initial_source_index q+phase"
    using comma_semantic_future_candidate_index_source_slot_exact[OF valid] q
    by (simp add: algebra_simps)
  have class_of:
    "comma_semantic_future_candidate_class_of q =
      comma_semantic_future_candidate_class_ids!
        (924*comma_semantic_future_initial_source_index q+phase)"
    using comma_semantic_future_candidate_class_of_index_exact[OF table valid]
      candidate_index by simp
  have parent_source:
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_candidate_parent_key_action
        (comma_semantic_future_initial_source_index q)) phase =
      comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action
          (comma_semantic_future_initial_source_index q)) phase"
    by (rule comma_semantic_future_candidate_parent_source_key_nf
      [OF source_index phase_bound])
  have parent:
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_candidate_parent_key_action
        (comma_semantic_future_initial_source_index q)) phase =
      Some (comma_semantic_future_candidate_class_output_key
        (comma_semantic_future_candidate_class_ids!
          (924*comma_semantic_future_initial_source_index q+phase)))"
    by (rule comma_semantic_future_candidate_parent_key_action_apply
      [OF table source_index phase_bound])
  have output_key:
    "comma_semantic_future_candidate_class_output_key
      (comma_semantic_future_candidate_class_of q) = (Some control,children)"
    using parent_source parent source class_of q by simp
  have class_id_valid:
    "comma_semantic_future_candidate_class_valid
      (comma_semantic_future_candidate_class_of q)"
    using output_key
    by (auto simp: comma_semantic_future_candidate_class_output_key_def
      comma_semantic_future_candidate_class_valid_def split: if_splits)
  have table_lengths:
    "length comma_semantic_future_candidate_controls =
      length comma_semantic_future_candidate_children"
    using table
    by (simp add: comma_semantic_future_candidate_class_table_check_def)
  have output_fact:
    "comma_semantic_future_candidate_class_output
      (comma_semantic_future_candidate_class_of q) = Some (control,children)"
    using output_key class_id_valid table_lengths
    by (auto simp: comma_semantic_future_candidate_class_output_key_def
        comma_semantic_future_candidate_class_output_def
        comma_semantic_future_candidate_class_step_def
        comma_semantic_future_candidate_class_valid_def
        comma_semantic_future_candidate_class_children_def Let_def
        split: comma_future_control.splits prod.splits if_splits)
  show ?thesis
    using output_fact boundary_control boundary_children
    by (simp add: comma_semantic_future_candidate_provider_row_def)
qed

lemma comma_semantic_future_candidate_provider_row_of_initial_nf_boundary:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_provider_row q"
proof -
  obtain J delta control ordered_children where
    action:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!
          (comma_semantic_future_initial_source_index q)) (snd (snd q)) =
        Some (Comma_Semantic_B1_CRT_Stop J delta)"
    and terminal: "J<9"
    and displacement: "delta\<le>27"
    and boundary_control:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some control"
    and control_exact:
      "control=comma_semantic_future_control_of_terminal_position J"
    and boundary_children:
      "comma_semantic_boundary_children comma_semantic_decade_summary q control =
        (case control of
           Comma_Future_Fork a \<Rightarrow>
             [(Comma_N,a,(snd (snd q)+delta) mod 924),
              (Comma_Z,a,(snd (snd q)+delta) mod 924)]
         | Comma_Future_Landmine \<Rightarrow> [])"
    and receiver:
      "comma_semantic_future_candidate_child_ids_at (Some control)
        ((snd (snd q)+delta) mod 924) = Some ordered_children"
    and receiver_ids:
      "ordered_children =
        (case control of
           Comma_Future_Fork a \<Rightarrow>
             [comma_semantic_future_candidate_class_ids!
                (924*(a-2)+((snd (snd q)+delta) mod 924)),
              comma_semantic_future_candidate_class_ids!
                (924*(8+(a-2))+((snd (snd q)+delta) mod 924))]
         | Comma_Future_Landmine \<Rightarrow> [])"
    and source:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action
          (comma_semantic_future_initial_source_index q)) (snd (snd q)) =
        Some (Some control,ordered_children)"
    by (rule comma_semantic_future_initial_nf_action_boundary_exact[OF valid])
  have target_phase: "(snd (snd q)+delta) mod 924<924" by simp
  have mapped_children:
    "map comma_semantic_future_candidate_class_of
      (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
        ordered_children"
  proof (cases control)
    case (Comma_Future_Fork target)
    have target_bounds: "2\<le>target \<and> target\<le>9"
      using control_exact terminal Comma_Future_Fork
      by (auto simp: comma_semantic_future_control_of_terminal_position_def
          split: if_splits; arith)
    let ?phase = "(snd (snd q)+delta) mod 924"
    have north_valid: "comma_boundary_valid (Comma_N,target,?phase)"
      using target_bounds target_phase
      by (simp add: comma_boundary_valid_def)
    have south_valid: "comma_boundary_valid (Comma_Z,target,?phase)"
      using target_bounds target_phase
      by (simp add: comma_boundary_valid_def)
    have north_id:
      "comma_semantic_future_candidate_class_of (Comma_N,target,?phase) =
        comma_semantic_future_candidate_class_ids!
          (924*(target-2)+?phase)"
      using comma_semantic_future_candidate_class_of_index_exact
        [OF table north_valid]
        comma_semantic_future_candidate_index_source_slot_exact[OF north_valid]
      by (simp add: comma_semantic_future_candidate_class_index_def
          comma_semantic_future_initial_source_index_def algebra_simps)
    have south_id:
      "comma_semantic_future_candidate_class_of (Comma_Z,target,?phase) =
        comma_semantic_future_candidate_class_ids!
          (924*(8+(target-2))+?phase)"
      using comma_semantic_future_candidate_class_of_index_exact
        [OF table south_valid]
        comma_semantic_future_candidate_index_source_slot_exact[OF south_valid]
      by (simp add: comma_semantic_future_candidate_class_index_def
          comma_semantic_future_initial_source_index_def algebra_simps)
    show ?thesis
      using boundary_children receiver_ids north_id south_id
        Comma_Future_Fork by simp
  next
    case Comma_Future_Landmine
    then show ?thesis
      using boundary_children receiver_ids by simp
  qed
  show ?thesis
    by (rule comma_semantic_future_candidate_provider_row_of_source_key
      [OF table valid source boundary_control mapped_children])
qed

lemma comma_semantic_future_candidate_provider_check_of_valid_rows:
  assumes rows:
    "\<And>q. comma_boundary_valid q \<Longrightarrow>
      comma_semantic_future_candidate_provider_row q"
  shows "comma_semantic_future_candidate_provider_check"
  using rows
  by (auto simp: comma_semantic_future_candidate_provider_check_def
      comma_semantic_future_candidate_provider_kind_check_def
      comma_semantic_future_candidate_provider_index_check_def
      comma_semantic_future_candidate_provider_cell_def
      comma_boundary_valid_def list_all_iff set_upt)

lemma comma_semantic_future_candidate_provider_check_from_table:
  assumes table: "comma_semantic_future_candidate_class_table_check"
  shows "comma_semantic_future_candidate_provider_check"
  by (rule comma_semantic_future_candidate_provider_check_of_valid_rows)
    (auto intro: comma_semantic_future_candidate_provider_row_of_initial_nf_boundary
      [OF table])

lemma comma_semantic_future_candidate_provider_check_checked:
  "comma_semantic_future_candidate_provider_check"
  by (rule comma_semantic_future_candidate_provider_check_from_table
      [OF comma_semantic_future_candidate_class_table_checked])

lemma comma_semantic_concrete_future_rank_check:
  "comma_semantic_rank_check comma_boundary_valid
    comma_semantic_concrete_future_rank
    (comma_semantic_boundary_children comma_semantic_decade_summary)
    (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
  by (rule comma_semantic_future_provider_check_lifts_rank
      [OF comma_semantic_future_candidate_provider_check_checked])

ML \<open>
  val published = @{thms
    comma_semantic_future_candidate_index_source_slot_exact
    comma_semantic_future_candidate_provider_row_of_source_key
    comma_semantic_future_candidate_provider_row_of_initial_nf_boundary
    comma_semantic_future_candidate_provider_check_of_valid_rows
    comma_semantic_future_candidate_provider_check_from_table
    comma_semantic_future_candidate_provider_check_checked
    comma_semantic_concrete_future_rank_check}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future source-key to candidate-provider closure" published
\<close>

end
