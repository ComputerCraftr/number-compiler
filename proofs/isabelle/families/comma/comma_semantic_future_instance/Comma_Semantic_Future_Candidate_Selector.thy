theory Comma_Semantic_Future_Candidate_Selector
  imports Comma_Semantic_Future_Candidate_Integrity
begin

text \<open>
The candidate source-ID vector is a 16-family input artifact with 924 phases
per family.  Its selector specification uses a compact four-axis CRT tree;
the publication compiler interns and normalizes all family trees before it
serializes them.  This theory proves the common slice/index law once, so the
consumer does not emit a separate phase-cell proof for each input label.
\<close>

definition comma_semantic_future_candidate_id_family_slice ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "comma_semantic_future_candidate_id_family_slice values family =
    take 924 (drop (924*family) values)"

definition comma_semantic_future_candidate_id_selector_specs ::
    "nat list \<Rightarrow> nat comma_semantic_weighted_crt_dag list" where
  "comma_semantic_future_candidate_id_selector_specs values =
    map (\<lambda>family. comma_weighted_crt_selector_aux [0,1,2,3] 924 0
      (comma_semantic_future_candidate_id_family_slice values family))
      [0..<16]"

definition comma_semantic_future_candidate_child_id_pair_at ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "comma_semantic_future_candidate_child_id_pair_at values target_family phase =
    (if length values=14784 \<and> target_family<8 \<and> phase<924 then
       Some (values!(924*target_family+phase),
         values!(924*(8+target_family)+phase))
     else None)"

definition comma_semantic_future_candidate_id_selector_spec_at ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_id_selector_spec_at values phase family =
    (if length values=14784 \<and> phase<924 \<and> family<16 then
       Some (values!(924*family+phase))
     else None)"

lemma comma_semantic_future_candidate_id_family_slice_length:
  assumes extent: "length values=14784"
    and family: "family<16"
  shows "length (comma_semantic_future_candidate_id_family_slice values family)=924"
proof -
  have start: "924*family \<le> length values"
    using extent family by (simp; nlinarith)
  have remaining: "924 \<le> length (drop (924*family) values)"
    using extent family by (simp; nlinarith)
  show ?thesis
    using remaining by (simp add: comma_semantic_future_candidate_id_family_slice_def)
qed

lemma comma_semantic_future_candidate_id_family_slice_nth:
  assumes extent: "length values=14784"
    and family: "family<16"
    and phase: "phase<924"
  shows "comma_semantic_future_candidate_id_family_slice values family ! phase =
    values ! (924*family+phase)"
proof -
  have family_start: "924*family < length values"
    using extent family by (simp; nlinarith)
  have index_bound: "924*family+phase < length values"
    using extent family phase by (simp; nlinarith)
  show ?thesis
    using family_start phase index_bound
    by (simp add: comma_semantic_future_candidate_id_family_slice_def)
qed

lemma comma_semantic_future_candidate_id_selector_spec_length:
  "length (comma_semantic_future_candidate_id_selector_specs values)=16"
  by (simp add: comma_semantic_future_candidate_id_selector_specs_def)

lemma comma_semantic_future_candidate_id_selector_spec_nth:
  assumes family: "family<16"
  shows "comma_semantic_future_candidate_id_selector_specs values ! family =
    comma_weighted_crt_selector_aux [0,1,2,3] 924 0
      (comma_semantic_future_candidate_id_family_slice values family)"
  using family
  by (simp add: comma_semantic_future_candidate_id_selector_specs_def)

lemma comma_semantic_future_candidate_id_selector_spec_apply:
  assumes extent: "length values=14784"
    and family: "family<16"
    and phase: "phase<924"
  shows "comma_weighted_crt_eval
      (comma_semantic_future_candidate_id_selector_specs values ! family) phase =
    Some (values!(924*family+phase),0)"
proof -
  have slice_length:
    "length (comma_semantic_future_candidate_id_family_slice values family)=924"
    by (rule comma_semantic_future_candidate_id_family_slice_length[OF extent family])
  have axes: "\<forall>axis\<in>set ([0,1,2,3]::nat list). axis<4" by simp
  have selected:
    "comma_weighted_crt_eval
      (comma_weighted_crt_selector_aux [0,1,2,3] 924 0
        (comma_semantic_future_candidate_id_family_slice values family)) phase =
      Some (comma_semantic_future_candidate_id_family_slice values family ! phase,0)"
    using comma_weighted_crt_selector_aux_exact[OF axes,
      of 924 0 "comma_semantic_future_candidate_id_family_slice values family" phase]
      slice_length phase
    by simp
  have nth:
    "comma_semantic_future_candidate_id_family_slice values family ! phase =
      values!(924*family+phase)"
    by (rule comma_semantic_future_candidate_id_family_slice_nth
      [OF extent family phase])
  show ?thesis
    using selected nth family
    by (simp add: comma_semantic_future_candidate_id_selector_spec_nth)
qed

lemma comma_semantic_future_candidate_id_selector_spec_action_apply:
  assumes extent: "length values=14784"
    and family: "family<16"
    and phase: "phase<924"
  shows "comma_weighted_crt_apply
      (0,comma_semantic_future_candidate_id_selector_specs values ! family) phase =
    Some (values!(924*family+phase),0)"
proof -
  have selected:
    "comma_weighted_crt_eval
        (comma_semantic_future_candidate_id_selector_specs values ! family) phase =
      Some (values!(924*family+phase),0)"
    by (rule comma_semantic_future_candidate_id_selector_spec_apply
      [OF extent family phase])
  show ?thesis
    using selected by (simp add: comma_weighted_crt_apply_def)
qed

lemma comma_semantic_future_candidate_child_id_pair_at_exact:
  assumes extent: "length values=14784"
    and target: "target_family<8"
    and phase: "phase<924"
  shows "comma_semantic_future_candidate_child_id_pair_at
      values target_family phase =
    Some (values!(924*target_family+phase),
      values!(924*(8+target_family)+phase))"
  using extent target phase
  by (simp add: comma_semantic_future_candidate_child_id_pair_at_def)

lemma comma_semantic_future_candidate_child_id_pair_at_rejects_bad_coordinates:
  "target_family\<ge>8 \<Longrightarrow>
      comma_semantic_future_candidate_child_id_pair_at values target_family phase=None"
  "phase\<ge>924 \<Longrightarrow>
      comma_semantic_future_candidate_child_id_pair_at values target_family phase=None"
  "length values\<noteq>14784 \<Longrightarrow>
      comma_semantic_future_candidate_child_id_pair_at values target_family phase=None"
  by (auto simp: comma_semantic_future_candidate_child_id_pair_at_def)

lemma comma_semantic_future_candidate_id_selector_spec_at_exact:
  assumes extent: "length values=14784"
    and family: "family<16"
    and phase: "phase<924"
  shows "comma_semantic_future_candidate_id_selector_spec_at values phase family =
    Some (values!(924*family+phase))"
  using extent family phase
  by (simp add: comma_semantic_future_candidate_id_selector_spec_at_def)

lemma comma_semantic_future_candidate_id_selector_spec_at_rejects_bad_coordinates:
  "phase<924 \<and> family<16 \<and> length values=14784 \<Longrightarrow>
      comma_semantic_future_candidate_id_selector_spec_at values phase family \<noteq> None"
  "phase\<ge>924 \<Longrightarrow>
      comma_semantic_future_candidate_id_selector_spec_at values phase family = None"
  "family\<ge>16 \<Longrightarrow>
      comma_semantic_future_candidate_id_selector_spec_at values phase family = None"
  "length values\<noteq>14784 \<Longrightarrow>
      comma_semantic_future_candidate_id_selector_spec_at values phase family = None"
  by (auto simp: comma_semantic_future_candidate_id_selector_spec_at_def)

lemma comma_semantic_future_candidate_id_selector_spec_boundary_fixtures:
  assumes extent: "length values=14784"
  shows
    "comma_semantic_future_candidate_id_family_slice values 0 ! 0 = values!0"
    "comma_semantic_future_candidate_id_family_slice values 1 ! 0 = values!924"
    "comma_semantic_future_candidate_id_family_slice values 15 ! 0 = values!13860"
    "comma_semantic_future_candidate_id_family_slice values 0 ! 923 = values!923"
    "comma_semantic_future_candidate_id_family_slice values 1 ! 923 = values!1847"
    "comma_semantic_future_candidate_id_family_slice values 15 ! 923 = values!14783"
  using comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 0 0]
    comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 1 0]
    comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 15 0]
    comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 0 923]
    comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 1 923]
    comma_semantic_future_candidate_id_family_slice_nth[OF extent, of 15 923]
  by simp_all

ML_file "semantic_future_candidate_selector.ML"

local_setup \<open>Comma_Semantic_Future_Candidate_Selector_Publisher.publish\<close>

definition comma_semantic_future_candidate_id_selector_action_at ::
    "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_id_selector_action_at phase family =
    (if phase<924 \<and> family<16 \<and>
        length comma_semantic_future_candidate_id_selector_actions=16 \<and>
        comma_weighted_crt_shape 0
          (snd (comma_semantic_future_candidate_id_selector_actions!family)) then
       (case comma_weighted_crt_apply
          (comma_semantic_future_candidate_id_selector_actions!family) phase of
          Some (candidate_id,0) \<Rightarrow> Some candidate_id
        | _ \<Rightarrow> None)
     else None)"

lemma comma_semantic_future_candidate_id_selector_action_at_exact:
  assumes phase: "phase<924"
    and family: "family<16"
  shows "comma_semantic_future_candidate_id_selector_action_at phase family =
    Some (comma_semantic_future_candidate_class_ids!(924*family+phase))"
proof -
  have family_rows:
    "list_all (\<lambda>family. \<forall>phase<924.
      comma_weighted_crt_apply
        (comma_semantic_future_candidate_id_selector_actions!family) phase =
          Some (comma_semantic_future_candidate_class_ids!(924*family+phase),0))
      [0..<16]"
    by (rule comma_semantic_future_candidate_id_selector_actions_refine)
  have action_shape:
    "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
      comma_semantic_future_candidate_id_selector_actions"
    by (rule comma_semantic_future_candidate_id_selector_actions_shape)
  have action_length:
    "length comma_semantic_future_candidate_id_selector_actions=16"
    by (rule comma_semantic_future_candidate_id_selector_actions_length)
  have member: "family\<in>set [0..<16]" using family by simp
  have row:
    "comma_weighted_crt_apply
        (comma_semantic_future_candidate_id_selector_actions!family) phase =
      Some (comma_semantic_future_candidate_class_ids!(924*family+phase),0)"
    using family_rows member phase by (auto simp: list_all_iff)
  have shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_candidate_id_selector_actions!family))"
    using action_shape action_length member by (auto simp: list_all_iff)
  show ?thesis
    using phase family action_length shape row
    by (simp add: comma_semantic_future_candidate_id_selector_action_at_def)
qed

definition comma_semantic_future_candidate_child_id_pair_projection ::
    "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "comma_semantic_future_candidate_child_id_pair_projection target_family phase =
    (if target_family<8 \<and> phase<924 then
       (case (comma_semantic_future_candidate_id_selector_action_at phase target_family,
              comma_semantic_future_candidate_id_selector_action_at phase
                (8+target_family)) of
          (Some north,Some south) \<Rightarrow> Some (north,south)
        | _ \<Rightarrow> None)
     else None)"

lemma comma_semantic_future_candidate_child_id_pair_projection_exact:
  assumes phase: "phase<924" and target: "target_family<8"
  shows "comma_semantic_future_candidate_child_id_pair_projection target_family phase =
    Some (comma_semantic_future_candidate_class_ids!(924*target_family+phase),
      comma_semantic_future_candidate_class_ids!(924*(8+target_family)+phase))"
proof -
  have north:
    "comma_semantic_future_candidate_id_selector_action_at phase target_family =
      Some (comma_semantic_future_candidate_class_ids!(924*target_family+phase))"
    by (rule comma_semantic_future_candidate_id_selector_action_at_exact
      [OF phase target])
  have south_family: "8+target_family<16" using target by arith
  have south:
    "comma_semantic_future_candidate_id_selector_action_at phase (8+target_family) =
      Some (comma_semantic_future_candidate_class_ids!
        (924*(8+target_family)+phase))"
    by (rule comma_semantic_future_candidate_id_selector_action_at_exact
      [OF phase south_family])
  show ?thesis using north south phase target
    by (simp add: comma_semantic_future_candidate_child_id_pair_projection_def)
qed

ML \<open>
  val published = @{thms
    comma_semantic_future_candidate_class_ids_def
    comma_semantic_future_candidate_controls_def
    comma_semantic_future_candidate_children_def
    comma_semantic_future_candidate_class_ids_length
    comma_semantic_future_candidate_id_selector_actions_def
    comma_semantic_future_candidate_id_selector_actions_refine
    comma_semantic_future_candidate_id_selector_actions_shape
    comma_semantic_future_candidate_id_selector_actions_wellformed
    comma_semantic_future_candidate_id_selector_actions_length
    comma_semantic_future_candidate_id_selector_spec_action_apply
    comma_semantic_future_candidate_child_id_pair_at_exact
    comma_semantic_future_candidate_child_id_pair_at_rejects_bad_coordinates
    comma_semantic_future_candidate_id_selector_spec_boundary_fixtures
    comma_semantic_future_candidate_id_selector_spec_at_rejects_bad_coordinates
    comma_semantic_future_candidate_id_selector_action_at_exact
    comma_semantic_future_candidate_child_id_pair_projection_exact}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Published future candidate ID selector actions and source-family transport"
    published
\<close>

end
