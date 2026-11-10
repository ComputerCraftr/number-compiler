theory Comma_CRT_MDD_Frontier_DAG
  imports Comma_Continue_Frontier_Certificate
begin

text \<open>
The Continue-only frontier is checked from finite root vectors and their
structural root-shift/bind certificates.  This relation is not itself the
executable raw-data parser: it is the exact proposition established after
the operation references are checked and replayed.  No terminal identity is
encoded here; public full-action and exact B32 contracts remain separate.
\<close>

definition comma_crt_mdd_frontier_vector_exact ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow>
      ((nat \<times> nat) \<Rightarrow> bool) \<Rightarrow> bool" where
  "comma_crt_mdd_frontier_vector_exact radices nodes roots predicate \<longleftrightarrow>
    length roots = 46 \<and>
    (\<forall>phase<924. \<forall>cid<46.
      comma_crt_mdd_eval_phase radices nodes phase (roots ! cid) =
        Some (if predicate (phase,cid) then 1 else 0))"

definition comma_crt_mdd_frontier_preimage_certificates ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow>
      nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots future_roots
      shifted_roots preimage_roots false_root \<longleftrightarrow>
    length action_roots = 46 \<and> length future_roots = 46 \<and>
    length shifted_roots = 46 \<and> length preimage_roots = 46 \<and>
    list_all (\<lambda>target. comma_crt_mdd_root_shift_certificate radices nodes 1
      (future_roots ! target) (shifted_roots ! target)) [0..<46] \<and>
    list_all (\<lambda>cid. comma_crt_mdd_bind_certificate radices nodes
      (zip [1..<Suc (length shifted_roots)] shifted_roots) false_root
      (action_roots ! cid) (preimage_roots ! cid)) [0..<46]"

lemma comma_crt_mdd_frontier_preimage_certificates_shiftD:
  assumes data: "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots
      future_roots shifted_roots preimage_roots false_root"
    and target: "target < 46"
  shows "comma_crt_mdd_root_shift_certificate radices nodes 1
    (future_roots ! target) (shifted_roots ! target)"
proof -
  have checked:
    "list_all (\<lambda>target. comma_crt_mdd_root_shift_certificate radices nodes 1
      (future_roots ! target) (shifted_roots ! target)) [0..<46]"
    using data unfolding comma_crt_mdd_frontier_preimage_certificates_def by blast
  show ?thesis
    by (rule comma_crt_mdd_indexed_allD[OF checked target])
qed

lemma comma_crt_mdd_frontier_preimage_certificates_bindD:
  assumes data: "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots
      future_roots shifted_roots preimage_roots false_root"
    and cid: "cid < 46"
  shows "comma_crt_mdd_bind_certificate radices nodes
    (zip [1..<Suc (length shifted_roots)] shifted_roots) false_root
    (action_roots ! cid) (preimage_roots ! cid)"
proof -
  have checked:
    "list_all (\<lambda>cid. comma_crt_mdd_bind_certificate radices nodes
      (zip [1..<Suc (length shifted_roots)] shifted_roots) false_root
      (action_roots ! cid) (preimage_roots ! cid)) [0..<46]"
    using data unfolding comma_crt_mdd_frontier_preimage_certificates_def by blast
  show ?thesis
    by (rule comma_crt_mdd_indexed_allD[OF checked cid])
qed

lemma comma_crt_mdd_frontier_vector_preimage_sound:
  fixes step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and period_divides:
      "\<And>axis. axis < length radices \<Longrightarrow> radices ! axis dvd 924"
    and action_exact:
      "\<And>phase cid. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase (action_roots ! cid) =
          (case step phase cid of
            Comma_Phase_Class_Continue next_phase target \<Rightarrow> Some (Suc target)
          | _ \<Rightarrow> Some 0)"
    and target_bound:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        step phase cid = Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        target < 46"
    and one_tick:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        step phase cid = Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        next_phase = (phase+1) mod 924"
    and false_exact:
      "\<And>phase. phase < 924 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase false_root = Some 0"
    and data: "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots
      future_roots shifted_roots preimage_roots false_root"
  shows "\<forall>phase<924. \<forall>cid<46.
    comma_crt_mdd_eval_phase radices nodes phase (preimage_roots ! cid) =
      (case step phase cid of
        Comma_Phase_Class_Continue next_phase target \<Rightarrow>
          comma_crt_mdd_eval_phase radices nodes next_phase (future_roots ! target)
      | _ \<Rightarrow> Some 0)"
proof (intro allI impI)
  fix phase :: nat
  assume phase: "phase < 924"
  fix cid :: nat
  assume cid: "cid < 46"
    let ?mapping = "zip [1..<Suc (length shifted_roots)] shifted_roots"
    have result_bound: "length shifted_roots = 46"
      using data unfolding comma_crt_mdd_frontier_preimage_certificates_def by blast
    have action_evaluation:
      "comma_crt_mdd_eval_phase radices nodes phase (action_roots ! cid) =
        (case step phase cid of
          Comma_Phase_Class_Continue next_phase target \<Rightarrow> Some (Suc target)
        | _ \<Rightarrow> Some 0)"
      by (rule action_exact[OF phase cid])
    have bind_certificate:
      "comma_crt_mdd_bind_certificate radices nodes ?mapping false_root
        (action_roots ! cid) (preimage_roots ! cid)"
      by (rule comma_crt_mdd_frontier_preimage_certificates_bindD[OF data cid])
    have fallback_evaluation:
      "comma_crt_mdd_eval_phase radices nodes phase false_root = Some 0"
      by (rule false_exact[OF phase])
    have zero_unmapped: "map_of ?mapping 0 = None"
      by (rule comma_frontier_successor_map_zero)
    have target_mapped: "\<And>target. target < 46 \<Longrightarrow>
        map_of ?mapping (Suc target) = Some (shifted_roots ! target)"
    proof -
      fix target :: nat assume target: "target < 46"
      have "target < length shifted_roots" using target result_bound by simp
      then show "map_of ?mapping (Suc target) = Some (shifted_roots ! target)"
        by (rule comma_frontier_successor_map)
    qed
    have shifted_evaluation: "\<And>target. target < 46 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase (shifted_roots ! target) =
          comma_crt_mdd_eval_phase radices nodes (phase+1) (future_roots ! target)"
    proof -
      fix target :: nat assume target: "target < 46"
      have shift_certificate:
        "comma_crt_mdd_root_shift_certificate radices nodes 1
          (future_roots ! target) (shifted_roots ! target)"
        by (rule comma_crt_mdd_frontier_preimage_certificates_shiftD[OF data target])
      show "comma_crt_mdd_eval_phase radices nodes phase (shifted_roots ! target) =
          comma_crt_mdd_eval_phase radices nodes (phase+1) (future_roots ! target)"
        by (rule comma_crt_mdd_root_shift_certificate_eval_phase
          [OF wellformed shift_certificate])
    qed
    show "comma_crt_mdd_eval_phase radices nodes phase (preimage_roots ! cid) =
        (case step phase cid of
          Comma_Phase_Class_Continue next_phase target \<Rightarrow>
            comma_crt_mdd_eval_phase radices nodes next_phase (future_roots ! target)
        | _ \<Rightarrow> Some 0)"
    proof (rule comma_crt_mdd_frontier_bind_step
        [where mapping="?mapping"
          and shifted_root="\<lambda>target. shifted_roots ! target"
          and previous_root="\<lambda>target. future_roots ! target"])
      show "comma_crt_mdd_table_wellformed radices nodes"
        by (rule wellformed)
      show "comma_crt_mdd_bind_certificate radices nodes ?mapping false_root
          (action_roots ! cid) (preimage_roots ! cid)"
        by (rule bind_certificate)
      show "comma_crt_mdd_eval_phase radices nodes phase (action_roots ! cid) =
          (case step phase cid of
            Comma_Phase_Class_Continue next_phase target \<Rightarrow> Some (Suc target)
          | _ \<Rightarrow> Some 0)"
        by (rule action_evaluation)
      show "comma_crt_mdd_eval_phase radices nodes phase false_root = Some 0"
        by (rule fallback_evaluation)
      show "map_of ?mapping 0 = None"
        by (rule zero_unmapped)
      show "\<And>target. target < 46 \<Longrightarrow>
          map_of ?mapping (Suc target) = Some (shifted_roots ! target)"
        by (rule target_mapped)
      show "\<And>next_phase target. step phase cid =
          Comma_Phase_Class_Continue next_phase target \<Longrightarrow> target < 46"
        by (rule target_bound[OF phase cid])
      show "\<And>next_phase target. step phase cid =
          Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
          next_phase = (phase+1) mod 924"
        by (rule one_tick[OF phase cid])
      show "\<And>target. target < 46 \<Longrightarrow>
          comma_crt_mdd_eval_phase radices nodes phase (shifted_roots ! target) =
            comma_crt_mdd_eval_phase radices nodes (phase+1) (future_roots ! target)"
        by (rule shifted_evaluation)
      show "\<And>axis. axis < length radices \<Longrightarrow> radices ! axis dvd 924"
        by (rule period_divides)
    qed
qed

definition comma_crt_mdd_frontier_chain_certificates ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow>
      nat list \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> bool" where
  "comma_crt_mdd_frontier_chain_certificates radices nodes action_roots false_root
      layers shifted_layers \<longleftrightarrow>
    length layers = 25 \<and> length shifted_layers = 24 \<and>
    list_all (\<lambda>roots. length roots = 46) layers \<and>
    list_all (\<lambda>roots. length roots = 46) shifted_layers \<and>
    list_all (\<lambda>depth. comma_crt_mdd_frontier_preimage_certificates radices nodes
      action_roots (layers ! depth) (shifted_layers ! depth) (layers ! Suc depth)
      false_root) [0..<24]"

lemma comma_crt_mdd_frontier_chain_edge:
  assumes chain: "comma_crt_mdd_frontier_chain_certificates radices nodes action_roots
      false_root layers shifted_layers"
    and depth: "depth < 24"
  shows "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots
    (layers ! depth) (shifted_layers ! depth) (layers ! Suc depth) false_root"
proof -
  have checked:
    "list_all (\<lambda>depth. comma_crt_mdd_frontier_preimage_certificates radices nodes
      action_roots (layers ! depth) (shifted_layers ! depth) (layers ! Suc depth)
      false_root) [0..<24]"
    using chain unfolding comma_crt_mdd_frontier_chain_certificates_def by blast
  show ?thesis
    by (rule comma_crt_mdd_indexed_allD[OF checked depth])
qed

definition comma_crt_mdd_frontier_bad_at ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_crt_mdd_frontier_bad_at radices nodes layers depth phase cid \<longleftrightarrow>
    comma_crt_mdd_eval_phase radices nodes phase (layers ! depth ! cid) = Some 1"

lemma comma_crt_mdd_frontier_bad_at_preimage:
  fixes step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
  assumes evaluation:
    "comma_crt_mdd_eval_phase radices nodes phase (layers ! Suc depth ! cid) =
      (case step phase cid of
        Comma_Phase_Class_Continue next_phase target \<Rightarrow>
          comma_crt_mdd_eval_phase radices nodes next_phase (layers ! depth ! target)
      | _ \<Rightarrow> Some 0)"
  shows "comma_crt_mdd_frontier_bad_at radices nodes layers (Suc depth) phase cid =
    (case step phase cid of
      Comma_Phase_Class_Continue next_phase target \<Rightarrow>
        comma_crt_mdd_frontier_bad_at radices nodes layers depth next_phase target
    | _ \<Rightarrow> False)"
  using evaluation by (cases "step phase cid")
    (auto simp: comma_crt_mdd_frontier_bad_at_def)

lemma comma_crt_mdd_frontier_chain_bad_successor:
  fixes step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and period_divides:
      "\<And>axis. axis < length radices \<Longrightarrow> radices ! axis dvd 924"
    and action_exact:
      "\<And>phase cid. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase (action_roots ! cid) =
          (case step phase cid of
            Comma_Phase_Class_Continue next_phase target \<Rightarrow> Some (Suc target)
          | _ \<Rightarrow> Some 0)"
    and target_bound:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        step phase cid = Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        target < 46"
    and one_tick:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        step phase cid = Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        next_phase = (phase+1) mod 924"
    and false_exact:
      "\<And>phase. phase < 924 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase false_root = Some 0"
    and chain: "comma_crt_mdd_frontier_chain_certificates radices nodes action_roots
      false_root layers shifted_layers"
  shows "depth < 24 \<Longrightarrow> phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
    comma_crt_mdd_frontier_bad_at radices nodes layers (Suc depth) phase cid =
      (case step phase cid of
        Comma_Phase_Class_Continue next_phase target \<Rightarrow>
          comma_crt_mdd_frontier_bad_at radices nodes layers depth next_phase target
      | _ \<Rightarrow> False)"
proof -
  assume depth: "depth < 24" and phase: "phase < 924" and cid: "cid < 46"
  have edge:
    "comma_crt_mdd_frontier_preimage_certificates radices nodes action_roots
      (layers ! depth) (shifted_layers ! depth) (layers ! Suc depth) false_root"
    by (rule comma_crt_mdd_frontier_chain_edge[OF chain depth])
  have preimage:
    "\<forall>phase<924. \<forall>cid<46.
      comma_crt_mdd_eval_phase radices nodes phase (layers ! Suc depth ! cid) =
        (case step phase cid of
          Comma_Phase_Class_Continue next_phase target \<Rightarrow>
            comma_crt_mdd_eval_phase radices nodes next_phase (layers ! depth ! target)
        | _ \<Rightarrow> Some 0)"
    by (rule comma_crt_mdd_frontier_vector_preimage_sound
      [OF wellformed period_divides action_exact target_bound one_tick false_exact edge])
  have evaluation:
    "comma_crt_mdd_eval_phase radices nodes phase (layers ! Suc depth ! cid) =
      (case step phase cid of
        Comma_Phase_Class_Continue next_phase target \<Rightarrow>
          comma_crt_mdd_eval_phase radices nodes next_phase (layers ! depth ! target)
      | _ \<Rightarrow> Some 0)"
    using preimage phase cid by blast
  show "comma_crt_mdd_frontier_bad_at radices nodes layers (Suc depth) phase cid =
      (case step phase cid of
        Comma_Phase_Class_Continue next_phase target \<Rightarrow>
          comma_crt_mdd_frontier_bad_at radices nodes layers depth next_phase target
      | _ \<Rightarrow> False)"
    by (rule comma_crt_mdd_frontier_bad_at_preimage
      [where radices=radices and nodes=nodes and layers=layers and depth=depth
        and phase=phase and cid=cid and step=step, OF evaluation])
qed

theorem comma_crt_mdd_frontier_dag_direct_image:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and period_divides:
      "\<And>axis. axis < length radices \<Longrightarrow> radices ! axis dvd 924"
    and action_exact:
      "\<And>phase cid. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase (action_roots ! cid) =
          (case comma_semantic_phase_program_class_step phase cid of
            Comma_Phase_Class_Continue next_phase target \<Rightarrow> Some (Suc target)
          | _ \<Rightarrow> Some 0)"
    and target_bound:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        comma_semantic_phase_program_class_step phase cid =
          Comma_Phase_Class_Continue next_phase target \<Longrightarrow> target < 46"
    and one_tick:
      "\<And>phase cid next_phase target. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
        comma_semantic_phase_program_class_step phase cid =
          Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        next_phase = (phase+1) mod 924"
    and false_exact:
      "\<And>phase. phase < 924 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase false_root = Some 0"
    and base_exact:
      "comma_crt_mdd_frontier_vector_exact radices nodes (layers ! 0)
        (\<lambda>(phase,cid). (phase,cid) \<notin> comma_continue24_endpoints)"
    and chain: "comma_crt_mdd_frontier_chain_certificates radices nodes action_roots
      false_root layers shifted_layers"
    and empty24: "\<And>phase cid. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (layers ! 24 ! cid) = Some 0"
  shows "comma_continue24_direct_image_certificate"
proof -
  let ?valid = comma_semantic_phase_class_valid
  let ?bad = "comma_crt_mdd_frontier_bad_at radices nodes layers"
  have closed: "\<And>phase cid next_phase target. ?valid phase cid \<Longrightarrow>
      comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
      ?valid next_phase target"
    by (rule comma_semantic_phase_program_class_step_continue_closed(2))
  have initial: "\<And>phase cid. ?valid phase cid \<Longrightarrow>
      ?bad 0 phase cid = ((phase,cid) \<notin> comma_continue24_endpoints)"
    using base_exact
    by (auto simp: comma_crt_mdd_frontier_vector_exact_def
        comma_crt_mdd_frontier_bad_at_def comma_semantic_phase_class_valid_def)
  have successor: "\<And>depth phase cid. depth < 24 \<Longrightarrow> ?valid phase cid \<Longrightarrow>
      ?bad (Suc depth) phase cid =
        (case comma_semantic_phase_program_class_step phase cid of
          Comma_Phase_Class_Continue next_phase target \<Rightarrow> ?bad depth next_phase target
        | _ \<Rightarrow> False)"
  proof -
    fix depth phase cid :: nat
    assume depth: "depth < 24" and valid: "?valid phase cid"
    have bounds: "phase < 924" "cid < 46"
      using valid by (auto simp: comma_semantic_phase_class_valid_def)
    show "?bad (Suc depth) phase cid =
        (case comma_semantic_phase_program_class_step phase cid of
          Comma_Phase_Class_Continue next_phase target \<Rightarrow> ?bad depth next_phase target
        | _ \<Rightarrow> False)"
      by (rule comma_crt_mdd_frontier_chain_bad_successor
        [OF wellformed period_divides action_exact target_bound one_tick false_exact chain
          depth bounds(1) bounds(2)])
  qed
  have empty: "\<And>phase cid. ?valid phase cid \<Longrightarrow> \<not> ?bad 24 phase cid"
    using empty24 by (auto simp: comma_crt_mdd_frontier_bad_at_def
        comma_semantic_phase_class_valid_def)
  have image:
    "\<And>phase cid terminal. phase < 924 \<Longrightarrow> cid < 46 \<Longrightarrow>
      comma_phase_class_continue_power comma_semantic_phase_program_class_step 24
        (phase,cid) = Some terminal \<Longrightarrow>
      terminal \<in> comma_continue24_endpoints"
  proof -
    fix phase cid :: nat
    fix terminal :: "nat \<times> nat"
    assume phase: "phase < 924" and cid: "cid < 46"
      and reached: "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,cid) = Some terminal"
    have valid: "?valid phase cid"
      using phase cid by (simp add: comma_semantic_phase_class_valid_def)
    show "terminal \<in> comma_continue24_endpoints"
      by (rule comma_continue_frontier_empty_implies_image
        [where step=comma_semantic_phase_program_class_step
          and valid=comma_semantic_phase_class_valid
          and bad="comma_crt_mdd_frontier_bad_at radices nodes layers"
          and accepted=comma_continue24_endpoints and limit=24,
          OF closed initial successor empty valid reached])
  qed
  show ?thesis
    by (rule comma_continue24_image_implies_direct_certificate[OF image])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Frontier24 operation-DAG vectors imply the public direct-image certificate"
    @{thms comma_crt_mdd_frontier_vector_preimage_sound
      comma_crt_mdd_frontier_chain_bad_successor
      comma_crt_mdd_frontier_dag_direct_image};
\<close>

end
