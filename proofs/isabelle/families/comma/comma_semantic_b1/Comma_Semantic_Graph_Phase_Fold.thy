theory Comma_Semantic_Graph_Phase_Fold
  imports Comma_Semantic_Graph Comma_Decade_Orbit.Comma_Phase_Mask_Arithmetic
begin

text \<open>
An observer mask is certified against the graph's full 924-phase result.
Local node periods select an action row, but recursive Goto evaluation keeps
the original phase.  This separates finite phase-mask construction from any
claim about a concrete rank or termination bound.
\<close>

definition comma_semantic_b1_graph_mask_refines ::
  "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
    (comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_graph_mask_refines nodes cid observe bits =
    (\<forall>r<924. \<exists>result.
      comma_semantic_b1_graph_eval nodes cid r=Some result \<and>
      comma_phase_member bits r=comma_phase_member (observe result) r)"

lemma comma_semantic_b1_graph_mask_refines_at:
  assumes refined: "comma_semantic_b1_graph_mask_refines nodes cid observe bits"
    and phase: "phase<924"
    and evaluation: "comma_semantic_b1_graph_eval nodes cid phase=Some result"
  shows "comma_phase_member bits phase=comma_phase_member (observe result) phase"
proof -
  obtain observed where actual:
      "comma_semantic_b1_graph_eval nodes cid phase=Some observed"
    and member: "comma_phase_member bits phase=
      comma_phase_member (observe observed) phase"
    using refined phase
    unfolding comma_semantic_b1_graph_mask_refines_def by blast
  have same: "Some observed=Some result"
    by (rule trans[OF sym[OF actual] evaluation])
  have observed: "observed=result"
    using same by (simp only: option.inject)
  show ?thesis using member by (simp only: observed)
qed

text \<open>
Backward reachability is defined on the phase-aware quotient action itself.
The receiving clock is advanced only after a Live result, and terminal
results retain their exact label in the action.  This relation is a bounded
Stop witness, not an exact residual rank.
\<close>

fun comma_semantic_b1_stop_within ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_stop_within 0 action phase root =
    (\<exists>terminal. action phase root=Comma_Semantic_B1_Stop terminal)"
| "comma_semantic_b1_stop_within (Suc k) action phase root =
    (comma_semantic_b1_stop_within k action phase root
      \<or> (\<exists>child. action phase root=Comma_Semantic_B1_Live child
        \<and> comma_semantic_b1_stop_within k action
          ((phase+1) mod 924) child))"

lemma comma_semantic_b1_stop_within_mono:
  assumes within: "comma_semantic_b1_stop_within k action phase root"
  shows "comma_semantic_b1_stop_within (Suc k) action phase root"
  using within by simp

lemma comma_semantic_b1_stop_within_stop:
  assumes stop: "action phase root=Comma_Semantic_B1_Stop terminal"
  shows "comma_semantic_b1_stop_within k action phase root"
  using stop by (induction k) auto

definition comma_semantic_b1_stop_pre_observer ::
    "nat list \<Rightarrow> comma_semantic_b1_result \<Rightarrow> nat" where
  "comma_semantic_b1_stop_pre_observer masks result =
    (case result of
       Comma_Semantic_B1_Stop _ \<Rightarrow> mask 924
     | Comma_Semantic_B1_Live child \<Rightarrow>
         if child<length masks then comma_rotate_phase 1 (masks!child) else 0
     | Comma_Semantic_B1_Invalid \<Rightarrow> 0)"

definition comma_semantic_b1_stop_seed_observer ::
    "comma_semantic_b1_result \<Rightarrow> nat" where
  "comma_semantic_b1_stop_seed_observer result =
    (case result of
       Comma_Semantic_B1_Stop _ \<Rightarrow> mask 924
     | _ \<Rightarrow> 0)"

definition comma_semantic_b1_stop_mask_next ::
    "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list \<Rightarrow>
      nat list \<Rightarrow> nat list" where
  "comma_semantic_b1_stop_mask_next transfers masks =
    map (\<lambda>root. if masks!root=mask 924 then mask 924
      else (transfers!root) (comma_semantic_b1_stop_pre_observer masks))
      [0..<length transfers]"

fun comma_semantic_b1_stop_mask_iteration ::
    "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list \<Rightarrow>
      nat \<Rightarrow> nat list" where
  "comma_semantic_b1_stop_mask_iteration transfers 0 =
    map (\<lambda>root. (transfers!root) comma_semantic_b1_stop_seed_observer)
      [0..<length transfers]"
| "comma_semantic_b1_stop_mask_iteration transfers (Suc k) =
    comma_semantic_b1_stop_mask_next transfers
      (comma_semantic_b1_stop_mask_iteration transfers k)"

lemma comma_semantic_b1_stop_mask_next_length:
  "length (comma_semantic_b1_stop_mask_next transfers masks)=length transfers"
  by (simp add: comma_semantic_b1_stop_mask_next_def)

lemma comma_semantic_b1_stop_mask_next_nth:
  assumes root: "root<length transfers"
  shows "comma_semantic_b1_stop_mask_next transfers masks!root =
    (if masks!root=mask 924 then mask 924
     else (transfers!root) (comma_semantic_b1_stop_pre_observer masks))"
  using root by (simp add: comma_semantic_b1_stop_mask_next_def)

lemma comma_semantic_b1_stop_mask_iteration_length:
  "length (comma_semantic_b1_stop_mask_iteration transfers k)=length transfers"
  by (induction k) (simp_all add: comma_semantic_b1_stop_mask_next_length)

lemma comma_semantic_b1_stop_mask_iteration_zero_nth:
  assumes root: "root<length transfers"
  shows "comma_semantic_b1_stop_mask_iteration transfers 0!root =
    (transfers!root) comma_semantic_b1_stop_seed_observer"
  using root by simp

lemma comma_semantic_b1_stop_mask_iteration_Suc_nth:
  assumes root: "root<length transfers"
  shows "comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root =
    (if comma_semantic_b1_stop_mask_iteration transfers k!root=mask 924
     then mask 924
     else (transfers!root)
       (comma_semantic_b1_stop_pre_observer
         (comma_semantic_b1_stop_mask_iteration transfers k)))"
  using comma_semantic_b1_stop_mask_next_nth
    [where root=root and transfers=transfers and
      masks="comma_semantic_b1_stop_mask_iteration transfers k"]
    root by simp

lemma comma_semantic_b1_stop_pre_mask_sound:
  assumes refined:
      "comma_semantic_b1_graph_mask_refines nodes cid
        (comma_semantic_b1_stop_pre_observer masks) bits"
    and phase: "phase<924"
    and evaluation:
      "comma_semantic_b1_graph_eval nodes cid phase=Some result"
    and selected: "action phase root=result"
    and next_sound: "\<And>child q. child<length masks \<Longrightarrow> q<924 \<Longrightarrow>
      comma_phase_member (masks!child) q \<Longrightarrow>
      comma_semantic_b1_stop_within k action q child"
  shows "comma_phase_member bits phase \<Longrightarrow>
    comma_semantic_b1_stop_within (Suc k) action phase root"
proof -
  assume member: "comma_phase_member bits phase"
  have observed:
    "comma_phase_member bits phase =
      comma_phase_member
        (comma_semantic_b1_stop_pre_observer masks result) phase"
    by (rule comma_semantic_b1_graph_mask_refines_at[OF refined phase evaluation])
  show "comma_semantic_b1_stop_within (Suc k) action phase root"
  proof (cases result)
    case (Comma_Semantic_B1_Stop terminal)
    have stop: "action phase root=Comma_Semantic_B1_Stop terminal"
      using selected Comma_Semantic_B1_Stop by simp
    show ?thesis
      by (rule comma_semantic_b1_stop_within_stop
        [where action=action and phase=phase and root=root
          and terminal=terminal and k="Suc k", OF stop])
  next
    case (Comma_Semantic_B1_Live child)
    have child_bound: "child<length masks"
      using member observed Comma_Semantic_B1_Live
      by (auto simp: comma_semantic_b1_stop_pre_observer_def
        comma_phase_member_def split: if_splits)
    have rotated_member:
      "comma_phase_member (comma_rotate_phase 1 (masks!child)) phase"
      using member observed Comma_Semantic_B1_Live child_bound
      by (simp add: comma_semantic_b1_stop_pre_observer_def)
    have next_phase: "((phase+1) mod 924)<924" by simp
    have child_member:
      "comma_phase_member (masks!child) ((phase+1) mod 924)"
      using comma_rotate_phase_member[OF phase, of 1 "masks!child"]
        rotated_member by simp
    have child_stop:
      "comma_semantic_b1_stop_within k action ((phase+1) mod 924) child"
      by (rule next_sound[OF child_bound next_phase child_member])
    have live: "action phase root=Comma_Semantic_B1_Live child"
      using selected Comma_Semantic_B1_Live by simp
    show ?thesis using live child_stop by simp
  next
    case Comma_Semantic_B1_Invalid
    have "comma_phase_member bits phase=False"
      using observed member Comma_Semantic_B1_Invalid
      by (simp add: comma_semantic_b1_stop_pre_observer_def)
    then show ?thesis using member by simp
  qed
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_graph_mask_refines_at
    comma_semantic_b1_stop_within_mono comma_semantic_b1_stop_within_stop
    comma_semantic_b1_stop_mask_next_nth
    comma_semantic_b1_stop_mask_iteration_length
    comma_semantic_b1_stop_mask_iteration_zero_nth
    comma_semantic_b1_stop_mask_iteration_Suc_nth
    comma_semantic_b1_stop_pre_mask_sound};
  Thm.consolidate checked;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic graph bounded-stop mask foundations" checked;
  if null (Thm_Deps.all_oracles checked) then ()
  else error "Bounded-stop mask foundations depend on an oracle"
\<close>

text \<open>
The host may propose a sequence of root masks, but the kernel consumes only
per-root observer-transfer theorems.  This induction establishes one-way
soundness of every layer: a set phase bit denotes a concrete path to a Stop
within the layer bound.  It neither demands exact ranks nor certifies bits
that are absent from a candidate mask.
\<close>

theorem comma_semantic_b1_stop_mask_sequence_sound:
  fixes nodes :: "comma_semantic_b1_node list"
    and root_cids :: "nat list"
    and masks :: "nat \<Rightarrow> nat list"
    and action :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
  assumes root_count: "length root_cids=46"
    and masks_length: "\<And>k. length (masks k)=46"
    and root_evaluation: "\<And>root phase. root<46 \<Longrightarrow> phase<924 \<Longrightarrow>
      \<exists>result. comma_semantic_b1_graph_eval nodes (root_cids!root) phase=
        Some result \<and> action phase root=result"
    and seed_refinement: "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
        comma_semantic_b1_stop_seed_observer (masks 0!root)"
    and step_refinement: "\<And>k root. root<46 \<Longrightarrow>
      (masks k!root=mask 924 \<and> masks (Suc k)!root=mask 924) \<or>
       comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
         (comma_semantic_b1_stop_pre_observer (masks k)) (masks (Suc k)!root)"
  shows "\<forall>k root phase. root<46 \<longrightarrow> phase<924 \<longrightarrow>
    comma_phase_member (masks k!root) phase \<longrightarrow>
    comma_semantic_b1_stop_within k action phase root"
proof (rule allI)
  fix k :: nat
  show "\<forall>root phase. root<46 \<longrightarrow> phase<924 \<longrightarrow>
      comma_phase_member (masks k!root) phase \<longrightarrow>
      comma_semantic_b1_stop_within k action phase root"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix root phase :: nat
      assume root: "root<46" and phase: "phase<924"
        and member: "comma_phase_member (masks 0!root) phase"
      obtain result where evaluation:
          "comma_semantic_b1_graph_eval nodes (root_cids!root) phase=Some result"
        and selected: "action phase root=result"
        using root_evaluation[OF root phase] by blast
      have refined:
        "comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
          comma_semantic_b1_stop_seed_observer (masks 0!root)"
        by (rule seed_refinement[OF root])
      have observed:
        "comma_phase_member (masks 0!root) phase =
          comma_phase_member (comma_semantic_b1_stop_seed_observer result) phase"
        by (rule comma_semantic_b1_graph_mask_refines_at
          [OF refined phase evaluation])
      show "comma_semantic_b1_stop_within 0 action phase root"
        using member observed selected
        by (cases result) (auto simp: comma_semantic_b1_stop_seed_observer_def
          comma_semantic_b1_stop_within.simps comma_phase_full_mask)
    qed
  next
    case (Suc k)
    show ?case
    proof (intro allI impI)
      fix root phase :: nat
      assume root: "root<46" and phase: "phase<924"
        and member: "comma_phase_member (masks (Suc k)!root) phase"
      obtain result where evaluation:
          "comma_semantic_b1_graph_eval nodes (root_cids!root) phase=Some result"
        and selected: "action phase root=result"
        using root_evaluation[OF root phase] by blast
      have step:
        "(masks k!root=mask 924 \<and> masks (Suc k)!root=mask 924) \<or>
         comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
           (comma_semantic_b1_stop_pre_observer (masks k))
           (masks (Suc k)!root)"
        by (rule step_refinement[OF root])
      have previous_sound:
        "\<And>child q. child<length (masks k) \<Longrightarrow> q<924 \<Longrightarrow>
          comma_phase_member (masks k!child) q \<Longrightarrow>
          comma_semantic_b1_stop_within k action q child"
        using Suc.IH masks_length by auto
      show "comma_semantic_b1_stop_within (Suc k) action phase root"
      proof (cases "masks k!root=mask 924")
        case True
        have previous_member: "comma_phase_member (masks k!root) phase"
          using phase True by (simp add: comma_phase_full_mask)
        have previous_stop:
          "comma_semantic_b1_stop_within k action phase root"
          by (rule Suc.IH[rule_format, OF root phase previous_member])
        show ?thesis
          by (rule comma_semantic_b1_stop_within_mono
            [where action=action and phase=phase and root=root and k=k,
              OF previous_stop])
      next
        case False
        have refined:
          "comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
            (comma_semantic_b1_stop_pre_observer (masks k))
            (masks (Suc k)!root)"
          using step False by blast
        show ?thesis
          by (rule comma_semantic_b1_stop_pre_mask_sound
            [where action=action and phase=phase and root=root and k=k,
              OF refined phase evaluation selected previous_sound member])
      qed
    qed
  qed
qed

theorem comma_semantic_b1_stop_mask_iteration_sound:
  fixes nodes :: "comma_semantic_b1_node list"
    and root_cids :: "nat list"
    and transfers :: "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list"
    and action :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
  assumes root_count: "length root_cids=46"
    and transfer_count: "length transfers=46"
    and root_evaluation: "\<And>root phase. root<46 \<Longrightarrow> phase<924 \<Longrightarrow>
      \<exists>result. comma_semantic_b1_graph_eval nodes (root_cids!root) phase=
        Some result \<and> action phase root=result"
    and transfer_refinement: "\<And>root observe. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines nodes (root_cids!root) observe
        ((transfers!root) observe)"
  shows "\<forall>k root phase. root<46 \<longrightarrow> phase<924 \<longrightarrow>
    comma_phase_member (comma_semantic_b1_stop_mask_iteration transfers k!root) phase
      \<longrightarrow> comma_semantic_b1_stop_within k action phase root"
proof -
  have masks_length:
    "\<And>k. length (comma_semantic_b1_stop_mask_iteration transfers k)=46"
    using transfer_count
    by (simp add: comma_semantic_b1_stop_mask_iteration_length)
  have seed_refinement:
    "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
        comma_semantic_b1_stop_seed_observer
        (comma_semantic_b1_stop_mask_iteration transfers 0!root)"
  proof -
    fix root :: nat
    assume root: "root<46"
    have below: "root<length transfers" using root transfer_count by simp
    have selected:
      "comma_semantic_b1_stop_mask_iteration transfers 0!root=
        (transfers!root) comma_semantic_b1_stop_seed_observer"
      by (rule comma_semantic_b1_stop_mask_iteration_zero_nth
        [where transfers=transfers and root=root, OF below])
    show "comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
        comma_semantic_b1_stop_seed_observer
        (comma_semantic_b1_stop_mask_iteration transfers 0!root)"
      using transfer_refinement[where root=root and
          observe=comma_semantic_b1_stop_seed_observer]
        root selected by simp
  qed
  have step_refinement:
    "\<And>k root. root<46 \<Longrightarrow>
      (comma_semantic_b1_stop_mask_iteration transfers k!root=mask 924 \<and>
       comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root=mask 924) \<or>
       comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
         (comma_semantic_b1_stop_pre_observer
           (comma_semantic_b1_stop_mask_iteration transfers k))
         (comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root)"
  proof -
    fix k root :: nat
    assume root: "root<46"
    have below: "root<length transfers" using root transfer_count by simp
    have next_value:
      "comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root=
        (if comma_semantic_b1_stop_mask_iteration transfers k!root=mask 924
         then mask 924
         else (transfers!root)
           (comma_semantic_b1_stop_pre_observer
             (comma_semantic_b1_stop_mask_iteration transfers k)))"
      by (rule comma_semantic_b1_stop_mask_iteration_Suc_nth
        [where transfers=transfers and root=root and k=k, OF below])
    show "(comma_semantic_b1_stop_mask_iteration transfers k!root=mask 924 \<and>
         comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root=mask 924) \<or>
       comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
         (comma_semantic_b1_stop_pre_observer
           (comma_semantic_b1_stop_mask_iteration transfers k))
         (comma_semantic_b1_stop_mask_iteration transfers (Suc k)!root)"
    proof (cases "comma_semantic_b1_stop_mask_iteration transfers k!root=mask 924")
      case True
      then show ?thesis using next_value by simp
    next
      case False
      have refined:
        "comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
          (comma_semantic_b1_stop_pre_observer
            (comma_semantic_b1_stop_mask_iteration transfers k))
          ((transfers!root) (comma_semantic_b1_stop_pre_observer
            (comma_semantic_b1_stop_mask_iteration transfers k)))"
        by (rule transfer_refinement[where root=root and
          observe="comma_semantic_b1_stop_pre_observer
            (comma_semantic_b1_stop_mask_iteration transfers k)", OF root])
      show ?thesis using False next_value refined by simp
    qed
  qed
  show ?thesis
    by (rule comma_semantic_b1_stop_mask_sequence_sound
      [where action=action,
        OF root_count masks_length root_evaluation seed_refinement step_refinement])
qed

corollary comma_semantic_b1_full_stop_mask_iteration_sound:
  fixes nodes :: "comma_semantic_b1_node list"
    and root_cids :: "nat list"
    and transfers :: "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list"
    and action :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
  assumes root_count: "length root_cids=46"
    and transfer_count: "length transfers=46"
    and root_evaluation: "\<And>root phase. root<46 \<Longrightarrow> phase<924 \<Longrightarrow>
      \<exists>result. comma_semantic_b1_graph_eval nodes (root_cids!root) phase=
        Some result \<and> action phase root=result"
    and transfer_refinement: "\<And>root observe. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines nodes (root_cids!root) observe
        ((transfers!root) observe)"
    and root: "root<46"
    and full: "comma_semantic_b1_stop_mask_iteration transfers depth!root=mask 924"
  shows "\<forall>phase<924. comma_semantic_b1_stop_within depth action phase root"
proof -
  have sequence:
    "\<forall>k root phase. root<46 \<longrightarrow> phase<924 \<longrightarrow>
      comma_phase_member (comma_semantic_b1_stop_mask_iteration transfers k!root) phase
        \<longrightarrow> comma_semantic_b1_stop_within k action phase root"
    by (rule comma_semantic_b1_stop_mask_iteration_sound
      [where transfers=transfers and action=action,
        OF root_count transfer_count root_evaluation transfer_refinement])
  show ?thesis
  proof (intro allI impI)
    fix phase :: nat
    assume phase: "phase<924"
    have member:
      "comma_phase_member (comma_semantic_b1_stop_mask_iteration transfers depth!root)
        phase"
      using phase full by (simp add: comma_phase_full_mask)
    show "comma_semantic_b1_stop_within depth action phase root"
      using sequence root phase member by blast
  qed
qed

corollary comma_semantic_b1_full_stop_mask_sequence_sound:
  assumes root_count: "length root_cids=46"
    and masks_length: "\<And>k. length (masks k)=46"
    and root_evaluation: "\<And>root phase. root<46 \<Longrightarrow> phase<924 \<Longrightarrow>
      \<exists>result. comma_semantic_b1_graph_eval nodes (root_cids!root) phase=
        Some result \<and> action phase root=result"
    and seed_refinement: "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
        comma_semantic_b1_stop_seed_observer (masks 0!root)"
    and step_refinement: "\<And>k root. root<46 \<Longrightarrow>
      (masks k!root=mask 924 \<and> masks (Suc k)!root=mask 924) \<or>
       comma_semantic_b1_graph_mask_refines nodes (root_cids!root)
         (comma_semantic_b1_stop_pre_observer (masks k)) (masks (Suc k)!root)"
    and root: "root<46"
    and full: "masks depth!root=mask 924"
  shows "\<forall>phase<924. comma_semantic_b1_stop_within depth action phase root"
proof (intro allI impI)
  fix phase :: nat
  assume phase: "phase<924"
  have member: "comma_phase_member (masks depth!root) phase"
    using phase full by (simp add: comma_phase_full_mask)
  have sequence:
    "\<forall>k root phase. root<46 \<longrightarrow> phase<924 \<longrightarrow>
      comma_phase_member (masks k!root) phase \<longrightarrow>
      comma_semantic_b1_stop_within k action phase root"
    by (rule comma_semantic_b1_stop_mask_sequence_sound
      [OF root_count masks_length root_evaluation seed_refinement step_refinement])
  show "comma_semantic_b1_stop_within depth action phase root"
    using sequence root phase member by blast
qed

text \<open>
For completed graphs, sharing a CID transports the exact completed result at
every receiving clock.  This uses the completed binding contract, including
its source-output transport; the older immediate-edge theorem for
\<open>graph_valid\<close> is not used here.  The result equality preserves both Live
successor indices and Stop labels.
\<close>

lemma comma_semantic_b1_graph_completed_cid_result_congruence:
  assumes graph: "comma_semantic_b1_graph_completed_valid bindings nodes"
    and left: "left_binding\<in>set bindings"
    and right: "right_binding\<in>set bindings"
    and left_cid: "comma_semantic_b1_binding_cid left_binding=cid"
    and right_cid: "comma_semantic_b1_binding_cid right_binding=cid"
  shows "\<forall>clock. comma_semantic_b1_graph_eval nodes cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding))
    \<and> comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding)"
proof (intro allI)
  fix clock :: nat
  have all: "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint[OF graph])
  have left_exact:
    "comma_semantic_b1_graph_eval nodes cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding))"
    using all left left_cid
    by (auto simp: comma_semantic_b1_graph_correct_at_def)
  have right_exact:
    "comma_semantic_b1_graph_eval nodes cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding))"
    using all right right_cid
    by (auto simp: comma_semantic_b1_graph_correct_at_def)
  show "comma_semantic_b1_graph_eval nodes cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding))
    \<and> comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding)"
    using left_exact right_exact by auto
qed

lemma comma_semantic_b1_graph_completed_rebased_result_congruence:
  assumes graph: "comma_semantic_b1_graph_completed_valid bindings nodes"
    and left: "left_binding\<in>set bindings"
    and right: "right_binding\<in>set bindings"
    and left_cid: "comma_semantic_b1_binding_cid left_binding=cid"
    and right_cid: "comma_semantic_b1_binding_cid right_binding=cid"
    and receiving_phase:
      "(phase+comma_source_continuation_shift
          (comma_semantic_b1_binding_source left_binding)) mod 924 =
       (phase+comma_source_continuation_shift
          (comma_semantic_b1_binding_source right_binding)) mod 924"
  shows "comma_semantic_b1_round_output
        ((phase+comma_source_continuation_shift
          (comma_semantic_b1_binding_source left_binding)) mod 924)
          (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output
        ((phase+comma_source_continuation_shift
          (comma_semantic_b1_binding_source right_binding)) mod 924)
          (comma_semantic_b1_binding_source right_binding)"
proof -
  let ?left_clock = "(phase+comma_source_continuation_shift
    (comma_semantic_b1_binding_source left_binding)) mod 924"
  let ?right_clock = "(phase+comma_source_continuation_shift
    (comma_semantic_b1_binding_source right_binding)) mod 924"
  have same_clock: "?left_clock=?right_clock"
    using receiving_phase by blast
  have congruent:
    "\<forall>clock. comma_semantic_b1_graph_eval nodes cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding))
      \<and> comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding)"
    by (rule comma_semantic_b1_graph_completed_cid_result_congruence
      [OF graph left right left_cid right_cid])
  have same_result:
    "comma_semantic_b1_round_output ?left_clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output ?left_clock
        (comma_semantic_b1_binding_source right_binding)"
    using congruent by blast
  show ?thesis using same_clock same_result by simp
qed

fun comma_semantic_b1_graph_edge_mask_refines ::
  "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
    (comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow>
    comma_semantic_b1_edge \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_graph_edge_mask_refines nodes parent observe
      (Comma_Semantic_B1_Goto child) bits =
    (child<parent \<and>
      comma_semantic_b1_graph_mask_refines nodes child observe bits)"
| "comma_semantic_b1_graph_edge_mask_refines nodes parent observe
      (Comma_Semantic_B1_Live_Edge root) bits =
    (root<46 \<and> (\<forall>r<924.
      comma_phase_member bits r=
        comma_phase_member (observe (Comma_Semantic_B1_Live root)) r))"
| "comma_semantic_b1_graph_edge_mask_refines nodes parent observe
      (Comma_Semantic_B1_Stop_Edge digit) bits =
    (digit\<le>8 \<and> (\<forall>r<924.
      comma_phase_member bits r=
        comma_phase_member (observe (Comma_Semantic_B1_Stop digit)) r))"
| "comma_semantic_b1_graph_edge_mask_refines nodes parent observe
      Comma_Semantic_B1_Invalid_Edge bits =
    (\<forall>r<924.
      comma_phase_member bits r=
        comma_phase_member (observe Comma_Semantic_B1_Invalid) r)"

lemma comma_indexed_phase_union_select:
  assumes positive: "0<period" and length: "length masks=period"
  shows "comma_phase_member
      (comma_indexed_phase_union (\<lambda>k r. r mod period=k) masks) r =
    comma_phase_member (masks!(r mod period)) r"
proof -
  let ?selected = "r mod period"
  have selected_bound: "?selected<length masks"
    using positive length by simp
  show ?thesis
    using comma_indexed_phase_union_member[of "\<lambda>k r. r mod period=k" masks r]
      selected_bound
    by auto
qed

lemma comma_semantic_b1_graph_node_mask_refines_indexed_union:
  assumes node: "comma_semantic_b1_node_of nodes cid=Some node"
    and positive: "0<comma_semantic_b1_node_period node"
    and action_length:
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    and rows: "list_all2
      (comma_semantic_b1_graph_edge_mask_refines nodes cid observe)
      (comma_semantic_b1_node_actions node) masks"
  shows "comma_semantic_b1_graph_mask_refines nodes cid observe
    (comma_indexed_phase_union
      (\<lambda>k r. r mod comma_semantic_b1_node_period node=k) masks)"
proof -
  let ?period = "comma_semantic_b1_node_period node"
  let ?actions = "comma_semantic_b1_node_actions node"
  have mask_length: "length masks=?period"
    using list_all2_lengthD[OF rows] action_length by simp
  have union_select:
    "comma_phase_member
      (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
      comma_phase_member (masks!(r mod ?period)) r" for r :: nat
    by (rule comma_indexed_phase_union_select[OF positive mask_length])
  show ?thesis
    unfolding comma_semantic_b1_graph_mask_refines_def
  proof (intro allI impI)
    fix r :: nat
    assume phase: "r<924"
    let ?slot = "r mod ?period"
    have slot_bound: "?slot<length ?actions"
      using positive action_length by simp
    have paired:
      "comma_semantic_b1_graph_edge_mask_refines nodes cid observe
        (?actions!?slot) (masks!?slot)"
      by (rule list_all2_nthD[OF rows slot_bound])
    have applied:
      "comma_semantic_b1_graph_apply nodes cid r=Some (?actions!?slot)"
      using node positive action_length
      by (simp add: comma_semantic_b1_graph_apply_def)
    show "\<exists>result. comma_semantic_b1_graph_eval nodes cid r=Some result \<and>
      comma_phase_member
        (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
        comma_phase_member (observe result) r"
    proof (cases "?actions!?slot")
      case (Comma_Semantic_B1_Goto child)
      have edge_facts:
        "child<cid \<and>
          comma_semantic_b1_graph_mask_refines nodes child observe
            (masks!?slot)"
        using paired Comma_Semantic_B1_Goto by simp
      have applied_goto:
        "comma_semantic_b1_graph_apply nodes cid r=
          Some (Comma_Semantic_B1_Goto child)"
        using applied Comma_Semantic_B1_Goto by simp
      have eval_same:
        "comma_semantic_b1_graph_eval nodes cid r=
          comma_semantic_b1_graph_eval nodes child r"
        by (rule comma_semantic_b1_graph_eval_apply_goto[OF applied_goto])
          (rule conjunct1[OF edge_facts])
      have child_refines:
        "comma_semantic_b1_graph_mask_refines nodes child observe
          (masks!?slot)"
        by (rule conjunct2[OF edge_facts])
      obtain result where child_eval:
        "comma_semantic_b1_graph_eval nodes child r=Some result"
        and child_bits:
        "comma_phase_member (masks!?slot) r=
          comma_phase_member (observe result) r"
        using child_refines phase
        by (auto simp: comma_semantic_b1_graph_mask_refines_def)
      have exact: "comma_semantic_b1_graph_eval nodes cid r=Some result"
        by (simp only: eval_same child_eval)
      have bits:
        "comma_phase_member
          (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
          comma_phase_member (observe result) r"
        by (rule trans[OF union_select[of r] child_bits])
      show ?thesis by (rule exI[of _ result]) (rule conjI[OF exact bits])
    next
      case (Comma_Semantic_B1_Live_Edge root)
      have edge_facts:
        "root<46 \<and> (\<forall>q<924.
          comma_phase_member (masks!?slot) q =
            comma_phase_member (observe (Comma_Semantic_B1_Live root)) q)"
        using paired Comma_Semantic_B1_Live_Edge by simp
      have applied_live:
        "comma_semantic_b1_graph_apply nodes cid r=
          Some (Comma_Semantic_B1_Live_Edge root)"
        using applied Comma_Semantic_B1_Live_Edge by simp
      have eval:
        "comma_semantic_b1_graph_eval nodes cid r=
          Some (Comma_Semantic_B1_Live root)"
        by (rule comma_semantic_b1_graph_eval_apply_live[OF applied_live])
          (rule conjunct1[OF edge_facts])
      have bits:
        "comma_phase_member (masks!?slot) r=
          comma_phase_member
            (observe (Comma_Semantic_B1_Live root)) r"
        using edge_facts phase by blast
      have selected_bits:
        "comma_phase_member
          (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
          comma_phase_member (observe (Comma_Semantic_B1_Live root)) r"
        by (rule trans[OF union_select[of r] bits])
      show ?thesis
        by (rule exI[of _ "Comma_Semantic_B1_Live root"]) (rule conjI[OF eval selected_bits])
    next
      case (Comma_Semantic_B1_Stop_Edge digit)
      have edge_facts:
        "digit\<le>8 \<and> (\<forall>q<924.
          comma_phase_member (masks!?slot) q =
            comma_phase_member (observe (Comma_Semantic_B1_Stop digit)) q)"
        using paired Comma_Semantic_B1_Stop_Edge by simp
      have applied_stop:
        "comma_semantic_b1_graph_apply nodes cid r=
          Some (Comma_Semantic_B1_Stop_Edge digit)"
        using applied Comma_Semantic_B1_Stop_Edge by simp
      have eval:
        "comma_semantic_b1_graph_eval nodes cid r=
          Some (Comma_Semantic_B1_Stop digit)"
        by (rule comma_semantic_b1_graph_eval_apply_stop[OF applied_stop])
          (rule conjunct1[OF edge_facts])
      have bits:
        "comma_phase_member (masks!?slot) r=
          comma_phase_member
            (observe (Comma_Semantic_B1_Stop digit)) r"
        using edge_facts phase by blast
      have selected_bits:
        "comma_phase_member
          (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
          comma_phase_member (observe (Comma_Semantic_B1_Stop digit)) r"
        by (rule trans[OF union_select[of r] bits])
      show ?thesis
        by (rule exI[of _ "Comma_Semantic_B1_Stop digit"]) (rule conjI[OF eval selected_bits])
    next
      case Comma_Semantic_B1_Invalid_Edge
      have bits:
        "comma_phase_member (masks!?slot) r=
          comma_phase_member (observe Comma_Semantic_B1_Invalid) r"
        using paired phase Comma_Semantic_B1_Invalid_Edge by simp
      have applied_invalid:
        "comma_semantic_b1_graph_apply nodes cid r=
          Some Comma_Semantic_B1_Invalid_Edge"
        using applied Comma_Semantic_B1_Invalid_Edge by simp
      have eval:
        "comma_semantic_b1_graph_eval nodes cid r=
          Some Comma_Semantic_B1_Invalid"
        by (rule comma_semantic_b1_graph_eval_apply_invalid[OF applied_invalid])
      have selected_bits:
        "comma_phase_member
          (comma_indexed_phase_union (\<lambda>k r. r mod ?period=k) masks) r =
          comma_phase_member (observe (Comma_Semantic_B1_Invalid)) r"
        by (rule trans[OF union_select[of r] bits])
      show ?thesis
        by (rule exI[of _ "Comma_Semantic_B1_Invalid"]) (rule conjI[OF eval selected_bits])
    qed
  qed
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_stop_mask_sequence_sound
    comma_semantic_b1_stop_mask_iteration_sound
    comma_semantic_b1_full_stop_mask_sequence_sound
    comma_semantic_b1_full_stop_mask_iteration_sound
    comma_semantic_b1_graph_completed_cid_result_congruence
    comma_semantic_b1_graph_completed_rebased_result_congruence};
  Thm.consolidate checked;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic graph phase-mask transfer and completed-result congruence" checked;
  if null (Thm_Deps.all_oracles checked) then ()
  else error "Graph phase-fold and bounded-stop transfer depends on an oracle"
\<close>

end
