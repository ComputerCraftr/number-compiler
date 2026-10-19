theory Double_Reverse_Periodic_Worklist_Refinement
  imports Double_Reverse_Packed_Request_Refinement
begin

text \<open>
This theory formalizes the expensive acceptance phase of
\<open>_certified_periodic_motif\<close>. Keys are exactly pairs
\<open>(arena node id, phase modulo motif length)\<close>. The worklist state
uses a finite \<open>pending\<close> set for the runtime \<open>tasks/queued\<close>
and a \<open>seen\<close> set for runtime \<open>discovered\<close>. Its transition
rules mirror the pop-seen and expand-fresh branches; only stack order is
erased. CONCAT uses the left child's recorded extent. REPEAT checks precisely
the first \<open>min(count, phase_cycle)\<close> child phases. The representation
relation below requires every view node and child extent to agree with a
well-founded source SLP, so malformed cyclic views cannot certify a source.

A completed discovery worklist is followed by the runtime's resolver. Its
initial true set contains exactly the passing EMPTY/TERM values. The
\<open>processed\<close> set models completed resolver entries; the ready set is exactly
the unprocessed keys whose children have all been processed (the runtime's
empty \<open>remaining\<close> condition). A resolver step stores a composite as true
only when every child is already true, which is the runtime's Boolean AND.
Successful publication requires a drained discovery queue, complete
resolution, and the root entry true. Induction on the represented source SLP
then yields the existing structural phase certificate. No certificate or
endpoint equality is assumed. The remaining executable boundary is the
explicit arena view correspondence: an application to the Python run must map
each node id to the matching node kind, terminal symbol, child ids and
lengths. Budget refusal is not success: it cannot produce the completed
discovery and resolver states required here.
\<close>

datatype double_reverse_source_arena_node =
    Double_Reverse_Arena_Empty
  | Double_Reverse_Arena_Term nat
  | Double_Reverse_Arena_Concat nat nat
  | Double_Reverse_Arena_Repeat nat nat

fun double_reverse_source_arena_represents ::
    "(nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
      double_reverse_source_slp \<Rightarrow> bool" where
  "double_reverse_source_arena_represents view extent node_id
      Double_Reverse_Source_Empty =
    (view node_id = Double_Reverse_Arena_Empty \<and> extent node_id = 0)"
| "double_reverse_source_arena_represents view extent node_id
      (Double_Reverse_Source_Term digit) =
    (view node_id = Double_Reverse_Arena_Term digit \<and> extent node_id = 1)"
| "double_reverse_source_arena_represents view extent node_id
      (Double_Reverse_Source_Concat left right) =
    (\<exists>left_id right_id.
      view node_id = Double_Reverse_Arena_Concat left_id right_id \<and>
      extent node_id = extent left_id + extent right_id \<and>
      double_reverse_source_arena_represents view extent left_id left \<and>
      double_reverse_source_arena_represents view extent right_id right)"
| "double_reverse_source_arena_represents view extent node_id
      (Double_Reverse_Source_Repeat child count) =
    (\<exists>child_id.
      view node_id = Double_Reverse_Arena_Repeat child_id count \<and>
      extent node_id = count * extent child_id \<and>
      double_reverse_source_arena_represents view extent child_id child)"

lemma double_reverse_source_arena_represents_extent:
  assumes represented:
    "double_reverse_source_arena_represents view extent node_id source"
  shows "extent node_id = double_reverse_source_slp_length source"
  using represented
  by (induction source arbitrary: node_id)
    (auto simp: double_reverse_source_slp_length.simps)

type_synonym double_reverse_periodic_worklist_key = "nat \<times> nat"
type_synonym double_reverse_periodic_worklist_set =
  "double_reverse_periodic_worklist_key set"

fun double_reverse_periodic_worklist_children ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow>
      double_reverse_periodic_worklist_set" where
  "double_reverse_periodic_worklist_children motif view extent (node_id, phase) =
    (case view node_id of
       Double_Reverse_Arena_Empty \<Rightarrow> {}
     | Double_Reverse_Arena_Term digit \<Rightarrow> {}
     | Double_Reverse_Arena_Concat left right \<Rightarrow>
         {(left, phase),
          (right, (phase + extent left) mod length motif)}
     | Double_Reverse_Arena_Repeat child count \<Rightarrow>
         {(child, (phase + copy * extent child) mod length motif) |
           copy. copy < min count
             (double_reverse_source_phase_cycle (length motif) (extent child))})"

fun double_reverse_periodic_worklist_terminal_ok ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow> bool" where
  "double_reverse_periodic_worklist_terminal_ok motif view (node_id, phase) =
    (case view node_id of
       Double_Reverse_Arena_Empty \<Rightarrow> True
     | Double_Reverse_Arena_Term digit \<Rightarrow>
         motif \<noteq> [] \<and> digit = double_reverse_ring_digit motif phase
     | Double_Reverse_Arena_Concat left right \<Rightarrow> True
     | Double_Reverse_Arena_Repeat child count \<Rightarrow> True)"

fun double_reverse_periodic_worklist_terminal_passes ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow> bool" where
  "double_reverse_periodic_worklist_terminal_passes motif view (node_id, phase) =
    (case view node_id of
       Double_Reverse_Arena_Empty \<Rightarrow> True
     | Double_Reverse_Arena_Term digit \<Rightarrow>
         digit = double_reverse_ring_digit motif phase
     | Double_Reverse_Arena_Concat left right \<Rightarrow> False
     | Double_Reverse_Arena_Repeat child count \<Rightarrow> False)"

definition double_reverse_periodic_worklist_terminal_true_set ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set" where
  "double_reverse_periodic_worklist_terminal_true_set motif view seen =
    {key\<in>seen. double_reverse_periodic_worklist_terminal_passes motif view key}"

definition double_reverse_periodic_worklist_children_closed ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool" where
  "double_reverse_periodic_worklist_children_closed motif view extent seen
    \<longleftrightarrow>
    (\<forall>key\<in>seen.
      double_reverse_periodic_worklist_children motif view extent key
        \<subseteq> seen)"

definition double_reverse_periodic_worklist_terminals_ok ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool" where
  "double_reverse_periodic_worklist_terminals_ok motif view seen \<longleftrightarrow>
    (\<forall>key\<in>seen. double_reverse_periodic_worklist_terminal_ok motif view key)"

fun double_reverse_periodic_resolver_add ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow>
      double_reverse_periodic_worklist_set" where
  "double_reverse_periodic_resolver_add motif view extent true_set (node_id, phase) =
    (case view node_id of
       Double_Reverse_Arena_Empty \<Rightarrow> true_set
     | Double_Reverse_Arena_Term digit \<Rightarrow> true_set
     | Double_Reverse_Arena_Concat left right \<Rightarrow>
         (if double_reverse_periodic_worklist_children motif view extent
               (node_id, phase) \<subseteq> true_set
          then insert (node_id, phase) true_set else true_set)
     | Double_Reverse_Arena_Repeat child count \<Rightarrow>
         (if double_reverse_periodic_worklist_children motif view extent
               (node_id, phase) \<subseteq> true_set
          then insert (node_id, phase) true_set else true_set))"

definition double_reverse_periodic_resolver_ready ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set" where
  "double_reverse_periodic_resolver_ready motif view extent seen processed =
    {key\<in>seen - processed.
      double_reverse_periodic_worklist_children motif view extent key
        \<subseteq> processed}"

definition double_reverse_periodic_resolver_wellformed ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool" where
  "double_reverse_periodic_resolver_wellformed motif view extent true_set
    \<longleftrightarrow>
      double_reverse_periodic_worklist_children_closed motif view extent true_set \<and>
      double_reverse_periodic_worklist_terminals_ok motif view true_set"

inductive double_reverse_periodic_resolver_step ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool"
  for motif view extent seen where
  process_ready:
    "key \<in> seen \<Longrightarrow> key \<notin> processed \<Longrightarrow>
     double_reverse_periodic_worklist_children motif view extent key
       \<subseteq> processed \<Longrightarrow>
     double_reverse_periodic_resolver_step motif view extent seen processed
       true_set (insert key processed)
       (double_reverse_periodic_resolver_add motif view extent true_set key)"

inductive double_reverse_periodic_resolver_reaches ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool"
  for motif view extent seen where
  resolver_start:
    "double_reverse_periodic_resolver_reaches motif view extent seen {}
       (double_reverse_periodic_worklist_terminal_true_set motif view seen)"
| resolver_advance:
    "double_reverse_periodic_resolver_reaches motif view extent seen
       processed true_set \<Longrightarrow>
     double_reverse_periodic_resolver_step motif view extent seen processed
       true_set processed' true_set' \<Longrightarrow>
     double_reverse_periodic_resolver_reaches motif view extent seen
       processed' true_set'"

lemma double_reverse_periodic_resolver_insert_preserves_wellformed:
  assumes wellformed:
    "double_reverse_periodic_resolver_wellformed motif view extent true_set"
      and children:
    "double_reverse_periodic_worklist_children motif view extent key
      \<subseteq> true_set"
      and terminal:
    "double_reverse_periodic_worklist_terminal_ok motif view key"
  shows "double_reverse_periodic_resolver_wellformed motif view extent
    (insert key true_set)"
  using wellformed children terminal
  unfolding double_reverse_periodic_resolver_wellformed_def
    double_reverse_periodic_worklist_children_closed_def
    double_reverse_periodic_worklist_terminals_ok_def
  by auto

lemma double_reverse_periodic_resolver_add_preserves_wellformed:
  assumes wellformed:
    "double_reverse_periodic_resolver_wellformed motif view extent true_set"
  shows "double_reverse_periodic_resolver_wellformed motif view extent
    (double_reverse_periodic_resolver_add motif view extent true_set key)"
proof -
  obtain node_id phase where key: "key = (node_id, phase)"
    by (cases key) auto
  show ?thesis
  proof (cases "view node_id")
    case Double_Reverse_Arena_Empty
    then show ?thesis using wellformed key
      by (simp add: double_reverse_periodic_resolver_add.simps)
  next
    case (Double_Reverse_Arena_Term digit)
    then show ?thesis using wellformed key
      by (simp add: double_reverse_periodic_resolver_add.simps)
  next
    case (Double_Reverse_Arena_Concat left right)
    let ?key = "(node_id, phase)"
    have child_form:
      "double_reverse_periodic_worklist_children motif view extent ?key
        \<subseteq> true_set \<longleftrightarrow>
       double_reverse_periodic_worklist_children motif view extent key
        \<subseteq> true_set"
      using key by simp
    show ?thesis
    proof (cases
        "double_reverse_periodic_worklist_children motif view extent ?key
          \<subseteq> true_set")
      case True
      have child_set:
        "double_reverse_periodic_worklist_children motif view extent key
          \<subseteq> true_set"
        using True child_form by blast
      have terminal:
        "double_reverse_periodic_worklist_terminal_ok motif view key"
        using Double_Reverse_Arena_Concat key
        by (simp add: double_reverse_periodic_worklist_terminal_ok.simps)
      show ?thesis
        using double_reverse_periodic_resolver_insert_preserves_wellformed
          [OF wellformed child_set terminal]
          Double_Reverse_Arena_Concat key True
        by (simp add: double_reverse_periodic_resolver_add.simps)
    next
      case False
      then show ?thesis using wellformed Double_Reverse_Arena_Concat key
        by (auto simp: double_reverse_periodic_resolver_add.simps)
    qed
  next
    case (Double_Reverse_Arena_Repeat child count)
    let ?key = "(node_id, phase)"
    have child_form:
      "double_reverse_periodic_worklist_children motif view extent ?key
        \<subseteq> true_set \<longleftrightarrow>
       double_reverse_periodic_worklist_children motif view extent key
        \<subseteq> true_set"
      using key by simp
    show ?thesis
    proof (cases
        "double_reverse_periodic_worklist_children motif view extent ?key
          \<subseteq> true_set")
      case True
      have child_set:
        "double_reverse_periodic_worklist_children motif view extent key
          \<subseteq> true_set"
        using True child_form by blast
      have terminal:
        "double_reverse_periodic_worklist_terminal_ok motif view key"
        using Double_Reverse_Arena_Repeat key
        by (simp add: double_reverse_periodic_worklist_terminal_ok.simps)
      show ?thesis
        using double_reverse_periodic_resolver_insert_preserves_wellformed
          [OF wellformed child_set terminal]
          Double_Reverse_Arena_Repeat key True
        by (simp add: double_reverse_periodic_resolver_add.simps)
    next
      case False
      then show ?thesis using wellformed Double_Reverse_Arena_Repeat key
        by (auto simp: double_reverse_periodic_resolver_add.simps)
    qed
  qed
qed

lemma double_reverse_periodic_resolver_step_preserves_wellformed:
  assumes wellformed:
    "double_reverse_periodic_resolver_wellformed motif view extent true_set"
      and step:
        "double_reverse_periodic_resolver_step motif view extent seen processed
          true_set processed' true_set'"
  shows "double_reverse_periodic_resolver_wellformed motif view extent true_set'"
proof -
  from step show ?thesis
  proof (cases rule: double_reverse_periodic_resolver_step.cases)
    case (process_ready key)
    have updated:
      "true_set' = double_reverse_periodic_resolver_add motif view extent
        true_set key"
      using process_ready by simp
    have added:
      "double_reverse_periodic_resolver_wellformed motif view extent
        (double_reverse_periodic_resolver_add motif view extent true_set key)"
      by (rule double_reverse_periodic_resolver_add_preserves_wellformed
        [OF wellformed])
    show ?thesis using added updated by simp
  qed
qed

lemma double_reverse_periodic_resolver_reaches_wellformed:
  assumes motif: "motif \<noteq> []"
      and run:
    "double_reverse_periodic_resolver_reaches motif view extent seen processed
      true_set"
  shows "double_reverse_periodic_resolver_wellformed motif view extent true_set"
  using run
proof (induction rule: double_reverse_periodic_resolver_reaches.induct)
  case resolver_start
  then show ?case using motif
    by (auto simp: double_reverse_periodic_resolver_wellformed_def
        double_reverse_periodic_worklist_children_closed_def
        double_reverse_periodic_worklist_terminals_ok_def
        double_reverse_periodic_worklist_terminal_ok.simps
        double_reverse_periodic_worklist_terminal_passes.simps
        double_reverse_periodic_worklist_terminal_true_set_def
        double_reverse_periodic_worklist_children.simps
      split: double_reverse_source_arena_node.splits)
next
  case (resolver_advance processed true_set processed' true_set')
  have step:
    "double_reverse_periodic_resolver_step motif view extent seen processed
      true_set processed' true_set'"
    using resolver_advance.hyps(2) .
  show ?case
    by (rule double_reverse_periodic_resolver_step_preserves_wellformed
      [OF resolver_advance.IH step])
qed

definition double_reverse_periodic_resolver_success ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow> bool" where
  "double_reverse_periodic_resolver_success motif view extent seen root
    \<longleftrightarrow>
    motif \<noteq> [] \<and> (\<exists>processed true_set.
      double_reverse_periodic_resolver_reaches motif view extent seen
        processed true_set \<and>
      processed = seen \<and>
      double_reverse_periodic_resolver_ready motif view extent seen processed = {} \<and>
      root \<in> true_set)"

inductive double_reverse_periodic_worklist_step ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool"
  for motif view extent where
  pop_seen:
    "key \<in> pending \<Longrightarrow> key \<in> seen \<Longrightarrow>
     double_reverse_periodic_worklist_step motif view extent pending seen
       (pending - {key}) seen"
| expand_fresh:
    "key \<in> pending \<Longrightarrow> key \<notin> seen \<Longrightarrow>
     double_reverse_periodic_worklist_step motif view extent pending seen
       (pending - {key} \<union>
          (double_reverse_periodic_worklist_children motif view extent key -
            (insert key seen \<union> (pending - {key}))))
       (insert key seen)"

inductive double_reverse_periodic_worklist_reaches ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow>
      double_reverse_periodic_worklist_key \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow>
      double_reverse_periodic_worklist_set \<Rightarrow> bool"
  for motif view extent root where
  worklist_start:
    "double_reverse_periodic_worklist_reaches motif view extent root
       {root} {}"
| worklist_advance:
    "double_reverse_periodic_worklist_reaches motif view extent root
       pending seen \<Longrightarrow>
     double_reverse_periodic_worklist_step motif view extent pending seen
       pending' seen' \<Longrightarrow>
     double_reverse_periodic_worklist_reaches motif view extent root
       pending' seen'"

lemma double_reverse_periodic_worklist_step_preserves_cover:
  assumes root: "root \<in> pending \<union> seen"
      and closed:
        "\<And>key. key \<in> seen \<Longrightarrow>
          double_reverse_periodic_worklist_children motif view extent key
            \<subseteq> pending \<union> seen"
      and step:
        "double_reverse_periodic_worklist_step motif view extent
          pending seen pending' seen'"
  shows "root \<in> pending' \<union> seen' \<and>
    (\<forall>key\<in>seen'.
      double_reverse_periodic_worklist_children motif view extent key
        \<subseteq> pending' \<union> seen')"
proof -
  from step show ?thesis
  proof (cases rule: double_reverse_periodic_worklist_step.cases)
    case (pop_seen key)
    then show ?thesis using root closed by auto
  next
    case (expand_fresh key)
    then show ?thesis using root closed by auto
  qed
qed

lemma double_reverse_periodic_worklist_reaches_cover:
  assumes run:
    "double_reverse_periodic_worklist_reaches motif view extent root
      pending seen"
      and empty: "pending = {}"
  shows "root \<in> pending \<union> seen"
    and "double_reverse_periodic_worklist_children_closed motif view extent seen"
proof -
  have invariant:
    "root \<in> current_pending \<union> current_seen \<and>
     (\<forall>key\<in>current_seen.
       double_reverse_periodic_worklist_children motif view extent key
         \<subseteq> current_pending \<union> current_seen)"
    if "double_reverse_periodic_worklist_reaches motif view extent root
        current_pending current_seen"
    for current_pending current_seen
    using that
  proof (induction rule: double_reverse_periodic_worklist_reaches.induct)
    case worklist_start
    then show ?case by auto
  next
    case (worklist_advance pending seen pending' seen')
    have old_cover:
      "root \<in> pending \<union> seen"
      "\<And>key. key \<in> seen \<Longrightarrow>
        double_reverse_periodic_worklist_children motif view extent key
          \<subseteq> pending \<union> seen"
      using worklist_advance.IH by auto
    have transition:
      "double_reverse_periodic_worklist_step motif view extent
        pending seen pending' seen'"
      using worklist_advance.hyps(2) .
    have new_cover:
      "root \<in> pending' \<union> seen' \<and>
       (\<forall>key\<in>seen'.
         double_reverse_periodic_worklist_children motif view extent key
           \<subseteq> pending' \<union> seen')"
      using double_reverse_periodic_worklist_step_preserves_cover[OF old_cover(1)]
        old_cover(2) transition by blast
    show ?case using new_cover by auto
  qed
  have final:
    "root \<in> pending \<union> seen \<and>
     (\<forall>key\<in>seen.
       double_reverse_periodic_worklist_children motif view extent key
         \<subseteq> pending \<union> seen)"
    using invariant[OF run] by simp
  show "root \<in> pending \<union> seen" using final by blast
  show "double_reverse_periodic_worklist_children_closed motif view extent seen"
    using final empty
    unfolding double_reverse_periodic_worklist_children_closed_def by simp
qed

lemma double_reverse_periodic_worklist_closed_implies_certificate:
  assumes motif: "motif \<noteq> []"
      and represented:
        "double_reverse_source_arena_represents view extent node_id source"
      and root_seen: "(node_id, phase) \<in> seen"
      and closed:
        "double_reverse_periodic_worklist_children_closed motif view extent seen"
      and terminals:
        "double_reverse_periodic_worklist_terminals_ok motif view seen"
  shows "double_reverse_source_slp_phase_certificate motif source phase"
  using represented root_seen
proof (induction source arbitrary: node_id phase)
  case Double_Reverse_Source_Empty
  then show ?case by simp
next
  case (Double_Reverse_Source_Term digit)
  then show ?case
    using terminals motif
    by (auto simp: double_reverse_periodic_worklist_terminals_ok_def)
next
  case (Double_Reverse_Source_Concat left right)
  obtain left_id right_id where view:
      "view node_id = Double_Reverse_Arena_Concat left_id right_id"
    and left_extent:
      "extent node_id = extent left_id + extent right_id"
    and left_represents:
      "double_reverse_source_arena_represents view extent left_id left"
    and right_represents:
      "double_reverse_source_arena_represents view extent right_id right"
    using Double_Reverse_Source_Concat.prems(1)
    by (auto simp: double_reverse_source_arena_represents.simps)
  have root_seen: "(node_id, phase) \<in> seen"
    using Double_Reverse_Source_Concat.prems(2) .
  have child_subset:
    "double_reverse_periodic_worklist_children motif view extent (node_id, phase)
       \<subseteq> seen"
    using closed root_seen
    unfolding double_reverse_periodic_worklist_children_closed_def by blast
  have left_seen: "(left_id, phase) \<in> seen"
    using child_subset view by auto
  have right_seen:
    "(right_id, (phase + extent left_id) mod length motif) \<in> seen"
    using child_subset view by auto
  have left_len: "extent left_id = double_reverse_source_slp_length left"
    by (rule double_reverse_source_arena_represents_extent[OF left_represents])
  have left_certificate:
    "double_reverse_source_slp_phase_certificate motif left phase"
    by (rule Double_Reverse_Source_Concat.IH(1)[OF left_represents left_seen])
  have right_phase:
    "(phase + extent left_id) mod length motif =
      (phase + double_reverse_source_slp_length left) mod length motif"
    using left_len by simp
  have right_certificate:
    "double_reverse_source_slp_phase_certificate motif right
      ((phase + double_reverse_source_slp_length left) mod length motif)"
    using Double_Reverse_Source_Concat.IH(2)[OF right_represents right_seen]
      right_phase motif closed terminals by simp
  show ?case using left_certificate right_certificate by simp
next
  case (Double_Reverse_Source_Repeat child count)
  obtain child_id where view:
      "view node_id = Double_Reverse_Arena_Repeat child_id count"
    and extent_eq: "extent node_id = count * extent child_id"
    and child_represents:
      "double_reverse_source_arena_represents view extent child_id child"
    using Double_Reverse_Source_Repeat.prems(1)
    by (auto simp: double_reverse_source_arena_represents.simps)
  have root_seen: "(node_id, phase) \<in> seen"
    using Double_Reverse_Source_Repeat.prems(2) .
  have child_subset:
    "double_reverse_periodic_worklist_children motif view extent (node_id, phase)
       \<subseteq> seen"
    using closed root_seen
    unfolding double_reverse_periodic_worklist_children_closed_def by blast
  have child_len: "extent child_id = double_reverse_source_slp_length child"
    by (rule double_reverse_source_arena_represents_extent[OF child_represents])
  have representatives:
    "double_reverse_source_slp_phase_certificate motif child
      ((phase + copy * double_reverse_source_slp_length child) mod length motif)"
    if copy: "copy < min count
      (double_reverse_source_phase_cycle (length motif)
        (double_reverse_source_slp_length child))"
    for copy
  proof -
    have child_seen:
      "(child_id, (phase + copy * extent child_id) mod length motif) \<in> seen"
      using child_subset view copy child_len by auto
    have child_phase:
      "(phase + copy * extent child_id) mod length motif =
       (phase + copy * double_reverse_source_slp_length child) mod length motif"
      using child_len by simp
    show ?thesis
      using Double_Reverse_Source_Repeat.IH[OF child_represents child_seen]
        child_phase motif closed terminals by simp
  qed
  show ?case
    using representatives motif
    by (auto simp: double_reverse_periodic_worklist_terminals_ok_def)
qed

definition double_reverse_periodic_worklist_success ::
    "nat list \<Rightarrow>
      (nat \<Rightarrow> double_reverse_source_arena_node) \<Rightarrow>
      (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
      double_reverse_source_slp \<Rightarrow> nat \<Rightarrow> bool" where
  "double_reverse_periodic_worklist_success motif view extent root_id source phase
    \<longleftrightarrow>
    motif \<noteq> [] \<and> phase < length motif \<and>
    double_reverse_source_arena_represents view extent root_id source \<and>
    (\<exists>seen. double_reverse_periodic_worklist_reaches motif view extent
        (root_id, phase) {} seen \<and>
      (root_id, phase) \<in> seen \<and>
      double_reverse_periodic_resolver_success motif view extent seen
        (root_id, phase))"

theorem double_reverse_periodic_worklist_success_certificate:
  assumes success:
    "double_reverse_periodic_worklist_success motif view extent root_id source phase"
  shows "double_reverse_source_slp_phase_certificate motif source phase"
proof -
  obtain seen where motif: "motif \<noteq> []"
      and phase: "phase < length motif"
      and represented:
        "double_reverse_source_arena_represents view extent root_id source"
      and run:
        "double_reverse_periodic_worklist_reaches motif view extent
          (root_id, phase) {} seen"
      and root_seen: "(root_id, phase) \<in> seen"
      and resolver:
        "double_reverse_periodic_resolver_success motif view extent seen
          (root_id, phase)"
    using success unfolding double_reverse_periodic_worklist_success_def by blast
  obtain processed true_set where resolver_run:
      "double_reverse_periodic_resolver_reaches motif view extent seen
        processed true_set"
    and processed_all: "processed = seen"
    and ready_empty:
      "double_reverse_periodic_resolver_ready motif view extent seen processed = {}"
    and root_true: "(root_id, phase) \<in> true_set"
    using resolver unfolding double_reverse_periodic_resolver_success_def
    by blast
  have resolver_wellformed:
      "double_reverse_periodic_resolver_wellformed motif view extent true_set"
    by (rule double_reverse_periodic_resolver_reaches_wellformed[OF motif resolver_run])
  have closed:
      "double_reverse_periodic_worklist_children_closed motif view extent true_set"
    and terminals:
      "double_reverse_periodic_worklist_terminals_ok motif view true_set"
    using resolver_wellformed
    by (auto simp: double_reverse_periodic_resolver_wellformed_def)
  show ?thesis
    by (rule double_reverse_periodic_worklist_closed_implies_certificate
      [OF motif represented root_true closed terminals])
qed

text \<open>This corollary wires the successful ID/phase worklist to the packed
pointed consumer. The arena root is explicitly represented by the exact
window SLP passed to the consumer; the worklist-derived phase certificate
replaces the former assumed certificate premise.\<close>

theorem double_reverse_packed_request_worklist_point_refines_ring:
  fixes source :: "double_reverse_source_slp"
    and merged_begin :: int
    and phase steps start count position span digit :: nat
    and motif :: "nat list"
    and source_word :: "nat list"
    and radius source_cells output_cells middle_length first :: nat
    and origin :: int
    and middle window_slp :: "double_reverse_source_slp"
    and view :: "nat \<Rightarrow> double_reverse_source_arena_node"
    and extent :: "nat \<Rightarrow> nat"
    and root_id :: nat
  defines "source_word \<equiv> double_reverse_source_slp_word source"
      and "radius \<equiv> double_reverse_packed_merged_radius span"
      and "source_cells \<equiv> double_reverse_packed_merged_source_cells span"
      and "output_cells \<equiv>
        double_reverse_packed_merged_output_cells span steps"
      and "origin \<equiv> merged_begin + int radius"
      and "middle_length \<equiv>
        double_reverse_source_window_middle_length source_word merged_begin source_cells"
      and "first \<equiv> double_reverse_source_window_first merged_begin"
      and "middle \<equiv>
        (if middle_length = 0 then Double_Reverse_Source_Empty
         else double_reverse_source_slp_part source first
           (first + middle_length))"
      and "window_slp \<equiv>
        double_reverse_source_window_slp source_word merged_begin source_cells middle"
  assumes phase: "phase < 4"
      and count: "0 < count"
      and position: "position < count"
      and merged_left_cover: "merged_begin \<le>
        double_reverse_packed_runtime_request_begin phase steps start count"
      and merged_right_cover: "double_reverse_packed_runtime_request_end
        phase steps start count \<le>
        merged_begin + int span"
      and output_positive: "0 < output_cells"
      and motif: "motif \<noteq> []"
      and worklist:
        "double_reverse_periodic_worklist_success motif view extent root_id
          window_slp 0"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source_word origin radius)"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes
        (double_reverse_pointed_source_window source_word origin radius))
      source_cells ! digit)
      (double_reverse_packed_row_position phase steps start count
        merged_begin position) \<longleftrightarrow>
    double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
      (double_reverse_packed_row_position phase steps start count
        merged_begin position) = digit"
proof -
  have certificate:
    "double_reverse_source_slp_phase_certificate motif window_slp 0"
    by (rule double_reverse_periodic_worklist_success_certificate[OF worklist])
  show ?thesis
    using phase count position merged_left_cover merged_right_cover
      output_positive motif certificate decimal digit
    unfolding source_word_def radius_def source_cells_def output_cells_def
      origin_def middle_length_def first_def middle_def window_slp_def
    by (rule double_reverse_packed_request_point_refines_ring)
qed

ML \<open>
  val checked = @{thms
    double_reverse_source_arena_represents_extent
    double_reverse_periodic_resolver_step_preserves_wellformed
    double_reverse_periodic_resolver_reaches_wellformed
    double_reverse_periodic_worklist_step_preserves_cover
    double_reverse_periodic_worklist_reaches_cover
    double_reverse_periodic_worklist_closed_implies_certificate
    double_reverse_periodic_worklist_success_certificate
    double_reverse_packed_request_worklist_point_refines_ring};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Periodic worklist refinement depends on an oracle";
\<close>

end
