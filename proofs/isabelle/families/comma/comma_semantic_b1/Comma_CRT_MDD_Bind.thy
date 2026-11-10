theory Comma_CRT_MDD_Bind
  imports Comma_CRT_MDD_Preimage
begin

text \<open>
A bind certificate is a flat-DAG proof of substitution.  At a leaf it selects
one mapped root.  At a branch it cofactors the source, fallback_root, and every
mapped root at the same axis and certifies each child under the slot binder.
The output table remains shared; the certificate does not enumerate full
coordinate vectors.
\<close>

definition comma_crt_mdd_bind_target :: "nat \<Rightarrow> ('a::equal \<times> nat) list \<Rightarrow> 'a \<Rightarrow> nat" where
  "comma_crt_mdd_bind_target fallback_root mapping payload =
    (case map_of mapping payload of None \<Rightarrow> fallback_root | Some root \<Rightarrow> root)"

lemma comma_crt_mdd_bind_target_boolean:
  fixes fallback_root no_root yes_root :: nat
  shows "comma_crt_mdd_bind_target fallback_root
      [(0::nat,no_root),(1::nat,yes_root)] (if condition then 1 else 0) =
    (if condition then yes_root else no_root)"
  by (cases condition)
     (simp_all add: comma_crt_mdd_bind_target_def map_of.simps)

lemma comma_crt_mdd_boolean_bind_hit:
  fixes evaluate :: "nat \<Rightarrow> nat option"
  assumes binding: "evaluate result =
      (case evaluate guard of None \<Rightarrow> evaluate no_root
       | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target no_root
             [(0,no_root),(1,yes_root)] payload))"
    and selection: "evaluate guard = Some (if condition then 1 else 0)"
    and yes: "(evaluate yes_root = Some value) = yes_observation"
    and no: "(evaluate no_root = Some value) = no_observation"
  shows "(evaluate result = Some value) =
    (if condition then yes_observation else no_observation)"
  using binding selection yes no
  by (cases condition)
     (simp_all add: comma_crt_mdd_bind_target_def map_of.simps)

fun comma_crt_mdd_cofactor_mapping ::
  "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('v \<times> nat) list \<Rightarrow> ('v \<times> nat) list option" where
  "comma_crt_mdd_cofactor_mapping radices nodes axis slot [] = Some []"
| "comma_crt_mdd_cofactor_mapping radices nodes axis slot ((payload,root)#mapping) =
    (case comma_crt_mdd_cofactor radices nodes axis slot root of
       None \<Rightarrow> None
     | Some child \<Rightarrow>
         (case comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping of
            None \<Rightarrow> None
          | Some rest \<Rightarrow> Some ((payload,child)#rest)))"

text \<open>
A frozen root has one cofactor family at a requested axis.  A leaf and a
branch that skips the requested earlier axis repeat the root in every slot; a
branch at the requested axis exposes its child vector.  Requesting an axis
past a branch is malformed and remains rejected by the partial cofactor.
\<close>

definition comma_crt_mdd_cofactor_family_admitted ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_crt_mdd_cofactor_family_admitted radices nodes axis root \<longleftrightarrow>
    axis < length radices \<and> 0 < radices ! axis \<and> root < length nodes \<and>
    (case nodes ! root of
       Comma_CRT_MDD_Leaf _ \<Rightarrow> True
     | Comma_CRT_MDD_Branch node_axis _ \<Rightarrow> axis \<le> node_axis)"

definition comma_crt_mdd_cofactor_family_child ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_mdd_cofactor_family_child radices nodes axis root slot =
    (case nodes ! root of
       Comma_CRT_MDD_Leaf _ \<Rightarrow> root
     | Comma_CRT_MDD_Branch node_axis children \<Rightarrow>
         if node_axis = axis then children ! slot else root)"

lemma comma_crt_mdd_cofactor_family_exact:
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and admitted:
      "comma_crt_mdd_cofactor_family_admitted radices nodes axis root"
  shows "\<And>slot. slot < radices ! axis \<Longrightarrow>
    comma_crt_mdd_cofactor radices nodes axis slot root =
      Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
proof -
  have axis: "axis < length radices"
    and positive: "0 < radices ! axis"
    and root: "root < length nodes"
    using admitted by (auto simp: comma_crt_mdd_cofactor_family_admitted_def)
  fix slot
  assume slot: "slot < radices ! axis"
  show "comma_crt_mdd_cofactor radices nodes axis slot root =
      Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
  proof (cases "nodes ! root")
    case (Comma_CRT_MDD_Leaf payload)
    then show ?thesis using axis positive root slot
      by (simp add: comma_crt_mdd_cofactor_def
        comma_crt_mdd_cofactor_family_child_def)
  next
    case (Comma_CRT_MDD_Branch node_axis children)
    have node_facts:
      "node_axis < length radices"
      "0 < radices ! node_axis"
      "length children = radices ! node_axis"
      using comma_crt_mdd_branch_facts[OF table root Comma_CRT_MDD_Branch]
      by blast+
    have ordered_axis: "axis \<le> node_axis"
      using admitted Comma_CRT_MDD_Branch
      by (simp add: comma_crt_mdd_cofactor_family_admitted_def)
    show ?thesis
      using axis positive root slot node_facts ordered_axis Comma_CRT_MDD_Branch
      by (auto simp: comma_crt_mdd_cofactor_def
        comma_crt_mdd_cofactor_family_child_def split: if_splits)
  qed
qed

lemma comma_crt_mdd_cofactor_family_skipped_axis_rejected:
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and axis: "axis < length radices"
    and positive: "0 < radices ! axis"
    and root: "root < length nodes"
    and slot: "slot < radices ! axis"
    and branch: "nodes ! root = Comma_CRT_MDD_Branch node_axis children"
    and skipped: "node_axis < axis"
  shows "comma_crt_mdd_cofactor radices nodes axis slot root = None"
proof -
  have node_facts:
    "node_axis < length radices"
    "0 < radices ! node_axis"
    "length children = radices ! node_axis"
    using comma_crt_mdd_branch_facts[OF table root branch]
    by blast+
  show ?thesis using axis positive root slot node_facts branch skipped
    by (simp add: comma_crt_mdd_cofactor_def)
qed

lemma comma_crt_mdd_cofactor_mapping_cons:
  assumes head:
      "comma_crt_mdd_cofactor radices nodes axis slot root = Some child"
    and tail:
      "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping = Some rest"
  shows "comma_crt_mdd_cofactor_mapping radices nodes axis slot
      ((payload,root)#mapping) = Some ((payload,child)#rest)"
  using head tail by simp

lemma comma_crt_mdd_cofactor_mapping_map_payload:
  "comma_crt_mdd_cofactor_mapping radices nodes axis slot
      (map (\<lambda>(payload,root). (project payload,root)) mapping) =
    map_option (map (\<lambda>(payload,root). (project payload,root)))
      (comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping)"
  by (induction mapping) (auto split: option.splits prod.splits)

lemma comma_crt_mdd_cofactor_map_nodes:
  "comma_crt_mdd_cofactor radices (comma_crt_mdd_map_nodes project nodes)
      axis slot root = comma_crt_mdd_cofactor radices nodes axis slot root"
  by (auto simp: comma_crt_mdd_cofactor_def comma_crt_mdd_map_nodes_def
      nth_map split: comma_crt_mdd_node.splits if_splits)

lemma comma_crt_mdd_cofactor_mapping_map_nodes:
  "comma_crt_mdd_cofactor_mapping radices
      (comma_crt_mdd_map_nodes project nodes) axis slot mapping =
    comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping"
  by (induction mapping) (auto simp: comma_crt_mdd_cofactor_map_nodes
      split: option.splits prod.splits)

lemma comma_crt_mdd_cofactor_mapping_family_from_roots:
  fixes mapping :: "('a::equal \<times> nat) list"
  assumes root_families: "\<And>root slot.
      root \<in> set (map snd mapping) \<Longrightarrow> slot < radix \<Longrightarrow>
      comma_crt_mdd_cofactor radices nodes axis slot root =
        Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
  shows "\<And>slot. slot < radix \<Longrightarrow>
    comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
      Some (map (\<lambda>(payload,root).
        (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)"
  proof -
  fix slot
  assume slot: "slot < radix"
  have root_families_at_slot: "\<And>root.
      root \<in> set (map snd mapping) \<Longrightarrow>
      comma_crt_mdd_cofactor radices nodes axis slot root =
        Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
    using root_families slot by blast
  show "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
      Some (map (\<lambda>(payload,root).
        (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)"
    using root_families_at_slot
  proof (induction mapping)
    case Nil
    then show ?case by simp
  next
    case (Cons item mapping)
    obtain payload root where item: "item = (payload,root)"
      by (cases item) auto
    have root_member: "root \<in> set (map snd (item#mapping))"
      using item by simp
    have head:
      "comma_crt_mdd_cofactor radices nodes axis slot root =
        Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
      using Cons.prems root_member by blast
    have tail_families: "\<And>root.
        root \<in> set (map snd mapping) \<Longrightarrow>
        comma_crt_mdd_cofactor radices nodes axis slot root =
          Some (comma_crt_mdd_cofactor_family_child radices nodes axis root slot)"
      using Cons.prems by auto
    have tail:
      "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
        Some (map (\<lambda>(payload,root).
          (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)"
      by (rule Cons.IH[OF tail_families])
    show ?case
      using comma_crt_mdd_cofactor_mapping_cons[OF head tail] item by simp
  qed
qed

lemma comma_crt_mdd_reduced_branch_eval:
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and bound: "result < length nodes"
    and axis: "axis < length radices"
    and positive: "0 < radices ! axis"
    and width: "length children = radices ! axis"
    and shape: "nodes ! result = Comma_CRT_MDD_Branch axis children \<or>
      list_all (\<lambda>child. child=result) children"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate result =
    comma_crt_mdd_eval_raw radices nodes coordinate
      (children ! (coordinate axis mod radices ! axis))"
proof -
  let ?child = "children ! (coordinate axis mod radices ! axis)"
  have position: "coordinate axis mod radices ! axis < length children"
    using positive width by simp
  have member: "?child \<in> set children" by (rule nth_mem[OF position])
  show ?thesis
  proof (cases "nodes ! result = Comma_CRT_MDD_Branch axis children")
    case True
    have ordered: "comma_crt_mdd_node_ordered radices nodes result"
      using table bound unfolding comma_crt_mdd_table_wellformed_def by blast
    have earlier: "?child < result"
      using ordered bound True member
      by (auto simp: comma_crt_mdd_node_ordered_def)
    show ?thesis
      by (rule comma_crt_mdd_eval_raw_branch
        [where coordinate=coordinate, OF bound True axis positive width refl earlier])
  next
    case False
    have same: "?child=result"
      using False shape member by (auto simp: list_all_iff)
    show ?thesis by (simp only: same)
  qed
qed

lemma comma_crt_mdd_bind_target_restrict:
  assumes "payload \<in> labels"
  shows "comma_crt_mdd_bind_target fallback_root
      (filter (\<lambda>item. fst item \<in> labels) mapping) payload =
    comma_crt_mdd_bind_target fallback_root mapping payload"
proof -
  have lookup: "map_of (filter (\<lambda>item. fst item \<in> labels) mapping) payload =
      map_of mapping payload"
  proof (induction mapping)
    case Nil
    then show ?case by simp
  next
    case (Cons item mapping)
    obtain label root where item: "item=(label,root)" by (cases item) auto
    show ?case using Cons.IH assms by (auto simp: item)
  qed
  show ?thesis by (simp only: comma_crt_mdd_bind_target_def lookup)
qed

inductive comma_crt_mdd_bind_certificate ::
  "nat list \<Rightarrow> ('a::equal comma_crt_mdd_node) list \<Rightarrow>
    ('a \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices nodes where
  bind_leaf:
    "\<lbrakk>source < length nodes;
      nodes ! source = Comma_CRT_MDD_Leaf payload;
      result = comma_crt_mdd_bind_target fallback_root mapping payload;
      result < length nodes; fallback_root < length nodes;
      \<forall>root\<in>set (map snd mapping). root < length nodes\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_bind_certificate radices nodes mapping fallback_root source result"
| bind_branch:
    "\<lbrakk>source < length nodes;
      result < length nodes;
      (nodes ! result = Comma_CRT_MDD_Branch axis children \<or>
        list_all (\<lambda>child. child=result) children);
      axis < length radices;
      0 < radices ! axis;
      length children = radices ! axis;
      (\<forall>root\<in>set (source # fallback_root # map snd mapping). root < length nodes);
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_cofactor radices nodes axis slot source = Some (source_child slot));
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_cofactor radices nodes axis slot fallback_root = Some (default_child slot));
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping = Some (mapping_child slot));
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_bind_certificate radices nodes (mapping_child slot)
          (default_child slot) (source_child slot) (children ! slot))\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_bind_certificate radices nodes mapping fallback_root source result"
| bind_restrict:
    "\<lbrakk>source < length nodes;
      comma_crt_mdd_payload_cover nodes source labels;
      comma_crt_mdd_bind_certificate radices nodes
        (filter (\<lambda>item. fst item \<in> set labels) mapping)
        fallback_root source result\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_bind_certificate radices nodes
        mapping fallback_root source result"

lemma comma_crt_mdd_bind_branch_row_transport:
  fixes mapping :: "('a::equal \<times> nat) list"
    and source_children fallback_children result_children :: "nat list"
    and mapping_children :: "('a \<times> nat) list list"
  assumes source_family:
      "\<And>slot. slot < radix \<Longrightarrow>
        comma_crt_mdd_cofactor radices nodes axis slot source =
          Some (comma_crt_mdd_cofactor_family_child radices nodes axis source slot)"
    and fallback_family:
      "\<And>slot. slot < radix \<Longrightarrow>
        comma_crt_mdd_cofactor radices nodes axis slot fallback_root =
          Some (comma_crt_mdd_cofactor_family_child radices nodes axis fallback_root slot)"
    and mapping_family:
      "\<And>slot. slot < radix \<Longrightarrow>
        comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
          Some (map (\<lambda>(payload,root).
            (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)"
    and source_children_exact:
      "source_children = map (\<lambda>slot.
        comma_crt_mdd_cofactor_family_child radices nodes axis source slot)
        [0..<radix]"
    and fallback_children_exact:
      "fallback_children = map (\<lambda>slot.
        comma_crt_mdd_cofactor_family_child radices nodes axis fallback_root slot)
        [0..<radix]"
    and mapping_children_exact:
      "mapping_children = map (\<lambda>slot. map (\<lambda>(payload,root).
        (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)
        [0..<radix]"
    and child_certificates:
      "list_all (\<lambda>slot. comma_crt_mdd_bind_certificate radices nodes
        (mapping_children ! slot) (fallback_children ! slot)
        (source_children ! slot) (result_children ! slot)) [0..<radix]"
  shows "\<And>slot. slot < radix \<Longrightarrow>
    comma_crt_mdd_cofactor radices nodes axis slot source =
      Some (source_children ! slot) \<and>
    comma_crt_mdd_cofactor radices nodes axis slot fallback_root =
      Some (fallback_children ! slot) \<and>
    comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
      Some (mapping_children ! slot) \<and>
    comma_crt_mdd_bind_certificate radices nodes (mapping_children ! slot)
      (fallback_children ! slot) (source_children ! slot) (result_children ! slot)"
proof -
  fix slot
  assume slot: "slot < radix"
  have source_at_slot:
    "comma_crt_mdd_cofactor radices nodes axis slot source =
      Some (comma_crt_mdd_cofactor_family_child radices nodes axis source slot)"
    by (rule source_family[OF slot])
  have fallback_at_slot:
    "comma_crt_mdd_cofactor radices nodes axis slot fallback_root =
      Some (comma_crt_mdd_cofactor_family_child radices nodes axis fallback_root slot)"
    by (rule fallback_family[OF slot])
  have mapping_at_slot:
    "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
      Some (map (\<lambda>(payload,root).
        (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping)"
    by (rule mapping_family[OF slot])
  have source_nth:
    "source_children ! slot =
      comma_crt_mdd_cofactor_family_child radices nodes axis source slot"
    using source_children_exact slot by simp
  have fallback_nth:
    "fallback_children ! slot =
      comma_crt_mdd_cofactor_family_child radices nodes axis fallback_root slot"
    using fallback_children_exact slot by simp
  have mapping_nth:
    "mapping_children ! slot = map (\<lambda>(payload,root).
      (payload, comma_crt_mdd_cofactor_family_child radices nodes axis root slot)) mapping"
    using mapping_children_exact slot by simp
  have child:
    "comma_crt_mdd_bind_certificate radices nodes (mapping_children ! slot)
      (fallback_children ! slot) (source_children ! slot) (result_children ! slot)"
    by (rule comma_crt_mdd_indexed_allD[OF child_certificates slot])
  show "comma_crt_mdd_cofactor radices nodes axis slot source =
      Some (source_children ! slot) \<and>
    comma_crt_mdd_cofactor radices nodes axis slot fallback_root =
      Some (fallback_children ! slot) \<and>
    comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping =
      Some (mapping_children ! slot) \<and>
    comma_crt_mdd_bind_certificate radices nodes (mapping_children ! slot)
      (fallback_children ! slot) (source_children ! slot) (result_children ! slot)"
    using source_at_slot fallback_at_slot mapping_at_slot
      source_nth fallback_nth mapping_nth child by simp
qed

lemma comma_crt_mdd_bind_certificate_result_bound:
  assumes "comma_crt_mdd_bind_certificate radices nodes mapping fallback_root source result"
  shows "result < length nodes"
  using assms
  by (induction rule: comma_crt_mdd_bind_certificate.induct) auto

lemma comma_crt_mdd_bind_target_cofactor:
  assumes default_cofactor:
      "comma_crt_mdd_cofactor radices nodes axis slot fallback_root = Some default_child"
    and mapping_cofactor:
      "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping = Some mapping_child"
  shows "comma_crt_mdd_cofactor radices nodes axis slot
      (comma_crt_mdd_bind_target fallback_root mapping payload) =
    Some (comma_crt_mdd_bind_target default_child mapping_child payload)"
  using default_cofactor mapping_cofactor
proof (induction mapping arbitrary: mapping_child)
  case Nil
  then show ?case by (simp add: comma_crt_mdd_bind_target_def)
next
  case (Cons item mapping)
  obtain label root where item: "item = (label,root)" by (cases item) auto
  obtain child rest where root_cofactor:
      "comma_crt_mdd_cofactor radices nodes axis slot root = Some child"
    and rest_cofactor:
      "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping = Some rest"
    and mapped: "mapping_child = (label,child)#rest"
    using Cons.prems(2) item
    by (cases "comma_crt_mdd_cofactor radices nodes axis slot root";
        cases "comma_crt_mdd_cofactor_mapping radices nodes axis slot mapping")
      auto
  show ?case
  proof (cases "payload = label")
    case True
    then show ?thesis
      using root_cofactor mapped
      by (simp add: comma_crt_mdd_bind_target_def item)
  next
    case False
    have ih:
      "comma_crt_mdd_cofactor radices nodes axis slot
          (comma_crt_mdd_bind_target fallback_root mapping payload) =
       Some (comma_crt_mdd_bind_target default_child rest payload)"
      by (rule Cons.IH[OF Cons.prems(1) rest_cofactor])
    show ?thesis
      using ih root_cofactor mapped False
      by (simp add: comma_crt_mdd_bind_target_def item)
  qed
qed

lemma comma_crt_mdd_bind_target_bound:
  assumes fallback_root: "fallback_root < length nodes"
    and mapped: "\<And>root. root \<in> set (map snd mapping) \<Longrightarrow> root < length nodes"
  shows "comma_crt_mdd_bind_target fallback_root mapping payload < length nodes"
proof (cases "map_of mapping payload")
  case None then show ?thesis using fallback_root
    by (simp add: comma_crt_mdd_bind_target_def)
next
  case (Some root)
  have pair_member: "(payload,root) \<in> set mapping"
    using Some by (rule map_of_SomeD)
  have root_member: "root \<in> set (map snd mapping)"
  proof -
    have "snd (payload,root) \<in> snd ` set mapping"
      by (rule imageI[OF pair_member])
    then show ?thesis by simp
  qed
  show ?thesis using mapped[OF root_member] Some
    by (simp add: comma_crt_mdd_bind_target_def)
qed

lemma comma_crt_mdd_bind_certificate_eval:
  fixes radices nodes
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and certificate:
      "comma_crt_mdd_bind_certificate radices nodes mapping fallback_root source result"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate result =
    (case comma_crt_mdd_eval_raw radices nodes coordinate source of
       None \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate fallback_root
     | Some payload \<Rightarrow>
         comma_crt_mdd_eval_raw radices nodes coordinate
           (comma_crt_mdd_bind_target fallback_root mapping payload))"
  using certificate
proof (induction rule: comma_crt_mdd_bind_certificate.induct)
  case (bind_leaf source payload result fallback_root mapping)
  have source_eval:
    "comma_crt_mdd_eval_raw radices nodes coordinate source = Some payload"
    by (rule comma_crt_mdd_eval_raw_leaf[OF bind_leaf.hyps(1) bind_leaf.hyps(2)])
  have result_eq: "result = comma_crt_mdd_bind_target fallback_root mapping payload"
    by (rule bind_leaf.hyps(3))
  show ?case using source_eval result_eq by simp
next
  case (bind_branch source result axis children fallback_root mapping source_child default_child mapping_child)
  let ?slot = "coordinate axis mod radices ! axis"
  have slot_bound: "?slot < radices ! axis"
    using bind_branch.hyps(4,5) by simp
  have source_cofactor:
    "comma_crt_mdd_cofactor radices nodes axis ?slot source = Some (source_child ?slot)"
    by (rule bind_branch.hyps(8)[OF slot_bound])
  have default_cofactor:
    "comma_crt_mdd_cofactor radices nodes axis ?slot fallback_root = Some (default_child ?slot)"
    by (rule bind_branch.hyps(9)[OF slot_bound])
  have mapping_cofactor:
    "comma_crt_mdd_cofactor_mapping radices nodes axis ?slot mapping = Some (mapping_child ?slot)"
    by (rule bind_branch.hyps(10)[OF slot_bound])
  have output_step:
    "comma_crt_mdd_eval_raw radices nodes coordinate result =
      comma_crt_mdd_eval_raw radices nodes coordinate (children ! ?slot)"
    by (rule comma_crt_mdd_reduced_branch_eval
      [where coordinate=coordinate, OF table bind_branch.hyps(2,4,5,6,3)])
  have child_semantics:
    "comma_crt_mdd_eval_raw radices nodes coordinate (children ! ?slot) =
      (case comma_crt_mdd_eval_raw radices nodes coordinate (source_child ?slot) of
        None \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate (default_child ?slot)
      | Some payload \<Rightarrow>
          comma_crt_mdd_eval_raw radices nodes coordinate
            (comma_crt_mdd_bind_target (default_child ?slot) (mapping_child ?slot) payload))"
    by (rule bind_branch.IH[OF slot_bound])
  have source_bound:
    "source < length nodes" by (rule bind_branch.hyps(1))
  have default_bound:
    "fallback_root < length nodes"
    using bind_branch.hyps(7) by (auto simp: set_ConsD)
  have source_current:
    "comma_crt_mdd_eval_raw radices nodes coordinate source =
      comma_crt_mdd_eval_raw radices nodes coordinate (source_child ?slot)"
    by (rule comma_crt_mdd_cofactor_current_eval
      [where coordinate=coordinate,
        OF source_bound table bind_branch.hyps(4,5) slot_bound refl source_cofactor])
  have default_current:
    "comma_crt_mdd_eval_raw radices nodes coordinate fallback_root =
      comma_crt_mdd_eval_raw radices nodes coordinate (default_child ?slot)"
    by (rule comma_crt_mdd_cofactor_current_eval
      [where coordinate=coordinate,
        OF default_bound table bind_branch.hyps(4,5) slot_bound refl default_cofactor])
  have mapped_bounds:
    "\<And>root. root \<in> set (map snd mapping) \<Longrightarrow> root < length nodes"
    using bind_branch.hyps(7) by (auto simp: set_ConsD)
  have destination_bound:
    "comma_crt_mdd_bind_target fallback_root mapping payload < length nodes" for payload
    by (rule comma_crt_mdd_bind_target_bound[OF default_bound mapped_bounds])
  have destination_cofactor:
    "comma_crt_mdd_cofactor radices nodes axis ?slot
        (comma_crt_mdd_bind_target fallback_root mapping payload) =
      Some (comma_crt_mdd_bind_target (default_child ?slot) (mapping_child ?slot) payload)"
    for payload
    by (rule comma_crt_mdd_bind_target_cofactor[OF default_cofactor mapping_cofactor])
  have destination_current:
    "comma_crt_mdd_eval_raw radices nodes coordinate
        (comma_crt_mdd_bind_target fallback_root mapping payload) =
      comma_crt_mdd_eval_raw radices nodes coordinate
        (comma_crt_mdd_bind_target (default_child ?slot) (mapping_child ?slot) payload)"
    for payload
    by (rule comma_crt_mdd_cofactor_current_eval
      [where coordinate=coordinate,
        OF destination_bound table bind_branch.hyps(4,5) slot_bound refl destination_cofactor])
  have combined:
    "comma_crt_mdd_eval_raw radices nodes coordinate result =
      (case comma_crt_mdd_eval_raw radices nodes coordinate (source_child ?slot) of
         None \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate (default_child ?slot)
       | Some payload \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate
           (comma_crt_mdd_bind_target (default_child ?slot) (mapping_child ?slot) payload))"
    by (rule trans[OF output_step child_semantics])
  show ?case
    using combined
    by (simp only: source_current[symmetric] default_current[symmetric]
        destination_current[symmetric])
next
  case (bind_restrict source labels mapping fallback_root result)
  show ?case
  proof (cases "comma_crt_mdd_eval_raw radices nodes coordinate source")
    case None
    then show ?thesis using bind_restrict.IH by simp
  next
    case (Some payload)
    have covered: "payload \<in> set labels"
      by (rule comma_crt_mdd_eval_raw_payload_covered
        [OF table bind_restrict.hyps(1,2) Some])
    show ?thesis using bind_restrict.IH Some
      comma_crt_mdd_bind_target_restrict[OF covered] by simp
  qed
qed

lemma comma_crt_mdd_bind_restricted_certificate_eval:
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and support: "\<And>payload.
      comma_crt_mdd_eval_raw radices nodes coordinate source = Some payload
      \<Longrightarrow> payload \<in> labels"
    and certificate: "comma_crt_mdd_bind_certificate radices nodes
      (filter (\<lambda>item. fst item \<in> labels) mapping) fallback_root source result"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate result =
    (case comma_crt_mdd_eval_raw radices nodes coordinate source of
       None \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate fallback_root
     | Some payload \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate
         (comma_crt_mdd_bind_target fallback_root mapping payload))"
proof -
  have restricted:
    "comma_crt_mdd_eval_raw radices nodes coordinate result =
      (case comma_crt_mdd_eval_raw radices nodes coordinate source of
         None \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate fallback_root
       | Some payload \<Rightarrow> comma_crt_mdd_eval_raw radices nodes coordinate
           (comma_crt_mdd_bind_target fallback_root
             (filter (\<lambda>item. fst item \<in> labels) mapping) payload))"
    by (rule comma_crt_mdd_bind_certificate_eval[OF table certificate])
  show ?thesis
  proof (cases "comma_crt_mdd_eval_raw radices nodes coordinate source")
    case None
    then show ?thesis using restricted by simp
  next
    case (Some payload)
    have member: "payload \<in> labels" by (rule support[OF Some])
    show ?thesis
      using restricted Some comma_crt_mdd_bind_target_restrict[OF member]
      by simp
  qed
qed

lemma comma_crt_mdd_bind_certificate_eval_phase:
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and certificate: "comma_crt_mdd_bind_certificate radices nodes
      mapping fallback_root source result"
  shows "comma_crt_mdd_eval_phase radices nodes phase result =
    (case comma_crt_mdd_eval_phase radices nodes phase source of
       None \<Rightarrow> comma_crt_mdd_eval_phase radices nodes phase fallback_root
     | Some payload \<Rightarrow> comma_crt_mdd_eval_phase radices nodes phase
         (comma_crt_mdd_bind_target fallback_root mapping payload))"
  using comma_crt_mdd_bind_certificate_eval[OF table certificate,
    where coordinate="\<lambda>axis. phase"]
  by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def table if_True)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Shared MDD substitution and support-restricted mapping"
    @{thms comma_crt_mdd_reduced_branch_eval
      comma_crt_mdd_bind_target_boolean
      comma_crt_mdd_boolean_bind_hit
      comma_crt_mdd_bind_certificate_result_bound
      comma_crt_mdd_bind_certificate_eval
      comma_crt_mdd_bind_certificate_eval_phase
      comma_crt_mdd_bind_restricted_certificate_eval
      comma_crt_mdd_cofactor_family_admitted_def
      comma_crt_mdd_cofactor_family_child_def
      comma_crt_mdd_cofactor_family_exact
      comma_crt_mdd_cofactor_family_skipped_axis_rejected
      comma_crt_mdd_cofactor_mapping_cons
      comma_crt_mdd_cofactor_mapping_map_payload
      comma_crt_mdd_cofactor_map_nodes
      comma_crt_mdd_cofactor_mapping_map_nodes
      comma_crt_mdd_cofactor_mapping_family_from_roots
      comma_crt_mdd_bind_branch_row_transport};
\<close>

end
