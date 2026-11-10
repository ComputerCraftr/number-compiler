theory Comma_CRT_MDD_Transport
  imports Comma_CRT_MDD_Bind
begin

text \<open>
Transport evaluation between a local typed MDD and a shared arena table.
The relation allows the shared arena to reduce a branch whose children all
intern to one root.  This theorem records semantic transport; proposal-side
integer IDs alone do not establish it.
\<close>

inductive comma_crt_mdd_root_map_certificate ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow>
      'b comma_crt_mdd_node list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices source_nodes target_nodes encode where
  map_leaf:
    "\<lbrakk>source < length source_nodes; target < length target_nodes;
      source_nodes ! source = Comma_CRT_MDD_Leaf payload;
      target_nodes ! target = Comma_CRT_MDD_Leaf (encode payload)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_map_certificate radices
        source_nodes target_nodes encode source target"
| map_branch:
    "\<lbrakk>source < length source_nodes; target < length target_nodes;
      source_nodes ! source = Comma_CRT_MDD_Branch axis source_children;
      target_nodes ! target = Comma_CRT_MDD_Branch axis target_children;
      axis < length radices; 0 < radices ! axis;
      length source_children = radices ! axis;
      length target_children = radices ! axis;
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_root_map_certificate radices source_nodes target_nodes
          encode (source_children ! slot) (target_children ! slot))\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_map_certificate radices
        source_nodes target_nodes encode source target"
| map_reduced_alias:
    "\<lbrakk>source < length source_nodes; target < length target_nodes;
      source_nodes ! source = Comma_CRT_MDD_Branch axis source_children;
      axis < length radices; 0 < radices ! axis;
      length source_children = radices ! axis;
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_root_map_certificate radices source_nodes target_nodes
          encode (source_children ! slot) target)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_map_certificate radices
        source_nodes target_nodes encode source target"

lemma comma_crt_mdd_root_map_certificate_eval_raw:
  assumes source_wf: "comma_crt_mdd_table_wellformed radices source_nodes"
    and target_wf: "comma_crt_mdd_table_wellformed radices target_nodes"
    and certificate:
      "comma_crt_mdd_root_map_certificate radices source_nodes target_nodes
        encode source target"
  shows "comma_crt_mdd_eval_raw radices target_nodes coordinate target =
    map_option encode (comma_crt_mdd_eval_raw radices source_nodes coordinate source)"
  using certificate
proof (induction rule: comma_crt_mdd_root_map_certificate.induct)
  case (map_leaf source target payload)
  have source_value:
    "comma_crt_mdd_eval_raw radices source_nodes coordinate source = Some payload"
    by (rule comma_crt_mdd_eval_raw_leaf[OF map_leaf.hyps(1) map_leaf.hyps(3)])
  have target_value:
    "comma_crt_mdd_eval_raw radices target_nodes coordinate target = Some (encode payload)"
    by (rule comma_crt_mdd_eval_raw_leaf[OF map_leaf.hyps(2) map_leaf.hyps(4)])
  show ?case using source_value target_value by simp
next
  case (map_branch source target axis source_children target_children)
  let ?radix = "radices ! axis"
  let ?slot = "coordinate axis mod ?radix"
  have slot_bound: "?slot < ?radix"
    using map_branch.hyps(5,6) by simp
  have source_step:
    "comma_crt_mdd_eval_raw radices source_nodes coordinate source =
      comma_crt_mdd_eval_raw radices source_nodes coordinate
        (source_children ! ?slot)"
    by (rule comma_crt_mdd_eval_raw_branch_selected
      [OF source_wf map_branch.hyps(1,3)])
  have target_step:
    "comma_crt_mdd_eval_raw radices target_nodes coordinate target =
      comma_crt_mdd_eval_raw radices target_nodes coordinate
        (target_children ! ?slot)"
    by (rule comma_crt_mdd_eval_raw_branch_selected
      [OF target_wf map_branch.hyps(2,4)])
  have child_exact:
    "comma_crt_mdd_eval_raw radices target_nodes coordinate
        (target_children ! ?slot) =
      map_option encode
        (comma_crt_mdd_eval_raw radices source_nodes coordinate
          (source_children ! ?slot))"
    by (rule map_branch.IH[OF slot_bound])
  show ?case using source_step target_step child_exact by simp
next
  case (map_reduced_alias source target axis source_children)
  let ?radix = "radices ! axis"
  let ?slot = "coordinate axis mod ?radix"
  have slot_bound: "?slot < ?radix"
    using map_reduced_alias.hyps(4,5) by simp
  have source_step:
    "comma_crt_mdd_eval_raw radices source_nodes coordinate source =
      comma_crt_mdd_eval_raw radices source_nodes coordinate
        (source_children ! ?slot)"
    by (rule comma_crt_mdd_eval_raw_branch_selected
      [OF source_wf map_reduced_alias.hyps(1,3)])
  have child_exact:
    "comma_crt_mdd_eval_raw radices target_nodes coordinate target =
      map_option encode
        (comma_crt_mdd_eval_raw radices source_nodes coordinate
          (source_children ! ?slot))"
    by (rule map_reduced_alias.IH[OF slot_bound])
  show ?case using source_step child_exact by simp
qed

lemma comma_crt_mdd_root_map_certificate_eval:
  assumes source_wf: "comma_crt_mdd_table_wellformed radices source_nodes"
    and target_wf: "comma_crt_mdd_table_wellformed radices target_nodes"
    and certificate:
      "comma_crt_mdd_root_map_certificate radices source_nodes target_nodes
        encode source target"
  shows "comma_crt_mdd_eval radices target_nodes coordinate target =
    map_option encode (comma_crt_mdd_eval radices source_nodes coordinate source)"
  using comma_crt_mdd_root_map_certificate_eval_raw
      [OF source_wf target_wf certificate] source_wf target_wf
  by (simp add: comma_crt_mdd_eval_def)

lemma comma_crt_mdd_root_map_certificate_eval_phase:
  assumes source_wf: "comma_crt_mdd_table_wellformed radices source_nodes"
    and target_wf: "comma_crt_mdd_table_wellformed radices target_nodes"
    and certificate:
      "comma_crt_mdd_root_map_certificate radices source_nodes target_nodes
        encode source target"
  shows "comma_crt_mdd_eval_phase radices target_nodes phase target =
    map_option encode (comma_crt_mdd_eval_phase radices source_nodes phase source)"
  unfolding comma_crt_mdd_eval_phase_def
  by (rule comma_crt_mdd_root_map_certificate_eval
      [OF source_wf target_wf certificate])

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "MDD root-map evaluation transport, including reduced aliases"
    @{thms comma_crt_mdd_root_map_certificate_eval_raw
      comma_crt_mdd_root_map_certificate_eval
      comma_crt_mdd_root_map_certificate_eval_phase}
\<close>

end
