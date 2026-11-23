theory Comma_CRT_MDD_Shift
  imports Comma_CRT_MDD_Bind
begin

text \<open>
A root shift certificate describes one shifted subgraph in its receiving
arena.  It never constructs a shifted copy of the whole node table.  Branch
children are matched after the bounded radix rotation; an alias rule records
the reduction case where every shifted child is the same existing root.
\<close>

inductive comma_crt_mdd_root_shift_map_certificate ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices nodes encode amount where
  root_shift_map_leaf:
    "\<lbrakk>source < length nodes; target < length nodes;
      nodes ! source = Comma_CRT_MDD_Leaf payload;
      nodes ! target = Comma_CRT_MDD_Leaf (encode payload)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_shift_map_certificate
        radices nodes encode amount source target"
| root_shift_map_branch:
    "\<lbrakk>source < length nodes; target < length nodes;
      nodes ! source = Comma_CRT_MDD_Branch axis children;
      nodes ! target = Comma_CRT_MDD_Branch axis shifted_children;
      axis < length radices; 0 < radices ! axis;
      length children = radices ! axis;
      length shifted_children = radices ! axis;
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_root_shift_map_certificate radices nodes encode amount
          (children ! ((slot + amount) mod radices ! axis))
          (shifted_children ! slot))\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_shift_map_certificate
        radices nodes encode amount source target"
| root_shift_map_alias:
    "\<lbrakk>source < length nodes; target < length nodes;
      nodes ! source = Comma_CRT_MDD_Branch axis children;
      axis < length radices; 0 < radices ! axis;
      length children = radices ! axis;
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_root_shift_map_certificate radices nodes encode amount
          (children ! ((slot + amount) mod radices ! axis)) target)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_root_shift_map_certificate
        radices nodes encode amount source target"

text \<open>A period certificate records only axes reachable from the source.
It is independent of the mapped payload law and is tied to the checked node
table.  A multiple of every reachable radix preserves each selected child.\<close>

inductive comma_crt_mdd_shift_period_certificate ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices nodes period where
  shift_period_leaf:
    "\<lbrakk>source < length nodes; nodes ! source = Comma_CRT_MDD_Leaf payload\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_shift_period_certificate radices nodes period source"
| shift_period_branch:
    "\<lbrakk>source < length nodes; nodes ! source = Comma_CRT_MDD_Branch axis children;
      axis < length radices; radices ! axis dvd period;
      length children = radices ! axis;
      (\<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_shift_period_certificate radices nodes period (children ! slot))\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_shift_period_certificate radices nodes period source"

lemma comma_crt_mdd_root_shift_map_certificate_period:
  assumes certificate:
      "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount source target"
    and period:
      "comma_crt_mdd_shift_period_certificate radices nodes p source"
    and congruent: "amount mod p = amount' mod p"
  shows "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount' source target"
  using certificate period congruent
proof (induction arbitrary: p amount' rule: comma_crt_mdd_root_shift_map_certificate.induct)
  case (root_shift_map_leaf source target payload)
  show ?case
    by (rule comma_crt_mdd_root_shift_map_certificate.root_shift_map_leaf;
        fact root_shift_map_leaf.hyps)
next
  case (root_shift_map_branch source target axis children shifted_children)
  have period_facts: "radices ! axis dvd p \<and>
      (\<forall>slot < radices ! axis.
        comma_crt_mdd_shift_period_certificate radices nodes p (children ! slot))"
    using root_shift_map_branch.prems(1) root_shift_map_branch.hyps(3)
    by (cases rule: comma_crt_mdd_shift_period_certificate.cases) auto
  have axis_dvd: "radices ! axis dvd p" using period_facts by blast
  have child_period: "\<And>slot. slot < radices ! axis \<Longrightarrow>
      comma_crt_mdd_shift_period_certificate radices nodes p (children ! slot)"
    using period_facts by blast
  have same_radix: "amount mod (radices ! axis) = amount' mod (radices ! axis)"
    using root_shift_map_branch.prems(2) axis_dvd by (metis mod_mod_cancel)
  show ?case
  proof (rule comma_crt_mdd_root_shift_map_certificate.root_shift_map_branch)
    show "source < length nodes" by (fact root_shift_map_branch.hyps(1))
    show "target < length nodes" by (fact root_shift_map_branch.hyps(2))
    show "nodes ! source = Comma_CRT_MDD_Branch axis children"
      by (fact root_shift_map_branch.hyps(3))
    show "nodes ! target = Comma_CRT_MDD_Branch axis shifted_children"
      by (fact root_shift_map_branch.hyps(4))
    show "axis < length radices" by (fact root_shift_map_branch.hyps(5))
    show "0 < radices ! axis" by (fact root_shift_map_branch.hyps(6))
    show "length children = radices ! axis" by (fact root_shift_map_branch.hyps(7))
    show "length shifted_children = radices ! axis" by (fact root_shift_map_branch.hyps(8))
    fix slot assume slot: "slot < radices ! axis"
    have index: "(slot + amount) mod radices ! axis =
        (slot + amount') mod radices ! axis"
    proof -
      have "(slot + amount) mod radices ! axis =
          (slot + amount mod radices ! axis) mod radices ! axis"
        by (rule sym[OF mod_add_right_eq])
      also have "... = (slot + amount' mod radices ! axis) mod radices ! axis"
        by (simp only: same_radix)
      also have "... = (slot + amount') mod radices ! axis"
        by (rule mod_add_right_eq)
      finally show ?thesis .
    qed
    have bound: "(slot + amount) mod radices ! axis < radices ! axis"
      using root_shift_map_branch.hyps(6) by simp
    show "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount'
        (children ! ((slot + amount') mod radices ! axis)) (shifted_children ! slot)"
      using root_shift_map_branch.IH[OF slot child_period[OF bound]
          root_shift_map_branch.prems(2)] index by simp
  qed
next
  case (root_shift_map_alias source target axis children)
  have period_facts: "radices ! axis dvd p \<and>
      (\<forall>slot < radices ! axis.
        comma_crt_mdd_shift_period_certificate radices nodes p (children ! slot))"
    using root_shift_map_alias.prems(1) root_shift_map_alias.hyps(3)
    by (cases rule: comma_crt_mdd_shift_period_certificate.cases) auto
  have axis_dvd: "radices ! axis dvd p" using period_facts by blast
  have child_period: "\<And>slot. slot < radices ! axis \<Longrightarrow>
      comma_crt_mdd_shift_period_certificate radices nodes p (children ! slot)"
    using period_facts by blast
  have same_radix: "amount mod (radices ! axis) = amount' mod (radices ! axis)"
    using root_shift_map_alias.prems(2) axis_dvd by (metis mod_mod_cancel)
  show ?case
  proof (rule comma_crt_mdd_root_shift_map_certificate.root_shift_map_alias)
    show "source < length nodes" by (fact root_shift_map_alias.hyps(1))
    show "target < length nodes" by (fact root_shift_map_alias.hyps(2))
    show "nodes ! source = Comma_CRT_MDD_Branch axis children"
      by (fact root_shift_map_alias.hyps(3))
    show "axis < length radices" by (fact root_shift_map_alias.hyps(4))
    show "0 < radices ! axis" by (fact root_shift_map_alias.hyps(5))
    show "length children = radices ! axis" by (fact root_shift_map_alias.hyps(6))
    fix slot assume slot: "slot < radices ! axis"
    have index: "(slot + amount) mod radices ! axis =
        (slot + amount') mod radices ! axis"
    proof -
      have "(slot + amount) mod radices ! axis =
          (slot + amount mod radices ! axis) mod radices ! axis"
        by (rule sym[OF mod_add_right_eq])
      also have "... = (slot + amount' mod radices ! axis) mod radices ! axis"
        by (simp only: same_radix)
      also have "... = (slot + amount') mod radices ! axis"
        by (rule mod_add_right_eq)
      finally show ?thesis .
    qed
    have bound: "(slot + amount) mod radices ! axis < radices ! axis"
      using root_shift_map_alias.hyps(5) by simp
    show "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount'
        (children ! ((slot + amount') mod radices ! axis)) target"
      using root_shift_map_alias.IH[OF slot child_period[OF bound]
          root_shift_map_alias.prems(2)] index by simp
  qed
qed

lemma comma_crt_mdd_root_shift_map_certificate_eval_raw:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and certificate:
      "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount source target"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate target =
    map_option encode (comma_crt_mdd_eval_raw radices nodes
      (comma_crt_mdd_shift_coordinate radices coordinate amount) source)"
  using certificate
proof (induction rule: comma_crt_mdd_root_shift_map_certificate.induct)
  case (root_shift_map_leaf source target payload)
  have target_value:
      "comma_crt_mdd_eval_raw radices nodes coordinate target = Some (encode payload)"
    by (rule comma_crt_mdd_eval_raw_leaf
        [OF root_shift_map_leaf.hyps(2) root_shift_map_leaf.hyps(4)])
  have source_value:
      "comma_crt_mdd_eval_raw radices nodes
        (comma_crt_mdd_shift_coordinate radices coordinate amount) source =
          Some payload"
    by (rule comma_crt_mdd_eval_raw_leaf
        [OF root_shift_map_leaf.hyps(1) root_shift_map_leaf.hyps(3)])
  show ?case using target_value source_value by simp
next
  case (root_shift_map_branch source target axis children shifted_children)
  let ?radix = "radices ! axis"
  let ?slot = "coordinate axis mod ?radix"
  let ?source_index = "(?slot + amount) mod ?radix"
  let ?source_child = "children ! ?source_index"
  let ?target_child = "shifted_children ! ?slot"
  have source_facts:
      "axis < length radices"
      "0 < ?radix"
      "length children = ?radix"
      "\<forall>child\<in>set children. child < source \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True | Some child_axis \<Rightarrow> axis < child_axis)"
    by (rule comma_crt_mdd_branch_facts[OF wellformed
        root_shift_map_branch.hyps(1) root_shift_map_branch.hyps(3)])+
  have target_facts:
      "axis < length radices"
      "0 < ?radix"
      "length shifted_children = ?radix"
      "\<forall>child\<in>set shifted_children. child < target \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True | Some child_axis \<Rightarrow> axis < child_axis)"
    by (rule comma_crt_mdd_branch_facts[OF wellformed
        root_shift_map_branch.hyps(2) root_shift_map_branch.hyps(4)])+
  have slot_bound: "?slot < ?radix" using source_facts(2) by simp
  have source_index_bound: "?source_index < length children"
    using source_facts(2,3) by simp
  have source_child_member: "?source_child \<in> set children"
    by (rule nth_mem[OF source_index_bound])
  have source_child_bound: "?source_child < source"
    using source_facts(4) source_child_member by blast
  have target_slot_bound: "?slot < length shifted_children"
    using target_facts(2,3) by simp
  have target_child_member: "?target_child \<in> set shifted_children"
    by (rule nth_mem[OF target_slot_bound])
  have target_child_bound: "?target_child < target"
    using target_facts(4) target_child_member by blast
  have shifted_slot:
      "?source_index =
        comma_crt_mdd_shift_coordinate radices coordinate amount axis mod ?radix"
    using source_facts(2)
    by (simp add: comma_crt_mdd_shift_coordinate_def mod_add_left_eq)
  have source_selection:
      "?source_child = children !
        (comma_crt_mdd_shift_coordinate radices coordinate amount axis mod ?radix)"
    using shifted_slot by simp
  have source_step:
      "comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) source =
        comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) ?source_child"
    by (rule comma_crt_mdd_eval_raw_branch
        [where coordinate="comma_crt_mdd_shift_coordinate radices coordinate amount",
         OF root_shift_map_branch.hyps(1) root_shift_map_branch.hyps(3)
            source_facts(1,2,3) source_selection source_child_bound])
  have target_step:
      "comma_crt_mdd_eval_raw radices nodes coordinate target =
        comma_crt_mdd_eval_raw radices nodes coordinate ?target_child"
    by (rule comma_crt_mdd_eval_raw_branch
        [where coordinate=coordinate,
         OF root_shift_map_branch.hyps(2) root_shift_map_branch.hyps(4)
            target_facts(1,2,3) refl target_child_bound])
  have child_exact:
      "comma_crt_mdd_eval_raw radices nodes coordinate ?target_child =
        map_option encode (comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) ?source_child)"
    by (rule root_shift_map_branch.IH[OF slot_bound])
  show ?case using source_step target_step child_exact by simp
next
  case (root_shift_map_alias source target axis children)
  let ?radix = "radices ! axis"
  let ?slot = "coordinate axis mod ?radix"
  let ?source_index = "(?slot + amount) mod ?radix"
  let ?source_child = "children ! ?source_index"
  have source_facts:
      "axis < length radices"
      "0 < ?radix"
      "length children = ?radix"
      "\<forall>child\<in>set children. child < source \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True | Some child_axis \<Rightarrow> axis < child_axis)"
    by (rule comma_crt_mdd_branch_facts[OF wellformed
        root_shift_map_alias.hyps(1) root_shift_map_alias.hyps(3)])+
  have slot_bound: "?slot < ?radix" using source_facts(2) by simp
  have source_index_bound: "?source_index < length children"
    using source_facts(2,3) by simp
  have source_child_member: "?source_child \<in> set children"
    by (rule nth_mem[OF source_index_bound])
  have source_child_bound: "?source_child < source"
    using source_facts(4) source_child_member by blast
  have shifted_slot:
      "?source_index =
        comma_crt_mdd_shift_coordinate radices coordinate amount axis mod ?radix"
    using source_facts(2)
    by (simp add: comma_crt_mdd_shift_coordinate_def mod_add_left_eq)
  have source_selection:
      "?source_child = children !
        (comma_crt_mdd_shift_coordinate radices coordinate amount axis mod ?radix)"
    using shifted_slot by simp
  have source_step:
      "comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) source =
        comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) ?source_child"
    by (rule comma_crt_mdd_eval_raw_branch
        [where coordinate="comma_crt_mdd_shift_coordinate radices coordinate amount",
         OF root_shift_map_alias.hyps(1) root_shift_map_alias.hyps(3)
            source_facts(1,2,3) source_selection source_child_bound])
  have child_exact:
      "comma_crt_mdd_eval_raw radices nodes coordinate target =
        map_option encode (comma_crt_mdd_eval_raw radices nodes
          (comma_crt_mdd_shift_coordinate radices coordinate amount) ?source_child)"
    by (rule root_shift_map_alias.IH[OF slot_bound])
  show ?case using source_step child_exact by simp
qed

lemma comma_crt_mdd_root_shift_map_certificate_eval:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and certificate:
      "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount source target"
  shows "comma_crt_mdd_eval radices nodes coordinate target =
    map_option encode (comma_crt_mdd_eval radices nodes
      (comma_crt_mdd_shift_coordinate radices coordinate amount) source)"
  using wellformed
    comma_crt_mdd_root_shift_map_certificate_eval_raw[OF wellformed certificate]
  by (simp add: comma_crt_mdd_eval_def)

lemma comma_crt_mdd_root_shift_map_certificate_eval_phase:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and certificate:
      "comma_crt_mdd_root_shift_map_certificate radices nodes encode amount source target"
  shows "comma_crt_mdd_eval_phase radices nodes phase target =
    map_option encode (comma_crt_mdd_eval_phase radices nodes (phase + amount) source)"
proof -
  have exact:
      "comma_crt_mdd_eval radices nodes (\<lambda>axis. phase) target =
        map_option encode (comma_crt_mdd_eval radices nodes
          (comma_crt_mdd_shift_coordinate radices (\<lambda>axis. phase) amount) source)"
    by (rule comma_crt_mdd_root_shift_map_certificate_eval[OF wellformed certificate])
  have transported:
      "comma_crt_mdd_eval radices nodes
          (comma_crt_mdd_shift_coordinate radices (\<lambda>axis. phase) amount) source =
        comma_crt_mdd_eval radices nodes (\<lambda>axis. phase + amount) source"
  proof (rule comma_crt_mdd_eval_coordinate_congruent[OF wellformed])
    fix axis
    assume axis: "axis < length radices"
    show "comma_crt_mdd_shift_coordinate radices (\<lambda>axis. phase) amount axis
          mod radices ! axis = (\<lambda>axis. phase + amount) axis mod radices ! axis"
      using axis by (simp add: comma_crt_mdd_shift_coordinate_def)
  qed
  show ?thesis using exact transported
    by (simp add: comma_crt_mdd_eval_phase_def)
qed

definition comma_crt_mdd_root_shift_certificate where
  "comma_crt_mdd_root_shift_certificate radices nodes amount source target =
    comma_crt_mdd_root_shift_map_certificate radices nodes id amount source target"

lemma comma_crt_mdd_root_shift_certificate_eval_raw:
  assumes "comma_crt_mdd_table_wellformed radices nodes"
    "comma_crt_mdd_root_shift_certificate radices nodes amount source target"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate target =
    comma_crt_mdd_eval_raw radices nodes
      (comma_crt_mdd_shift_coordinate radices coordinate amount) source"
  using comma_crt_mdd_root_shift_map_certificate_eval_raw[where encode=id, OF assms(1)] assms(2)
  by (simp add: comma_crt_mdd_root_shift_certificate_def option.map_id)

lemma comma_crt_mdd_root_shift_certificate_eval:
  assumes "comma_crt_mdd_table_wellformed radices nodes"
    "comma_crt_mdd_root_shift_certificate radices nodes amount source target"
  shows "comma_crt_mdd_eval radices nodes coordinate target =
    comma_crt_mdd_eval radices nodes
      (comma_crt_mdd_shift_coordinate radices coordinate amount) source"
  using comma_crt_mdd_root_shift_map_certificate_eval[where encode=id, OF assms(1)] assms(2)
  by (simp add: comma_crt_mdd_root_shift_certificate_def option.map_id)

lemma comma_crt_mdd_root_shift_certificate_eval_phase:
  assumes "comma_crt_mdd_table_wellformed radices nodes"
    "comma_crt_mdd_root_shift_certificate radices nodes amount source target"
  shows "comma_crt_mdd_eval_phase radices nodes phase target =
    comma_crt_mdd_eval_phase radices nodes (phase + amount) source"
  using comma_crt_mdd_root_shift_map_certificate_eval_phase[where encode=id, OF assms(1)] assms(2)
  by (simp add: comma_crt_mdd_root_shift_certificate_def option.map_id)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "same-arena MDD root shift certificate"
    @{thms comma_crt_mdd_root_shift_map_certificate_eval_raw
      comma_crt_mdd_root_shift_map_certificate_period
      comma_crt_mdd_root_shift_map_certificate_eval
      comma_crt_mdd_root_shift_map_certificate_eval_phase
      comma_crt_mdd_root_shift_certificate_eval_raw
      comma_crt_mdd_root_shift_certificate_eval
      comma_crt_mdd_root_shift_certificate_eval_phase}
\<close>

end
