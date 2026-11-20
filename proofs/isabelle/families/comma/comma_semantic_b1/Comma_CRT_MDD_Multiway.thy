theory Comma_CRT_MDD_Multiway
  imports Comma_CRT_MDD_Zip
begin

text \<open>Ordered guards have first-active semantics.  A terminal result is
  accepted only when each guard is Boolean and every action and fallback is
  an authenticated leaf in the same checked table.\<close>

definition comma_crt_mdd_multiway_leaf_value ::
    "nat comma_crt_mdd_node list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_mdd_multiway_leaf_value nodes cases fallback =
    foldr (\<lambda>(guard,action) tail.
      case nodes!guard of Comma_CRT_MDD_Leaf g \<Rightarrow>
        (if g=1 then (case nodes!action of Comma_CRT_MDD_Leaf value \<Rightarrow> value | _ \<Rightarrow> 0)
         else tail)
      | _ \<Rightarrow> tail) cases fallback"

definition comma_crt_mdd_multiway_eval ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_crt_mdd_multiway_eval radices nodes coordinate cases fallback =
    foldr (\<lambda>(guard,action) tail.
      case comma_crt_mdd_eval radices nodes coordinate guard of
        Some g \<Rightarrow> (if g=1 then comma_crt_mdd_eval radices nodes coordinate action
          else if g=0 then tail else None) | None \<Rightarrow> None)
      cases (comma_crt_mdd_eval radices nodes coordinate fallback)"


inductive comma_crt_mdd_multiway_normalize ::
    "nat comma_crt_mdd_node list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow>
      (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" for nodes where
  empty: "comma_crt_mdd_multiway_normalize nodes [] fallback [] fallback"
| keep: "comma_crt_mdd_multiway_normalize nodes rest fallback normalized final \<Longrightarrow>
    comma_crt_mdd_multiway_normalize nodes ((guard,action)#rest) fallback
      ((guard,action)#normalized) final"
| drop: "\<lbrakk>guard<length nodes; nodes!guard=Comma_CRT_MDD_Leaf 0;
    comma_crt_mdd_multiway_normalize nodes rest fallback normalized final\<rbrakk> \<Longrightarrow>
    comma_crt_mdd_multiway_normalize nodes ((guard,action)#rest) fallback normalized final"
| stop: "\<lbrakk>guard<length nodes; nodes!guard=Comma_CRT_MDD_Leaf 1\<rbrakk> \<Longrightarrow>
    comma_crt_mdd_multiway_normalize nodes ((guard,action)#rest) fallback [] action"

lemma comma_crt_mdd_multiway_normalize_eval:
  assumes normalized: "comma_crt_mdd_multiway_normalize nodes cases fallback cases' fallback'"
    and wf: "comma_crt_mdd_table_wellformed radices nodes"
  shows "comma_crt_mdd_multiway_eval radices nodes coordinate cases fallback =
    comma_crt_mdd_multiway_eval radices nodes coordinate cases' fallback'"
  using normalized
proof (induction rule: comma_crt_mdd_multiway_normalize.induct)
  case empty
  then show ?case by (simp only: comma_crt_mdd_multiway_eval_def)
next
  case (keep rest fallback normalized final guard action)
  then show ?case by (simp only: comma_crt_mdd_multiway_eval_def foldr.simps prod.case comp_apply id_apply)
next
  case (drop guard rest fallback normalized final action)
  have guard: "comma_crt_mdd_eval radices nodes coordinate guard=Some 0"
    using wf comma_crt_mdd_eval_raw_leaf[OF drop.hyps(1,2), where coordinate=coordinate]
    by (simp only: comma_crt_mdd_eval_def if_True)
  show ?case using drop.IH guard by (simp only: comma_crt_mdd_multiway_eval_def foldr.simps prod.case comp_apply id_apply guard option.simps if_True if_False zero_neq_one one_neq_zero HOL.simp_thms)
next
  case (stop guard action rest fallback)
  have guard: "comma_crt_mdd_eval radices nodes coordinate guard=Some 1"
    using wf comma_crt_mdd_eval_raw_leaf[OF stop.hyps(1,2), where coordinate=coordinate]
    by (simp only: comma_crt_mdd_eval_def if_True)
  show ?case using guard by (simp only: comma_crt_mdd_multiway_eval_def foldr.simps prod.case comp_apply id_apply guard option.simps if_True if_False zero_neq_one one_neq_zero HOL.simp_thms)
qed

inductive comma_crt_mdd_multiway_certificate ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices nodes where
  normalize:
    "\<lbrakk>comma_crt_mdd_multiway_normalize nodes cases fallback cases' fallback';
      comma_crt_mdd_multiway_certificate radices nodes cases' fallback' output\<rbrakk>
     \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
| fallback:
    "fallback<length nodes \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes [] fallback fallback"
| skip:
    "\<lbrakk>guard<length nodes; nodes!guard=Comma_CRT_MDD_Leaf 0;
      comma_crt_mdd_multiway_certificate radices nodes cases fallback output\<rbrakk>
     \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes ((guard,action)#cases) fallback output"
| take:
    "\<lbrakk>guard<length nodes; action<length nodes; nodes!guard=Comma_CRT_MDD_Leaf 1\<rbrakk>
     \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes ((guard,action)#cases) fallback action"
|  leaf:
    "\<lbrakk>fallback<length nodes; output<length nodes;
      nodes!fallback=Comma_CRT_MDD_Leaf value;
      list_all (\<lambda>(guard,action). guard<length nodes \<and> action<length nodes \<and>
        (nodes!guard=Comma_CRT_MDD_Leaf 0 \<or> nodes!guard=Comma_CRT_MDD_Leaf 1) \<and>
        (\<exists>v. nodes!action=Comma_CRT_MDD_Leaf v)) cases;
      nodes!output=Comma_CRT_MDD_Leaf (comma_crt_mdd_multiway_leaf_value nodes cases value)\<rbrakk>
     \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
| split:
    "\<lbrakk>fallback<length nodes; output<length nodes;
      list_all (\<lambda>(guard,action). guard<length nodes \<and> action<length nodes) cases;
      axis<length radices; 0<radices!axis;
      \<And>slot. slot<radices!axis \<Longrightarrow>
        comma_crt_mdd_multiway_certificate radices nodes
          (map (\<lambda>(guard,action).
             (comma_crt_mdd_zip_child nodes guard axis slot,
              comma_crt_mdd_zip_child nodes action axis slot)) cases)
          (comma_crt_mdd_zip_child nodes fallback axis slot)
          (comma_crt_mdd_zip_child nodes output axis slot)\<rbrakk>
     \<Longrightarrow> comma_crt_mdd_multiway_certificate radices nodes cases fallback output"

lemma comma_crt_mdd_multiway_split_list:
  assumes fb: "fallback<length nodes" and out: "output<length nodes"
    and bounds: "list_all (\<lambda>(guard,action). guard<length nodes \<and> action<length nodes) cases"
    and axis: "axis<length radices" and width: "0<radices!axis"
    and slots: "list_all (\<lambda>slot. comma_crt_mdd_multiway_certificate radices nodes
      (map (\<lambda>(guard,action). (comma_crt_mdd_zip_child nodes guard axis slot,
          comma_crt_mdd_zip_child nodes action axis slot)) cases)
      (comma_crt_mdd_zip_child nodes fallback axis slot)
      (comma_crt_mdd_zip_child nodes output axis slot)) [0..<radices!axis]"
  shows "comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
  by (rule comma_crt_mdd_multiway_certificate.split[OF fb out bounds axis width])
     (use slots in \<open>auto simp: list_all_iff\<close>)

lemma comma_crt_mdd_multiway_leaf_eval:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and leaves: "list_all (\<lambda>(guard,action). guard<length nodes \<and> action<length nodes \<and>
        (nodes!guard=Comma_CRT_MDD_Leaf 0 \<or> nodes!guard=Comma_CRT_MDD_Leaf 1) \<and>
        (\<exists>v. nodes!action=Comma_CRT_MDD_Leaf v)) cases"
  shows "foldr (\<lambda>(guard,action) tail.
      case comma_crt_mdd_eval radices nodes coordinate guard of
        Some g \<Rightarrow> (if g=1 then comma_crt_mdd_eval radices nodes coordinate action
          else if g=0 then tail else None) | None \<Rightarrow> None) cases (Some value) =
    Some (comma_crt_mdd_multiway_leaf_value nodes cases value)"
  using leaves
  by (induction cases) (auto simp: wf comma_crt_mdd_multiway_leaf_value_def
    comma_crt_mdd_eval_def comma_crt_mdd_eval_raw_leaf
    split: prod.splits)

lemma comma_crt_mdd_multiway_cofactor_eval:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and bounded: "list_all (\<lambda>(guard,action). guard<length nodes \<and> action<length nodes) cases"
    and fb: "fallback<length nodes" and axis: "axis<length radices"
  shows "comma_crt_mdd_multiway_eval radices nodes coordinate
    (map (\<lambda>(guard,action). (comma_crt_mdd_zip_child nodes guard axis
      (coordinate axis mod radices!axis), comma_crt_mdd_zip_child nodes action axis
      (coordinate axis mod radices!axis))) cases)
    (comma_crt_mdd_zip_child nodes fallback axis (coordinate axis mod radices!axis)) =
    comma_crt_mdd_multiway_eval radices nodes coordinate cases fallback"
proof -
  have base: "comma_crt_mdd_eval_raw radices nodes coordinate
      (comma_crt_mdd_zip_child nodes fallback axis (coordinate axis mod radices!axis)) =
      comma_crt_mdd_eval_raw radices nodes coordinate fallback"
    by (rule comma_crt_mdd_zip_child_eval[OF wf fb axis])
  show ?thesis using bounded base
    unfolding comma_crt_mdd_multiway_eval_def
    by (induction cases)
       (auto simp: comma_crt_mdd_eval_def comma_crt_mdd_zip_child_eval[OF wf _ axis]
         split: prod.splits option.splits nat.splits)
qed

theorem comma_crt_mdd_multiway_certificate_sound:
  assumes cert: "comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
    and wf: "comma_crt_mdd_table_wellformed radices nodes"
  shows "comma_crt_mdd_eval radices nodes coordinate output =
    comma_crt_mdd_multiway_eval radices nodes coordinate cases fallback"
  using cert
proof (induction rule: comma_crt_mdd_multiway_certificate.induct)
  case (normalize cases fallback cases' fallback' result)
  then show ?case using comma_crt_mdd_multiway_normalize_eval[OF normalize.hyps(1) wf] by simp
next
  case (fallback fallback)
  then show ?case by (simp add: comma_crt_mdd_multiway_eval_def)
next
  case (skip guard cases fallback result action)
  then show ?case using wf comma_crt_mdd_eval_raw_leaf[OF skip.hyps(1,2), where coordinate=coordinate]
    by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_def)
next
  case (take guard action cases fallback)
  then show ?case using wf comma_crt_mdd_eval_raw_leaf[OF take.hyps(1,3), where coordinate=coordinate]
    by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_def)
next
  case (leaf fallback result payload cases)
  then show ?case using wf comma_crt_mdd_multiway_leaf_eval[OF wf, of cases coordinate payload]
    by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_def
      comma_crt_mdd_eval_raw_leaf)
next
  case (split fallback result cases axis)
  let ?slot = "coordinate axis mod radices!axis"
  have slot: "?slot<radices!axis" using split.hyps(5) by simp
  note ih = split.IH[OF slot]
  have out: "comma_crt_mdd_eval radices nodes coordinate
      (comma_crt_mdd_zip_child nodes result axis ?slot) =
      comma_crt_mdd_eval radices nodes coordinate result"
    using comma_crt_mdd_zip_child_eval[OF wf split.hyps(2,4), where coordinate=coordinate]
    by (simp add: comma_crt_mdd_eval_def)
  show ?case using ih out comma_crt_mdd_multiway_cofactor_eval
      [OF wf split.hyps(3,1,4), where coordinate=coordinate] by simp
qed

lemma comma_crt_mdd_multiway_certificate_phase:
  assumes cert: "comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
    and wf: "comma_crt_mdd_table_wellformed radices nodes"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    comma_crt_mdd_multiway_eval radices nodes (\<lambda>_. phase) cases fallback"
  using comma_crt_mdd_multiway_certificate_sound[OF cert wf, where coordinate="\<lambda>_. phase"] wf
  by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)

lemma comma_crt_mdd_multiway_value:
  assumes guards: "\<And>guard action. (guard,action)\<in>set cases \<Longrightarrow>
      comma_crt_mdd_eval radices nodes coordinate guard = Some (if active guard action then 1 else 0)"
    and actions: "\<And>guard action. (guard,action)\<in>set cases \<Longrightarrow>
      comma_crt_mdd_eval radices nodes coordinate action = Some (value guard action)"
    and fallback: "comma_crt_mdd_eval radices nodes coordinate root = Some initial"
  shows "comma_crt_mdd_multiway_eval radices nodes coordinate cases root =
    Some (foldr (\<lambda>(guard,action) tail. if active guard action then value guard action else tail)
      cases initial)"
proof -
  have folded: "foldr (\<lambda>(guard,action) tail.
      case comma_crt_mdd_eval radices nodes coordinate guard of
        Some g \<Rightarrow> (if g=1 then comma_crt_mdd_eval radices nodes coordinate action
          else if g=0 then tail else None) | None \<Rightarrow> None)
      cases (Some initial) =
    Some (foldr (\<lambda>(guard,action) tail. if active guard action then value guard action else tail)
      cases initial)"
    using guards actions
  proof (induction cases)
    case Nil
    then show ?case by simp
  next
    case (Cons pair rest)
    obtain guard action where pair: "pair=(guard,action)" by (cases pair) auto
    have g: "comma_crt_mdd_eval radices nodes coordinate guard =
      Some (if active guard action then 1 else 0)"
      by (rule Cons.prems(1)) (simp add: pair)
    have v: "comma_crt_mdd_eval radices nodes coordinate action = Some (value guard action)"
      by (rule Cons.prems(2)) (simp add: pair)
    have tail: "foldr (\<lambda>(guard,action) tail.
        case comma_crt_mdd_eval radices nodes coordinate guard of
          Some g \<Rightarrow> (if g=1 then comma_crt_mdd_eval radices nodes coordinate action
            else if g=0 then tail else None) | None \<Rightarrow> None)
        rest (Some initial) =
      Some (foldr (\<lambda>(guard,action) tail. if active guard action then value guard action else tail)
        rest initial)"
      by (rule Cons.IH) (use Cons.prems in auto)+
    show ?case using g v tail by (simp add: pair split: if_splits)
  qed
  show ?thesis using folded fallback by (simp only: comma_crt_mdd_multiway_eval_def)
qed

end
