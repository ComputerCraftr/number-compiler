theory Comma_CRT_MDD_Zip
  imports Comma_CRT_MDD
begin

text \<open>A zip certificate relates three independently shaped diagrams.  A
branch may split either input or both.  An input that does not split on the
selected axis stays at its current node; no equality of the input layouts or
source occurrences is assumed.  The output's ordered node and checked child
certificates provide the termination measure.\<close>

definition comma_crt_mdd_zip_child ::
    "'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_mdd_zip_child nodes root axis slot =
    (case nodes ! root of
       Comma_CRT_MDD_Leaf _ \<Rightarrow> root
     | Comma_CRT_MDD_Branch other children \<Rightarrow>
         if other=axis then children ! slot else root)"

lemma comma_crt_mdd_zip_child_eval:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and bound: "root < length nodes"
    and axis: "axis < length radices"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate
      (comma_crt_mdd_zip_child nodes root axis
        (coordinate axis mod radices ! axis)) =
    comma_crt_mdd_eval_raw radices nodes coordinate root"
proof (cases "nodes ! root")
  case (Comma_CRT_MDD_Leaf payload)
  then show ?thesis by (simp add: comma_crt_mdd_zip_child_def)
next
  case (Comma_CRT_MDD_Branch other children)
  show ?thesis
  proof (cases "other=axis")
    case True
    have selected: "comma_crt_mdd_eval_raw radices nodes coordinate root =
      comma_crt_mdd_eval_raw radices nodes coordinate
        (children ! (coordinate other mod radices ! other))"
      by (rule comma_crt_mdd_eval_raw_branch_selected
          [OF wellformed bound Comma_CRT_MDD_Branch])
    show ?thesis using selected True Comma_CRT_MDD_Branch
      by (simp add: comma_crt_mdd_zip_child_def)
  next
    case False
    then show ?thesis using Comma_CRT_MDD_Branch
      by (simp add: comma_crt_mdd_zip_child_def)
  qed
qed

inductive comma_crt_mdd_zip_certificate ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow>
      'b comma_crt_mdd_node list \<Rightarrow> 'c comma_crt_mdd_node list \<Rightarrow>
      ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  for radices left right result combine where
  leaf:
    "\<lbrakk>l < length left; r < length right; z < length result;
      left ! l = Comma_CRT_MDD_Leaf x;
      right ! r = Comma_CRT_MDD_Leaf y;
      result ! z = Comma_CRT_MDD_Leaf (combine x y)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_zip_certificate radices left right result combine l r z"
| branch:
    "\<lbrakk>l < length left; r < length right; z < length result;
      result ! z = Comma_CRT_MDD_Branch axis children;
      axis < length radices; 0 < radices ! axis;
      length children = radices ! axis;
      \<And>slot. slot < length children \<Longrightarrow>
        comma_crt_mdd_zip_certificate radices left right result combine
          (comma_crt_mdd_zip_child left l axis slot)
          (comma_crt_mdd_zip_child right r axis slot) (children ! slot)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_zip_certificate radices left right result combine l r z"
| split:
    "\<lbrakk>l < length left; r < length right; z < length result;
      axis < length radices; 0 < radices ! axis;
      \<And>slot. slot < radices ! axis \<Longrightarrow>
        comma_crt_mdd_zip_certificate radices left right result combine
          (comma_crt_mdd_zip_child left l axis slot)
          (comma_crt_mdd_zip_child right r axis slot)
          (comma_crt_mdd_zip_child result z axis slot)\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_zip_certificate radices left right result combine l r z"

theorem comma_crt_mdd_zip_certificate_sound:
  assumes certificate: "comma_crt_mdd_zip_certificate radices left right result combine l r z"
    and left_wf: "comma_crt_mdd_table_wellformed radices left"
    and right_wf: "comma_crt_mdd_table_wellformed radices right"
    and result_wf: "comma_crt_mdd_table_wellformed radices result"
  shows "comma_crt_mdd_eval radices result coordinate z =
    (case comma_crt_mdd_eval radices left coordinate l of
       None \<Rightarrow> None
     | Some x \<Rightarrow> map_option (combine x)
         (comma_crt_mdd_eval radices right coordinate r))"
  using certificate
proof (induction rule: comma_crt_mdd_zip_certificate.induct)
  case (leaf l r z x y)
  then show ?case using left_wf right_wf result_wf
    by (simp add: comma_crt_mdd_eval_def comma_crt_mdd_eval_raw_leaf)
next
  case (branch l r z axis children)
  let ?slot = "coordinate axis mod radices ! axis"
  have slot: "?slot < length children" using branch.hyps(6,7) by simp
  have ih: "comma_crt_mdd_eval radices result coordinate (children ! ?slot) =
    (case comma_crt_mdd_eval radices left coordinate
       (comma_crt_mdd_zip_child left l axis ?slot) of
       None \<Rightarrow> None
     | Some x \<Rightarrow> map_option (combine x)
       (comma_crt_mdd_eval radices right coordinate
         (comma_crt_mdd_zip_child right r axis ?slot)))"
    by (rule branch.IH[OF slot])
  have l: "comma_crt_mdd_eval radices left coordinate
       (comma_crt_mdd_zip_child left l axis ?slot) =
      comma_crt_mdd_eval radices left coordinate l"
    using comma_crt_mdd_zip_child_eval[OF left_wf branch.hyps(1,5),
      where coordinate=coordinate] left_wf by (simp add: comma_crt_mdd_eval_def)
  have r: "comma_crt_mdd_eval radices right coordinate
       (comma_crt_mdd_zip_child right r axis ?slot) =
      comma_crt_mdd_eval radices right coordinate r"
    using comma_crt_mdd_zip_child_eval[OF right_wf branch.hyps(2,5),
      where coordinate=coordinate] right_wf by (simp add: comma_crt_mdd_eval_def)
  have out: "comma_crt_mdd_eval radices result coordinate z =
      comma_crt_mdd_eval radices result coordinate (children ! ?slot)"
    using comma_crt_mdd_eval_raw_branch_selected
      [OF result_wf branch.hyps(3,4), where coordinate=coordinate]
      result_wf by (simp add: comma_crt_mdd_eval_def)
  show ?case using out ih l r
    by (cases "comma_crt_mdd_eval radices left coordinate l") simp_all
next
  case (split l r z axis)
  let ?slot = "coordinate axis mod radices ! axis"
  have slot: "?slot < radices ! axis" using split.hyps(5) by simp
  have ih: "comma_crt_mdd_eval radices result coordinate
      (comma_crt_mdd_zip_child result z axis ?slot) =
    (case comma_crt_mdd_eval radices left coordinate
       (comma_crt_mdd_zip_child left l axis ?slot) of
       None \<Rightarrow> None
     | Some x \<Rightarrow> map_option (combine x)
       (comma_crt_mdd_eval radices right coordinate
         (comma_crt_mdd_zip_child right r axis ?slot)))"
    by (rule split.IH[OF slot])
  have l: "comma_crt_mdd_eval radices left coordinate
       (comma_crt_mdd_zip_child left l axis ?slot) =
      comma_crt_mdd_eval radices left coordinate l"
    using comma_crt_mdd_zip_child_eval[OF left_wf split.hyps(1,4),
      where coordinate=coordinate] left_wf by (simp add: comma_crt_mdd_eval_def)
  have r: "comma_crt_mdd_eval radices right coordinate
       (comma_crt_mdd_zip_child right r axis ?slot) =
      comma_crt_mdd_eval radices right coordinate r"
    using comma_crt_mdd_zip_child_eval[OF right_wf split.hyps(2,4),
      where coordinate=coordinate] right_wf by (simp add: comma_crt_mdd_eval_def)
  have out: "comma_crt_mdd_eval radices result coordinate
      (comma_crt_mdd_zip_child result z axis ?slot) =
      comma_crt_mdd_eval radices result coordinate z"
    using comma_crt_mdd_zip_child_eval[OF result_wf split.hyps(3,4),
      where coordinate=coordinate] result_wf by (simp add: comma_crt_mdd_eval_def)
  show ?case using out ih l r
    by (cases "comma_crt_mdd_eval radices left coordinate l") simp_all
qed

corollary comma_crt_mdd_zip_certificate_phase:
  assumes "comma_crt_mdd_zip_certificate radices left right result combine l r z"
    "comma_crt_mdd_table_wellformed radices left"
    "comma_crt_mdd_table_wellformed radices right"
    "comma_crt_mdd_table_wellformed radices result"
  shows "comma_crt_mdd_eval_phase radices result phase z =
    (case comma_crt_mdd_eval_phase radices left phase l of
       None \<Rightarrow> None
     | Some x \<Rightarrow> map_option (combine x)
         (comma_crt_mdd_eval_phase radices right phase r))"
  using comma_crt_mdd_zip_certificate_sound[OF assms, where coordinate="\<lambda>_. phase"]
  by (simp only: comma_crt_mdd_eval_phase_def)

text \<open>Finite regression: the left input branches on axis zero, while the
right input branches only on axis one.  The combined output must retain their
ordered coordinates rather than treating either input root as the other.\<close>

definition comma_zip_fixture_left :: "nat comma_crt_mdd_node list" where
  "comma_zip_fixture_left = [Comma_CRT_MDD_Leaf 0, Comma_CRT_MDD_Leaf 1,
    Comma_CRT_MDD_Branch 0 [0,1]]"

definition comma_zip_fixture_right :: "nat comma_crt_mdd_node list" where
  "comma_zip_fixture_right = [Comma_CRT_MDD_Leaf 0, Comma_CRT_MDD_Leaf 1,
    Comma_CRT_MDD_Branch 1 [0,1]]"

definition comma_zip_fixture_result :: "nat comma_crt_mdd_node list" where
  "comma_zip_fixture_result = [Comma_CRT_MDD_Leaf 0, Comma_CRT_MDD_Leaf 1,
    Comma_CRT_MDD_Leaf 2, Comma_CRT_MDD_Leaf 3,
    Comma_CRT_MDD_Branch 1 [0,1], Comma_CRT_MDD_Branch 1 [2,3],
    Comma_CRT_MDD_Branch 0 [4,5]]"

lemma comma_zip_fixture_leaf:
  assumes "l<2" "r<2"
  shows "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) l r (2*l+r)"
proof -
  have f00: "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) 0 0 0"
    by (rule comma_crt_mdd_zip_certificate.leaf[where x=0 and y=0];
      simp add: comma_zip_fixture_left_def comma_zip_fixture_right_def comma_zip_fixture_result_def)
  have f01: "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) 0 1 1"
    by (rule comma_crt_mdd_zip_certificate.leaf[where x=0 and y=1];
      simp add: comma_zip_fixture_left_def comma_zip_fixture_right_def comma_zip_fixture_result_def)
  have f10: "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) 1 0 2"
    by (rule comma_crt_mdd_zip_certificate.leaf[where x=1 and y=0];
      simp add: comma_zip_fixture_left_def comma_zip_fixture_right_def comma_zip_fixture_result_def)
  have f11: "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) 1 1 3"
    by (rule comma_crt_mdd_zip_certificate.leaf[where x=1 and y=1];
      simp add: comma_zip_fixture_left_def comma_zip_fixture_right_def comma_zip_fixture_result_def)
  have lc: "l=0 \<or> l=1" and rc: "r=0 \<or> r=1" using assms by arith+
  show ?thesis using lc rc f00 f01 f10 f11 by auto
qed

lemma comma_zip_fixture_inner:
  assumes "l<2"
  shows "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) l 2 (4+l)"
proof (rule comma_crt_mdd_zip_certificate.branch
    [where axis=1 and children="[2*l,2*l+1]"])
  show "l < length comma_zip_fixture_left" using assms
    by (simp add: comma_zip_fixture_left_def)
  show "2 < length comma_zip_fixture_right"
    by (simp add: comma_zip_fixture_right_def)
  show "4+l < length comma_zip_fixture_result" using assms
    by (simp add: comma_zip_fixture_result_def)
  show "comma_zip_fixture_result ! (4+l) =
      Comma_CRT_MDD_Branch 1 [2*l,2*l+1]"
    using assms by (cases l; auto simp: comma_zip_fixture_result_def)
  show "1 < length ([2,2]::nat list)" by simp
  show "0 < ([2,2]::nat list) ! 1" by simp
  show "length [2*l,2*l+1] = ([2,2]::nat list) ! 1" by simp
  fix slot
  assume slot: "slot < length [2*l,2*l+1]"
  have slot_bound: "slot<2" using slot by simp
  have left_child: "comma_crt_mdd_zip_child comma_zip_fixture_left l 1 slot=l"
    using assms by (cases l; auto simp: comma_crt_mdd_zip_child_def
      comma_zip_fixture_left_def)
  have right_child: "comma_crt_mdd_zip_child comma_zip_fixture_right 2 1 slot=slot"
    using slot_bound by (cases slot; auto simp: comma_crt_mdd_zip_child_def
      comma_zip_fixture_right_def)
  have result_child: "[2*l,2*l+1] ! slot=2*l+slot"
    using slot_bound by (cases slot; auto)
  show "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
      comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y)
      (comma_crt_mdd_zip_child comma_zip_fixture_left l 1 slot)
      (comma_crt_mdd_zip_child comma_zip_fixture_right 2 1 slot)
      ([2*l,2*l+1] ! slot)"
    using comma_zip_fixture_leaf[OF assms slot_bound]
    by (simp only: left_child right_child result_child)
qed

lemma comma_zip_fixture_distinct_axes:
  "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
    comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y) 2 2 6"
proof (rule comma_crt_mdd_zip_certificate.branch [where axis=0 and children="[4,5]"])
  show "2 < length comma_zip_fixture_left" by (simp add: comma_zip_fixture_left_def)
  show "2 < length comma_zip_fixture_right" by (simp add: comma_zip_fixture_right_def)
  show "6 < length comma_zip_fixture_result" by (simp add: comma_zip_fixture_result_def)
  show "comma_zip_fixture_result ! 6 = Comma_CRT_MDD_Branch 0 [4,5]"
    by (simp add: comma_zip_fixture_result_def)
  show "0 < length ([2,2]::nat list)" by simp
  show "0 < ([2,2]::nat list) ! 0" by simp
  show "length [4,5] = ([2,2]::nat list) ! 0" by simp
  fix slot
  assume slot: "slot < length [4,5]"
  have slot_bound: "slot<2" using slot by simp
  have left_child: "comma_crt_mdd_zip_child comma_zip_fixture_left 2 0 slot=slot"
    using slot_bound by (cases slot; auto simp: comma_crt_mdd_zip_child_def
      comma_zip_fixture_left_def)
  have right_child: "comma_crt_mdd_zip_child comma_zip_fixture_right 2 0 slot=2"
    by (simp add: comma_crt_mdd_zip_child_def comma_zip_fixture_right_def)
  have result_child: "[4,5] ! slot=4+slot"
    using slot_bound by (cases slot; auto)
  show "comma_crt_mdd_zip_certificate [2,2] comma_zip_fixture_left
      comma_zip_fixture_right comma_zip_fixture_result (\<lambda>x y. 2*x+y)
      (comma_crt_mdd_zip_child comma_zip_fixture_left 2 0 slot)
      (comma_crt_mdd_zip_child comma_zip_fixture_right 2 0 slot) ([4,5] ! slot)"
    using comma_zip_fixture_inner[OF slot_bound]
    by (simp only: left_child right_child result_child)
qed

lemma comma_zip_fixture_rejects_swapped_leaf:
  "\<not> comma_crt_mdd_zip_certificate [2,2] [Comma_CRT_MDD_Leaf (0::nat)]
     [Comma_CRT_MDD_Leaf (1::nat)] [Comma_CRT_MDD_Leaf (2::nat)]
     (\<lambda>x y. 2*x+y) 0 0 0"
proof
  assume cert: "comma_crt_mdd_zip_certificate [2,2] [Comma_CRT_MDD_Leaf (0::nat)]
     [Comma_CRT_MDD_Leaf (1::nat)] [Comma_CRT_MDD_Leaf (2::nat)]
     (\<lambda>x y. 2*x+y) 0 0 0"
  have wf: "comma_crt_mdd_table_wellformed [2,2] [Comma_CRT_MDD_Leaf (n::nat)]" for n
    by (auto simp: comma_crt_mdd_table_wellformed_def comma_crt_mdd_node_ordered_def)
  note exact = comma_crt_mdd_zip_certificate_phase[OF cert wf wf wf, where phase=0]
  show False using exact
    by (simp add: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def
      comma_crt_mdd_eval_raw.simps wf)
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Heterogeneous CRT MDD zip and adversarial fixtures"
    @{thms comma_crt_mdd_zip_certificate_sound comma_crt_mdd_zip_certificate_phase
      comma_zip_fixture_distinct_axes comma_zip_fixture_rejects_swapped_leaf};
\<close>

end
