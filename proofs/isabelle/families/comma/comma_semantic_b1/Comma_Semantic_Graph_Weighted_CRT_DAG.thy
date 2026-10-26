theory Comma_Semantic_Graph_Weighted_CRT_DAG
  imports Comma_CRT_Phase_Clock
begin

text \<open>
A finite clock decision carries control at leaves and additive occurrence
weights on edges.  Malformed axes and rows are rejected by the evaluator;
an unchecked list lookup is never interpreted as an admitted result.
\<close>

datatype 'a comma_semantic_weighted_crt_dag =
    Comma_Weighted_CRT_Leaf 'a
  | Comma_Weighted_CRT_Branch nat
      "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"

fun comma_weighted_crt_eval ::
    "'a comma_semantic_weighted_crt_dag \<Rightarrow> nat \<Rightarrow>
      ('a \<times> nat) option" where
  "comma_weighted_crt_eval (Comma_Weighted_CRT_Leaf control) phase =
    Some (control,0)"
| "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
    (if axis<4 \<and> length rows=comma_crt_axis_radix axis then
       (map (\<lambda>(weight,child). map_option
           (\<lambda>(control,elapsed). (control,weight+elapsed))
           (comma_weighted_crt_eval child phase)) rows) !
         (phase mod comma_crt_axis_radix axis)
     else None)"

definition comma_weighted_crt_apply ::
    "(nat \<times> 'a comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<Rightarrow> ('a \<times> nat) option" where
  "comma_weighted_crt_apply action phase =
    map_option (\<lambda>(control,elapsed). (control,fst action+elapsed))
      (comma_weighted_crt_eval (snd action) phase)"

lemma comma_weighted_crt_apply_add_offset:
  "comma_weighted_crt_apply (extra+fst action,snd action) phase =
    map_option (\<lambda>(control,elapsed). (control,extra+elapsed))
      (comma_weighted_crt_apply action phase)"
  by (cases "comma_weighted_crt_eval (snd action) phase")
    (auto simp: comma_weighted_crt_apply_def algebra_simps
      split: prod.splits)

fun comma_weighted_crt_wellformed ::
    "'a comma_semantic_weighted_crt_dag \<Rightarrow> bool" where
  "comma_weighted_crt_wellformed (Comma_Weighted_CRT_Leaf control) = True"
| "comma_weighted_crt_wellformed (Comma_Weighted_CRT_Branch axis rows) =
    (axis<4 \<and> length rows=comma_crt_axis_radix axis \<and>
      list_all (\<lambda>(weight,child). comma_weighted_crt_wellformed child) rows)"

fun comma_weighted_crt_shape ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow> bool" where
  "comma_weighted_crt_shape lower (Comma_Weighted_CRT_Leaf control) = True"
| "comma_weighted_crt_shape lower (Comma_Weighted_CRT_Branch axis rows) =
    (lower\<le>axis \<and> axis<4 \<and>
      length rows=comma_crt_axis_radix axis \<and>
      list_all (\<lambda>(weight,child). comma_weighted_crt_shape (Suc axis) child) rows)"

lemma comma_weighted_crt_shape_wellformed:
  assumes "comma_weighted_crt_shape lower tree"
  shows "comma_weighted_crt_wellformed tree"
  using assms
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_weighted_crt_axis_positive:
  assumes "axis<4"
  shows "0<comma_crt_axis_radix axis"
  using comma_crt_axis_cases[OF assms]
  by (auto simp: comma_crt_axis_radix_def)

lemma comma_weighted_crt_eval_selected:
  "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
    (if axis<4 \<and> length rows=comma_crt_axis_radix axis then
      (case rows!(phase mod comma_crt_axis_radix axis) of
        (weight,child) \<Rightarrow> map_option
          (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child phase))
     else None)"
  using comma_weighted_crt_axis_positive
  by (auto simp: nth_map case_prod_beta)

declare comma_weighted_crt_eval.simps(2)[simp del, code del]
declare comma_weighted_crt_eval.simps(1)[code]
declare comma_weighted_crt_eval_selected[simp, code]

lemma comma_weighted_crt_eval_branch:
  assumes axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
  shows "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
    (case rows!(phase mod comma_crt_axis_radix axis) of
      (weight,child) \<Rightarrow> map_option
        (\<lambda>(control,elapsed). (control,weight+elapsed))
        (comma_weighted_crt_eval child phase))"
  using comma_weighted_crt_axis_positive[OF axis] extent axis
  by (simp add: nth_map case_prod_beta)

lemma comma_weighted_crt_shape_total:
  assumes "comma_weighted_crt_shape lower tree"
  shows "\<exists>control elapsed. comma_weighted_crt_eval tree phase=Some (control,elapsed)"
  using assms
proof (induction tree arbitrary: lower)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  let ?index = "phase mod comma_crt_axis_radix axis"
  have index: "?index<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain weight child where selected: "rows!?index=(weight,child)"
    by (cases "rows!?index") auto
  have member: "(weight,child)\<in>set rows"
    using nth_mem[OF index] selected by simp
  have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
    by (simp add: prod_set_defs)
  have child_shape: "comma_weighted_crt_shape (Suc axis) child"
    using Comma_Weighted_CRT_Branch.prems member
    by (auto simp: list_all_iff)
  obtain control elapsed where endpoint_fact:
      "comma_weighted_crt_eval child phase=Some (control,elapsed)"
    using Comma_Weighted_CRT_Branch.IH[OF member child_member child_shape]
    by blast
  show ?case
    using comma_weighted_crt_eval_branch[OF axis extent, of phase] selected endpoint_fact
    by auto
qed

fun comma_weighted_crt_shift ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      'a comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_shift delta (Comma_Weighted_CRT_Leaf control) =
    Comma_Weighted_CRT_Leaf control"
| "comma_weighted_crt_shift delta (Comma_Weighted_CRT_Branch axis rows) =
    Comma_Weighted_CRT_Branch axis
      (rotate delta (map (\<lambda>(weight,child).
        (weight,comma_weighted_crt_shift delta child)) rows))"

lemma comma_weighted_crt_shift_shape:
  "comma_weighted_crt_shape lower (comma_weighted_crt_shift delta tree) =
    comma_weighted_crt_shape lower tree"
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_weighted_crt_shift_wellformed:
  "comma_weighted_crt_wellformed (comma_weighted_crt_shift delta tree) =
    comma_weighted_crt_wellformed tree"
  by (induction tree) (auto simp: list_all_iff prod_set_defs)

lemma comma_weighted_crt_shift_exact:
  assumes "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_eval (comma_weighted_crt_shift delta tree) phase =
    comma_weighted_crt_eval tree (phase+delta)"
  using assms
proof (induction tree arbitrary: phase)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  have positive: "0<comma_crt_axis_radix axis"
    by (rule comma_weighted_crt_axis_positive[OF axis])
  have index: "phase mod comma_crt_axis_radix axis<length rows"
    using positive extent by simp
  have shifted_index: "(phase+delta) mod comma_crt_axis_radix axis<length rows"
    using positive extent by simp
  obtain weight child where selected:
      "rows!((phase+delta) mod comma_crt_axis_radix axis)=(weight,child)"
    by (cases "rows!((phase+delta) mod comma_crt_axis_radix axis)") auto
  have member: "(weight,child)\<in>set rows"
    using nth_mem[OF shifted_index] selected by simp
  have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
    by (simp add: prod_set_defs)
  have child_shape: "comma_weighted_crt_wellformed child"
    using Comma_Weighted_CRT_Branch.prems member
    by (auto simp: list_all_iff)
  have child_exact:
      "comma_weighted_crt_eval (comma_weighted_crt_shift delta child) phase =
        comma_weighted_crt_eval child (phase+delta)"
    using Comma_Weighted_CRT_Branch.IH[OF member child_member child_shape]
    by blast
  show ?case
    using axis extent positive index shifted_index selected child_exact
    by (simp add: comma_weighted_crt_eval_branch nth_rotate nth_map
      mod_add_right_eq add.commute)
qed

fun comma_weighted_crt_bind ::
    "'a comma_semantic_weighted_crt_dag \<Rightarrow>
      ('a \<Rightarrow> nat \<times> 'b comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<times> 'b comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_bind (Comma_Weighted_CRT_Leaf control) next = next control"
| "comma_weighted_crt_bind (Comma_Weighted_CRT_Branch axis rows) next =
    (0, Comma_Weighted_CRT_Branch axis
      (map (\<lambda>(weight,child).
        (weight+fst (comma_weighted_crt_bind child next),
          snd (comma_weighted_crt_bind child next))) rows))"

lemma comma_weighted_crt_bind_exact:
  "comma_weighted_crt_apply (comma_weighted_crt_bind tree next) phase =
    Option.bind (comma_weighted_crt_eval tree phase)
      (\<lambda>(control,elapsed). map_option
        (\<lambda>(result,more). (result,elapsed+more))
        (comma_weighted_crt_apply (next control) phase))"
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case
    by (simp add: comma_weighted_crt_apply_def option.map_id)
next
  case (Comma_Weighted_CRT_Branch axis rows)
  show ?case
  proof (cases "axis<4 \<and> length rows=comma_crt_axis_radix axis")
    case False
    then show ?thesis
      by (auto simp: comma_weighted_crt_apply_def option.map_id)
  next
    case True
    then have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
      by auto
    have index: "phase mod comma_crt_axis_radix axis<length rows"
      using comma_weighted_crt_axis_positive[OF axis] extent by simp
    obtain weight child where selected:
        "rows!(phase mod comma_crt_axis_radix axis)=(weight,child)"
      by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
    have member: "(weight,child)\<in>set rows"
      using nth_mem[OF index] selected by simp
    have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
      by (simp add: prod_set_defs)
    have child_exact:
      "comma_weighted_crt_apply (comma_weighted_crt_bind child next) phase =
        Option.bind (comma_weighted_crt_eval child phase)
          (\<lambda>(control,elapsed). map_option
            (\<lambda>(result,more). (result,elapsed+more))
            (comma_weighted_crt_apply (next control) phase))"
      using Comma_Weighted_CRT_Branch.IH[OF member child_member]
      by blast
    have lifted:
      "map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_apply (comma_weighted_crt_bind child next) phase) =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (Option.bind (comma_weighted_crt_eval child phase)
            (\<lambda>(control,elapsed). map_option
              (\<lambda>(result,more). (result,elapsed+more))
              (comma_weighted_crt_apply (next control) phase)))"
      by (rule arg_cong[OF child_exact])
    show ?thesis
      using axis extent index selected lifted
      by (simp add: comma_weighted_crt_apply_def nth_map
        map_option_bind bind_map_option option.map_comp o_def
        case_prod_unfold algebra_simps option.map_id)
  qed
qed

lemma comma_weighted_crt_wellformed_bind:
  assumes tree: "comma_weighted_crt_wellformed tree"
    and callback: "\<And>control.
      comma_weighted_crt_wellformed (snd (next control))"
  shows "comma_weighted_crt_wellformed
    (snd (comma_weighted_crt_bind tree next))"
  using tree
  by (induction tree)
    (auto simp: list_all_iff prod_set_defs case_prod_unfold Let_def
      intro: callback)

lemma comma_weighted_crt_recenter_exact:
  assumes axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
    and common: "\<forall>edge\<in>set rows. common\<le>fst edge"
  shows "comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis rows) phase =
    comma_weighted_crt_apply
      (offset+common,Comma_Weighted_CRT_Branch axis
        (map (\<lambda>(weight,child). (weight-common,child)) rows)) phase"
proof -
  have index: "phase mod comma_crt_axis_radix axis<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain weight child where selected:
      "rows!(phase mod comma_crt_axis_radix axis)=(weight,child)"
    by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
  have bound: "common\<le>weight"
    using common nth_mem[OF index] selected by auto
  show ?thesis
    using axis extent index selected bound
    by (cases "comma_weighted_crt_eval child phase")
      (auto simp: comma_weighted_crt_apply_def nth_map algebra_simps
        split: prod.splits)
qed

lemma comma_weighted_crt_branch_apply:
  assumes axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
  shows "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
    comma_weighted_crt_apply (rows!(phase mod comma_crt_axis_radix axis)) phase"
  using comma_weighted_crt_eval_branch[OF axis extent, of phase]
  by (simp add: comma_weighted_crt_apply_def case_prod_beta)

lemma comma_weighted_crt_branch_congruence:
  assumes axis: "axis<4"
    and left: "length left=comma_crt_axis_radix axis"
    and right: "length right=comma_crt_axis_radix axis"
    and rows: "\<And>slot. slot<comma_crt_axis_radix axis \<Longrightarrow>
      comma_weighted_crt_apply (left!slot) phase =
        comma_weighted_crt_apply (right!slot) phase"
  shows "comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis left) phase =
    comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis right) phase"
proof -
  have bound: "phase mod comma_crt_axis_radix axis<comma_crt_axis_radix axis"
    using comma_weighted_crt_axis_positive[OF axis] by simp
  show ?thesis
    unfolding comma_weighted_crt_apply_def
    using comma_weighted_crt_branch_apply[OF axis left, of phase]
      comma_weighted_crt_branch_apply[OF axis right, of phase]
      rows[OF bound]
    by simp
qed

lemma comma_weighted_crt_collapse_equal:
  assumes axis: "axis<4"
  shows "comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis
        (replicate (comma_crt_axis_radix axis) (weight,child))) phase =
    comma_weighted_crt_apply (offset+weight,child) phase"
  using comma_weighted_crt_axis_positive[OF axis] axis
  by (cases "comma_weighted_crt_eval child phase")
    (auto simp: comma_weighted_crt_apply_def nth_map algebra_simps
      split: prod.splits)

text \<open>
The selector is constructed from the external clock characters, skipping every
axis whose CRT idempotent is zero modulo the local period. It never builds a
924-element phase table. Its public constructor rejects unsupported periods
and incomplete rows before any source action is selected.
\<close>

fun comma_weighted_crt_selector_aux ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow>
      'a comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_selector_aux [] period accumulated values =
    Comma_Weighted_CRT_Leaf (values!(accumulated mod period))"
| "comma_weighted_crt_selector_aux (axis#axes) period accumulated values =
    (if comma_crt_axis_weight axis mod period=0 then
       comma_weighted_crt_selector_aux axes period accumulated values
     else Comma_Weighted_CRT_Branch axis
       (map (\<lambda>slot. (0,comma_weighted_crt_selector_aux axes period
         (accumulated+comma_crt_axis_weight axis*slot) values))
         [0..<comma_crt_axis_radix axis]))"

definition comma_weighted_crt_selector ::
    "nat \<Rightarrow> 'a list \<Rightarrow> 'a comma_semantic_weighted_crt_dag option" where
  "comma_weighted_crt_selector period values =
    (if 0<period \<and> period dvd 924 \<and> length values=period then
      Some (comma_weighted_crt_selector_aux [0,1,2,3] period 0 values)
     else None)"

lemma comma_weighted_crt_selector_aux_exact:
  assumes axes: "\<forall>axis\<in>set axes. axis<4"
  shows "comma_weighted_crt_eval
      (comma_weighted_crt_selector_aux axes period accumulated values) phase =
    Some (values!((accumulated+sum_list
      (map (\<lambda>axis. comma_crt_axis_weight axis*
        (phase mod comma_crt_axis_radix axis)) axes)) mod period),0)"
  using axes
proof (induction axes arbitrary: accumulated)
  case Nil
  then show ?case by simp
next
  case (Cons axis axes)
  have axis: "axis<4" and tail: "\<forall>a\<in>set axes. a<4"
    using Cons.prems by auto
  have positive: "0<comma_crt_axis_radix axis"
    by (rule comma_weighted_crt_axis_positive[OF axis])
  show ?case
  proof (cases "comma_crt_axis_weight axis mod period=0")
    case True
    have zero: "(comma_crt_axis_weight axis*
        (phase mod comma_crt_axis_radix axis)) mod period=0"
      using comma_crt_weighted_term[OF True,
        of "phase mod comma_crt_axis_radix axis"] by simp
    have omitted:
      "(accumulated+comma_crt_axis_weight axis*
          (phase mod comma_crt_axis_radix axis)+sum_list
          (map (\<lambda>a. comma_crt_axis_weight a*
            (phase mod comma_crt_axis_radix a)) axes)) mod period =
       (accumulated+sum_list (map (\<lambda>a. comma_crt_axis_weight a*
          (phase mod comma_crt_axis_radix a)) axes)) mod period"
    proof -
      let ?tail = "sum_list (map (\<lambda>a. comma_crt_axis_weight a*
        (phase mod comma_crt_axis_radix a)) axes)"
      have replacement:
        "(accumulated+?tail+comma_crt_axis_weight axis*
            (phase mod comma_crt_axis_radix axis)) mod period =
          (accumulated+?tail+0) mod period"
        by (rule mod_add_cong[OF refl]) (use zero in simp)
      show ?thesis using replacement
        by (simp add: add.assoc add.commute add.left_commute)
    qed
    show ?thesis
      using Cons.IH[OF tail, of accumulated] True omitted
      by (simp add: add.assoc)
  next
    case False
    show ?thesis
      using Cons.IH[OF tail,
          of "accumulated+comma_crt_axis_weight axis*
            (phase mod comma_crt_axis_radix axis)"] axis positive False
      by (simp add: comma_weighted_crt_eval_branch nth_map add.assoc)
  qed
qed

lemma comma_weighted_crt_selector_exact:
  assumes period: "0<period" "period dvd 924"
    and extent: "length values=period"
  shows "comma_weighted_crt_selector period values =
      Some (comma_weighted_crt_selector_aux [0,1,2,3] period 0 values)"
    and "comma_weighted_crt_eval
      (comma_weighted_crt_selector_aux [0,1,2,3] period 0 values) phase =
      Some (values!(phase mod period),0)"
proof -
  show "comma_weighted_crt_selector period values =
      Some (comma_weighted_crt_selector_aux [0,1,2,3] period 0 values)"
    using period extent by (simp add: comma_weighted_crt_selector_def)
  have axes: "\<forall>axis\<in>set ([0,1,2,3]::nat list). axis<4" by simp
  have clock:
    "(sum_list (map (\<lambda>axis. comma_crt_axis_weight axis*
        (phase mod comma_crt_axis_radix axis)) [0,1,2,3])) mod period =
      phase mod period"
    using comma_crt_clock_mod[OF period(2), of phase]
      mod_mod_cancel[OF period(2), of
        "sum_list (map (\<lambda>axis. comma_crt_axis_weight axis*
          (phase mod comma_crt_axis_radix axis)) [0,1,2,3])"]
    by (simp add: comma_crt_clock_def comma_crt_axis_radix_def
      comma_crt_axis_weight_def add.assoc)
  show "comma_weighted_crt_eval
      (comma_weighted_crt_selector_aux [0,1,2,3] period 0 values) phase =
      Some (values!(phase mod period),0)"
    using comma_weighted_crt_selector_aux_exact[OF axes,
      of period 0 "values" phase] clock by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT decision semantics, shifts, joins and normalization"
    @{thms comma_weighted_crt_eval_branch comma_weighted_crt_shape_total
      comma_weighted_crt_apply_add_offset
      comma_weighted_crt_shift_shape comma_weighted_crt_shift_wellformed
      comma_weighted_crt_shape_wellformed comma_weighted_crt_shift_exact
      comma_weighted_crt_bind_exact comma_weighted_crt_wellformed_bind
      comma_weighted_crt_recenter_exact
      comma_weighted_crt_collapse_equal comma_weighted_crt_branch_apply
      comma_weighted_crt_branch_congruence
      comma_weighted_crt_selector_aux_exact comma_weighted_crt_selector_exact};
\<close>

end
