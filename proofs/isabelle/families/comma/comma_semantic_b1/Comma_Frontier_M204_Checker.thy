theory Comma_Frontier_M204_Checker
  imports Comma_Frontier_M204_Generic Comma_CRT_MDD_Zip
    Comma_CRT_MDD_Bind Comma_CRT_MDD_Shift
begin

text \<open>One checked bind root selects a previously checked Boolean comparison.
The association-list labels are the typed one-step codes, while the shifted
D lookup is separate from the source and its occurrence payload.  The premises
are evaluation equations supplied by the MDD operation certificates; no
Bellman equation is assumed.\<close>

definition comma_frontier_m204_mdd_value ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_frontier_m204_mdd_value radices nodes roots phase cid =
    the (comma_crt_mdd_eval_phase radices nodes phase (roots ! cid))"

lemma comma_frontier_m204_mdd_value_exact:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and cid: "cid<length roots" and root: "roots!cid<length nodes"
  shows "comma_crt_mdd_eval_phase radices nodes phase (roots!cid) =
    Some (comma_frontier_m204_mdd_value radices nodes roots phase cid)"
proof -
  obtain payload where eval:
    "comma_crt_mdd_eval_phase radices nodes phase (roots!cid) = Some payload"
    using comma_crt_mdd_eval_phase_total[OF wf root, of phase] by blast
  then show ?thesis by (simp add: comma_frontier_m204_mdd_value_def)
qed

lemma comma_frontier_m204_shifted_value:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and cid: "cid<length roots" and root: "roots!cid<length nodes"
    and shift: "comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!cid) shifted"
  shows "comma_crt_mdd_eval_phase radices nodes phase shifted =
    Some (comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) cid)"
proof -
  have transport: "comma_crt_mdd_eval_phase radices nodes phase shifted =
    comma_crt_mdd_eval_phase radices nodes (phase+1) (roots!cid)"
    by (rule comma_crt_mdd_root_shift_certificate_eval_phase[OF wf shift])
  have period: "comma_crt_mdd_eval_phase radices nodes ((phase+1) mod 924) (roots!cid) =
    comma_crt_mdd_eval_phase radices nodes (phase+1) (roots!cid)"
    by (rule comma_crt_mdd_eval_phase_periodic[OF wf periodic])
  have exact: "comma_crt_mdd_eval_phase radices nodes ((phase+1) mod 924) (roots!cid) =
    Some (comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) cid)"
    by (rule comma_frontier_m204_mdd_value_exact[OF wf cid root])
  show ?thesis using transport period exact by simp
qed

lemma comma_frontier_m204_mapped_shifted_value:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and cid: "cid<length roots" and root: "roots!cid<length nodes"
    and shift: "comma_crt_mdd_root_shift_map_certificate radices nodes
      (\<lambda>x::nat. x+9) 1 (roots!cid) shifted"
  shows "comma_crt_mdd_eval_phase radices nodes phase shifted =
    Some (9+comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) cid)"
proof -
  have transport: "comma_crt_mdd_eval_phase radices nodes phase shifted =
    map_option (\<lambda>x. x+9) (comma_crt_mdd_eval_phase radices nodes (phase+1) (roots!cid))"
    by (rule comma_crt_mdd_root_shift_map_certificate_eval_phase[OF wf shift])
  have period: "comma_crt_mdd_eval_phase radices nodes ((phase+1) mod 924) (roots!cid) =
    comma_crt_mdd_eval_phase radices nodes (phase+1) (roots!cid)"
    by (rule comma_crt_mdd_eval_phase_periodic[OF wf periodic])
  have exact: "comma_crt_mdd_eval_phase radices nodes ((phase+1) mod 924) (roots!cid) =
    Some (comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) cid)"
    by (rule comma_frontier_m204_mdd_value_exact[OF wf cid root])
  show ?thesis using transport period exact by (simp add: add.commute)
qed

lemma comma_frontier_m204_import_equal:
  assumes cert: "comma_crt_mdd_zip_certificate radices source work work
      (\<lambda>x y::nat. if x=y then 1 else 0) source_root work_root truth"
    and source_wf: "comma_crt_mdd_table_wellformed radices source"
    and work_wf: "comma_crt_mdd_table_wellformed radices work"
    and source_bound: "source_root<length source"
    and work_bound: "work_root<length work"
    and truth: "comma_crt_mdd_eval_phase radices work phase truth = Some 1"
  shows "comma_crt_mdd_eval_phase radices source phase source_root =
    comma_crt_mdd_eval_phase radices work phase work_root"
proof -
  obtain x where source: "comma_crt_mdd_eval_phase radices source phase source_root = Some x"
    using comma_crt_mdd_eval_phase_total[OF source_wf source_bound, of phase] by blast
  obtain y where target: "comma_crt_mdd_eval_phase radices work phase work_root = Some y"
    using comma_crt_mdd_eval_phase_total[OF work_wf work_bound, of phase] by blast
  note exact = comma_crt_mdd_zip_certificate_phase
    [OF cert source_wf work_wf work_wf, where phase=phase]
  have scalar: "Some (if x=y then 1 else 0) = Some (1::nat)"
    using exact source target truth by (simp only: option.simps)
  have "x=y" using scalar by (cases "x=y") (simp_all only: if_True if_False option.inject zero_neq_one HOL.simp_thms)
  with source target show ?thesis by (simp only:)
qed

lemma comma_frontier_m204_zip_equal_eval:
  assumes cert: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
      (\<lambda>x y::nat. if x=y then 1 else 0) left right output"
    and wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and l: "comma_crt_mdd_eval_phase radices nodes phase left = Some x"
    and r: "comma_crt_mdd_eval_phase radices nodes phase right = Some y"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    Some (if x=y then 1 else 0)"
  using comma_crt_mdd_zip_certificate_phase[OF cert wellformed wellformed wellformed,
      where phase=phase] l r by simp

lemma comma_frontier_m204_zip_plus9_eval:
  assumes cert: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
      (\<lambda>x y::nat. if x=y+9 then 1 else 0) left right output"
    and wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and l: "comma_crt_mdd_eval_phase radices nodes phase left = Some x"
    and r: "comma_crt_mdd_eval_phase radices nodes phase right = Some y"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    Some (if x=y+9 then 1 else 0)"
  using comma_crt_mdd_zip_certificate_phase[OF cert wellformed wellformed wellformed,
      where phase=phase] l r by simp

lemma comma_frontier_m204_continue_comparison:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and source_cid: "cid<length roots" and source_bound: "roots!cid<length nodes"
    and target_cid: "target<length roots" and target_bound: "roots!target<length nodes"
    and shift: "comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!target) shifted"
    and zip: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
      (\<lambda>x y::nat. if x=y+9 then 1 else 0) (roots!cid) shifted output"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    Some (if comma_frontier_m204_mdd_value radices nodes roots phase cid =
      9+comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) target
      then 1 else 0)"
proof -
  have left: "comma_crt_mdd_eval_phase radices nodes phase (roots!cid) =
      Some (comma_frontier_m204_mdd_value radices nodes roots phase cid)"
    by (rule comma_frontier_m204_mdd_value_exact[OF wf source_cid source_bound])
  have right: "comma_crt_mdd_eval_phase radices nodes phase shifted =
      Some (comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) target)"
    by (rule comma_frontier_m204_shifted_value[OF wf periodic target_cid target_bound shift])
  show ?thesis using comma_frontier_m204_zip_plus9_eval[OF zip wf left right]
    by (simp add: add.commute)
qed

lemma comma_frontier_m204_terminal_comparison:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and source_cid: "cid<length roots" and source_bound: "roots!cid<length nodes"
    and terminal: "comma_crt_mdd_eval_phase radices nodes phase terminal_root = Some J"
    and zip: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
      (\<lambda>x y::nat. if x=y then 1 else 0) (roots!cid) terminal_root output"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    Some (if comma_frontier_m204_mdd_value radices nodes roots phase cid=J then 1 else 0)"
  using comma_frontier_m204_zip_equal_eval[OF zip wf
    comma_frontier_m204_mdd_value_exact[OF wf source_cid source_bound] terminal] .

lemma comma_frontier_m204_checked_payload_bound:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root: "root < length nodes"
    and cover: "comma_crt_mdd_payload_cover nodes root labels"
    and bounded: "list_all (\<lambda>value. value\<le>242) labels"
    and evaluation: "comma_crt_mdd_eval_phase radices nodes phase root = Some value"
  shows "value\<le>242"
proof -
  have raw: "comma_crt_mdd_eval_raw radices nodes (\<lambda>_. phase) root = Some value"
    using evaluation wellformed
    by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)
  have "value \<in> set labels"
    by (rule comma_crt_mdd_eval_raw_payload_covered[OF wellformed root cover raw])
  then show ?thesis using bounded by (auto simp only: list_all_iff set_upt atLeastLessThan_iff HOL.simp_thms)
qed

record comma_frontier_m204_comparison =
  m204_code :: nat
  m204_right :: nat
  m204_output :: nat

definition comma_frontier_m204_comparison_checked ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow>
      nat \<Rightarrow> comma_frontier_m204_comparison \<Rightarrow> bool" where
  "comma_frontier_m204_comparison_checked radices nodes shifted left comparison \<longleftrightarrow>
    (let code=m204_code comparison; right=m204_right comparison;
         output=m204_output comparison in
       1\<le>code \<and> code\<le>55 \<and>
       (if code\<le>46 then
          code-1<length shifted \<and> right=shifted!(code-1) \<and>
          comma_crt_mdd_zip_certificate radices nodes nodes nodes
            (\<lambda>x y. if x=y+9 then 1 else 0) left right output
        else right<length nodes \<and> nodes!right=Comma_CRT_MDD_Leaf (code-47) \<and>
          comma_crt_mdd_zip_certificate radices nodes nodes nodes
            (\<lambda>x y. if x=y then 1 else 0) left right output))"

lemma comma_frontier_m204_comparison_checked_sound:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and cid: "cid<length roots" and bound: "roots!cid<length nodes"
    and target_bounds: "\<And>i. i<46 \<Longrightarrow> i<length roots \<and> roots!i<length nodes"
    and shifts: "\<And>i. i<46 \<Longrightarrow> i<length shifted \<and>
      comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i)"
    and checked: "comma_frontier_m204_comparison_checked radices nodes shifted (roots!cid) comparison"
  shows "1\<le>m204_code comparison \<and> m204_code comparison\<le>55 \<and>
    comma_crt_mdd_eval_phase radices nodes phase (m204_output comparison) =
      Some (if m204_code comparison\<le>46 then
        (if comma_frontier_m204_mdd_value radices nodes roots phase cid =
          9+comma_frontier_m204_mdd_value radices nodes roots
            ((phase+1) mod 924) (m204_code comparison-1) then 1 else 0)
        else (if comma_frontier_m204_mdd_value radices nodes roots phase cid =
          m204_code comparison-47 then 1 else 0))"
proof -
  let ?code = "m204_code comparison"
  have range: "1\<le>?code" "?code\<le>55"
    using checked by (auto simp only: comma_frontier_m204_comparison_checked_def Let_def if_True if_False split: if_splits)
  show ?thesis
  proof (cases "?code\<le>46")
    case True
    have target: "?code-1<46" using True range by arith
    have target_bounds': "?code-1<length roots" "roots!(?code-1)<length nodes"
      using target_bounds[OF target] by blast+
    have shift: "comma_crt_mdd_root_shift_certificate radices nodes 1
      (roots!(?code-1)) (m204_right comparison)"
      using shifts[OF target] checked True
      by (auto simp only: comma_frontier_m204_comparison_checked_def Let_def if_True if_False)
    have zip: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
      (\<lambda>x y::nat. if x=y+9 then 1 else 0) (roots!cid)
      (m204_right comparison) (m204_output comparison)"
      using checked True by (auto simp only: comma_frontier_m204_comparison_checked_def Let_def if_True if_False)
    show ?thesis using range True
      comma_frontier_m204_continue_comparison[OF wf periodic cid bound target_bounds' shift zip,
        where phase=phase] by simp
  next
    case False
    have right_bound: "m204_right comparison<length nodes"
      and leaf: "nodes!(m204_right comparison)=Comma_CRT_MDD_Leaf (?code-47)"
      and zip: "comma_crt_mdd_zip_certificate radices nodes nodes nodes
        (\<lambda>x y::nat. if x=y then 1 else 0) (roots!cid)
        (m204_right comparison) (m204_output comparison)"
      using checked False by (auto simp only: comma_frontier_m204_comparison_checked_def Let_def if_True if_False)
    have terminal: "comma_crt_mdd_eval_phase radices nodes phase (m204_right comparison) = Some (?code-47)"
      by (rule comma_crt_mdd_eval_phase_leaf[OF wf right_bound leaf])
    show ?thesis using range False
      comma_frontier_m204_terminal_comparison[OF wf cid bound terminal zip] by simp
  qed
qed

lemma comma_frontier_m204_checked_comparison_row:
  fixes evaluate :: "nat \<Rightarrow> nat option"
  assumes selection: "evaluate result =
      (case evaluate step of None \<Rightarrow> evaluate fallback
       | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target fallback mapping payload))"
    and step: "evaluate step = Some code"
    and fallback: "evaluate fallback = Some 0"
    and result: "evaluate result = Some 1"
    and labels: "\<And>c root. map_of mapping c = Some root \<Longrightarrow> 1\<le>c \<and> c\<le>55"
    and comparison: "\<And>c root. map_of mapping c = Some root \<Longrightarrow>
      evaluate root = Some (if c\<le>46 then
        (if d=9+next (c-1) then 1 else 0)
       else (if d=c-47 then 1 else 0))"
  shows "code\<noteq>0 \<and>
    (if code\<le>46 then d=9+next (code-1)
     else if code\<le>55 then d=code-47 else False)"
proof -
  obtain root where selected: "map_of mapping code = Some root"
  proof (cases "map_of mapping code")
    case None
    then have "evaluate result = Some 0"
      using selection step fallback None by (simp only: comma_crt_mdd_bind_target_def option.simps)
    with result show ?thesis by simp
  next
    case (Some root)
    then show ?thesis by (rule that)
  qed
  have range: "1\<le>code \<and> code\<le>55" by (rule labels[OF selected])
  have nonzero: "code\<noteq>0" using range by arith
  have upper: "code\<le>55" using range by blast
  have equal: "evaluate root = Some 1"
    using selection step result selected
    by (simp only: comma_crt_mdd_bind_target_def step selected option.simps)
  have computed: "evaluate root = Some (if code\<le>46 then
        (if d=9+next (code-1) then 1 else 0)
       else (if d=code-47 then 1 else 0))"
    by (rule comparison[OF selected])
  have scalar: "Some (if code\<le>46 then
        (if d=9+next (code-1) then 1 else 0)
       else (if d=code-47 then 1 else 0)) = Some (1::nat)"
    using equal computed by (simp only: equal)
  show ?thesis
  proof (cases "code\<le>46")
    case True
    then have "d=9+next (code-1)" using scalar
      by (cases "d=9+next (code-1)") (simp_all only: if_True if_False option.inject zero_neq_one HOL.simp_thms)
    with True nonzero show ?thesis by (simp only: if_True HOL.simp_thms)
  next
    case False
    then have "d=code-47" using scalar
      by (cases "d=code-47") (simp_all only: if_True if_False option.inject zero_neq_one HOL.simp_thms)
    with False upper nonzero show ?thesis by (simp only: if_False if_True HOL.simp_thms)
  qed
qed

lemma comma_frontier_m204_checked_rows_bellman:
  fixes D action :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes rows: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
    \<exists>evaluate result step fallback mapping.
      D phase cid\<le>242 \<and>
      evaluate result =
        (case evaluate step of None \<Rightarrow> evaluate fallback
         | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target fallback mapping payload)) \<and>
      evaluate step = Some (action phase cid) \<and>
      evaluate fallback = Some 0 \<and> evaluate result = Some 1 \<and>
      (\<forall>c root. map_of mapping c=Some root \<longrightarrow> 1\<le>c \<and> c\<le>55) \<and>
      (\<forall>c root. map_of mapping c=Some root \<longrightarrow>
        evaluate root = Some (if c\<le>46 then
          (if D phase cid=9+D ((phase+1) mod 924) (c-1) then 1 else 0)
         else (if D phase cid=c-47 then 1 else 0)))"
  shows "comma_frontier_m204_code_bellman D action"
proof (unfold comma_frontier_m204_code_bellman_def, intro allI impI)
  fix phase cid :: nat
  assume phase: "phase<924" and cid: "cid<46"
  obtain evaluate result step fallback mapping where
    bound: "D phase cid\<le>242"
    and selection: "evaluate result =
      (case evaluate step of None \<Rightarrow> evaluate fallback
       | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target fallback mapping payload))"
    and step: "evaluate step = Some (action phase cid)"
    and fallback: "evaluate fallback = Some 0" and result: "evaluate result = Some 1"
    and labels: "\<forall>c root. map_of mapping c=Some root \<longrightarrow> 1\<le>c \<and> c\<le>55"
    and comparisons: "\<forall>c root. map_of mapping c=Some root \<longrightarrow>
      evaluate root = Some (if c\<le>46 then
        (if D phase cid=9+D ((phase+1) mod 924) (c-1) then 1 else 0)
       else (if D phase cid=c-47 then 1 else 0))"
    using rows[OF phase cid] by blast
  have row: "action phase cid\<noteq>0 \<and>
    (if action phase cid\<le>46 then
       D phase cid=9+D ((phase+1) mod 924) (action phase cid-1)
     else if action phase cid\<le>55 then D phase cid=action phase cid-47 else False)"
    by (rule comma_frontier_m204_checked_comparison_row
      [OF selection step fallback result]) (use labels comparisons in blast)+
  show "D phase cid\<le>242 \<and>
      (let code=action phase cid in
        if code=0 then False else if code\<le>46 then
          D phase cid=9+D ((phase+1) mod 924) (code-1)
        else if code\<le>55 then D phase cid=code-47 else False)"
  proof -
    have nonzero: "action phase cid \<noteq> 0" using row by blast
    have action: "(if action phase cid\<le>46 then
       D phase cid=9+D ((phase+1) mod 924) (action phase cid-1)
     else if action phase cid\<le>55 then D phase cid=action phase cid-47 else False)"
      using row by blast
    show ?thesis using bound nonzero action
      by (simp only: Let_def if_False HOL.simp_thms)
  qed
qed

record comma_frontier_m204_row =
  m204_step_root :: nat
  m204_result_root :: nat
  m204_comparisons :: "comma_frontier_m204_comparison list"

definition comma_frontier_m204_row_mapping ::
    "comma_frontier_m204_row \<Rightarrow> (nat * nat) list" where
  "comma_frontier_m204_row_mapping row = map
    (\<lambda>entry. (m204_code entry,m204_output entry)) (m204_comparisons row)"

definition comma_frontier_m204_row_checked ::
    "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_frontier_m204_row \<Rightarrow> bool" where
  "comma_frontier_m204_row_checked radices nodes roots shifted fallback cid row \<longleftrightarrow>
    cid<length roots \<and> roots!cid<length nodes \<and>
    m204_step_root row<length nodes \<and> m204_result_root row<length nodes \<and>
    nodes!(m204_result_root row)=Comma_CRT_MDD_Leaf 1 \<and>
    comma_crt_mdd_bind_certificate radices nodes (comma_frontier_m204_row_mapping row)
      fallback (m204_step_root row) (m204_result_root row) \<and>
    list_all (comma_frontier_m204_comparison_checked radices nodes shifted (roots!cid))
      (m204_comparisons row)"

lemma comma_frontier_m204_row_checked_sound:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and targets: "\<And>i. i<46 \<Longrightarrow> i<length roots \<and> roots!i<length nodes"
    and shifts: "\<And>i. i<46 \<Longrightarrow> i<length shifted \<and>
      comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i)"
    and fallback_bound: "fallback<length nodes"
    and fallback_leaf: "nodes!fallback=Comma_CRT_MDD_Leaf 0"
    and cover: "comma_crt_mdd_payload_cover nodes (roots!cid) labels"
    and labels: "list_all (\<lambda>value. value\<le>242) labels"
    and row: "comma_frontier_m204_row_checked radices nodes roots shifted fallback cid row"
  defines "D \<equiv> comma_frontier_m204_mdd_value radices nodes roots"
  shows "D phase cid \<le> 242 \<and>
    (let code = the (comma_crt_mdd_eval_phase radices nodes phase (m204_step_root row)) in
      if code=0 then False else if code\<le>46 then
        D phase cid=9+D ((phase+1) mod 924) (code-1)
      else if code\<le>55 then D phase cid=code-47 else False)"
proof -
  have cid: "cid<length roots" and root_bound: "roots!cid<length nodes"
    and step_bound: "m204_step_root row<length nodes"
    and result_bound: "m204_result_root row<length nodes"
    and result_leaf: "nodes!(m204_result_root row)=Comma_CRT_MDD_Leaf 1"
    and binding: "comma_crt_mdd_bind_certificate radices nodes
      (comma_frontier_m204_row_mapping row) fallback
      (m204_step_root row) (m204_result_root row)"
    and comparisons: "list_all
      (comma_frontier_m204_comparison_checked radices nodes shifted (roots!cid))
      (m204_comparisons row)"
    using row by (auto simp only: comma_frontier_m204_row_checked_def if_True if_False)
  obtain code where step: "comma_crt_mdd_eval_phase radices nodes phase (m204_step_root row) = Some code"
    using comma_crt_mdd_eval_phase_total[OF wf step_bound, of phase] by blast
  have source: "comma_crt_mdd_eval_phase radices nodes phase (roots!cid) = Some (D phase cid)"
    using comma_frontier_m204_mdd_value_exact[OF wf cid root_bound, of phase] by (simp add: D_def)
  have dbound: "D phase cid\<le>242"
    by (rule comma_frontier_m204_checked_payload_bound[OF wf root_bound cover labels source])
  have selected: "comma_crt_mdd_eval_phase radices nodes phase (m204_result_root row) =
    (case comma_crt_mdd_eval_phase radices nodes phase (m204_step_root row) of
       None \<Rightarrow> comma_crt_mdd_eval_phase radices nodes phase fallback
     | Some payload \<Rightarrow> comma_crt_mdd_eval_phase radices nodes phase
         (comma_crt_mdd_bind_target fallback (comma_frontier_m204_row_mapping row) payload))"
    by (rule comma_crt_mdd_bind_certificate_eval_phase[OF wf binding])
  have f: "comma_crt_mdd_eval_phase radices nodes phase fallback = Some 0"
    by (rule comma_crt_mdd_eval_phase_leaf[OF wf fallback_bound fallback_leaf])
  have t: "comma_crt_mdd_eval_phase radices nodes phase (m204_result_root row) = Some 1"
    by (rule comma_crt_mdd_eval_phase_leaf[OF wf result_bound result_leaf])
  have item: "\<And>c out. map_of (comma_frontier_m204_row_mapping row) c = Some out \<Longrightarrow>
      \<exists>entry\<in>set (m204_comparisons row). m204_code entry=c \<and> m204_output entry=out"
  proof -
    fix c out
    assume selected: "map_of (comma_frontier_m204_row_mapping row) c = Some out"
    have member: "(c,out) \<in> set (comma_frontier_m204_row_mapping row)"
      by (rule map_of_SomeD[OF selected])
    show "\<exists>entry\<in>set (m204_comparisons row). m204_code entry=c \<and> m204_output entry=out"
      using member by (auto simp only: comma_frontier_m204_row_mapping_def set_map image_iff prod.inject)
  qed
  have properties: "\<And>c out. map_of (comma_frontier_m204_row_mapping row) c = Some out \<Longrightarrow>
    1\<le>c \<and> c\<le>55 \<and>
    comma_crt_mdd_eval_phase radices nodes phase out = Some
      (if c\<le>46 then (if D phase cid=9+D ((phase+1) mod 924) (c-1) then 1 else 0)
       else (if D phase cid=c-47 then 1 else 0))"
  proof -
    fix c out
    assume entry: "map_of (comma_frontier_m204_row_mapping row) c = Some out"
    obtain comparison where member: "comparison\<in>set (m204_comparisons row)"
      and fields: "m204_code comparison=c" "m204_output comparison=out"
      using item[OF entry] by blast
    have checked: "comma_frontier_m204_comparison_checked radices nodes shifted (roots!cid) comparison"
      using comparisons member by (simp add: list_all_iff)
    show "1\<le>c \<and> c\<le>55 \<and>
      comma_crt_mdd_eval_phase radices nodes phase out = Some
        (if c\<le>46 then (if D phase cid=9+D ((phase+1) mod 924) (c-1) then 1 else 0)
         else (if D phase cid=c-47 then 1 else 0))"
      using comma_frontier_m204_comparison_checked_sound
        [OF wf periodic cid root_bound targets shifts checked, where phase=phase] fields
      by (simp add: D_def)
  qed
  have row_result: "code\<noteq>0 \<and>
    (if code\<le>46 then D phase cid=9+D ((phase+1) mod 924) (code-1)
     else if code\<le>55 then D phase cid=code-47 else False)"
    by (rule comma_frontier_m204_checked_comparison_row[OF selected step f t])
      (use properties in blast)+
  have nonzero: "code\<noteq>0" using row_result by blast
  have action: "(if code\<le>46 then D phase cid=9+D ((phase+1) mod 924) (code-1)
     else if code\<le>55 then D phase cid=code-47 else False)"
    using row_result by blast
  show ?thesis using dbound step nonzero action
    by (simp only: Let_def step option.sel if_True if_False HOL.simp_thms)
qed

definition comma_frontier_m204_bulk_checked ::
  "nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    comma_frontier_m204_row list \<Rightarrow> bool" where
  "comma_frontier_m204_bulk_checked radices nodes roots steps shifted fallback labels rows \<longleftrightarrow>
    comma_crt_mdd_table_wellformed radices nodes \<and>
    (\<forall>axis<length radices. radices!axis dvd 924) \<and>
    length roots=46 \<and> length steps=46 \<and> length shifted=46 \<and> length rows=46 \<and>
    fallback<length nodes \<and> nodes!fallback=Comma_CRT_MDD_Leaf 0 \<and>
    list_all (\<lambda>value. value\<le>242) labels \<and>
    list_all (\<lambda>i. roots!i<length nodes \<and> steps!i<length nodes \<and>
      comma_crt_mdd_payload_cover nodes (roots!i) labels \<and>
      comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i) \<and>
      m204_step_root (rows!i)=steps!i \<and>
      comma_frontier_m204_row_checked radices nodes roots shifted fallback i (rows!i)) [0..<46]"

theorem comma_frontier_m204_bulk_checked_bellman:
  assumes checked: "comma_frontier_m204_bulk_checked radices nodes roots steps shifted fallback labels rows"
  shows "comma_frontier_m204_code_bellman
    (comma_frontier_m204_mdd_value radices nodes roots)
    (comma_frontier_m204_mdd_value radices nodes steps)"
proof (unfold comma_frontier_m204_code_bellman_def, intro allI impI)
  fix phase cid :: nat
  assume "phase<924" and cid: "cid<46"
  have wf: "comma_crt_mdd_table_wellformed radices nodes"
    and periodic: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
    and roots_len: "length roots=46" and steps_len: "length steps=46"
    and shifts_len: "length shifted=46" and rows_len: "length rows=46"
    and fallback_bound: "fallback<length nodes"
    and fallback_leaf: "nodes!fallback=Comma_CRT_MDD_Leaf 0"
    and labels: "list_all (\<lambda>value. value\<le>242) labels"
    and all: "list_all (\<lambda>i. roots!i<length nodes \<and> steps!i<length nodes \<and>
      comma_crt_mdd_payload_cover nodes (roots!i) labels \<and>
      comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i) \<and>
      m204_step_root (rows!i)=steps!i \<and>
      comma_frontier_m204_row_checked radices nodes roots shifted fallback i (rows!i)) [0..<46]"
    using checked by (auto simp only: comma_frontier_m204_bulk_checked_def if_True if_False)
  have row_facts: "roots!cid<length nodes" "steps!cid<length nodes"
    "comma_crt_mdd_payload_cover nodes (roots!cid) labels"
    "m204_step_root (rows!cid)=steps!cid"
    "comma_frontier_m204_row_checked radices nodes roots shifted fallback cid (rows!cid)"
    using all cid by (auto simp only: list_all_iff set_upt atLeastLessThan_iff HOL.simp_thms)
  have targets: "\<And>i. i<46 \<Longrightarrow> i<length roots \<and> roots!i<length nodes"
    using all roots_len by (auto simp only: list_all_iff set_upt atLeastLessThan_iff HOL.simp_thms)
  have shifts: "\<And>i. i<46 \<Longrightarrow> i<length shifted \<and>
      comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i)"
    using all shifts_len by (auto simp only: list_all_iff set_upt atLeastLessThan_iff HOL.simp_thms)
  have exact: "comma_frontier_m204_mdd_value radices nodes roots phase cid \<le> 242 \<and>
    (let code = the (comma_crt_mdd_eval_phase radices nodes phase (m204_step_root (rows!cid))) in
      if code=0 then False else if code\<le>46 then
        comma_frontier_m204_mdd_value radices nodes roots phase cid =
          9+comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) (code-1)
      else if code\<le>55 then
        comma_frontier_m204_mdd_value radices nodes roots phase cid=code-47 else False)"
    by (rule comma_frontier_m204_row_checked_sound
      [OF wf periodic targets shifts fallback_bound fallback_leaf row_facts(3) labels row_facts(5)])
  show "comma_frontier_m204_mdd_value radices nodes roots phase cid \<le> 242 \<and>
    (let code=comma_frontier_m204_mdd_value radices nodes steps phase cid in
      if code=0 then False else if code\<le>46 then
        comma_frontier_m204_mdd_value radices nodes roots phase cid=
          9+comma_frontier_m204_mdd_value radices nodes roots ((phase+1) mod 924) (code-1)
      else if code\<le>55 then
        comma_frontier_m204_mdd_value radices nodes roots phase cid=code-47 else False)"
    using exact row_facts(4) by (simp add: comma_frontier_m204_mdd_value_def)
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "M204 checked comparison-to-Bellman assembly"
    @{thms comma_frontier_m204_mdd_value_exact comma_frontier_m204_shifted_value
      comma_frontier_m204_import_equal
      comma_frontier_m204_zip_equal_eval comma_frontier_m204_zip_plus9_eval
      comma_frontier_m204_continue_comparison comma_frontier_m204_terminal_comparison
      comma_frontier_m204_checked_payload_bound comma_frontier_m204_comparison_checked_sound
      comma_frontier_m204_checked_comparison_row
      comma_frontier_m204_checked_rows_bellman
      comma_frontier_m204_row_checked_sound comma_frontier_m204_bulk_checked_bellman};
\<close>

end
