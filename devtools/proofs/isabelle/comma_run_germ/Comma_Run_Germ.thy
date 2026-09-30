theory Comma_Run_Germ
  imports Comma_Round_Weights.Comma_Round_Weights
    Prefix_Effect_Core.Prefix_Effect
    Comma_Fast_Arithmetic.Comma_Fast_Arithmetic
begin

text \<open>A Near germ is keyed by sector and headroom only. It retains the
number of internal unit edges and the first decisive chart, not their history.
Absolute delta and evaluated Entry weight remain occurrence annotations.\<close>

lemma comma_near_internal_shape:
  assumes move: "comma_finite_step 0 (Comma_Near f 0 h) =
    Comma_Next (Comma_Near g d j)"
  shows "g = f" "d = 0" "j < h"
proof -
  have all: "g=f \<and> d=0 \<and> j<h" using move
    by (auto simp: comma_near_control_formula Let_def split: if_splits; arith)
  then show "g=f" "d=0" "j<h" by blast+
qed

function comma_near_germ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_near_germ f h =
    (case comma_finite_step 0 (Comma_Near f 0 h) of
      Comma_Next (Comma_Near g d j) \<Rightarrow>
        (let (n,t) = comma_near_germ f j in (Suc n,t))
    | _ \<Rightarrow> (0,h))"
  by pat_completeness auto
termination
  by (relation "measure snd") (auto dest: comma_near_internal_shape(3))

declare comma_near_germ.simps [simp del]

fun comma_near_prefix :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_near_prefix 0 f h t = (h=t)"
| "comma_near_prefix (Suc n) f h t =
    (\<exists>j. comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j) \<and> comma_near_prefix n f j t)"

definition comma_near_decisive :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_near_decisive f h =
    (\<forall>g d j. comma_finite_step 0 (Comma_Near f 0 h) \<noteq>
      Comma_Next (Comma_Near g d j))"

lemma comma_near_germ_refines:
  assumes result: "comma_near_germ f h = (n,t)"
  shows "comma_near_prefix n f h t \<and> comma_near_decisive f t"
  using result
proof (induction f h arbitrary: n t rule: comma_near_germ.induct)
  case (1 f h)
  then show ?case
    using comma_near_internal_shape
    by (cases "comma_finite_step 0 (Comma_Near f 0 h)")
      (auto simp: comma_near_germ.simps comma_near_decisive_def
        split: comma_finite_position.splits prod.splits)
qed

lemma comma_near_prefix_bound:
  assumes "comma_near_prefix n f h t"
  shows "n \<le> h"
  using assms
proof (induction n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain j where move:
    "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t" by auto
  have "j<h" by (rule comma_near_internal_shape(3)[OF move])
  moreover have "n\<le>j" by (rule Suc.IH[OF tail])
  ultimately show ?case by arith
qed

lemma comma_near_germ_control_bound:
  assumes "comma_near_germ f h = (n,t)"
  shows "n \<le> h"
  using comma_near_germ_refines[OF assms] comma_near_prefix_bound by blast

lemma comma_near_prefix_weighted:
  assumes path: "comma_near_prefix n f h t"
  shows "comma_round_weighted_prefix p r n
    (Comma_Near f delta h) (Comma_Near f delta t) n"
  using path
proof (induction n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain j where step:
    "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t" by auto
  have weighted: "comma_weighted_step (r mod 924) (Comma_Near f delta h) =
    Comma_WNext (Comma_Near f delta j) (Comma_Chart_Weight 0 0 1 1)"
    using step by (auto simp: comma_finite_step_def comma_weighted_step_def
      Let_def split: if_splits)
  show ?case
    unfolding comma_round_weighted_prefix.simps
    apply (rule exI[of _ "Comma_Near f delta j"])
    apply (rule exI[of _ "Comma_Chart_Weight 0 0 1 1"])
    apply (rule exI[of _ n])
    using weighted Suc.IH[OF tail]
    by (simp only: comma_chart_weight_unit; simp del: comma_weighted_step_def)
qed

lemma comma_near_prefix_round_close:
  assumes path: "comma_near_prefix n f h t"
    and terminal: "comma_round_close r (Comma_Near f delta t) = (k,u,event)"
  shows "comma_round_close r (Comma_Near f delta h) = (n+k,u,event)"
  using path
proof (induction n arbitrary: h)
  case 0
  then show ?case using terminal by simp
next
  case (Suc n)
  then obtain j where step:
    "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t" by auto
  have transported: "comma_finite_step (r mod 924) (Comma_Near f delta h) =
    Comma_Next (Comma_Near f delta j)"
    using comma_near_step_delta_transport[of "r mod 924" f 0 delta h 0] step
    by simp
  show ?case
    using comma_round_close.simps[of r "Comma_Near f delta h"]
    by (simp only: transported comma_finite_move.case comma_round_crossing_def
      comma_finite_position.case if_False Suc.IH[OF tail] Let_def prod.case add_Suc)
qed

theorem comma_near_germ_round_close:
  assumes germ: "comma_near_germ f h = (n,t)"
    and terminal: "comma_round_close r (Comma_Near f delta t) = (k,u,event)"
  shows "comma_round_close r (Comma_Near f delta h) = (n+k,u,event)"
  using comma_near_germ_refines[OF germ] terminal
    comma_near_prefix_round_close by blast

corollary comma_near_germ_expand:
  assumes germ: "comma_near_germ f h = (n,t)"
  shows "comma_round_close r (Comma_Near f delta h) =
    (case comma_round_close r (Comma_Near f delta t) of
      (k,u,event) \<Rightarrow> (n+k,u,event))"
  using comma_near_germ_round_close[OF germ]
  by (cases "comma_round_close r (Comma_Near f delta t)") auto

corollary comma_near_germ_literal:
  assumes germ: "comma_near_germ f h = (n,t)"
    and exponent: "5 \<le> p"
    and valid: "comma_round_admitted (Comma_Near f delta h)"
  shows "comma_literal_path n (comma_chart_value p (Comma_Near f delta h))
    (comma_chart_value p (Comma_Near f delta t))"
  using comma_near_germ_refines[OF germ]
    comma_near_prefix_weighted[of n f h t p p delta]
    comma_round_weighted_prefix_literal[of p p n
      "Comma_Near f delta h" "Comma_Near f delta t" n]
    exponent valid by blast

text \<open>This relation is an independent specification of the actual signed
headroom changes on canonical Near edges. It is used only in refinement;
the executable germ above never constructs its displacement list.\<close>
inductive comma_near_displacements ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool" where
  empty: "comma_near_displacements f h h []"
| step: "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Next (Comma_Near f 0 j)
    \<Longrightarrow> comma_near_displacements f j t ds
    \<Longrightarrow> comma_near_displacements f h t ((int j-int h)#ds)"

lemma comma_near_displacements_exact:
  assumes "comma_near_displacements f h t ds"
  shows "sum_list ds = int t-int h \<and> (\<forall>d\<in>set ds. d\<le>0)"
  using assms
proof induction
  case (empty f h)
  then show ?case by simp
next
  case (step f h j t ds)
  have "j<h" by (rule comma_near_internal_shape(3)[OF step.hyps(1)])
  then show ?case using step.IH by (auto simp: algebra_simps)
qed

lemma comma_near_prefix_displacements:
  assumes "comma_near_prefix n f h t"
  shows "\<exists>ds. comma_near_displacements f h t ds \<and> length ds=n"
  using assms
proof (induction n arbitrary: h)
  case 0
  then show ?case by (auto intro: comma_near_displacements.empty)
next
  case (Suc n)
  then obtain j where move:
    "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t" by auto
  obtain ds where ds: "comma_near_displacements f j t ds" "length ds=n"
    using Suc.IH[OF tail] by blast
  show ?case using comma_near_displacements.step[OF move ds(1)] ds(2) by auto
qed

theorem comma_near_germ_tropical_exact:
  assumes germ: "comma_near_germ f h = (n,t)"
  shows "\<exists>ds. comma_near_displacements f h t ds \<and> length ds=n \<and>
    prefix_summary id ds = (int t-int h,int t-int h)"
proof -
  obtain ds where ds: "comma_near_displacements f h t ds" "length ds=n"
    using comma_near_germ_refines[OF germ] comma_near_prefix_displacements by blast
  have exact: "sum_list ds=int t-int h" "\<forall>d\<in>set ds. d\<le>0"
    using comma_near_displacements_exact[OF ds(1)] by blast+
  have "prefix_summary id ds = (int t-int h,int t-int h)"
    using prefix_summary_nonpositive[of ds id] exact by simp
  then show ?thesis using ds by blast
qed

text \<open>The first decisive move is not consumed by the prefix. Thus a
Fork/Landmine contributes no literal edge; a sector/crossing Next contributes
one. These are consequences of the canonical weighted transition, not a
second arithmetic implementation.\<close>

definition comma_near_event :: "nat \<Rightarrow> nat \<Rightarrow> comma_finite_move" where
  "comma_near_event f t = comma_finite_step 0 (Comma_Near f 0 t)"

lemma comma_near_germ_event_transport:
  assumes "comma_near_germ f h = (n,t)"
  shows "comma_finite_step r (Comma_Near f delta t) =
    comma_shift_move delta (comma_near_event f t)"
  using comma_near_step_delta_transport[of r f 0 delta t 0]
  by (simp add: comma_near_event_def)

lemma comma_near_germ_first_event:
  assumes "comma_near_germ f h = (n,t)"
  shows "comma_near_prefix n f h t"
    "\<forall>g d j. comma_near_event f t \<noteq> Comma_Next (Comma_Near g d j)"
  using comma_near_germ_refines[OF assms]
  by (simp_all add: comma_near_decisive_def comma_near_event_def)


text \<open>The sector combines one already-powered Entry with the cached Near
closure. Its weight descriptor contains at most one Entry affine weight and
a unit-edge count. No internal chart list is published.\<close>

type_synonym comma_sector_payload =
  "nat \<times> comma_finite_position \<times> comma_chart_weight option \<times> nat"

definition comma_sector_germ ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_sector_payload" where
  "comma_sector_germ r source =
    (case source of
      Comma_Near f delta h \<Rightarrow>
        (let (n,t) = comma_near_germ f h
          in (n,Comma_Near f delta t,None,n))
    | Comma_Entry f delta x \<Rightarrow>
        (case comma_weighted_step (r mod 924) source of
          Comma_WNext (Comma_Near g d h) weight \<Rightarrow>
            (let (n,t) = comma_near_germ g h
              in (Suc n,Comma_Near g d t,Some weight,n))
        | _ \<Rightarrow> (0,source,None,0)))"

definition comma_sector_weight :: "nat \<Rightarrow> comma_chart_weight option \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_sector_weight p entry units =
    (case entry of None \<Rightarrow> units
      | Some w \<Rightarrow> comma_chart_weight_value p w + units)"

lemma comma_sector_germ_weighted:
  assumes germ: "comma_sector_germ r source = (n,t,entry,units)"
  shows "comma_round_weighted_prefix p r n source t
    (comma_sector_weight p entry units)"
proof (cases source)
  case (Comma_Near f delta h)
  obtain k u where near: "comma_near_germ f h = (k,u)"
    by (cases "comma_near_germ f h") auto
  have prefix: "comma_near_prefix k f h u"
    using comma_near_germ_refines[OF near] by blast
  show ?thesis
    using germ comma_near_prefix_weighted[OF prefix, of p r delta]
    by (auto simp: Comma_Near comma_sector_germ_def near comma_sector_weight_def)
next
  case (Comma_Entry f delta x)
  show ?thesis
  proof (cases "comma_weighted_step (r mod 924) (Comma_Entry f delta x)")
    case (Comma_WNext target weight)
    show ?thesis
    proof (cases target)
      case (Comma_Near g d h)
      obtain k u where near: "comma_near_germ g h = (k,u)"
        by (cases "comma_near_germ g h") auto
      have prefix: "comma_near_prefix k g h u"
        using comma_near_germ_refines[OF near] by blast
      have tail: "comma_round_weighted_prefix p r k
        (Comma_Near g d h) (Comma_Near g d u) k"
        by (rule comma_near_prefix_weighted[OF prefix])
      have move: "comma_weighted_step (r mod 924) (Comma_Entry f delta x) =
        Comma_WNext (Comma_Near g d h) weight"
        using Comma_WNext by (simp only: Comma_Entry Comma_Near)
      have fields: "n=Suc k" "t=Comma_Near g d u" "entry=Some weight" "units=k"
        using germ by (simp_all add: comma_sector_germ_def Comma_Entry move near
          del: comma_weighted_step_def)
      have path: "comma_round_weighted_prefix p r (Suc k)
        (Comma_Entry f delta x) (Comma_Near g d u)
        (comma_chart_weight_value p weight+k)"
        unfolding comma_round_weighted_prefix.simps
        apply (rule exI[of _ "Comma_Near g d h"])
        apply (rule exI[of _ weight])
        apply (rule exI[of _ k])
        using move tail by blast
      show ?thesis using path by (simp only: Comma_Entry fields
        comma_sector_weight_def option.case)
    next
      case (Comma_Entry g d y)
      have False using Comma_WNext Comma_Entry
        by (simp add: comma_weighted_step_def Let_def split: if_splits)
      then show ?thesis by blast
    qed
  qed (use germ Comma_Entry in
    \<open>auto simp: comma_sector_germ_def comma_sector_weight_def
      simp del: comma_weighted_step_def\<close>)
qed

lemma comma_sector_germ_literal:
  assumes germ: "comma_sector_germ r source = (n,t,entry,units)"
    and phase: "r mod 924 = p mod 924"
    and exponent: "5 \<le> p" and valid: "comma_round_admitted source"
  shows "comma_literal_path (comma_sector_weight p entry units)
    (comma_chart_value p source) (comma_chart_value p t)"
  by (rule comma_round_weighted_prefix_literal
      [OF comma_sector_germ_weighted[OF germ] phase exponent valid])

text \<open>Control is an erasure of the one sector constructor.  The derived
case equation is a proof rewrite, not a second constructor.\<close>
definition comma_sector_control ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<times> comma_finite_position" where
  "comma_sector_control r source =
    (case comma_sector_germ r source of (n,t,entry,units) \<Rightarrow> (n,t))"

lemma comma_sector_control_projection:
  "comma_sector_control r source =
    (case comma_sector_germ r source of (n,t,entry,units) \<Rightarrow> (n,t))"
  by (rule comma_sector_control_def)

lemma comma_sector_control_evaluation:
  "comma_sector_control r source =
    (case source of
      Comma_Near f delta h \<Rightarrow>
        (let (n,t) = comma_near_germ f h in (n,Comma_Near f delta t))
    | Comma_Entry f delta x \<Rightarrow>
        (case comma_finite_step (r mod 924) source of
          Comma_Next (Comma_Near g d h) \<Rightarrow>
            (let (n,t) = comma_near_germ g h in (Suc n,Comma_Near g d t))
        | _ \<Rightarrow> (0,source)))"
  by (cases source; cases "comma_weighted_step (r mod 924) source")
    (auto simp: comma_sector_control_def comma_sector_germ_def comma_finite_step_def
      simp del: comma_weighted_step_def
      split: comma_finite_position.splits prod.splits)

lemma comma_sector_control_near:
  assumes "comma_near_germ f h=(n,t)"
  shows "comma_sector_control r (Comma_Near f delta h)=(n,Comma_Near f delta t)"
  by (simp add: comma_sector_control_evaluation assms)

lemma comma_sector_control_entry:
  assumes move: "comma_finite_step (r mod 924) (Comma_Entry f delta x)=
      Comma_Next (Comma_Near g d h)"
    and germ: "comma_near_germ g h=(n,t)"
  shows "comma_sector_control r (Comma_Entry f delta x)=(Suc n,Comma_Near g d t)"
  by (simp add: comma_sector_control_evaluation move germ)

lemma comma_sector_control_expand:
  assumes sector: "comma_sector_control r source=(n,t)"
  shows "comma_round_close r source =
    (case comma_round_close r t of (k,u,event) \<Rightarrow> (n+k,u,event))"
proof (cases source)
  case (Comma_Near f delta h)
  obtain k u where germ: "comma_near_germ f h=(k,u)"
    by (cases "comma_near_germ f h") auto
  have fields: "n=k" "t=Comma_Near f delta u"
    using sector by (simp_all add: Comma_Near comma_sector_control_evaluation germ)
  show ?thesis using comma_near_germ_expand[OF germ, of r delta]
    by (simp only: Comma_Near fields)
next
  case (Comma_Entry f delta x)
  show ?thesis
  proof (cases "comma_finite_step (r mod 924) (Comma_Entry f delta x)")
    case (Comma_Next target)
    show ?thesis
    proof (cases target)
      case (Comma_Near g d h)
      obtain k u where germ: "comma_near_germ g h=(k,u)"
        by (cases "comma_near_germ g h") auto
      have fields: "n=Suc k" "t=Comma_Near g d u"
        using sector by (simp_all add: comma_sector_control_evaluation Comma_Entry
          Comma_Next Comma_Near germ)
      obtain j v event where tail: "comma_round_close r (Comma_Near g d u)=(j,v,event)"
        by (cases "comma_round_close r (Comma_Near g d u)") auto
      have suffix: "comma_round_close r (Comma_Near g d h)=(k+j,v,event)"
        by (rule comma_near_germ_round_close[OF germ tail])
      show ?thesis
        using comma_round_close.simps[of r source]
        by (simp only: Comma_Next comma_finite_move.case Comma_Near
          Comma_Entry comma_round_crossing_def comma_finite_position.case
          if_False suffix fields tail prod.case Let_def add_Suc)
    next
      case (Comma_Entry g d y)
      have "n=0" "t=source" using sector
        by (simp_all add: comma_sector_control_evaluation \<open>source=Comma_Entry f delta x\<close>
          Comma_Next Comma_Entry)
      then show ?thesis by (simp split: prod.splits)
    qed
  qed (use sector Comma_Entry in
    \<open>auto simp: comma_sector_control_evaluation split: prod.splits\<close>)
qed


fun comma_sector_number :: "comma_finite_position \<Rightarrow> nat" where
  "comma_sector_number (Comma_Entry f d x)=f"
| "comma_sector_number (Comma_Near f d h)=f"

lemma comma_sector_control_same_sector:
  assumes "comma_sector_control r source=(n,t)"
  shows "comma_sector_number t=comma_sector_number source"
  using assms
  by (cases source)
    (auto simp: comma_sector_control_evaluation comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits prod.splits)

lemma comma_near_germ_terminal_no_near:
  assumes germ: "comma_near_germ f h=(n,t)"
  shows "comma_finite_step r (Comma_Near f delta t) \<noteq> Comma_Next (Comma_Near g d j)"
proof -
  have decisive: "\<forall>g d j. comma_near_event f t \<noteq> Comma_Next (Comma_Near g d j)"
    using comma_near_germ_first_event(2)[OF germ] .
  have transport: "comma_finite_step r (Comma_Near f delta t)=
    comma_shift_move delta (comma_near_event f t)"
    by (rule comma_near_germ_event_transport[OF germ])
  show ?thesis
  proof (cases "comma_near_event f t")
    case (Comma_Next target)
    then show ?thesis using decisive
      by (cases target) (auto simp: transport)
  qed (simp_all add: transport)
qed

lemma comma_sector_control_no_near_next:
  assumes sector: "comma_sector_control r source=(n,t)"
  shows "comma_finite_step (r mod 924) t \<noteq> Comma_Next (Comma_Near g d j)"
proof (cases source)
  case (Comma_Near f delta h)
  obtain k u where germ: "comma_near_germ f h=(k,u)"
    by (cases "comma_near_germ f h") auto
  have terminal: "t=Comma_Near f delta u"
    using sector by (auto simp: comma_sector_control_evaluation Comma_Near germ)
  show ?thesis unfolding terminal
    by (rule comma_near_germ_terminal_no_near[OF germ])
next
  case (Comma_Entry f delta x)
  show ?thesis
  proof (cases "f<1 \<or> 9<f \<or> 98<x \<or> comma_finite_period f (x mod 10)=0")
    case True
    have move: "comma_finite_step (r mod 924) (Comma_Entry f delta x)=Comma_Invalid"
      using True by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def)
    have terminal: "t=Comma_Entry f delta x"
      using sector by (auto simp: comma_sector_control_evaluation Comma_Entry move)
    show ?thesis by (simp only: terminal move comma_finite_move.distinct not_False_eq_True)
  next
    case False
    let ?h = "comma_finite_headroom f (r mod 924) delta x"
    have move: "comma_finite_step (r mod 924) (Comma_Entry f delta x)=
      Comma_Next (Comma_Near f delta ?h)"
      using False by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def)
    obtain k u where germ: "comma_near_germ f ?h=(k,u)"
      by (cases "comma_near_germ f ?h") auto
    have terminal: "t=Comma_Near f delta u"
      using sector by (auto simp: comma_sector_control_evaluation Comma_Entry move germ)
    show ?thesis unfolding terminal
      by (rule comma_near_germ_terminal_no_near[OF germ])
  qed
qed

lemma comma_sector_continue_increases:
  assumes sector: "comma_sector_control r source=(n,t)"
    and move: "comma_finite_step (r mod 924) t=Comma_Next target"
    and within: "\<not>comma_round_crossing t target"
  shows "comma_sector_number source<comma_sector_number target \<and>
    comma_sector_number target\<le>9"
proof -
  have same: "comma_sector_number t=comma_sector_number source"
    by (rule comma_sector_control_same_sector[OF sector])
  have not_near: "\<forall>g d j. target\<noteq>Comma_Near g d j"
    using move comma_sector_control_no_near_next[OF sector] by blast
  show ?thesis
  proof (cases target)
    case (Comma_Near g d j)
    then show ?thesis using not_near by blast
  next
    case (Comma_Entry g d x)
    note target = Comma_Entry
    show ?thesis
    proof (cases t)
      case (Comma_Entry f delta y)
      have False using move
        by (simp add: Comma_Entry target comma_finite_step_def
          comma_weighted_step_def Let_def split: if_splits)
      then show ?thesis by blast
    next
      case (Comma_Near f delta h)
      show ?thesis using move within same
        by (auto simp: Comma_Near target comma_near_control_formula
          comma_round_crossing_def Let_def split: if_splits; arith)
    qed
  qed
qed

corollary comma_sector_call_budget:
  assumes sector: "comma_sector_control r source=(n,t)"
    and move: "comma_finite_step (r mod 924) t=Comma_Next target"
    and within: "\<not>comma_round_crossing t target"
  shows "Suc (9-comma_sector_number target)\<le>9-comma_sector_number source"
  using comma_sector_continue_increases[OF sector move within] by arith

lemma comma_sector_recursion_decreases:
  assumes sector: "(n,t)=comma_sector_control r source"
    and move: "comma_finite_step (r mod 924) t=Comma_Next target"
    and within: "\<not>comma_round_crossing t target"
  shows "9-comma_sector_number target<9-comma_sector_number source"
  using comma_sector_call_budget[OF sector[symmetric] move within] by arith

text \<open>The whole round executes sector germs, never their internal Near
rows. Every recursive call strictly increases the decimal sector, giving a
budget of at most nine sector calls for admitted sources. Actual deltas are
retained. Literal weights are not identified with chart operation counts.\<close>
function comma_round_control_germ ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    nat \<times> comma_finite_position \<times> comma_round_result" where
  "comma_round_control_germ r source =
    (case comma_sector_control r source of (n,t) \<Rightarrow>
      (case comma_finite_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then (n,t,Comma_Round_Cross target)
          else (let (k,u,event)=comma_round_control_germ r target
            in (n+Suc k,u,event))
      | Comma_Fork a d \<Rightarrow> (n,t,Comma_Round_Fork a d)
      | Comma_Landmine d \<Rightarrow> (n,t,Comma_Round_Landmine d)
      | Comma_Invalid \<Rightarrow> (n,t,Comma_Round_Invalid)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(r,source). 9-comma_sector_number source)")
    (auto intro: comma_sector_recursion_decreases)

declare comma_round_control_germ.simps [simp del]

theorem comma_round_control_germ_refines:
  "comma_round_control_germ r source=comma_round_close r source"
proof (induction r source rule: comma_round_control_germ.induct)
  case (1 r source)
  obtain n t where sector: "comma_sector_control r source=(n,t)"
    by (cases "comma_sector_control r source") auto
  note germ = comma_round_control_germ.simps[of r source]
  note expand = comma_sector_control_expand[OF sector]
  note terminal = comma_round_close.simps[of r t]
  show ?case
  proof (cases "comma_finite_step (r mod 924) t")
    case (Comma_Next target)
    show ?thesis
    proof (cases "comma_round_crossing t target")
      case True
      show ?thesis using germ expand terminal
        by (simp only: sector prod.case Comma_Next comma_finite_move.case True
          if_True add_0_left add_0_right)
    next
      case False
      have ih: "comma_round_control_germ r target=comma_round_close r target"
        using "1.IH" sector[symmetric] Comma_Next False by blast
      obtain k u event where tail: "comma_round_close r target=(k,u,event)"
        by (cases "comma_round_close r target") auto
      show ?thesis using germ expand terminal
        by (simp only: sector prod.case Comma_Next comma_finite_move.case False
          if_False ih tail Let_def)
    qed
  qed (use germ expand terminal sector in
    \<open>auto simp only: prod.case comma_finite_move.case add_0_left add_0_right\<close>)
qed

inductive comma_round_control_germ_calls :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<Rightarrow> bool" where
  stop: "comma_sector_control r source=(n,t) \<Longrightarrow>
    (case comma_finite_step (r mod 924) t of
      Comma_Next target \<Rightarrow> comma_round_crossing t target | _ \<Rightarrow> True)
    \<Longrightarrow> comma_round_control_germ_calls r source 1"
| continue: "comma_sector_control r source=(n,t) \<Longrightarrow>
    comma_finite_step (r mod 924) t=Comma_Next target \<Longrightarrow>
    \<not>comma_round_crossing t target \<Longrightarrow>
    comma_round_control_germ_calls r target calls \<Longrightarrow>
    comma_round_control_germ_calls r source (Suc calls)"

lemma comma_round_control_germ_calls_bound:
  assumes "comma_round_control_germ_calls r source calls"
  shows "calls\<le>Suc (9-comma_sector_number source)"
  using assms
proof induction
  case (stop r source n t)
  then show ?case by simp
next
  case (continue r source n t target calls)
  have "Suc (9-comma_sector_number target)\<le>9-comma_sector_number source"
    by (rule comma_sector_call_budget[OF continue.hyps(1,2,3)])
  then show ?case using continue.IH by arith
qed

lemma comma_round_control_germ_has_calls:
  "\<exists>calls. comma_round_control_germ_calls r source calls"
proof (induction r source rule: comma_round_control_germ.induct)
  case (1 r source)
  obtain n t where sector: "comma_sector_control r source=(n,t)"
    by (cases "comma_sector_control r source") auto
  show ?case
  proof (cases "comma_finite_step (r mod 924) t")
    case (Comma_Next target)
    show ?thesis
    proof (cases "comma_round_crossing t target")
      case True
      have "comma_round_control_germ_calls r source 1"
        by (rule comma_round_control_germ_calls.stop[OF sector])
          (simp only: Comma_Next comma_finite_move.case True)
      then show ?thesis by blast
    next
      case False
      obtain calls where tail: "comma_round_control_germ_calls r target calls"
        using "1.IH" sector[symmetric] Comma_Next False by blast
      show ?thesis
        using comma_round_control_germ_calls.continue[OF sector Comma_Next False tail] by blast
    qed
  qed (use comma_round_control_germ_calls.stop[OF sector] in auto)
qed

theorem comma_round_control_germ_at_most_nine_sectors:
  assumes valid: "comma_round_admitted source"
  shows "\<exists>calls\<le>9. comma_round_control_germ_calls r source calls"
proof -
  obtain calls where calls: "comma_round_control_germ_calls r source calls"
    using comma_round_control_germ_has_calls by blast
  have lower: "1\<le>comma_sector_number source"
    using valid by (cases source) simp_all
  have "calls\<le>9"
    using comma_round_control_germ_calls_bound[OF calls] lower by arith
  then show ?thesis using calls by blast
qed

corollary comma_round_control_germ_literal_prefix:
  assumes germ: "comma_round_control_germ r source=(n,t,event)"
    and phase: "r mod 924=p mod 924"
    and exponent: "5\<le>p" and valid: "comma_round_admitted source"
  shows "\<exists>weight. comma_round_weighted_prefix p r n source t weight \<and>
    comma_literal_path weight (comma_chart_value p source) (comma_chart_value p t)"
  using comma_round_close_literal_prefix[OF _ phase exponent valid] germ
  by (simp only: comma_round_control_germ_refines)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_near_internal_shape comma_near_germ_refines
      comma_near_germ_control_bound comma_near_prefix_weighted
      comma_near_germ_round_close comma_near_germ_expand
      comma_near_germ_literal
      comma_near_germ_event_transport comma_near_germ_first_event
      comma_sector_germ_weighted comma_sector_germ_literal
      comma_near_germ_tropical_exact comma_sector_control_projection
      comma_sector_control_expand comma_sector_call_budget comma_round_control_germ_refines
      comma_round_control_germ_literal_prefix comma_round_control_germ_at_most_nine_sectors})
    then () else error "Comma Near germ depends on an oracle";
\<close>
end
