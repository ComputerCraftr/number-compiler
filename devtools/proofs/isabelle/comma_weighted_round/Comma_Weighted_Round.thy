theory Comma_Weighted_Round
  imports Comma_Weighted_Run_Germ.Comma_Weighted_Run_Germ
begin

text \<open>The predecessor evaluator is a reference specification here.
Its recursive equations are used explicitly at a proved frontier; importing
this theory must not reactivate scalar round execution in simplification.\<close>
declare comma_round_close.simps [simp del]

text \<open>The round constructor owns weighted transport and guard pullback.
The decisive position is retained separately because a power-crossing edge
is included in the completed germ but excluded from the historical control
prefix.\<close>

lemma comma_sector_weighted_germ_fields:
  "germ_source (comma_sector_weighted_germ r source)=source"
  "comma_sector_control r source=
    (germ_controls (comma_sector_weighted_germ r source),
     germ_target (comma_sector_weighted_germ r source))"
  by (simp_all add: comma_sector_weighted_germ_def comma_sector_control_projection
    split: prod.splits)

lemma comma_terminal_weighted_germ_source:
  "germ_source (comma_terminal_weighted_germ r source)=source"
  by (cases source) (simp_all add: comma_terminal_weighted_germ_def Let_def)

lemma comma_weighted_germ_admitted_target:
  assumes "comma_weighted_germ_source_refines p r G"
    and "comma_round_admitted (germ_source G)"
  shows "comma_round_admitted (germ_target G)"
proof -
  have "comma_round_prefix_steps (germ_controls G) r (germ_source G) (germ_target G)"
    using assms(1) comma_round_weighted_prefix_erasure
    unfolding comma_weighted_germ_source_refines_def by blast
  then show ?thesis using comma_round_prefix_admitted assms(2) by blast
qed

lemma comma_entry_weight_from_control:
  assumes move: "comma_finite_step r (Comma_Entry f delta x)=
    Comma_Next (Comma_Near f delta h)"
  shows "comma_weighted_step r (Comma_Entry f delta x)=
    Comma_WNext (Comma_Near f delta h)
      (Comma_Chart_Weight (comma_cycle_length f) delta
       (-int (comma_cycle_length f*(x+h))) (comma_finite_period f (x mod 10)))"
  using move
  by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def split: if_splits)

fun comma_terminal_payload_at ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_terminal_payload" where
  "comma_terminal_payload_at r (Comma_Near f delta h)=
    comma_terminal_event_germ (r mod 924) f delta h"
| "comma_terminal_payload_at r (Comma_Entry f delta x)=
    \<lparr>terminal_action=Comma_Chart_Action 1 0 0,terminal_guards=[],
      terminal_move=Comma_Invalid,terminal_units=0\<rparr>"

definition comma_terminal_payload_weighted ::
  "comma_finite_position \<Rightarrow> comma_terminal_payload \<Rightarrow> comma_weighted_germ" where
  "comma_terminal_payload_weighted source E=
    \<lparr>germ_source=source,germ_target=comma_event_target source (terminal_move E),
      germ_chart=terminal_action E,
      germ_guards=map comma_lift_event_guard (terminal_guards E),
      germ_weight=\<lparr>weight_entries=[],weight_units=terminal_units E\<rparr>,
      germ_controls=terminal_units E\<rparr>"

lemma comma_terminal_payload_projection:
  "comma_terminal_payload_weighted source (comma_terminal_payload_at r source)=
    comma_terminal_weighted_germ r source"
  by (cases source) (simp_all add: comma_terminal_payload_weighted_def
    comma_terminal_weighted_germ_def Let_def)

function comma_round_germ ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
   comma_weighted_germ \<times> comma_finite_position \<times> comma_round_result" where
  "comma_round_germ r source =
    (let P=comma_sector_weighted_germ r source;
         t=germ_target P;
         T=comma_terminal_payload_at r t;
         E=comma_terminal_payload_weighted t T;
         F=comma_weighted_germ_then P E
     in case terminal_move T of
       Comma_Next target \<Rightarrow>
         if comma_move_kind (comma_sector_number t) (terminal_move T)=Comma_Power_Event
         then (F,t,Comma_Round_Cross target)
         else if comma_sector_number source<comma_sector_number target \<and>
                 comma_sector_number target\<le>9
         then (let (G,u,event)=comma_round_germ r target
               in (comma_weighted_germ_then F G,u,event))
         else (F,t,Comma_Round_Invalid)
     | Comma_Fork a d \<Rightarrow> (F,t,Comma_Round_Fork a d)
     | Comma_Landmine d \<Rightarrow> (F,t,Comma_Round_Landmine d)
     | Comma_Invalid \<Rightarrow> (F,t,Comma_Round_Invalid))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(r,source). 9-comma_sector_number source)") auto

declare comma_round_germ.simps [simp del]

lemma comma_weighted_germ_then_source:
  "germ_source (comma_weighted_germ_then A B)=germ_source A"
  by (simp add: comma_weighted_germ_then_def)

lemma comma_round_germ_source:
  assumes "comma_round_germ r source=(G,t,event)"
  shows "germ_source G=source"
  using assms
  by (auto simp only: comma_round_germ.simps[of r source] Let_def
    comma_weighted_germ_then_source comma_sector_weighted_germ_fields(1)
    split: comma_finite_move.splits if_splits prod.splits)

lemma comma_terminal_weighted_payload_refines:
  assumes "r mod 924=p mod 924" "comma_round_admitted source"
  shows "comma_weighted_germ_source_refines p r
    (comma_terminal_payload_weighted source (comma_terminal_payload_at r source))"
  unfolding comma_terminal_payload_projection
  by (rule comma_terminal_weighted_germ_refines[OF assms])

lemma comma_round_germ_refines:
  assumes phase: "r mod 924=p mod 924" and valid: "comma_round_admitted source"
    and result: "comma_round_germ r source=(G,t,event)"
  shows "comma_weighted_germ_source_refines p r G"
  using phase valid result
proof (induction r source arbitrary: G t event rule: comma_round_germ.induct)
  case (1 r source)
  note equation = comma_round_germ.simps[of r source]
  let ?P = "comma_sector_weighted_germ r source"
  let ?t = "germ_target ?P"
  let ?T = "comma_terminal_payload_at r ?t"
  let ?E = "comma_terminal_payload_weighted ?t ?T"
  let ?F = "comma_weighted_germ_then ?P ?E"
  have P: "comma_weighted_germ_source_refines p r ?P"
    by (rule comma_sector_weighted_germ_refines)
  have admitted: "comma_round_admitted ?t"
    using comma_weighted_germ_admitted_target[OF P] "1.prems"(2)
    by (simp only: comma_sector_weighted_germ_fields)
  have E: "comma_weighted_germ_source_refines p r ?E"
    by (rule comma_terminal_weighted_payload_refines[OF "1.prems"(1) admitted])
  have compatible: "germ_target ?P=germ_source ?E"
    by (simp add: comma_terminal_payload_weighted_def)
  have F: "comma_weighted_germ_source_refines p r ?F"
    by (rule comma_weighted_germ_then_refines[OF P E compatible])
  show ?case
  proof (cases "terminal_move ?T")
    case (Comma_Next target)
    have targetF: "germ_target ?F=target"
      by (simp add: comma_weighted_germ_then_def comma_terminal_payload_weighted_def Comma_Next)
    have valid_target: "comma_round_admitted target"
      using comma_weighted_germ_admitted_target[OF F] "1.prems"(2)
      by (simp only: targetF comma_weighted_germ_then_source comma_sector_weighted_germ_fields(1))
    show ?thesis
    proof (cases "comma_move_kind (comma_sector_number ?t) (terminal_move ?T)=Comma_Power_Event")
      case True
      have power: "comma_move_kind (comma_sector_number ?t) (Comma_Next target)=Comma_Power_Event"
        using True by (simp only: Comma_Next HOL.simp_thms)
      show ?thesis using F "1.prems"(3)
        by (auto simp only: equation Let_def Comma_Next comma_finite_move.case
          power if_True HOL.simp_thms prod.inject)
    next
      case False
      have not_power: "comma_move_kind (comma_sector_number ?t) (Comma_Next target)\<noteq>Comma_Power_Event"
        using False by (simp only: Comma_Next HOL.simp_thms)
      show ?thesis
      proof (cases "comma_sector_number source<comma_sector_number target \<and>
                     comma_sector_number target\<le>9")
        case True
        obtain H u e where tail: "comma_round_germ r target=(H,u,e)"
          by (cases "comma_round_germ r target") auto
        have H: "comma_weighted_germ_source_refines p r H"
          using "1.IH" Comma_Next False True "1.prems"(1) valid_target tail by blast
        have "germ_target ?F=germ_source H"
          using comma_round_germ_source[OF tail] targetF by simp
        then have combined: "comma_weighted_germ_source_refines p r (comma_weighted_germ_then ?F H)"
          by (rule comma_weighted_germ_then_refines[OF F H])
        show ?thesis using combined "1.prems"(3)
          by (auto simp only: equation Let_def Comma_Next comma_finite_move.case
            not_power if_False True if_True HOL.simp_thms tail prod.case prod.inject)
      next
        case False
        then show ?thesis using F "1.prems"(3)
          by (auto simp only: equation Let_def Comma_Next comma_finite_move.case
            not_power if_False HOL.simp_thms prod.inject)
      qed
    qed
  qed (use F "1.prems"(3) in
    \<open>auto simp only: equation Let_def comma_finite_move.case prod.inject\<close>)
qed

corollary comma_round_germ_literal:
  assumes result: "comma_round_germ r source=(G,t,event)"
    and phase: "r mod 924=p mod 924"
    and exponent: "5\<le>p"
    and valid: "comma_round_admitted source"
  shows "comma_literal_path (comma_weight_evaluate p (germ_weight G))
    (comma_chart_value p source) (comma_chart_value p (germ_target G))"
proof -
  have source: "germ_source G=source" by (rule comma_round_germ_source[OF result])
  have refined: "comma_weighted_germ_source_refines p r G"
    by (rule comma_round_germ_refines[OF phase valid result])
  have path: "comma_round_weighted_prefix p r (germ_controls G) source
      (germ_target G) (comma_weight_evaluate p (germ_weight G))"
    using refined unfolding comma_weighted_germ_source_refines_def
    by (simp only: source; blast)
  show ?thesis by (rule comma_round_weighted_prefix_literal[OF path phase exponent valid])
qed

lemma comma_sector_target_is_near:
  assumes valid: "comma_round_admitted source"
  shows "\<exists>f delta h. germ_target (comma_sector_weighted_germ r source)=Comma_Near f delta h"
proof (cases source)
  case (Comma_Near f delta h)
  then show ?thesis
    by (auto simp: comma_sector_weighted_germ_def comma_sector_germ_def split: prod.splits)
next
  case (Comma_Entry f delta x)
  have not_invalid: "comma_finite_step (r mod 924) source\<noteq>Comma_Invalid"
    by (rule comma_round_admitted_not_invalid[OF valid])
  have entry_exists: "\<exists>h w. comma_weighted_step (r mod 924) source=
    Comma_WNext (Comma_Near f delta h) w"
    using not_invalid
    by (auto simp: Comma_Entry comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  then obtain h w where move: "comma_weighted_step (r mod 924) source=
    Comma_WNext (Comma_Near f delta h) w" by blast
  have entry_move: "comma_weighted_step (r mod 924) (Comma_Entry f delta x)=
    Comma_WNext (Comma_Near f delta h) w"
    using move by (simp only: Comma_Entry)
  have finite: "comma_finite_step (r mod 924) (Comma_Entry f delta x)=
    Comma_Next (Comma_Near f delta h)"
    by (simp only: comma_finite_step_def entry_move comma_erase_weight.simps)
  obtain n u where near_germ: "comma_near_germ f h=(n,u)"
    by (cases "comma_near_germ f h") auto
  have control: "comma_sector_control r source=(Suc n,Comma_Near f delta u)"
    using comma_sector_control_entry[OF finite near_germ]
    by (simp only: Comma_Entry)
  show ?thesis using control comma_sector_weighted_germ_fields(2)[of r source]
    by auto
qed

fun comma_round_inspection_units :: "comma_round_result \<Rightarrow> nat" where
  "comma_round_inspection_units (Comma_Round_Cross target)=1"
| "comma_round_inspection_units (Comma_Round_Fork a d)=0"
| "comma_round_inspection_units (Comma_Round_Landmine d)=0"
| "comma_round_inspection_units Comma_Round_Invalid=0"

definition comma_round_germ_control where
  "comma_round_germ_control r source =
    (case comma_round_germ r source of (G,t,event) \<Rightarrow>
      (germ_controls G-comma_round_inspection_units event,t,event))"

lemma comma_round_germ_exact_control:
  assumes valid: "comma_round_admitted source"
    and result: "comma_round_germ r source=(G,t,event)"
  shows "\<exists>n. comma_round_close r source=(n,t,event) \<and>
    germ_controls G=n+comma_round_inspection_units event"
  using valid result
proof (induction r source arbitrary: G t event rule: comma_round_germ.induct)
  case (1 r source)
  note equation = comma_round_germ.simps[of r source]
  let ?P = "comma_sector_weighted_germ r source"
  let ?v = "germ_target ?P"
  let ?T = "comma_terminal_payload_at r ?v"
  let ?E = "comma_terminal_payload_weighted ?v ?T"
  let ?F = "comma_weighted_germ_then ?P ?E"
  let ?n = "germ_controls ?P"
  obtain f delta h where near: "?v=Comma_Near f delta h"
    using comma_sector_target_is_near[OF "1.prems"(1), of r] by blast
  have sector: "comma_sector_control r source=(?n,?v)"
    by (rule comma_sector_weighted_germ_fields)
  have move: "terminal_move ?T=comma_finite_step (r mod 924) ?v"
    by (simp add: near comma_terminal_event_germ_def Let_def)
  have units: "germ_controls ?E=comma_event_units (terminal_move ?T)"
    by (simp add: near comma_terminal_payload_weighted_def comma_terminal_event_germ_def Let_def)
  have close: "comma_round_close r source=
    (case comma_round_close r ?v of (k,u,e)\<Rightarrow>(?n+k,u,e))"
    by (rule comma_sector_control_expand[OF sector])
  note close_v = comma_round_close.simps[of r ?v]
  show ?case
  proof (cases "terminal_move ?T")
    case (Comma_Next target)
    have canonical: "comma_finite_step (r mod 924) ?v=Comma_Next target"
      using move Comma_Next by simp
    have crossing: "comma_round_crossing ?v target=
      (comma_move_kind (comma_sector_number ?v) (terminal_move ?T)=Comma_Power_Event)"
      using comma_terminal_event_crossing[of "r mod 924" f delta h target] Comma_Next
      by (simp only: near comma_terminal_payload_at.simps comma_sector_number.simps)
    show ?thesis
    proof (cases "comma_round_crossing ?v target")
      case True
      have power: "comma_move_kind (comma_sector_number ?v) (Comma_Next target)=Comma_Power_Event"
        using crossing True by (simp add: Comma_Next)
      have selected: "(?F,?v,Comma_Round_Cross target)=(G,t,event)"
        using "1.prems"(2)
        by (simp only: equation Let_def Comma_Next comma_finite_move.case
          power if_True HOL.simp_thms)
      have fields: "G=?F" "t=?v" "event=Comma_Round_Cross target"
        using selected by auto
      show ?thesis using close close_v True canonical units fields
        by (auto simp: comma_weighted_germ_then_def Comma_Next)
    next
      case False
      have not_power: "comma_move_kind (comma_sector_number ?v) (Comma_Next target)\<noteq>Comma_Power_Event"
        using crossing False by (simp add: Comma_Next)
      have guard: "comma_sector_number source<comma_sector_number target \<and>
          comma_sector_number target\<le>9"
        using comma_sector_continue_increases[OF sector canonical False] by blast
      have target_valid: "comma_round_admitted target"
      proof -
        have vp: "comma_round_admitted ?v"
          using comma_weighted_germ_admitted_target[OF comma_sector_weighted_germ_refines]
            "1.prems"(1) by (simp only: comma_sector_weighted_germ_fields)
        show ?thesis by (rule comma_round_next_admitted[OF vp canonical])
      qed
      obtain H u e where tail: "comma_round_germ r target=(H,u,e)"
        by (cases "comma_round_germ r target") auto
      obtain k where ih: "comma_round_close r target=(k,u,e)"
        "germ_controls H=k+comma_round_inspection_units e"
        using "1.IH" Comma_Next crossing False guard target_valid tail by blast
      have selected: "(comma_weighted_germ_then ?F H,u,e)=(G,t,event)"
        using "1.prems"(2)
        by (simp only: equation Let_def Comma_Next comma_finite_move.case
          not_power if_False guard if_True tail prod.case HOL.simp_thms)
      have fields: "G=comma_weighted_germ_then ?F H" "t=u" "event=e"
        using selected by auto
      show ?thesis using close close_v canonical False ih units fields
        by (auto simp: comma_weighted_germ_then_def Comma_Next add.assoc)
    qed
  qed (use close close_v equation "1.prems"(2) move units in
    \<open>auto simp: Let_def comma_weighted_germ_then_def\<close>)
qed

corollary comma_round_germ_complete:
  assumes result: "comma_round_germ r source=(G,t,event)"
    and valid: "comma_round_admitted source"
  shows "comma_round_admitted t" "event\<noteq>Comma_Round_Invalid"
proof -
  obtain n where close: "comma_round_close r source=(n,t,event)"
    using comma_round_germ_exact_control[OF valid result] by blast
  show "comma_round_admitted t" "event\<noteq>Comma_Round_Invalid"
    using comma_round_close_admitted[OF close valid] by blast+
qed

lemma comma_round_germ_control_refines:
  assumes "comma_round_admitted source"
  shows "comma_round_germ_control r source=comma_round_close r source"
proof -
  obtain G t event where result: "comma_round_germ r source=(G,t,event)"
    by (cases "comma_round_germ r source") auto
  obtain n where close: "comma_round_close r source=(n,t,event)"
    "germ_controls G=n+comma_round_inspection_units event"
    using comma_round_germ_exact_control[OF assms result] by blast
  show ?thesis by (simp only: comma_round_germ_control_def result prod.case close
    add_diff_cancel_right')
qed

definition comma_weighted_germ_round_frontier :: "nat \<Rightarrow> comma_weighted_germ \<Rightarrow> bool" where
  "comma_weighted_germ_round_frontier r G =
    (comma_round_close r (germ_source G)=
      (case comma_round_close r (germ_target G) of (k,u,e)\<Rightarrow>(germ_controls G+k,u,e)))"

lemma comma_sector_weighted_germ_frontier:
  "comma_weighted_germ_round_frontier r (comma_sector_weighted_germ r source)"
  using comma_sector_control_expand[OF comma_sector_weighted_germ_fields(2)[of r source]]
  by (simp only: comma_weighted_germ_round_frontier_def comma_sector_weighted_germ_fields)

lemma comma_weighted_germ_frontier_then:
  assumes A: "comma_weighted_germ_round_frontier r A"
    and B: "comma_weighted_germ_round_frontier r B"
    and compatible: "germ_target A=germ_source B"
  shows "comma_weighted_germ_round_frontier r (comma_weighted_germ_then A B)"
proof -
  obtain k u e where tail: "comma_round_close r (germ_target B)=(k,u,e)"
    by (cases "comma_round_close r (germ_target B)") auto
  have mid: "comma_round_close r (germ_target A)=(germ_controls B+k,u,e)"
    using B compatible unfolding comma_weighted_germ_round_frontier_def
    by (simp only: tail prod.case)
  show ?thesis using A
    by (simp add: comma_weighted_germ_round_frontier_def comma_weighted_germ_then_def
      mid tail add.assoc)
qed

lemma comma_terminal_weighted_germ_frontier:
  assumes move: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Next target"
    and ordinary: "\<not>comma_round_crossing (Comma_Near f delta h) target"
  shows "comma_weighted_germ_round_frontier r
    (comma_terminal_weighted_germ r (Comma_Near f delta h))"
proof -
  have canonical: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Next target"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show ?thesis
    using comma_round_close.simps[of r "Comma_Near f delta h"]
    by (simp add: comma_weighted_germ_round_frontier_def comma_terminal_weighted_germ_def
      comma_terminal_event_germ_def canonical ordinary Let_def split: prod.splits)
qed

lemma comma_weighted_germ_frontier_stop:
  assumes prefix: "comma_weighted_germ_round_frontier r G"
    and stop: "comma_round_close r (germ_target G)=(0,t,event)"
  shows "comma_round_close r (germ_source G)=(germ_controls G,t,event)"
  using prefix by (simp add: comma_weighted_germ_round_frontier_def stop)

lemma comma_weighted_germ_then_entries:
  "length (weight_entries (germ_weight (comma_weighted_germ_then A B)))=
    length (weight_entries (germ_weight A))+length (weight_entries (germ_weight B))"
  by (simp add: comma_weighted_germ_then_def comma_weight_then_def)

lemma comma_terminal_payload_entries:
  "weight_entries (germ_weight (comma_terminal_payload_weighted source E))=[]"
  by (simp add: comma_terminal_payload_weighted_def)

lemma comma_round_germ_entry_bound:
  assumes result: "comma_round_germ r source=(G,t,event)"
    and sector: "comma_sector_number source\<le>9"
  shows "length (weight_entries (germ_weight G))\<le>10-comma_sector_number source"
  using result sector
proof (induction r source arbitrary: G t event rule: comma_round_germ.induct)
  case (1 r source)
  note equation = comma_round_germ.simps[of r source]
  let ?P = "comma_sector_weighted_germ r source"
  let ?v = "germ_target ?P"
  let ?T = "comma_terminal_payload_at r ?v"
  let ?E = "comma_terminal_payload_weighted ?v ?T"
  let ?F = "comma_weighted_germ_then ?P ?E"
  have local_bound: "length (weight_entries (germ_weight ?F))\<le>1"
    using comma_sector_weighted_germ_entry_bound[of r source]
    by (simp only: comma_weighted_germ_then_entries comma_terminal_payload_entries
      list.size add_0_right)
  have base: "length (weight_entries (germ_weight ?F))\<le>10-comma_sector_number source"
    using local_bound "1.prems"(2) by arith
  show ?case
  proof (cases "terminal_move ?T")
    case (Comma_Next target)
    show ?thesis
    proof (cases "comma_move_kind (comma_sector_number ?v) (terminal_move ?T)=Comma_Power_Event")
      case True
      have power: "comma_move_kind (comma_sector_number ?v) (Comma_Next target)=Comma_Power_Event"
        using True by (simp only: Comma_Next HOL.simp_thms)
      have selected: "(?F,?v,Comma_Round_Cross target)=(G,t,event)"
        using "1.prems"(1)
        by (simp only: equation Let_def Comma_Next comma_finite_move.case power
          if_True HOL.simp_thms)
      show ?thesis using selected base by auto
    next
      case False
      have not_power: "comma_move_kind (comma_sector_number ?v) (Comma_Next target)\<noteq>Comma_Power_Event"
        using False by (simp only: Comma_Next HOL.simp_thms)
      show ?thesis
      proof (cases "comma_sector_number source<comma_sector_number target \<and>
          comma_sector_number target\<le>9")
        case True
        obtain H u e where tail: "comma_round_germ r target=(H,u,e)"
          by (cases "comma_round_germ r target") auto
        have ih: "length (weight_entries (germ_weight H))\<le>10-comma_sector_number target"
          using "1.IH" Comma_Next False True tail by blast
        have selected: "(comma_weighted_germ_then ?F H,u,e)=(G,t,event)"
          using "1.prems"(1)
          by (simp only: equation Let_def Comma_Next comma_finite_move.case not_power
            if_False True if_True tail prod.case HOL.simp_thms)
        have field: "G=comma_weighted_germ_then ?F H" using selected by auto
        have count: "length (weight_entries (germ_weight G))=
            length (weight_entries (germ_weight ?F))+length (weight_entries (germ_weight H))"
          by (simp only: field comma_weighted_germ_then_entries)
        show ?thesis using count local_bound ih True by arith
      next
        case False
        have selected: "(?F,?v,Comma_Round_Invalid)=(G,t,event)"
          using "1.prems"(1)
          by (simp only: equation Let_def Comma_Next comma_finite_move.case not_power
            if_False False HOL.simp_thms)
        show ?thesis using selected base by auto
      qed
    qed
  qed (use base "1.prems"(1) in
    \<open>auto simp only: equation Let_def comma_finite_move.case prod.inject\<close>)
qed

lemma comma_round_germ_at_most_nine_entries:
  assumes result: "comma_round_germ r source=(G,t,event)"
    and valid: "comma_round_admitted source"
  shows "length (weight_entries (germ_weight G))\<le>9"
proof -
  have bounds: "1\<le>comma_sector_number source" "comma_sector_number source\<le>9"
    using valid by (cases source; simp_all)+
  show ?thesis using comma_round_germ_entry_bound[OF result bounds(2)] bounds(1) by arith
qed

lemma comma_terminal_ordinary_frontier:
  assumes move: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Next target"
    and ordinary: "comma_move_kind f (terminal_move
      (comma_terminal_payload_at r (Comma_Near f delta h)))\<noteq>Comma_Power_Event"
  shows "comma_weighted_germ_round_frontier r
    (comma_terminal_weighted_germ r (Comma_Near f delta h))"
proof -
  have crossing: "\<not>comma_round_crossing (Comma_Near f delta h) target"
    using comma_terminal_event_crossing[of "r mod 924" f delta h target] move ordinary
    by (simp only: comma_terminal_payload_at.simps HOL.simp_thms)
  show ?thesis by (rule comma_terminal_weighted_germ_frontier[OF move crossing])
qed

lemma comma_terminal_fork_stop:
  assumes move: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Fork a d"
  shows "comma_round_close r (Comma_Near f delta h)=
    (0,Comma_Near f delta h,Comma_Round_Fork a d)"
proof -
  have canonical: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Fork a d"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show ?thesis using comma_round_close.simps[of r "Comma_Near f delta h"]
    by (simp only: canonical comma_finite_move.case)
qed

lemma comma_terminal_landmine_stop:
  assumes move: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Landmine d"
  shows "comma_round_close r (Comma_Near f delta h)=
    (0,Comma_Near f delta h,Comma_Round_Landmine d)"
proof -
  have canonical: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Landmine d"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show ?thesis using comma_round_close.simps[of r "Comma_Near f delta h"]
    by (simp only: canonical comma_finite_move.case)
qed

lemma comma_terminal_power_stop:
  assumes move: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Next target"
    and power: "comma_move_kind f (terminal_move
      (comma_terminal_payload_at r (Comma_Near f delta h)))=Comma_Power_Event"
  shows "comma_round_close r (Comma_Near f delta h)=
    (0,Comma_Near f delta h,Comma_Round_Cross target)"
proof -
  have canonical: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Next target"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  have crossing: "comma_round_crossing (Comma_Near f delta h) target"
    using comma_terminal_event_crossing[of "r mod 924" f delta h target] move power
    by (simp only: comma_terminal_payload_at.simps HOL.simp_thms)
  show ?thesis using comma_round_close.simps[of r "Comma_Near f delta h"]
    by (simp only: canonical comma_finite_move.case crossing if_True)
qed

definition comma_occurrence_certificate :: "nat \<Rightarrow> comma_weighted_germ \<Rightarrow> bool" where
  "comma_occurrence_certificate r G = (\<forall>p.
    r mod 924=p mod 924 \<longrightarrow> comma_round_admitted (germ_source G) \<longrightarrow>
      comma_weighted_germ_source_refines p r G)"

lemma comma_sector_occurrence_certificate:
  "comma_occurrence_certificate r (comma_sector_weighted_germ r source)"
  unfolding comma_occurrence_certificate_def
  using comma_sector_weighted_germ_refines by blast

lemma comma_terminal_occurrence_certificate:
  "comma_occurrence_certificate r (comma_terminal_weighted_germ r source)"
  unfolding comma_occurrence_certificate_def
  using comma_terminal_weighted_germ_refines comma_terminal_weighted_germ_source by metis

lemma comma_occurrence_certificate_then:
  assumes A: "comma_occurrence_certificate r A"
    and B: "comma_occurrence_certificate r B"
    and compatible: "germ_target A=germ_source B"
  shows "comma_occurrence_certificate r (comma_weighted_germ_then A B)"
  unfolding comma_occurrence_certificate_def
proof (intro allI impI)
  fix p
  assume phase: "r mod 924=p mod 924"
    and valid: "comma_round_admitted (germ_source (comma_weighted_germ_then A B))"
  have validA: "comma_round_admitted (germ_source A)"
    using valid by (simp only: comma_weighted_germ_then_source)
  have refinedA: "comma_weighted_germ_source_refines p r A"
    using A phase validA unfolding comma_occurrence_certificate_def by blast
  have validB: "comma_round_admitted (germ_source B)"
    using comma_weighted_germ_admitted_target[OF refinedA validA] compatible by simp
  have refinedB: "comma_weighted_germ_source_refines p r B"
    using B phase validB unfolding comma_occurrence_certificate_def by blast
  show "comma_weighted_germ_source_refines p r (comma_weighted_germ_then A B)"
    by (rule comma_weighted_germ_then_refines[OF refinedA refinedB compatible])
qed

text \<open>Rank checking demands only the counted decisive observation. This
is a projection of the weighted constructor, not an independently recursive
executor. Its evaluation rules erase charts, guards and literal weights before
any concrete instance is constructed. The scalar count is retained so existing
control checks remain exact.\<close>

definition comma_round_observation where
  "comma_round_observation r source = comma_round_germ_control r source"

lemma comma_round_observation_control:
  assumes "comma_round_admitted source"
  shows "comma_round_observation r source=comma_round_close r source"
  unfolding comma_round_observation_def
  by (rule comma_round_germ_control_refines[OF assms])

definition comma_observation_link where
  "comma_observation_link r n source target =
    (comma_round_admitted source \<longrightarrow>
      comma_round_admitted target \<and>
      comma_round_observation r source=
        (case comma_round_observation r target of (k,t,event)\<Rightarrow>(n+k,t,event)))"

definition comma_observation_stop where
  "comma_observation_stop r source t event =
    (comma_round_admitted source \<longrightarrow>
      comma_round_observation r source=(0,t,event))"

lemma comma_observation_sector:
  assumes sector: "comma_sector_control r source=(n,target)"
  shows "comma_observation_link r n source target"
  unfolding comma_observation_link_def
proof (intro impI)
  assume valid: "comma_round_admitted source"
  have fields: "germ_target (comma_sector_weighted_germ r source)=target"
    using sector comma_sector_weighted_germ_fields(2)[of r source] by simp
  have source: "comma_round_admitted (germ_source (comma_sector_weighted_germ r source))"
    using valid by (simp only: comma_sector_weighted_germ_fields(1))
  have refined: "comma_weighted_germ_source_refines 0 r
    (comma_sector_weighted_germ r source)"
    by (rule comma_sector_weighted_germ_refines)
  have target: "comma_round_admitted target"
    using comma_weighted_germ_admitted_target[OF refined source]
    by (simp only: fields)
  have equation: "comma_round_observation r source=
    (case comma_round_observation r target of (k,t,event)\<Rightarrow>(n+k,t,event))"
    using comma_sector_control_expand[OF sector]
    by (simp only: comma_round_observation_control[OF valid]
      comma_round_observation_control[OF target])
  show "comma_round_admitted target \<and>
    comma_round_observation r source=
      (case comma_round_observation r target of (k,t,event)\<Rightarrow>(n+k,t,event))"
    using target equation by blast
qed

lemma comma_observation_link_then:
  assumes A: "comma_observation_link r n source middle"
    and B: "comma_observation_link r m middle target"
  shows "comma_observation_link r (n+m) source target"
  using A B unfolding comma_observation_link_def
  by (auto simp: add.assoc split: prod.splits)

lemma comma_observation_ordinary:
  assumes move: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Next target"
    and ordinary: "comma_move_kind f (Comma_Next target)\<noteq>Comma_Power_Event"
  shows "comma_observation_link r 1 (Comma_Near f delta h) target"
proof -
  let ?source = "Comma_Near f delta h"
  have payload: "terminal_move (comma_terminal_payload_at r ?source)=Comma_Next target"
    by (simp add: comma_terminal_event_germ_def move Let_def)
  have not_cross: "\<not>comma_round_crossing ?source target"
    using comma_terminal_event_crossing[of "r mod 924" f delta h target]
      payload ordinary
    by (simp only: comma_terminal_payload_at.simps payload HOL.simp_thms)
  show ?thesis unfolding comma_observation_link_def
  proof (intro impI)
    assume valid: "comma_round_admitted ?source"
    have target: "comma_round_admitted target"
      by (rule comma_round_next_admitted[OF valid move])
    have equation: "comma_round_close r ?source=
      (case comma_round_close r target of (k,t,event)\<Rightarrow>(1+k,t,event))"
      using comma_round_close.simps[of r ?source]
      by (simp add: move not_cross Let_def split: prod.splits)
    show "comma_round_admitted target \<and>
      comma_round_observation r ?source=
        (case comma_round_observation r target of (k,t,event)\<Rightarrow>(1+k,t,event))"
      using target equation
      by (simp only: comma_round_observation_control[OF valid]
        comma_round_observation_control[OF target] HOL.simp_thms)
  qed
qed

lemma comma_observation_fork:
  assumes move: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Fork a d"
  shows "comma_observation_stop r (Comma_Near f delta h)
    (Comma_Near f delta h) (Comma_Round_Fork a d)"
proof -
  have payload: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Fork a d"
    by (simp add: comma_terminal_event_germ_def move Let_def)
  show ?thesis using comma_terminal_fork_stop[OF payload]
    unfolding comma_observation_stop_def
    by (simp add: comma_round_observation_control)
qed

lemma comma_observation_landmine:
  assumes move: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Landmine d"
  shows "comma_observation_stop r (Comma_Near f delta h)
    (Comma_Near f delta h) (Comma_Round_Landmine d)"
proof -
  have payload: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Landmine d"
    by (simp add: comma_terminal_event_germ_def move Let_def)
  show ?thesis using comma_terminal_landmine_stop[OF payload]
    unfolding comma_observation_stop_def
    by (simp add: comma_round_observation_control)
qed

lemma comma_observation_power:
  assumes move: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Next target"
    and power: "comma_move_kind f (Comma_Next target)=Comma_Power_Event"
  shows "comma_observation_stop r (Comma_Near f delta h)
    (Comma_Near f delta h) (Comma_Round_Cross target)"
proof -
  have payload: "terminal_move (comma_terminal_payload_at r (Comma_Near f delta h))=Comma_Next target"
    by (simp add: comma_terminal_event_germ_def move Let_def)
  have kind: "comma_move_kind f (terminal_move
    (comma_terminal_payload_at r (Comma_Near f delta h)))=Comma_Power_Event"
    using power by (simp only: payload)
  show ?thesis using comma_terminal_power_stop[OF payload kind]
    unfolding comma_observation_stop_def
    by (simp add: comma_round_observation_control)
qed

lemma comma_observation_finish:
  assumes link: "comma_observation_link r n source target"
    and valid: "comma_round_admitted source"
    and stop: "comma_observation_stop r target t event"
  shows "comma_round_observation r source=(n,t,event)"
  using link valid stop
  unfolding comma_observation_link_def comma_observation_stop_def
  by simp

lemma comma_observation_close:
  assumes valid: "comma_round_admitted source"
    and observed: "comma_round_observation r source=result"
  shows "comma_round_close r source=result"
  using observed by (simp only: comma_round_observation_control[OF valid])

text \<open>The complete round agrees with the canonical decisive event and
retains exact symbolic literal weights and transported guards. This is
occurrence refinement; it is not a theorem permitting arbitrary residue-fiber
merges or the global winning-cycle cutover.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_entry_weight_from_control comma_round_germ_refines comma_round_germ_literal
      comma_round_germ_control_refines comma_round_germ_complete comma_round_germ_at_most_nine_entries
      comma_weighted_germ_frontier_then comma_weighted_germ_frontier_stop
      comma_terminal_ordinary_frontier comma_terminal_fork_stop
      comma_terminal_landmine_stop comma_terminal_power_stop
      comma_sector_occurrence_certificate comma_terminal_occurrence_certificate
      comma_occurrence_certificate_then comma_round_observation_control
      comma_observation_sector comma_observation_link_then comma_observation_ordinary
      comma_observation_fork comma_observation_landmine comma_observation_power
      comma_observation_finish comma_observation_close})
    then () else error "Comma weighted round depends on an oracle";
\<close>
end
