theory Comma_Weighted_Run_Germ
  imports Comma_Run_Germ.Comma_Run_Germ Comma_Terminal_Event.Comma_Terminal_Event
begin

text \<open>Exact weight pieces remain bounded occurrence data. In particular,
we do not use the false identity that the floor of a sum is the sum of its
floors. A decimal round has at most nine Entry pieces; unit Near and seam
edges are accumulated separately. The actual delta in every Entry piece is
retained and evaluated at the requested exponent.\<close>

record comma_weight_expression =
  weight_entries :: "comma_chart_weight list"
  weight_units :: nat

definition comma_weight_evaluate :: "nat \<Rightarrow> comma_weight_expression \<Rightarrow> nat" where
  "comma_weight_evaluate p W =
    sum_list (map (comma_chart_weight_value p) (weight_entries W)) + weight_units W"

definition comma_weight_then ::
  "comma_weight_expression \<Rightarrow> comma_weight_expression \<Rightarrow> comma_weight_expression" where
  "comma_weight_then A B = \<lparr>weight_entries=weight_entries A @ weight_entries B,
    weight_units=weight_units A+weight_units B\<rparr>"

lemma comma_weight_then_exact:
  "comma_weight_evaluate p (comma_weight_then A B) =
    comma_weight_evaluate p A+comma_weight_evaluate p B"
  by (simp add: comma_weight_evaluate_def comma_weight_then_def algebra_simps)

lemma comma_weight_then_assoc:
  "comma_weight_then (comma_weight_then A B) C =
    comma_weight_then A (comma_weight_then B C)"
  by (simp add: comma_weight_then_def append_assoc add.assoc)

fun comma_weight_piece_shift :: "nat \<Rightarrow> comma_chart_weight \<Rightarrow> comma_chart_weight" where
  "comma_weight_piece_shift gain (Comma_Chart_Weight a delta b d) =
    Comma_Chart_Weight a (gain+delta) b d"

definition comma_weight_shift :: "nat \<Rightarrow> comma_weight_expression \<Rightarrow> comma_weight_expression" where
  "comma_weight_shift gain W = W\<lparr>weight_entries:=
    map (comma_weight_piece_shift gain) (weight_entries W)\<rparr>"

lemma comma_weight_piece_shift_exact:
  "comma_chart_weight_value p (comma_weight_piece_shift gain w) =
    comma_chart_weight_value (p+gain) w"
  by (cases w) (simp add: comma_chart_weight_value_def add.assoc)

lemma comma_weight_shift_exact:
  "comma_weight_evaluate p (comma_weight_shift gain W) =
    comma_weight_evaluate (p+gain) W"
  by (simp add: comma_weight_evaluate_def comma_weight_shift_def
    map_map comp_def comma_weight_piece_shift_exact)

lemma comma_weight_skew_exact:
  "comma_weight_evaluate p (comma_weight_then A (comma_weight_shift gain B)) =
    comma_weight_evaluate p A+comma_weight_evaluate (p+gain) B"
  by (simp only: comma_weight_then_exact comma_weight_shift_exact)

text \<open>The source and target positions below are occurrence bindings,
not normalized semantic identities. The chart action and pulled guard family
can be shared only alongside their checked source admission. The optional
guard label distinguishes an occurrence-binding equality from a canonical
event guard; it does not invent a new event.\<close>
record comma_weighted_germ =
  germ_source :: comma_finite_position
  germ_target :: comma_finite_position
  germ_chart :: comma_chart_action
  germ_guards :: "comma_event_kind option comma_decorated_guard list"
  germ_weight :: comma_weight_expression
  germ_controls :: nat

definition comma_weighted_germ_then ::
  "comma_weighted_germ \<Rightarrow> comma_weighted_germ \<Rightarrow> comma_weighted_germ" where
  "comma_weighted_germ_then A B = \<lparr>
    germ_source=germ_source A, germ_target=germ_target B,
    germ_chart=comma_chart_then (germ_chart A) (germ_chart B),
    germ_guards=germ_guards A @ map (comma_guard_pullback (germ_chart A)) (germ_guards B),
    germ_weight=comma_weight_then (germ_weight A) (germ_weight B),
    germ_controls=germ_controls A+germ_controls B\<rparr>"

definition comma_weighted_germ_source_refines ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_weighted_germ \<Rightarrow> bool" where
  "comma_weighted_germ_source_refines p r G =
    (comma_round_weighted_prefix p r (germ_controls G)
       (germ_source G) (germ_target G) (comma_weight_evaluate p (germ_weight G)) \<and>
     comma_chart_apply (germ_chart G) (comma_chart_coordinates p (germ_source G)) =
       comma_chart_coordinates p (germ_target G) \<and>
     list_all (\<lambda>g. comma_guard_holds g (comma_chart_coordinates p (germ_source G)))
       (germ_guards G))"

lemma comma_weighted_germ_then_assoc:
  "comma_weighted_germ_then (comma_weighted_germ_then A B) C =
    comma_weighted_germ_then A (comma_weighted_germ_then B C)"
  by (simp add: comma_weighted_germ_then_def comma_chart_then_assoc
    comma_guard_pullback_compose map_map comp_def append_assoc
    comma_weight_then_assoc add.assoc)

lemma comma_weighted_germ_then_refines:
  assumes left: "comma_weighted_germ_source_refines p r A"
    and right: "comma_weighted_germ_source_refines p r B"
    and compatible: "germ_target A=germ_source B"
  shows "comma_weighted_germ_source_refines p r (comma_weighted_germ_then A B)"
proof -
  have pathA: "comma_round_weighted_prefix p r (germ_controls A)
    (germ_source A) (germ_target A) (comma_weight_evaluate p (germ_weight A))"
    and chartA: "comma_chart_apply (germ_chart A) (comma_chart_coordinates p (germ_source A))=
      comma_chart_coordinates p (germ_target A)"
    and guardsA: "list_all (\<lambda>g. comma_guard_holds g
      (comma_chart_coordinates p (germ_source A))) (germ_guards A)"
    using left unfolding comma_weighted_germ_source_refines_def by blast+
  have pathB: "comma_round_weighted_prefix p r (germ_controls B)
    (germ_target A) (germ_target B) (comma_weight_evaluate p (germ_weight B))"
    and chartB: "comma_chart_apply (germ_chart B) (comma_chart_coordinates p (germ_target A))=
      comma_chart_coordinates p (germ_target B)"
    and guardsB: "list_all (\<lambda>g. comma_guard_holds g
      (comma_chart_coordinates p (germ_target A))) (germ_guards B)"
    using right compatible unfolding comma_weighted_germ_source_refines_def by auto
  have path: "comma_round_weighted_prefix p r (germ_controls A+germ_controls B)
    (germ_source A) (germ_target B)
    (comma_weight_evaluate p (germ_weight A)+comma_weight_evaluate p (germ_weight B))"
    by (rule comma_round_weighted_prefix_concat[OF pathA pathB])
  have guards: "list_all (\<lambda>g. comma_guard_holds g
      (comma_chart_coordinates p (germ_source A)))
      (germ_guards A @ map (comma_guard_pullback (germ_chart A)) (germ_guards B))"
    using comma_guarded_then_admission[where
      x="comma_chart_coordinates p (germ_source A)" and A="germ_chart A"
      and GA="germ_guards A" and B="germ_chart B" and GB="germ_guards B"]
    by (simp only: comma_guarded_then.simps snd_conv chartA guardsA guardsB)
  show ?thesis using path chartA chartB guards
    by (simp add: comma_weighted_germ_source_refines_def comma_weighted_germ_then_def
      comma_weight_then_exact comma_chart_then_refines)
qed

fun comma_occurrence_guards ::
  "comma_finite_position \<Rightarrow> comma_event_kind option comma_decorated_guard list" where
  "comma_occurrence_guards (Comma_Entry f delta x) =
    [(Comma_Affine_Form (-1) 1 (int x),Comma_EQ,None)]"
| "comma_occurrence_guards (Comma_Near f delta h) =
    [(Comma_Affine_Form 0 1 (-int h),Comma_EQ,None)]"

lemma comma_occurrence_guards_hold:
  "list_all (\<lambda>g. comma_guard_holds g (comma_chart_coordinates p source))
    (comma_occurrence_guards source)"
  by (cases source) (simp_all add: algebra_simps)

fun comma_prefix_chart ::
  "comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow> comma_chart_action" where
  "comma_prefix_chart (Comma_Entry f delta x) (Comma_Near g d t) =
    Comma_Chart_Action 1 (-1) (int x+int t)"
| "comma_prefix_chart (Comma_Near f delta h) (Comma_Near g d t) =
    Comma_Chart_Action 1 0 (int t-int h)"
| "comma_prefix_chart source target=Comma_Chart_Action 1 0 0"

lemma comma_sector_control_chart:
  assumes sector: "comma_sector_control r source=(n,t)"
  shows "comma_chart_apply (comma_prefix_chart source t)
    (comma_chart_coordinates p source)=comma_chart_coordinates p t"
  using sector
  by (cases source)
    (auto simp: comma_sector_control_evaluation comma_finite_step_def
      comma_weighted_step_def Let_def algebra_simps split: if_splits prod.splits)

definition comma_sector_weighted_germ ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_weighted_germ" where
  "comma_sector_weighted_germ r source =
    (case comma_sector_germ r source of (n,t,entry,units) \<Rightarrow>
      \<lparr>germ_source=source,germ_target=t,germ_chart=comma_prefix_chart source t,
        germ_guards=comma_occurrence_guards source,
        germ_weight=\<lparr>weight_entries=(case entry of None \<Rightarrow> [] | Some w \<Rightarrow> [w]),
          weight_units=units\<rparr>,germ_controls=n\<rparr>)"

lemma comma_sector_weighted_germ_refines:
  "comma_weighted_germ_source_refines p r (comma_sector_weighted_germ r source)"
proof -
  obtain n t entry units where sector: "comma_sector_germ r source=(n,t,entry,units)"
    by (cases "comma_sector_germ r source") auto
  have control: "comma_sector_control r source=(n,t)"
    by (simp only: comma_sector_control_projection sector prod.case)
  have path: "comma_round_weighted_prefix p r n source t
    (comma_sector_weight p entry units)"
    by (rule comma_sector_germ_weighted[OF sector])
  have chart: "comma_chart_apply (comma_prefix_chart source t)
    (comma_chart_coordinates p source)=comma_chart_coordinates p t"
    by (rule comma_sector_control_chart[OF control])
  show ?thesis using path chart comma_occurrence_guards_hold[of p source]
    by (cases entry)
      (simp_all add: comma_sector_weighted_germ_def sector
        comma_weighted_germ_source_refines_def comma_weight_evaluate_def comma_sector_weight_def)
qed

lemma comma_sector_weighted_germ_entry_bound:
  "length (weight_entries (germ_weight (comma_sector_weighted_germ r source)))\<le>1"
  by (auto simp: comma_sector_weighted_germ_def split: prod.splits option.splits)

fun comma_lift_event_guard ::
  "comma_event_kind comma_decorated_guard \<Rightarrow> comma_event_kind option comma_decorated_guard" where
  "comma_lift_event_guard (form,relation,event)=(form,relation,Some event)"

lemma comma_lift_event_guard_holds:
  "comma_guard_holds (comma_lift_event_guard g) x=comma_guard_holds g x"
  by (cases g) (simp split: prod.splits)

fun comma_event_target :: "comma_finite_position \<Rightarrow> comma_finite_move \<Rightarrow> comma_finite_position" where
  "comma_event_target source (Comma_Next target)=target"
| "comma_event_target source (Comma_Fork a d)=source"
| "comma_event_target source (Comma_Landmine d)=source"
| "comma_event_target source Comma_Invalid=source"

definition comma_terminal_weighted_germ ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_weighted_germ" where
  "comma_terminal_weighted_germ r source =
    (case source of Comma_Near f delta h \<Rightarrow>
      (let E=comma_terminal_event_germ (r mod 924) f delta h
       in \<lparr>germ_source=source,
         germ_target=comma_event_target source (terminal_move E),
         germ_chart=terminal_action E,
         germ_guards=map comma_lift_event_guard (terminal_guards E),
         germ_weight=\<lparr>weight_entries=[],weight_units=terminal_units E\<rparr>,
         germ_controls=terminal_units E\<rparr>)
    | _ \<Rightarrow> \<lparr>germ_source=source,germ_target=source,
        germ_chart=Comma_Chart_Action 1 0 0,germ_guards=[],
        germ_weight=\<lparr>weight_entries=[],weight_units=0\<rparr>,germ_controls=0\<rparr>)"

lemma comma_near_event_weighted_prefix:
  assumes phase: "r mod 924=p mod 924"
  shows "comma_round_weighted_prefix p r
      (comma_event_units (comma_finite_step (r mod 924) (Comma_Near f delta h)))
      (Comma_Near f delta h)
      (comma_event_target (Comma_Near f delta h)
        (comma_finite_step (r mod 924) (Comma_Near f delta h)))
      (comma_event_units (comma_finite_step (r mod 924) (Comma_Near f delta h)))"
proof (cases "comma_weighted_step (r mod 924) (Comma_Near f delta h)")
  case (Comma_WNext target weight)
  have finite: "comma_finite_step (r mod 924) (Comma_Near f delta h)=Comma_Next target"
    by (simp only: comma_finite_step_def Comma_WNext comma_erase_weight.simps)
  have weight_value: "comma_chart_weight_value p weight=1"
    using comma_finite_near_next_weight[of p f delta h target] finite Comma_WNext
    by (simp add: comma_finite_next_weight_def phase del: comma_weighted_step_def)
  have path: "comma_round_weighted_prefix p r 1 (Comma_Near f delta h) target 1"
    unfolding One_nat_def comma_round_weighted_prefix_simps
    apply (rule exI[of _ target])
    apply (rule exI[of _ weight])
    apply (rule exI[of _ 0])
    using Comma_WNext weight_value by simp
  show ?thesis using path by (simp only: finite comma_event_units.simps comma_event_target.simps)
qed (simp_all add: comma_finite_step_def del: comma_weighted_step_def)

lemma comma_terminal_weighted_germ_refines:
  assumes phase: "r mod 924=p mod 924"
    and valid: "comma_round_admitted source"
  shows "comma_weighted_germ_source_refines p r (comma_terminal_weighted_germ r source)"
proof (cases source)
  case (Comma_Entry f delta x)
  then show ?thesis
    by (simp add: comma_terminal_weighted_germ_def comma_weighted_germ_source_refines_def
      comma_weight_evaluate_def)
next
  case (Comma_Near f delta h)
  have bounds: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
    using valid by (simp_all add: Comma_Near)
  let ?E = "comma_terminal_event_germ (r mod 924) f delta h"
  have guards: "list_all (\<lambda>g. comma_guard_holds g
      (comma_chart_coordinates p (Comma_Near f delta h)))
      (map comma_lift_event_guard (terminal_guards ?E))"
    using comma_terminal_guards_admitted[OF bounds, of "int (10^(p+delta))" "r mod 924" delta]
    by (simp add: list_all_iff comma_lift_event_guard_holds)
  note path = comma_near_event_weighted_prefix[OF phase, of f delta h]
  have chart: "comma_chart_apply (terminal_action ?E)
      (comma_chart_coordinates p (Comma_Near f delta h)) =
      comma_chart_coordinates p (comma_event_target (Comma_Near f delta h) (terminal_move ?E))"
  proof (cases "comma_finite_step (r mod 924) (Comma_Near f delta h)")
    case (Comma_Next target)
    show ?thesis
      using comma_event_action_refines_step[OF Comma_Next, of p]
      by (simp add: comma_terminal_event_germ_def Let_def Comma_Next)
  qed (simp_all add: comma_terminal_event_germ_def Let_def)
  show ?thesis using guards path chart
    by (simp add: Comma_Near comma_terminal_weighted_germ_def
      comma_weighted_germ_source_refines_def comma_weight_evaluate_def
      comma_terminal_event_germ_def Let_def)
qed

text \<open>This refinement is source-bound: guard truth at this occurrence
does not prove complete admission over other residue fibers. It never
authorizes normalized future-state sharing. Constructors must establish the
exact path and this source-bound refinement from the
canonical weighted transition and source admission. Supplying a record which
satisfies an abstract algebraic law does not discharge that constructor gate.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_weight_then_exact comma_weight_then_assoc
      comma_weight_piece_shift_exact comma_weight_shift_exact comma_weight_skew_exact
      comma_weighted_germ_then_assoc comma_weighted_germ_then_refines
      comma_sector_weighted_germ_refines comma_sector_weighted_germ_entry_bound
      comma_terminal_weighted_germ_refines})
    then () else error "Comma weighted germ algebra depends on an oracle";
\<close>
end
