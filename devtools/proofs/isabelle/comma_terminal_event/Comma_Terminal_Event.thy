theory Comma_Terminal_Event
  imports Comma_Chart_Action.Comma_Chart_Action
begin

text \<open>The canonical Near move remains the arithmetic owner. This
projection retains its event, affine chart action, exact inspection weight and
strict/equality guards. A digit is derived from the admitted source headroom;
affine guards alone do not admit another residue fiber.\<close>

datatype comma_event_kind = Comma_Continue_Event | Comma_Cross_Event |
  Comma_Power_Event | Comma_Fork_Event | Comma_Landmine_Event | Comma_Invalid_Event

fun comma_move_kind :: "nat \<Rightarrow> comma_finite_move \<Rightarrow> comma_event_kind" where
  "comma_move_kind f (Comma_Next (Comma_Near g e j)) = Comma_Continue_Event"
| "comma_move_kind f (Comma_Next (Comma_Entry g e x)) =
    (if f<9 then Comma_Cross_Event else Comma_Power_Event)"
| "comma_move_kind f (Comma_Fork a e) = Comma_Fork_Event"
| "comma_move_kind f (Comma_Landmine e) = Comma_Landmine_Event"
| "comma_move_kind f Comma_Invalid = Comma_Invalid_Event"

definition comma_event_wall ::
  "nat \<Rightarrow> comma_guard_relation \<Rightarrow> comma_event_kind \<Rightarrow> comma_event_kind comma_decorated_guard" where
  "comma_event_wall threshold relation event =
    (Comma_Affine_Form 0 1 (-int threshold),relation,event)"

definition comma_event_false :: "comma_event_kind \<Rightarrow> comma_event_kind comma_decorated_guard" where
  "comma_event_false event = (Comma_Affine_Form 0 0 1,Comma_EQ,event)"

fun comma_event_guards :: "nat \<Rightarrow> nat \<Rightarrow> comma_event_kind \<Rightarrow> comma_event_kind comma_decorated_guard list" where
  "comma_event_guards f d Comma_Continue_Event =
    [comma_event_wall (if f<9 then 10*d+f+1 else 10*d+9)
      Comma_GT Comma_Continue_Event]"
| "comma_event_guards f d Comma_Cross_Event =
    (if f<9 then [comma_event_wall (10*d+f+1) Comma_LT Comma_Cross_Event]
     else [comma_event_false Comma_Cross_Event])"
| "comma_event_guards f d Comma_Power_Event =
    (if f=9 then [comma_event_wall (10*d+1) Comma_LE Comma_Power_Event]
     else [comma_event_false Comma_Power_Event])"
| "comma_event_guards f d Comma_Fork_Event =
    (if f<9 then [comma_event_wall (10*d+f+1) Comma_EQ Comma_Fork_Event]
     else [comma_event_false Comma_Fork_Event])"
| "comma_event_guards f d Comma_Landmine_Event =
    (if f=9 then [comma_event_wall (10*d+1) Comma_GT Comma_Landmine_Event,
      comma_event_wall (10*d+9) Comma_LE Comma_Landmine_Event]
     else [comma_event_false Comma_Landmine_Event])"
| "comma_event_guards f d Comma_Invalid_Event = [comma_event_false Comma_Invalid_Event]"

lemma comma_event_guards_exact:
  assumes valid: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
    and phase: "d=(10-h mod 10) mod 10"
  shows "list_all (\<lambda>g. comma_guard_holds g (X,int h))
      (comma_event_guards f d event) =
    (comma_move_kind f (comma_finite_step r (Comma_Near f delta h)) = event)"
  using valid phase
  by (cases event)
    (auto simp: comma_event_wall_def comma_event_false_def
      list_all_iff comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits; arith)+

fun comma_event_action :: "nat \<Rightarrow> nat \<Rightarrow> comma_finite_move \<Rightarrow> comma_chart_action" where
  "comma_event_action delta h (Comma_Next (Comma_Near g e j)) =
    Comma_Chart_Action 1 0 (int j-int h)"
| "comma_event_action delta h (Comma_Next (Comma_Entry g e x)) =
    Comma_Chart_Action (10^(e-delta)) (10^(e-delta)) (-int (h+x))"
| "comma_event_action delta h (Comma_Fork a e) = Comma_Chart_Action 1 0 0"
| "comma_event_action delta h (Comma_Landmine e) = Comma_Chart_Action 1 0 0"
| "comma_event_action delta h Comma_Invalid = Comma_Chart_Action 1 0 0"

fun comma_event_units :: "comma_finite_move \<Rightarrow> nat" where
  "comma_event_units (Comma_Next next) = 1"
| "comma_event_units (Comma_Fork a e) = 0"
| "comma_event_units (Comma_Landmine e) = 0"
| "comma_event_units Comma_Invalid = 0"

record comma_terminal_payload =
  terminal_action :: comma_chart_action
  terminal_guards :: "comma_event_kind comma_decorated_guard list"
  terminal_move :: comma_finite_move
  terminal_units :: nat

definition comma_terminal_event_germ ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_terminal_payload" where
  "comma_terminal_event_germ r f delta h =
    (let move = comma_finite_step r (Comma_Near f delta h);
      d = (10-h mod 10) mod 10
     in \<lparr>terminal_action=comma_event_action delta h move,
       terminal_guards=comma_event_guards f d (comma_move_kind f move),
       terminal_move=move, terminal_units=comma_event_units move\<rparr>)"

lemma comma_terminal_event_phase_erase:
  "comma_terminal_event_germ r f delta h = comma_terminal_event_germ 0 f delta h"
  by (simp only: comma_terminal_event_germ_def comma_near_control_formula)

lemma comma_terminal_guards_admitted:
  assumes "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
  shows "list_all (\<lambda>g. comma_guard_holds g (X,int h))
    (terminal_guards (comma_terminal_event_germ r f delta h))"
proof -
  have exact: "list_all (\<lambda>g. comma_guard_holds g (X,int h))
      (comma_event_guards f ((10-h mod 10) mod 10)
        (comma_move_kind f (comma_finite_step r (Comma_Near f delta h)))) =
    (comma_move_kind f (comma_finite_step r (Comma_Near f delta h)) =
      comma_move_kind f (comma_finite_step r (Comma_Near f delta h)))"
    by (rule comma_event_guards_exact[OF assms refl])
  show ?thesis using exact
    by (simp add: comma_terminal_event_germ_def Let_def)
qed

lemma comma_event_action_refines_step:
  assumes step: "comma_finite_step r (Comma_Near f delta h) = Comma_Next next"
  shows "comma_chart_apply (comma_event_action delta h (Comma_Next next))
      (comma_chart_coordinates p (Comma_Near f delta h)) =
    comma_chart_coordinates p next"
proof (cases "next")
  case (Comma_Near g e j)
  have near_step: "comma_finite_step r (Comma_Near f delta h) =
      Comma_Next (Comma_Near g e j)"
    using step by (simp add: Comma_Near)
  show ?thesis using comma_chart_canonical_near[OF near_step, of p]
    by (simp add: Comma_Near)
next
  case (Comma_Entry g e x)
  define d :: nat where "d=(10-h mod 10) mod 10"
  define I :: nat where "I=(if f<9 then 10*d+f+1 else 10*d+1)"
  define k :: nat where "k=(if f<9 then 0 else 1)"
  have shape: "h\<le>I" "e=delta+k" "x=I-h"
    using step[unfolded Comma_Entry]
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      d_def I_def k_def split: if_splits; arith)+
  have total: "h+x=I" using shape by arith
  have coordinates: "comma_chart_coordinates p (Comma_Entry g (delta+k) (I-h)) =
    comma_chart_apply (Comma_Chart_Action (10^k) (10^k) (-int I))
      (comma_chart_coordinates p (Comma_Near f delta h))"
    by (rule comma_chart_cross_coordinates[OF shape(1)])
  show ?thesis using coordinates total
    by (simp add: Comma_Entry shape(2,3))
qed

lemma comma_terminal_event_weight:
  "terminal_units (comma_terminal_event_germ (p mod 924) f delta h) =
    comma_finite_next_weight p (Comma_Near f delta h)"
  by (auto simp: comma_terminal_event_germ_def comma_finite_next_weight_def
    comma_finite_step_def comma_weighted_step_def comma_chart_weight_value_def
    Let_def split: if_splits)

lemma comma_terminal_event_refines_step:
  assumes move: "terminal_move (comma_terminal_event_germ r f delta h) = Comma_Next next"
  shows "comma_chart_apply (terminal_action (comma_terminal_event_germ r f delta h))
      (comma_chart_coordinates p (Comma_Near f delta h)) =
    comma_chart_coordinates p next"
    "terminal_units (comma_terminal_event_germ r f delta h) = 1"
proof -
  have step: "comma_finite_step r (Comma_Near f delta h) = Comma_Next next"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show "comma_chart_apply (terminal_action (comma_terminal_event_germ r f delta h))
      (comma_chart_coordinates p (Comma_Near f delta h)) =
    comma_chart_coordinates p next"
    using comma_event_action_refines_step[OF step, of p]
    by (simp add: comma_terminal_event_germ_def Let_def step)
  show "terminal_units (comma_terminal_event_germ r f delta h) = 1"
    by (simp add: comma_terminal_event_germ_def Let_def step)
qed

lemma comma_terminal_event_crossing:
  assumes move: "terminal_move (comma_terminal_event_germ r f delta h) =
    Comma_Next target"
  shows "comma_round_crossing (Comma_Near f delta h) target =
    (comma_move_kind f (terminal_move (comma_terminal_event_germ r f delta h)) =
      Comma_Power_Event)"
proof -
  have step: "comma_finite_step r (Comma_Near f delta h) = Comma_Next target"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  have crossing: "comma_round_crossing (Comma_Near f delta h) target =
      (comma_move_kind f (Comma_Next target) = Comma_Power_Event)"
    using step
    by (cases target; auto simp: comma_round_crossing_def
      comma_near_control_formula Let_def split: if_splits; arith)
  show ?thesis using crossing by (simp only: move)
qed

lemma comma_terminal_next_children:
  assumes valid: "1\<le>f" "f\<le>9" "5\<le>p" "1\<le>h" "h\<le>540"
    and move: "terminal_move (comma_terminal_event_germ (p mod 924) f delta h) =
      Comma_Next next"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta h)) = [comma_chart_value p next]"
proof -
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta h) = Comma_Next next"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show ?thesis
    by (rule comma_near_chart_next_literal(3)[OF valid step]; simp)
qed

lemma comma_terminal_fork_children:
  assumes valid: "1\<le>f" "f\<le>9" "5\<le>p" "1\<le>h" "h\<le>540"
    and move: "terminal_move (comma_terminal_event_germ (p mod 924) f delta h) =
      Comma_Fork a delta"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta h)) =
    [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
    "terminal_units (comma_terminal_event_germ (p mod 924) f delta h) = 0"
proof -
  have sector: "comma_sector f (p+delta) (comma_chart_value p (Comma_Near f delta h))"
    by (rule comma_near_chart_checked_sector[OF valid])
  have exponent: "2\<le>p+delta" using valid by arith
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta h) = Comma_Fork a delta"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta h)) =
    [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
    by (rule comma_near_chart_fork(3)[OF sector exponent refl refl step])
  show "terminal_units (comma_terminal_event_germ (p mod 924) f delta h) = 0"
    by (simp add: comma_terminal_event_germ_def Let_def step)
qed

lemma comma_terminal_landmine_children:
  assumes valid: "1\<le>f" "f\<le>9" "5\<le>p" "1\<le>h" "h\<le>540"
    and move: "terminal_move (comma_terminal_event_germ (p mod 924) f delta h) =
      Comma_Landmine delta"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta h)) = []"
    "terminal_units (comma_terminal_event_germ (p mod 924) f delta h) = 0"
proof -
  have sector: "comma_sector f (p+delta) (comma_chart_value p (Comma_Near f delta h))"
    by (rule comma_near_chart_checked_sector[OF valid])
  have exponent: "2\<le>p+delta" using valid by arith
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta h) = Comma_Landmine delta"
    using move by (simp add: comma_terminal_event_germ_def Let_def)
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta h)) = []"
    by (rule comma_near_chart_landmine(1)[OF sector exponent refl refl step])
  show "terminal_units (comma_terminal_event_germ (p mod 924) f delta h) = 0"
    by (simp add: comma_terminal_event_germ_def Let_def step)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_event_guards_exact comma_terminal_event_phase_erase
      comma_terminal_guards_admitted
      comma_event_action_refines_step comma_terminal_event_weight
      comma_terminal_event_refines_step comma_terminal_event_crossing
      comma_terminal_next_children
      comma_terminal_fork_children
      comma_terminal_landmine_children})
    then () else error "Comma terminal event depends on an oracle";
\<close>
end
