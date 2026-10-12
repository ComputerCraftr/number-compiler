theory Comma_Python_Chart_Refinement
  imports Comma_Semantic_Producer_Coefficients
begin

text \<open>
The runtime scalar chart has the same state coordinates as the finite
position datatype: an Entry stores its offset and a Near stores its headroom.
This theory records the branches and payload fields of the runtime scalar
chart step in Isabelle, then proves that the returned move erases to the
canonical finite transition.  The grouped Near locator is deliberately
outside this scalar refinement theorem.
\<close>

record comma_python_cycle_transfer =
  comma_python_transfer_leading :: nat
  comma_python_transfer_entering_digit :: nat
  comma_python_transfer_period :: nat
  comma_python_transfer_displacement :: nat
  comma_python_transfer_maximum_guard :: nat

record comma_python_chart_move =
  comma_python_chart_next :: "comma_finite_position option"
  comma_python_chart_weight :: comma_chart_weight
  comma_python_chart_fork_a :: "nat option"
  comma_python_chart_cycle :: "comma_python_cycle_transfer option"
  comma_python_chart_terminal :: "comma_finite_position option"
  comma_python_chart_literal_increment :: nat

definition comma_python_chart_position_admitted ::
  "comma_finite_position \<Rightarrow> bool" where
  "comma_python_chart_position_admitted position \<longleftrightarrow>
    (case position of
       Comma_Entry f delta offset \<Rightarrow>
         1 \<le> f \<and> f \<le> 9 \<and> offset \<le> 89 + f
     | Comma_Near f delta headroom \<Rightarrow>
         1 \<le> f \<and> f \<le> 9 \<and> 1 \<le> headroom \<and>
           headroom \<le> 540)"

definition comma_python_unit_chart_weight :: comma_chart_weight where
  "comma_python_unit_chart_weight = Comma_Chart_Weight 0 0 1 1"

definition comma_python_zero_chart_weight :: comma_chart_weight where
  "comma_python_zero_chart_weight = Comma_Chart_Weight 0 0 0 1"

definition comma_python_chart_expected_literal_increment ::
  "comma_finite_position \<Rightarrow> nat" where
  "comma_python_chart_expected_literal_increment position =
    (case position of
       Comma_Entry f delta offset \<Rightarrow> 0
     | Comma_Near f delta headroom \<Rightarrow>
         (let d = (10 - headroom mod 10) mod 10 in
           if f < 9 then
             (let low = 10 * d + f;
                  high = low + 1
              in if headroom > high then low
                 else if headroom = high then 0
                 else high)
           else
             (let same = 10 * d + 9;
                  cross = 10 * d + 1
              in if headroom > same then same
                 else if headroom \<le> cross then cross
                 else 0)))"

definition comma_python_cycle_displacement :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_python_cycle_displacement f entering_digit =
    (let divisor = gcd f 10;
         period = 10 div divisor;
         residue = entering_digit mod divisor
     in 10 * (period * residue +
          divisor * period * (period - 1) div 2) + period * f)"

lemma comma_python_cycle_displacement_eq_finite_period:
  "comma_python_cycle_displacement f digit = comma_finite_period f digit"
  by (simp add: comma_python_cycle_displacement_def comma_finite_period_def
      Let_def mult_ac)

fun comma_python_chart_position_delta :: "comma_finite_position \<Rightarrow> nat" where
  "comma_python_chart_position_delta (Comma_Entry f delta offset) = delta"
| "comma_python_chart_position_delta (Comma_Near f delta headroom) = delta"

definition comma_python_scalar_chart_step ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_chart_move option" where
  "comma_python_scalar_chart_step residue position =
    (if residue < 924 then (case position of
       Comma_Entry f delta offset \<Rightarrow>
         if comma_python_chart_position_admitted position then
           (let h = comma_finite_headroom f residue delta offset;
                L = comma_cycle_length f;
                P = comma_python_cycle_displacement f (offset mod 10);
                extra = comma_finite_guard_extra f
            in Some \<lparr>
              comma_python_chart_next = Some (Comma_Near f delta h),
              comma_python_chart_weight =
                Comma_Chart_Weight L delta (- int (L * (offset + h))) P,
              comma_python_chart_fork_a = None,
              comma_python_chart_cycle = Some \<lparr>
                comma_python_transfer_leading = f,
                comma_python_transfer_entering_digit = offset mod 10,
                comma_python_transfer_period = L,
                comma_python_transfer_displacement = P,
                comma_python_transfer_maximum_guard = P + extra\<rparr>,
              comma_python_chart_terminal = None,
              comma_python_chart_literal_increment = 0\<rparr>)
         else None
     | Comma_Near f delta headroom \<Rightarrow>
         if \<not> comma_python_chart_position_admitted position then None
         else
           (let d = (10 - headroom mod 10) mod 10 in
             if f < 9 then
               (let low = 10 * d + f;
                    high = low + 1
                in if headroom > high then
                     Some \<lparr>
                       comma_python_chart_next = Some
                         (Comma_Near f delta (headroom - low)),
                       comma_python_chart_weight = comma_python_unit_chart_weight,
                       comma_python_chart_fork_a = None,
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = None,
                       comma_python_chart_literal_increment = low\<rparr>
                   else if headroom = high then
                     Some \<lparr>
                       comma_python_chart_next = None,
                       comma_python_chart_weight = comma_python_zero_chart_weight,
                       comma_python_chart_fork_a = Some (f + 1),
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = Some position,
                       comma_python_chart_literal_increment = 0\<rparr>
                   else
                     Some \<lparr>
                       comma_python_chart_next = Some
                         (Comma_Entry (f + 1) delta (high - headroom)),
                       comma_python_chart_weight = comma_python_unit_chart_weight,
                       comma_python_chart_fork_a = None,
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = None,
                       comma_python_chart_literal_increment = high\<rparr>)
             else
               (let same = 10 * d + 9;
                    cross = 10 * d + 1
                in if headroom > same then
                     Some \<lparr>
                       comma_python_chart_next = Some
                         (Comma_Near 9 delta (headroom - same)),
                       comma_python_chart_weight = comma_python_unit_chart_weight,
                       comma_python_chart_fork_a = None,
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = None,
                       comma_python_chart_literal_increment = same\<rparr>
                   else if headroom \<le> cross then
                     Some \<lparr>
                       comma_python_chart_next = Some
                         (Comma_Entry 1 (Suc delta) (cross - headroom)),
                       comma_python_chart_weight = comma_python_unit_chart_weight,
                       comma_python_chart_fork_a = None,
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = None,
                       comma_python_chart_literal_increment = cross\<rparr>
                   else
                     Some \<lparr>
                       comma_python_chart_next = None,
                       comma_python_chart_weight = comma_python_zero_chart_weight,
                       comma_python_chart_fork_a = None,
                       comma_python_chart_cycle = None,
                       comma_python_chart_terminal = Some position,
                       comma_python_chart_literal_increment = 0\<rparr>)))
     else None)"

definition comma_python_chart_move_erasure ::
  "comma_finite_position \<Rightarrow> comma_python_chart_move \<Rightarrow>
    comma_finite_move" where
  "comma_python_chart_move_erasure source move =
    (case comma_python_chart_next move of
       Some next \<Rightarrow> Comma_Next next
     | None \<Rightarrow>
         (case comma_python_chart_fork_a move of
            Some a \<Rightarrow> Comma_Fork a
              (comma_python_chart_position_delta source)
          | None \<Rightarrow> Comma_Landmine
              (comma_python_chart_position_delta source)))"

definition comma_python_chart_cycle_for_entry ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_python_cycle_transfer" where
  "comma_python_chart_cycle_for_entry f offset =
    (let P = comma_python_cycle_displacement f (offset mod 10)
    in \<lparr>comma_python_transfer_leading = f,
        comma_python_transfer_entering_digit = offset mod 10,
        comma_python_transfer_period = comma_cycle_length f,
        comma_python_transfer_displacement = P,
        comma_python_transfer_maximum_guard =
          P + (if f < 9 then 1 else 0)\<rparr>)"

lemma comma_python_chart_cycle_guard_exact:
  assumes leading: "1 \<le> f" "f \<le> 9"
    and digit: "digit < 10"
  shows "comma_python_transfer_maximum_guard
      (comma_python_chart_cycle_for_entry f digit) =
    comma_phase_max_guard f digit (comma_cycle_length f)"
proof -
  have guard:
    "comma_phase_max_guard f digit (comma_cycle_length f) =
      comma_finite_period f digit + comma_finite_guard_extra f"
    by (rule comma_finite_entry_guard_refines[OF leading digit])
  show ?thesis
    using guard
    by (simp add: comma_python_chart_cycle_for_entry_def
        comma_python_cycle_displacement_eq_finite_period
        comma_finite_guard_extra_def Let_def)
qed

definition comma_python_chart_move_matches_weighted ::
  "comma_finite_position \<Rightarrow> comma_python_chart_move \<Rightarrow>
    comma_weighted_move \<Rightarrow> bool" where
  "comma_python_chart_move_matches_weighted source move weighted \<longleftrightarrow>
    (case weighted of
       Comma_WNext next weight \<Rightarrow>
         comma_python_chart_next move = Some next \<and>
         comma_python_chart_weight move = weight \<and>
         comma_python_chart_fork_a move = None \<and>
         comma_python_chart_terminal move = None \<and>
         (case source of
            Comma_Entry f delta offset \<Rightarrow>
              comma_python_chart_literal_increment move = 0 \<and>
              comma_python_chart_cycle move = Some
                (comma_python_chart_cycle_for_entry f offset)
          | Comma_Near f delta headroom \<Rightarrow>
              comma_python_chart_cycle move = None \<and>
              comma_python_chart_literal_increment move =
                comma_python_chart_expected_literal_increment source)
     | Comma_WFork terminal a delta \<Rightarrow>
         comma_python_chart_next move = None \<and>
         comma_python_chart_weight move = comma_python_zero_chart_weight \<and>
         comma_python_chart_fork_a move = Some a \<and>
         comma_python_chart_cycle move = None \<and>
         comma_python_chart_terminal move = Some terminal \<and>
         comma_python_chart_position_delta source = delta \<and>
         comma_python_chart_literal_increment move = 0
     | Comma_WLandmine terminal delta \<Rightarrow>
         comma_python_chart_next move = None \<and>
         comma_python_chart_weight move = comma_python_zero_chart_weight \<and>
         comma_python_chart_fork_a move = None \<and>
         comma_python_chart_cycle move = None \<and>
         comma_python_chart_terminal move = Some terminal \<and>
         comma_python_chart_position_delta source = delta \<and>
         comma_python_chart_literal_increment move = 0
     | Comma_WInvalid \<Rightarrow> False)"

lemma comma_python_finite_period_positive:
  assumes leading: "1 \<le> f" "f \<le> 9"
  shows "0 < comma_finite_period f (offset mod 10)"
proof -
  have member:
    "comma_finite_period f (offset mod 10) \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog leading by auto
  show ?thesis using member by (auto simp: comma_cycle_displacements_def)
qed

lemma comma_python_scalar_chart_step_refines_entry:
  assumes residue: "residue < 924"
    and leading: "1 \<le> f" "f \<le> 9"
    and offset: "offset \<le> 89 + f"
  shows "\<exists>move.
    comma_python_scalar_chart_step residue (Comma_Entry f delta offset) =
      Some move \<and>
    comma_python_chart_move_erasure (Comma_Entry f delta offset) move =
      comma_finite_step residue (Comma_Entry f delta offset) \<and>
    comma_python_chart_move_matches_weighted
      (Comma_Entry f delta offset) move
      (comma_weighted_step residue (Comma_Entry f delta offset))"
proof -
  have offset98: "offset \<le> 98" using leading offset by arith
  have period: "0 < comma_finite_period f (offset mod 10)"
    by (rule comma_python_finite_period_positive[OF leading])
  let ?h = "comma_finite_headroom f residue delta offset"
  let ?L = "comma_cycle_length f"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?move = "\<lparr>
    comma_python_chart_next = Some (Comma_Near f delta ?h),
    comma_python_chart_weight =
      Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P,
    comma_python_chart_fork_a = None,
    comma_python_chart_cycle = Some
      (comma_python_chart_cycle_for_entry f offset),
    comma_python_chart_terminal = None,
    comma_python_chart_literal_increment = 0\<rparr>"
  have step:
    "comma_python_scalar_chart_step residue (Comma_Entry f delta offset) =
      Some ?move"
    using residue leading offset
    by (simp add: comma_python_scalar_chart_step_def
        comma_python_chart_position_admitted_def
        comma_python_chart_cycle_for_entry_def
        comma_python_cycle_displacement_eq_finite_period
        comma_finite_guard_extra_def Let_def)
  have weighted:
    "comma_weighted_step residue (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta ?h)
        (Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P)"
    using leading offset98 period
    by (simp add: comma_weighted_step_def Let_def)
  show ?thesis
    using step weighted
    by (intro exI[of _ ?move])
      (simp add: comma_python_chart_move_erasure_def
        comma_python_chart_move_matches_weighted_def
        comma_python_chart_cycle_for_entry_def
        comma_python_cycle_displacement_eq_finite_period
        comma_finite_guard_extra_def)
qed

lemma comma_python_scalar_chart_step_refines_near:
  assumes residue: "residue < 924"
    and leading: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> headroom" "headroom \<le> 540"
  shows "\<exists>move.
    comma_python_scalar_chart_step residue (Comma_Near f delta headroom) =
      Some move \<and>
    comma_python_chart_move_erasure (Comma_Near f delta headroom) move =
      comma_finite_step residue (Comma_Near f delta headroom) \<and>
    comma_python_chart_move_matches_weighted
      (Comma_Near f delta headroom) move
      (comma_weighted_step residue (Comma_Near f delta headroom))"
  using residue leading headroom
  unfolding comma_python_scalar_chart_step_def
    comma_python_chart_position_admitted_def
    comma_python_chart_move_erasure_def
    comma_python_chart_move_matches_weighted_def
  by (auto simp: comma_finite_step_def comma_weighted_step_def
      comma_python_unit_chart_weight_def comma_python_zero_chart_weight_def
      comma_python_chart_cycle_for_entry_def
      comma_python_chart_expected_literal_increment_def
      comma_python_cycle_displacement_eq_finite_period
      comma_finite_guard_extra_def
      comma_near_control_formula Let_def split: if_splits)

lemma comma_python_scalar_chart_step_refines:
  assumes residue: "residue < 924"
    and admitted: "comma_python_chart_position_admitted position"
  shows "\<exists>move.
    comma_python_scalar_chart_step residue position = Some move \<and>
    comma_python_chart_move_erasure position move =
      comma_finite_step residue position \<and>
    comma_python_chart_move_matches_weighted position move
      (comma_weighted_step residue position)"
proof (cases position)
  case (Comma_Entry f delta offset)
  have admitted_fields: "1 \<le> f" "f \<le> 9" "offset \<le> 89 + f"
    using admitted by (simp_all add: Comma_Entry
      comma_python_chart_position_admitted_def)
  show ?thesis
    using comma_python_scalar_chart_step_refines_entry
      [OF residue admitted_fields(1,2,3)] Comma_Entry by simp
next
  case (Comma_Near f delta headroom)
  have admitted_fields: "1 \<le> f" "f \<le> 9"
    "1 \<le> headroom" "headroom \<le> 540"
    using admitted by (simp_all add: Comma_Near
      comma_python_chart_position_admitted_def)
  show ?thesis
    using comma_python_scalar_chart_step_refines_near
      [OF residue admitted_fields(1,2,3,4)] Comma_Near by simp
qed

lemma comma_python_chart_position_admitted_iff_canonical:
  "comma_python_chart_position_admitted position =
    comma_canonical_position_admitted position"
  by (cases position)
    (simp_all add: comma_python_chart_position_admitted_def
      comma_canonical_position_admitted_def comma_sector_entry_bound_def)

lemma comma_python_scalar_chart_step_preserves_admission:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and admitted: "comma_python_chart_position_admitted source"
    and step: "comma_python_scalar_chart_step (p mod 924) source = Some move"
    and next: "comma_python_chart_next move = Some successor"
  shows "comma_python_chart_position_admitted successor"
proof -
  have residue: "p mod 924 < 924" by simp
  obtain checked where checked_step:
      "comma_python_scalar_chart_step (p mod 924) source = Some checked"
    and checked_erasure:
      "comma_python_chart_move_erasure source checked =
        comma_finite_step (p mod 924) source"
    and checked_fields:
      "comma_python_chart_move_matches_weighted source checked
        (comma_weighted_step (p mod 924) source)"
    using comma_python_scalar_chart_step_refines[OF residue admitted]
    by blast
  have same: "checked = move" using checked_step step by simp
  have finite_next:
      "comma_finite_step (p mod 924) source = Comma_Next successor"
    using checked_erasure next same
    by (simp add: comma_python_chart_move_erasure_def)
  show ?thesis
  proof (cases source)
    case (Comma_Entry f delta offset)
    have f: "1 \<le> f" "f \<le> 9"
      and bound: "offset \<le> 89 + f"
      using admitted by (simp_all add: Comma_Entry
        comma_python_chart_position_admitted_def)
    have offset98: "offset \<le> 98" using f bound by arith
    have headroom:
      "1 \<le> comma_finite_headroom f (p mod 924) delta offset"
      "comma_finite_headroom f (p mod 924) delta offset \<le> 540"
      using comma_finite_entry_headroom_admitted
        [OF f(1) f(2) exponent offset98, of delta] by simp_all
    have target:
      "successor = Comma_Near f delta
        (comma_finite_headroom f (p mod 924) delta offset)"
      using finite_next f bound
      by (simp add: Comma_Entry comma_finite_step_def
          comma_weighted_step_def Let_def
          comma_python_finite_period_positive)
    show ?thesis using target f headroom
      by (simp add: Comma_Entry comma_python_chart_position_admitted_def)
  next
    case (Comma_Near f delta headroom)
    have f: "1 \<le> f" "f \<le> 9"
      and h: "1 \<le> headroom" "headroom \<le> 540"
      using admitted by (simp_all add: Comma_Near
        comma_python_chart_position_admitted_def)
    have canonical: "comma_canonical_position_admitted successor"
      by (rule comma_near_next_canonical[OF f h])
        (use finite_next in \<open>simp only: Comma_Near\<close>)
    show ?thesis
      using canonical by (simp only:
        comma_python_chart_position_admitted_iff_canonical)
  qed
qed

inductive comma_python_scalar_chart_walk ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_chart_move list \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  fork: "comma_weighted_step (p mod 924) source =
      Comma_WFork source a delta \<Longrightarrow>
    comma_python_scalar_chart_step (p mod 924) source = Some move \<Longrightarrow>
    comma_python_chart_move_erasure source move =
      comma_finite_step (p mod 924) source \<Longrightarrow>
    comma_python_chart_move_matches_weighted source move
      (Comma_WFork source a delta) \<Longrightarrow>
    comma_python_scalar_chart_walk p source [move]
      (Comma_Fork_At a delta) source"
| landmine: "comma_weighted_step (p mod 924) source =
      Comma_WLandmine source delta \<Longrightarrow>
    comma_python_scalar_chart_step (p mod 924) source = Some move \<Longrightarrow>
    comma_python_chart_move_erasure source move =
      comma_finite_step (p mod 924) source \<Longrightarrow>
    comma_python_chart_move_matches_weighted source move
      (Comma_WLandmine source delta) \<Longrightarrow>
    comma_python_scalar_chart_walk p source [move]
      (Comma_Landmine_At delta) source"
| advance: "comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight \<Longrightarrow>
    comma_python_scalar_chart_step (p mod 924) source = Some move \<Longrightarrow>
    comma_python_chart_move_erasure source move =
      comma_finite_step (p mod 924) source \<Longrightarrow>
    comma_python_chart_move_matches_weighted source move
      (Comma_WNext successor weight) \<Longrightarrow>
    comma_python_scalar_chart_walk p successor moves outcome terminal \<Longrightarrow>
    comma_python_scalar_chart_walk p source (move # moves) outcome terminal"

lemma comma_python_first_terminal_walk_to_scalar_chart_walk:
  fixes p :: nat
  assumes walk:
    "comma_python_first_terminal_walk p source events outcome terminal"
  shows "5 \<le> p \<longrightarrow>
    comma_python_chart_position_admitted source \<longrightarrow>
    (\<exists>moves. comma_python_scalar_chart_walk p source moves
      outcome terminal)"
  using walk
proof (induction rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  show ?case
  proof (intro impI)
    assume exponent: "5 \<le> p"
    assume admitted: "comma_python_chart_position_admitted source"
    have residue: "p mod 924 < 924" by simp
    obtain move where step:
        "comma_python_scalar_chart_step (p mod 924) source = Some move"
      and erased:
        "comma_python_chart_move_erasure source move =
          comma_finite_step (p mod 924) source"
      and fields:
        "comma_python_chart_move_matches_weighted source move
          (comma_weighted_step (p mod 924) source)"
      using comma_python_scalar_chart_step_refines[OF residue admitted]
      by blast
    have exact_fields: "comma_python_chart_move_matches_weighted source move
        (Comma_WFork source a delta)"
      using fields fork.hyps(1) by simp
    show "\<exists>moves. comma_python_scalar_chart_walk p source moves
        (Comma_Fork_At a delta) source"
      by (intro exI[of _ "[move]"] comma_python_scalar_chart_walk.fork
          fork.hyps(1) step erased exact_fields)
  qed
next
  case (landmine p source delta)
  show ?case
  proof (intro impI)
    assume exponent: "5 \<le> p"
    assume admitted: "comma_python_chart_position_admitted source"
    have residue: "p mod 924 < 924" by simp
    obtain move where step:
        "comma_python_scalar_chart_step (p mod 924) source = Some move"
      and erased:
        "comma_python_chart_move_erasure source move =
          comma_finite_step (p mod 924) source"
      and fields:
        "comma_python_chart_move_matches_weighted source move
          (comma_weighted_step (p mod 924) source)"
      using comma_python_scalar_chart_step_refines[OF residue admitted]
      by blast
    have exact_fields: "comma_python_chart_move_matches_weighted source move
        (Comma_WLandmine source delta)"
      using fields landmine.hyps(1) by simp
    show "\<exists>moves. comma_python_scalar_chart_walk p source moves
        (Comma_Landmine_At delta) source"
      by (intro exI[of _ "[move]"] comma_python_scalar_chart_walk.landmine
          landmine.hyps(1) step erased exact_fields)
  qed
next
  case (advance p source successor weight events outcome terminal)
  show ?case
  proof (intro impI)
    assume exponent: "5 \<le> p"
    assume admitted: "comma_python_chart_position_admitted source"
    have residue: "p mod 924 < 924" by simp
    obtain move where step:
        "comma_python_scalar_chart_step (p mod 924) source = Some move"
      and erased:
        "comma_python_chart_move_erasure source move =
          comma_finite_step (p mod 924) source"
      and fields:
        "comma_python_chart_move_matches_weighted source move
          (comma_weighted_step (p mod 924) source)"
      using comma_python_scalar_chart_step_refines[OF residue admitted]
      by blast
    have exact_fields:
      "comma_python_chart_move_matches_weighted source move
        (Comma_WNext successor weight)"
      using fields advance.hyps(1) by simp
    have next: "comma_python_chart_next move = Some successor"
      using exact_fields by (simp add: comma_python_chart_move_matches_weighted_def)
    have successor_admitted: "comma_python_chart_position_admitted successor"
      by (rule comma_python_scalar_chart_step_preserves_admission
        [OF exponent admitted step next])
    obtain tail_moves where tail:
        "comma_python_scalar_chart_walk p successor tail_moves outcome terminal"
      using advance.IH[OF exponent successor_admitted] .
    show "\<exists>moves. comma_python_scalar_chart_walk p source moves
        outcome terminal"
      by (intro exI[of _ "move # tail_moves"]
          comma_python_scalar_chart_walk.advance
          advance.hyps(1) step erased exact_fields tail)
  qed
qed

theorem comma_python_decade_summary_scalar_chart_walk:
  fixes p :: nat
  assumes summary: "comma_decade_exact_summary s h terminal"
    and admitted: "comma_decade_admitted s"
    and exponent: "5 \<le> p"
    and binding: "s = Comma_Decade (p mod 924) x"
  shows "\<exists>moves final_position.
    comma_python_scalar_chart_walk p (Comma_Entry 1 0 x) moves
      (comma_summary_outcome h terminal)
      (comma_shift_position h final_position)"
proof -
  obtain events final_position where first_terminal:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using comma_decade_summary_python_first_terminal_walk
      [OF summary admitted exponent binding] by blast
  have x_bound: "x \<le> 90" using admitted binding by simp
  have root_admitted:
      "comma_python_chart_position_admitted (Comma_Entry 1 0 x)"
    using x_bound by (simp add: comma_python_chart_position_admitted_def)
  obtain moves where scalar_walk:
      "comma_python_scalar_chart_walk p (Comma_Entry 1 0 x) moves
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using comma_python_first_terminal_walk_to_scalar_chart_walk
      [OF first_terminal] exponent root_admitted by blast
  show ?thesis using scalar_walk by blast
qed

lemma comma_python_chart_initial_position_refines:
  shows "(if near then Comma_Near (a - 1) 0 1 else Comma_Entry a 0 0) =
    (if near then comma_finite_initial (Comma_N,a,phase)
     else comma_finite_initial (Comma_Z,a,phase))"
  by (cases near) (simp_all add: comma_finite_initial_def)

lemma comma_python_chart_initial_position_admitted:
  assumes lower: "2 \<le> a" and upper: "a \<le> 9"
  shows "comma_python_chart_position_admitted
    (if near then Comma_Near (a - 1) 0 1 else Comma_Entry a 0 0)"
  using lower upper
  by (cases near)
    (simp_all add: comma_python_chart_position_admitted_def; arith)

lemmas comma_python_chart_refinement_oracle_audit_bundle =
  comma_python_cycle_displacement_eq_finite_period
  comma_python_chart_cycle_guard_exact
  comma_python_scalar_chart_step_refines_entry
  comma_python_scalar_chart_step_refines_near
  comma_python_scalar_chart_step_refines
  comma_python_scalar_chart_step_preserves_admission
  comma_python_first_terminal_walk_to_scalar_chart_walk
  comma_python_decade_summary_scalar_chart_walk
  comma_python_chart_initial_position_refines
  comma_python_chart_initial_position_admitted

ML \<open>
val endpoints = @{thms comma_python_chart_refinement_oracle_audit_bundle}
val _ = Thm.consolidate endpoints
val _ = if null (Thm_Deps.all_oracles endpoints) then ()
  else error "Comma_Python_Chart_Refinement local oracle audit failed"
\<close>

end
