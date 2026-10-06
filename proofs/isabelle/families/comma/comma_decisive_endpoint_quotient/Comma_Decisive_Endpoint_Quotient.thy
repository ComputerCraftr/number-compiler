theory Comma_Decisive_Endpoint_Quotient
  imports Comma_Sparse_Core.Comma_Orbit_Words
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
    Comma_AddSub_Entry_Core_Bridge.Comma_AddSub_Entry_Core_Bridge
    Comma_Cyclotomic_Clock.Comma_Cyclotomic_Clock
begin

text \<open>
The B1 source action is evaluated by one Entry-to-Near pullback, the closed
Near germ, and a finite endpoint transition.  The recursive result contains
no fuel, prefix weight, endpoint history, or phase table.  Its recursive
calls move strictly to a later decimal sector.
\<close>

lemma comma_fast_sector_target_is_control:
  assumes admitted: "comma_round_admitted source"
  obtains n where
    "comma_sector_control r source=(n,comma_fast_sector_target r source)"
proof -
  obtain n t where sector: "comma_sector_control r source=(n,t)"
    by (cases "comma_sector_control r source") auto
  have fast: "comma_fast_sector r source=(n,t)"
    using comma_fast_sector_refines[OF admitted, of r] sector by simp
  have source_target: "comma_fast_sector_target r source=t"
    using comma_fast_sector_target_correct[of r source] fast by simp
  show thesis using that[of n] sector source_target by simp
qed

definition comma_decisive_entry_clock_key ::
    "comma_cyclotomic_clock \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_decisive_entry_clock_key C f x =
    (let P=comma_finite_period_fast f (x mod 10);
         c=comma_core_modulus P;
         t=comma_cyclotomic_phase C (comma_core_period c) 919
     in (x mod 10,
       comma_entry_diagonal P x
         (comma_core_primary P *
           ((comma_core_seed P * comma_recursive_core_residue c t) mod c))))"

lemma comma_decisive_entry_clock_key_refines_core:
  assumes sector: "1\<le>f" "f\<le>9"
    and source_bound: "x\<le>98"
    and clock: "C=comma_cyclotomic_clock_of ((r+delta) mod 924)"
  shows "comma_decisive_entry_clock_key C f x =
    comma_addsub_entry_core_key (comma_c1_phase_of f x) r delta"
proof -
  have x_bound: "x<100" using source_bound by arith
  let ?P = "comma_finite_period_fast f (x mod 10)"
  let ?c = "comma_core_modulus ?P"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have core_residue:
    "comma_recursive_core_power_residue ?P ((r+delta) mod 924) =
      comma_core_primary ?P *
        ((comma_core_seed ?P * comma_recursive_core_residue ?c
          (comma_cyclotomic_phase C (comma_core_period ?c) 919)) mod ?c)"
    using comma_cyclotomic_clock_core_residue[OF catalog,
      of "(r+delta) mod 924"] clock by (simp add: Let_def)
  show ?thesis using core_residue x_bound
    by (simp add: comma_decisive_entry_clock_key_def
      comma_addsub_entry_core_key_def comma_c1_phase_of_def
      comma_c1_decode_residue Let_def)
qed

theorem comma_decisive_entry_core_clock_refines:
  assumes sector: "1\<le>f" "f\<le>9"
    and source_bound: "x\<le>98"
  shows "\<exists>d eta active residual h.
    comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x = (d,eta) \<and>
    comma_entry_port_refined_locator f d eta=Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  let ?C = "comma_c1_phase_of f x"
  have phase_admitted: "comma_c1_phase_admitted ?C"
    by (rule comma_c1_phase_of_admitted[OF sector])
  have x_bound: "x<100" using source_bound by arith
  have decoded:
    "comma_c1_decode (c1_mod4 ?C) (c1_mod25 ?C)=x"
    using x_bound by (simp add: comma_c1_phase_of_def comma_c1_decode_residue)
  have offset: "comma_c1_decode (c1_mod4 ?C) (c1_mod25 ?C)\<le>98"
    using decoded source_bound by simp
  have bridge_source:
    "\<exists>d eta active residual h.
      comma_addsub_entry_core_key ?C r delta=(d,eta) \<and>
      comma_entry_port_refined_locator f d eta=Some (active,residual,h) \<and>
      1\<le>active \<and> active\<le>9 \<and>
      residual<comma_port_dwell f active \<and>
      comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
    using comma_addsub_entry_core_locator_refines[OF phase_admitted] offset
    by (simp add: comma_c1_phase_of_def comma_c1_decode_residue x_bound)
  obtain d eta active residual h where bridge:
    "comma_addsub_entry_core_key ?C r delta=(d,eta) \<and>
     comma_entry_port_refined_locator f d eta=Some (active,residual,h) \<and>
     1\<le>active \<and> active\<le>9 \<and>
     residual<comma_port_dwell f active \<and>
     comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
    using bridge_source by blast
  have clock_key:
    "comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x =
      comma_addsub_entry_core_key ?C r delta"
    by (rule comma_decisive_entry_clock_key_refines_core[OF sector source_bound refl])
  have clock_result:
    "comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x=(d,eta)"
    using bridge clock_key by simp
  show ?thesis
    by (intro exI[of _ d] exI[of _ eta] exI[of _ active]
      exI[of _ residual] exI[of _ h])
      (use bridge clock_result in simp)
qed

text \<open>The executable endpoint constructor owns the Entry phase by the
external cyclotomic clock and recursive carry core.  It applies the checked
weighted locator once to obtain the active Near residual.  Near states use
the closed local germ directly.  The legacy fast target occurs only in the
refinement theorem below; it is not evaluated by this constructor.\<close>

fun comma_decisive_sector_target ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position" where
  "comma_decisive_sector_target r (Comma_Entry f delta x) =
    (let key=comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x
     in case comma_entry_port_refined_locator f (fst key) (snd key) of
       Some (_,_,h) \<Rightarrow> Comma_Near f delta h
     | None \<Rightarrow> Comma_Entry f delta x)"
| "comma_decisive_sector_target r (Comma_Near f delta h) =
    Comma_Near f delta (snd (comma_near_closed_germ f h))"

lemma comma_decisive_sector_target_refines_fast:
  assumes admitted: "comma_round_admitted source"
  shows "comma_decisive_sector_target r source=comma_fast_sector_target r source"
proof (cases source)
  case (Comma_Entry f delta x)
  have sector: "1\<le>f" "f\<le>9" and bound: "x\<le>98"
    using admitted by (simp_all add: Comma_Entry)
  obtain d eta active residual h where key:
    "comma_decisive_entry_clock_key
       (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x=(d,eta)"
    and locator: "comma_entry_port_refined_locator f d eta=Some (active,residual,h)"
    and target: "comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
    using comma_decisive_entry_core_clock_refines[OF sector bound] by blast
  have direct: "comma_decisive_sector_target r (Comma_Entry f delta x)=
      Comma_Near f delta h"
    using key locator
    by (simp add: comma_decisive_sector_target.simps Let_def key locator)
  show ?thesis using direct target
    by (simp only: Comma_Entry direct target)
next
  case (Comma_Near f delta h)
  have valid: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
    using admitted by (simp_all add: Comma_Near)
  show ?thesis using valid
    by (simp only: Comma_Near comma_decisive_sector_target.simps
      comma_fast_sector_target.simps)
qed

text \<open>On admitted Entry inputs the checked recursive core key is also
the exact diagonal key.  This endpoint projection avoids evaluating the full
weighted locator tuple when the B1 consumer needs only the Near headroom.  The
public constructor remains total; its unadmitted branch is not changed by this
refinement theorem.\<close>

theorem comma_decisive_entry_target_diagonal:
  assumes admitted: "comma_round_admitted (Comma_Entry f delta x)"
  shows "comma_decisive_sector_target r (Comma_Entry f delta x) =
    Comma_Near f delta
      (comma_entry_diagonal_endpoint f
        (comma_finite_period_fast f (x mod 10))
        (fst (comma_decisive_entry_clock_key
          (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x))
        (snd (comma_decisive_entry_clock_key
          (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x)))"
proof -
  have sector: "1\<le>f" "f\<le>9"
    and source_bound: "x\<le>98"
    using admitted by (simp_all add: comma_round_admitted.simps)
  have source_lt_100: "x<100"
    using source_bound by arith
  let ?C = "comma_cyclotomic_clock_of ((r+delta) mod 924)"
  let ?key = "comma_decisive_entry_clock_key ?C f x"
  have phase_admitted: "comma_c1_phase_admitted (comma_c1_phase_of f x)"
    by (rule comma_c1_phase_of_admitted[OF sector])
  have key_core:
    "?key = comma_addsub_entry_core_key (comma_c1_phase_of f x) r delta"
    by (rule comma_decisive_entry_clock_key_refines_core[OF sector source_bound refl])
  have key_diagonal:
    "comma_addsub_entry_core_key (comma_c1_phase_of f x) r delta =
      comma_entry_diagonal_key f r delta x"
  proof -
    have decoded:
      "comma_c1_decode
        (c1_mod4 (comma_c1_phase_of f x))
        (c1_mod25 (comma_c1_phase_of f x)) = x"
      using source_lt_100
      by (simp add: comma_c1_phase_of_def comma_c1_decode_residue)
    show ?thesis
      using comma_addsub_entry_core_key_refines[OF phase_admitted, of r delta]
        decoded
      by (simp add: comma_c1_phase_of_def comma_c1_decode_residue)
  qed
  have clock_diagonal: "?key = comma_entry_diagonal_key f r delta x"
    by (rule trans[OF key_core key_diagonal])
  have diagonal_fst:
    "fst (comma_entry_diagonal_key f r delta x)=x mod 10"
    by (simp add: comma_entry_diagonal_key_def)
  have clock_fst: "fst ?key=x mod 10"
    using clock_diagonal diagonal_fst by simp
  have fast_direct:
    "comma_fast_sector_target r (Comma_Entry f delta x) =
      Comma_Near f delta
        (comma_entry_diagonal_endpoint f
          (comma_finite_period_fast f (x mod 10))
          (fst ?key) (snd ?key))"
  proof -
    have direct:
      "comma_fast_sector_target r (Comma_Entry f delta x) =
        (let (d,eta)=comma_entry_diagonal_key f r delta x in
          Comma_Near f delta (comma_entry_diagonal_endpoint f
            (comma_finite_period_fast f d) d eta))"
      by (rule comma_entry_diagonal_refines[OF sector source_bound])
    have projected:
      "(let (d,eta)=comma_entry_diagonal_key f r delta x in
        Comma_Near f delta (comma_entry_diagonal_endpoint f
          (comma_finite_period_fast f d) d eta)) =
       Comma_Near f delta (comma_entry_diagonal_endpoint f
          (comma_finite_period_fast f (x mod 10)) (fst ?key) (snd ?key))"
      using clock_diagonal clock_fst
      by (simp only: Let_def case_prod_beta
        clock_diagonal[symmetric] clock_fst)
    show ?thesis by (rule trans[OF direct projected])
  qed
  show ?thesis
    using comma_decisive_sector_target_refines_fast[OF admitted] fast_direct
    by simp
qed

definition comma_decisive_sector_period :: "comma_finite_position \<Rightarrow> nat" where
  "comma_decisive_sector_period source = (case source of
    Comma_Entry f _ x \<Rightarrow>
      comma_core_period (comma_core_modulus (comma_finite_period_fast f (x mod 10)))
  | Comma_Near _ _ _ \<Rightarrow> 1)"

lemma comma_decisive_entry_clock_key_period:
  assumes sector: "1\<le>f" "f\<le>9"
    and period: "T=comma_core_period
      (comma_core_modulus (comma_finite_period_fast f (x mod 10)))"
    and same: "r mod T=s mod T"
  shows "comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x =
    comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((s+delta) mod 924)) f x"
proof -
  let ?P = "comma_finite_period_fast f (x mod 10)"
  let ?c = "comma_core_modulus ?P"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have lift: "comma_core_lift_admitted ?P"
    by (rule comma_core_lift_catalog[OF catalog])
  have divides: "T dvd 924"
    using lift period by (auto simp: comma_core_lift_admitted_def Let_def)
  have period_values: "T\<in>{1,2,3,6,22,28}"
    using period by (auto simp: comma_core_period_def)
  have reduced: "((r+delta) mod 924) mod T = ((s+delta) mod 924) mod T"
  proof -
    have left: "((r+delta) mod 924) mod T=(r+delta) mod T"
      by (rule mod_mod_cancel[OF divides])
    have right: "((s+delta) mod 924) mod T=(s+delta) mod T"
      by (rule mod_mod_cancel[OF divides])
    have same_shift:
      "(r mod T + delta) mod T=(s mod T + delta) mod T"
      using same by simp
    have shifted: "(r+delta) mod T=(s+delta) mod T"
    proof -
      have left: "(r+delta) mod T=(r mod T+delta) mod T"
        by (rule mod_add_left_eq[symmetric])
      have right: "(s+delta) mod T=(s mod T+delta) mod T"
        by (rule mod_add_left_eq[symmetric])
      show ?thesis by (simp only: left right same_shift)
    qed
    show ?thesis by (simp only: left right shifted)
  qed
  have phase:
    "comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((r+delta) mod 924)) T 919 =
      comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((s+delta) mod 924)) T 919"
  proof -
    have left:
      "comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((r+delta) mod 924)) T 919 =
       (((r+delta) mod 924 + 919) mod T)"
      by (rule comma_cyclotomic_clock_projection[OF period_values])
    have right:
      "comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((s+delta) mod 924)) T 919 =
       (((s+delta) mod 924 + 919) mod T)"
      by (rule comma_cyclotomic_clock_projection[OF period_values])
    have same_phase:
      "((((r+delta) mod 924) mod T + 919) mod T) =
       ((((s+delta) mod 924) mod T + 919) mod T)"
      using reduced by simp
    have left_reduce:
      "(((r+delta) mod 924 + 919) mod T) =
       ((((r+delta) mod 924) mod T + 919) mod T)"
      by (rule mod_add_left_eq[symmetric])
    have right_reduce:
      "(((s+delta) mod 924 + 919) mod T) =
       ((((s+delta) mod 924) mod T + 919) mod T)"
      by (rule mod_add_left_eq[symmetric])
    show ?thesis by (simp only: left right left_reduce right_reduce same_phase)
  qed
  have actual_phase:
    "comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((r+delta) mod 924))
        (comma_core_period ?c) 919 =
      comma_cyclotomic_phase
        (comma_cyclotomic_clock_of ((s+delta) mod 924))
        (comma_core_period ?c) 919"
    using phase period by simp
  show ?thesis
    by (simp only: comma_decisive_entry_clock_key_def Let_def actual_phase)
qed

theorem comma_decisive_sector_target_period:
  assumes admitted: "comma_round_admitted source"
    and same: "r mod comma_decisive_sector_period source =
      s mod comma_decisive_sector_period source"
  shows "comma_decisive_sector_target r source=
    comma_decisive_sector_target s source"
proof (cases source)
  case (Comma_Entry f delta x)
  have sector: "1\<le>f" "f\<le>9" and bound: "x\<le>98"
    using admitted by (simp_all add: Comma_Entry)
  let ?T = "comma_core_period
      (comma_core_modulus (comma_finite_period_fast f (x mod 10)))"
  have key:
    "comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((r+delta) mod 924)) f x =
     comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of ((s+delta) mod 924)) f x"
    by (rule comma_decisive_entry_clock_key_period[OF sector refl])
      (use same in \<open>simp add: comma_decisive_sector_period_def Comma_Entry\<close>)
  show ?thesis using key
    by (simp only: Comma_Entry comma_decisive_sector_target.simps Let_def key)
next
  case (Comma_Near f delta h)
  show ?thesis by (simp only: Comma_Near comma_decisive_sector_target.simps)
qed

lemma comma_decisive_sector_target_near:
  assumes admitted: "comma_round_admitted source"
  obtains f delta h where
    "comma_decisive_sector_target r source=Comma_Near f delta h"
proof -
  have fast_near: "\<exists>f delta h.
      comma_fast_sector_target r source=Comma_Near f delta h"
    using admitted
    by (cases source)
      (auto simp: comma_fast_sector_target.simps split: comma_finite_move.splits)
  then obtain f delta h where
    fast: "comma_fast_sector_target r source=Comma_Near f delta h"
    by blast
  have direct:
    "comma_decisive_sector_target r source=comma_fast_sector_target r source"
    by (rule comma_decisive_sector_target_refines_fast[OF admitted])
  show thesis using that[of f delta h] direct fast by simp
qed

definition comma_decisive_endpoint_packet ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position \<times> comma_finite_move" where
  "comma_decisive_endpoint_packet r source =
    (let target=comma_decisive_sector_target r source
     in (target, comma_fast_step (r mod 924) target))"

theorem comma_decisive_endpoint_packet_period:
  assumes admitted: "comma_round_admitted source"
    and same: "r mod comma_decisive_sector_period source =
      s mod comma_decisive_sector_period source"
  shows "comma_decisive_endpoint_packet r source=
    comma_decisive_endpoint_packet s source"
proof -
  have target:
    "comma_decisive_sector_target r source=
      comma_decisive_sector_target s source"
    by (rule comma_decisive_sector_target_period[OF admitted same])
  obtain f delta h where near:
    "comma_decisive_sector_target r source=Comma_Near f delta h"
    by (rule comma_decisive_sector_target_near[OF admitted])
  have near_s:
    "comma_decisive_sector_target s source=Comma_Near f delta h"
    using near target by simp
  have moves:
    "comma_fast_step (r mod 924) (comma_decisive_sector_target r source)=
      comma_fast_step (s mod 924) (comma_decisive_sector_target s source)"
    by (simp only: comma_fast_step.simps(2) near near_s)
  show ?thesis using target moves
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
qed

lemma comma_fast_endpoint_successor_decreases:
  assumes admitted: "comma_round_admitted source"
    and move: "comma_fast_step (r mod 924)
      (comma_fast_sector_target r source)=Comma_Next target"
    and internal: "\<not> comma_round_crossing
      (comma_fast_sector_target r source) target"
  shows "9-comma_sector_number target < 9-comma_sector_number source"
proof -
  obtain n where sector:
    "comma_sector_control r source=(n,comma_fast_sector_target r source)"
    by (rule comma_fast_sector_target_is_control[OF admitted])
  have finite:
    "comma_finite_step (r mod 924) (comma_fast_sector_target r source)=
      Comma_Next target"
    using move by (simp only: comma_fast_step_correct)
  show ?thesis
    by (rule comma_sector_recursion_decreases[OF sector[symmetric] finite internal])
qed

lemma comma_decisive_endpoint_successor_decreases:
  assumes admitted: "comma_round_admitted source"
    and move: "comma_fast_step (r mod 924)
      (comma_decisive_sector_target r source)=Comma_Next target"
    and internal: "\<not> comma_round_crossing
      (comma_decisive_sector_target r source) target"
  shows "9-comma_sector_number target < 9-comma_sector_number source"
proof -
  have target_eq:
    "comma_decisive_sector_target r source=comma_fast_sector_target r source"
    by (rule comma_decisive_sector_target_refines_fast[OF admitted])
  show ?thesis
    by (rule comma_fast_endpoint_successor_decreases[OF admitted])
      (use move internal target_eq in simp_all)
qed

function comma_decisive_endpoint_round ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_round_result" where
  "comma_decisive_endpoint_round r source =
    (if comma_round_admitted source then
      (let t=comma_decisive_sector_target r source in
        case comma_fast_step (r mod 924) t of
          Comma_Next target \<Rightarrow>
            if comma_round_crossing t target then Comma_Round_Cross target
            else comma_decisive_endpoint_round r target
        | Comma_Fork a delta \<Rightarrow> Comma_Round_Fork a delta
        | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
        | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)
    else Comma_Round_Invalid)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(r,source). 9-comma_sector_number source)")
    (auto simp: Let_def intro: comma_decisive_endpoint_successor_decreases)

declare comma_decisive_endpoint_round.simps [simp del]

definition comma_decisive_endpoint_observation ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_round_result" where
  "comma_decisive_endpoint_observation r source =
    (case comma_round_control_germ r source of (_,_,event) \<Rightarrow> event)"

theorem comma_decisive_endpoint_round_refines:
  assumes admitted: "comma_round_admitted source"
  shows "comma_decisive_endpoint_round r source =
    comma_decisive_endpoint_observation r source"
  using admitted
proof (induction r source rule: comma_decisive_endpoint_round.induct)
  case (1 r source)
  note source_admitted = "1.prems"
  note endpoint_induction = "1.IH"
  obtain n t where sector: "comma_sector_control r source=(n,t)"
    by (cases "comma_sector_control r source") auto
  have fast_sector: "comma_fast_sector r source=(n,t)"
    using comma_fast_sector_refines[OF source_admitted, of r] sector by simp
  have source_target: "comma_fast_sector_target r source=t"
    using comma_fast_sector_target_correct[of r source] fast_sector by simp
  have decisive_target: "comma_decisive_sector_target r source=t"
    using comma_decisive_sector_target_refines_fast[OF source_admitted]
      source_target by simp
  have fast_equation:
    "comma_decisive_endpoint_round r source =
      (case comma_finite_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then Comma_Round_Cross target
          else comma_decisive_endpoint_round r target
      | Comma_Fork a delta \<Rightarrow> Comma_Round_Fork a delta
      | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
      | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
    using source_admitted decisive_target
    by (subst comma_decisive_endpoint_round.simps)
      (simp only: if_True Let_def comma_fast_step_correct)
  have slow_equation:
    "comma_round_control_germ r source =
      (case comma_finite_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then (n,t,Comma_Round_Cross target)
          else (let (steps,terminal,event)=comma_round_control_germ r target
            in (n+Suc steps,terminal,event))
      | Comma_Fork a delta \<Rightarrow> (n,t,Comma_Round_Fork a delta)
      | Comma_Landmine delta \<Rightarrow> (n,t,Comma_Round_Landmine delta)
      | Comma_Invalid \<Rightarrow> (n,t,Comma_Round_Invalid))"
    using sector by (subst comma_round_control_germ.simps) (simp only: prod.case)
  show ?case
  proof (cases "comma_finite_step (r mod 924) t")
    case (Comma_Next successor)
    show ?thesis
    proof (cases "comma_round_crossing t successor")
      case True
      then show ?thesis using fast_equation slow_equation Comma_Next
        by (simp add: comma_decisive_endpoint_observation_def)
    next
      case False
      have t_admitted: "comma_round_admitted t"
        by (rule comma_sector_control_admitted[OF source_admitted sector])
      have successor_admitted: "comma_round_admitted successor"
        by (rule comma_round_next_admitted[OF t_admitted Comma_Next])
      have fast_move:
        "comma_fast_step (r mod 924) t=Comma_Next successor"
        using Comma_Next
        by (simp only: comma_fast_step_correct)
      have ih: "comma_decisive_endpoint_round r successor =
          comma_decisive_endpoint_observation r successor"
        using endpoint_induction[OF source_admitted decisive_target[symmetric]
            fast_move False successor_admitted] .
      show ?thesis using fast_equation slow_equation Comma_Next False ih
        by (simp add: comma_decisive_endpoint_observation_def
          split: prod.splits)
    qed
  qed (use fast_equation slow_equation in
    \<open>auto simp: comma_decisive_endpoint_observation_def
      split: comma_finite_move.splits prod.splits\<close>)
qed

corollary comma_decisive_endpoint_round_refines_fast:
  assumes admitted: "comma_round_admitted source"
    and budget: "Suc (9-comma_sector_number source)\<le>fuel"
  shows "comma_decisive_endpoint_round r source = comma_fast_round_aux fuel r source"
proof -
  have observation:
    "comma_decisive_endpoint_round r source =
      (case comma_round_control_germ r source of (_,_,event) \<Rightarrow> event)"
    using comma_decisive_endpoint_round_refines[OF admitted]
    unfolding comma_decisive_endpoint_observation_def .
  have germ: "comma_round_control_germ r source=comma_round_close r source"
    by (rule comma_round_control_germ_refines)
  have fast:
    "comma_fast_round_aux fuel r source=snd (snd (comma_round_close r source))"
    by (rule comma_fast_round_aux_correct[OF admitted budget])
  show ?thesis using observation germ fast
    by (cases "comma_round_close r source")
      (auto simp: comma_decisive_endpoint_observation_def)
qed

text \<open>The existing projection owns output semantics; this theory changes
the constructor path, not the definition of a live result or terminal label.\<close>

definition comma_decisive_B1_source :: "nat \<Rightarrow> nat \<Rightarrow> comma_word_result" where
  "comma_decisive_B1_source r x = comma_sector_base_project
    (comma_decisive_endpoint_round r (Comma_Entry 1 0 x))"

definition comma_decisive_B1 :: "nat \<Rightarrow> nat \<Rightarrow> comma_word_result" where
  "comma_decisive_B1 r i =
    (if r<924 \<and> i<46 then
      comma_decisive_B1_source r (comma_offset_representatives!i)
     else Comma_Word_Invalid)"

lemma comma_decisive_endpoint_result_admitted:
  assumes offset: "x\<le>90"
  shows "comma_sector_base_admitted
    (comma_decisive_endpoint_round r (Comma_Entry 1 0 x))"
proof -
  let ?source = "Comma_Entry 1 0 x"
  have valid: "comma_round_admitted ?source"
    using offset by simp
  have budget: "Suc (9-comma_sector_number ?source)\<le>9" by simp
  have exact: "comma_fast_round_aux 9 r ?source=
      comma_decisive_endpoint_round r ?source"
    using comma_decisive_endpoint_round_refines_fast[OF valid budget] by simp
  show ?thesis
    by (rule comma_sector_base_output_admitted[OF offset exact])
qed

lemma comma_decisive_B1_source_refines_atom:
  assumes phase: "r<924" and offset: "x\<le>90"
  shows "comma_decisive_B1_source r x =
    comma_word_project comma_offset_orbit
      (comma_decade_block_atom (Comma_Decade r x))"
proof -
  have admitted:
    "comma_sector_base_admitted
      (comma_decisive_endpoint_round r (Comma_Entry 1 0 x))"
    by (rule comma_decisive_endpoint_result_admitted[OF offset])
  have exact: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=
      comma_decisive_endpoint_round r (Comma_Entry 1 0 x)"
  proof -
    have source_admitted: "comma_round_admitted (Comma_Entry 1 0 x)"
      using offset by simp
    have budget: "Suc (9-comma_sector_number (Comma_Entry 1 0 x))\<le>9"
      by simp
    have endpoint_eq_fast:
      "comma_decisive_endpoint_round r (Comma_Entry 1 0 x) =
        comma_fast_round_aux 9 r (Comma_Entry 1 0 x)"
      by (rule comma_decisive_endpoint_round_refines_fast
        [OF source_admitted budget])
    show ?thesis using endpoint_eq_fast by simp
  qed
  have projected: "comma_sector_base_project
      (comma_decisive_endpoint_round r (Comma_Entry 1 0 x)) =
      comma_word_project comma_offset_orbit
        (comma_decade_block_atom (Comma_Decade r x))"
    by (rule comma_sector_base_project_refines[OF phase offset exact admitted])
  show ?thesis by (simp only: comma_decisive_B1_source_def projected)
qed

theorem comma_decisive_B1_refines_orbit_word:
  assumes phase: "r<924" and index: "i<46"
  shows "comma_decisive_B1 r i=comma_orbit_word 0 r i"
proof -
  let ?x = "comma_offset_representatives!i"
  have offset: "?x\<le>90" and fiber: "comma_offset_orbit ?x=i"
    using comma_orbit_representative_index[OF index] by auto
  have projected: "comma_decisive_B1_source r ?x =
      comma_word_project comma_offset_orbit
        (comma_decade_block_atom (Comma_Decade r ?x))"
    by (rule comma_decisive_B1_source_refines_atom[OF phase offset])
  show ?thesis using phase index projected fiber
    by (simp add: comma_decisive_B1_def comma_orbit_word_def
      comma_decade_block_power.simps)
qed

lemma comma_decisive_sector_period_admitted_pair:
  assumes admitted: "comma_round_admitted source"
  shows "0<comma_decisive_sector_period source \<and>
    comma_decisive_sector_period source dvd 924"
proof (cases source)
  case (Comma_Entry f delta x)
  have sector: "1\<le>f" "f\<le>9" using admitted by (simp_all add: Comma_Entry)
  let ?P = "comma_finite_period_fast f (x mod 10)"
  let ?C = "comma_core_modulus ?P"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have lift: "comma_core_lift_admitted ?P"
    by (rule comma_core_lift_catalog[OF catalog])
  have core_positive: "0 < comma_core_period (comma_core_modulus ?P)"
    using lift by (auto simp: comma_core_lift_admitted_def Let_def)
  have core_divides: "comma_core_period (comma_core_modulus ?P) dvd 924"
    using lift by (auto simp: comma_core_lift_admitted_def Let_def)
  from core_positive core_divides
  show ?thesis
    by (simp add: Comma_Entry comma_decisive_sector_period_def)
next
  case (Comma_Near f delta h)
  then show ?thesis by (simp add: comma_decisive_sector_period_def)
qed

lemma comma_decisive_sector_period_admitted:
  assumes "comma_round_admitted source"
  shows "0<comma_decisive_sector_period source"
    "comma_decisive_sector_period source dvd 924"
  using comma_decisive_sector_period_admitted_pair[OF assms] by blast+

lemma comma_decisive_packet_target_admitted:
  assumes admitted: "comma_round_admitted source"
  shows "comma_round_admitted (fst (comma_decisive_endpoint_packet r source))"
proof -
  obtain n where control:
    "comma_sector_control r source=(n,comma_fast_sector_target r source)"
    by (rule comma_fast_sector_target_is_control[OF admitted])
  have target_admitted:
    "comma_round_admitted (comma_fast_sector_target r source)"
    by (rule comma_sector_control_admitted[OF admitted control])
  have same:
    "fst (comma_decisive_endpoint_packet r source)=comma_fast_sector_target r source"
    by (simp add: comma_decisive_endpoint_packet_def
      comma_decisive_sector_target_refines_fast[OF admitted] Let_def)
  show ?thesis using target_admitted same by simp
qed

lemma comma_decisive_endpoint_round_packet:
  assumes admitted: "comma_round_admitted source"
  shows "comma_decisive_endpoint_round r source =
    (case comma_decisive_endpoint_packet r source of
       (target,Comma_Next next) \<Rightarrow>
         if comma_round_crossing target next then Comma_Round_Cross next
         else comma_decisive_endpoint_round r next
     | (target,Comma_Fork a delta) \<Rightarrow> Comma_Round_Fork a delta
     | (target,Comma_Landmine delta) \<Rightarrow> Comma_Round_Landmine delta
     | (target,Comma_Invalid) \<Rightarrow> Comma_Round_Invalid)"
  using admitted
  by (subst comma_decisive_endpoint_round.simps)
    (simp add: comma_decisive_endpoint_packet_def Let_def)

ML \<open>
  val endpoint = @{thms comma_fast_sector_target_is_control comma_fast_endpoint_successor_decreases
      comma_decisive_endpoint_round_refines comma_decisive_endpoint_round_refines_fast
      comma_decisive_endpoint_result_admitted comma_decisive_B1_source_refines_atom
      comma_decisive_B1_refines_orbit_word}
  val _ = if null (Thm_Deps.all_oracles endpoint) then ()
    else error "Decisive endpoint quotient depends on an oracle"
  val core_endpoint = @{thms comma_decisive_entry_clock_key_refines_core
    comma_decisive_entry_core_clock_refines comma_decisive_entry_target_diagonal}
  val _ = if null (Thm_Deps.all_oracles core_endpoint) then ()
    else error "Decisive Entry core bridge depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Decisive Entry core/clock endpoint authority"
    ["comma_addsub_entry_core_locator_refines",
      "comma_addsub_entry_core_key_refines",
      "comma_entry_diagonal_refines",
      "comma_recursive_core_power_residue_refines",
      "comma_cyclotomic_clock_core_residue",
      "comma_cyclotomic_clock_projection"] core_endpoint
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Decisive endpoint constructors" endpoint
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Decisive Entry core/clock bridge" core_endpoint
\<close>

ML_file "decisive_endpoint_kernel.ML"

ML \<open>
  val ctxt = @{context}
  val fast_kernel = Comma_Fast_Kernel.make ctxt
  val endpoint_kernel = Comma_Decisive_Endpoint_Kernel.make ctxt
    (#context fast_kernel)
  val nat = HOLogic.mk_number @{typ nat}
  val target = @{term
    "comma_decisive_sector_target :: nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position"}
  val fast_target = @{term
    "comma_fast_sector_target :: nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position"}
  val entry = @{term
    "Comma_Entry :: nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_finite_position"}
  fun source f x = entry $ nat f $ nat 0 $ nat x
  fun request r f x = target $ nat r $ source f x
  fun require_some label value = (case value of
      SOME theorem => theorem
    | NONE => error ("Direct endpoint smoke test did not rewrite " ^ label))
  fun prove_admitted proposition = Goal.prove ctxt [] [] proposition
    (fn _ => simp_tac (ctxt addsimps @{thms comma_round_admitted.simps}) 1)
  fun check_valid (r, f, x) =
    let
      val source_term = source f x
      val request_term = request r f x
      val hits_before = #direct_entry_hits endpoint_kernel ()
      val direct = require_some (Int.toString f ^ "/" ^ Int.toString x)
        (#rewrite endpoint_kernel (Thm.cterm_of ctxt request_term))
      val _ = if Thm.term_of (Thm.lhs_of direct) aconv request_term andalso
          Thm.nprems_of direct = 0 andalso null (Thm.hyps_of direct) then ()
        else error "Direct endpoint smoke theorem is not a closed request equation"
      val refinement = Drule.infer_instantiate ctxt
        [(("r",0), Thm.cterm_of ctxt (nat r)),
         (("source",0), Thm.cterm_of ctxt source_term)]
        @{thm comma_decisive_sector_target_refines_fast}
      val _ = if Thm.nprems_of refinement = 1 then ()
        else error "Fast-target refinement has unexpected premises"
      val admitted = prove_admitted (Thm.term_of (Thm.cprem_of refinement 1))
      val fast_refinement = Thm.implies_elim refinement admitted
      val fast_reflection = fast_refinement RS @{thm eq_reflection}
      val legacy_to_direct = Thm.transitive (Thm.symmetric fast_reflection) direct
      val expected = fast_target $ nat r $ source_term
      val _ = if Thm.term_of (Thm.lhs_of legacy_to_direct) aconv expected andalso
          Thm.nprems_of legacy_to_direct = 0 andalso
          null (Thm.hyps_of legacy_to_direct) then ()
        else error "Direct Entry endpoint disagrees with the checked fast target"
      val hits_after = #direct_entry_hits endpoint_kernel ()
      val _ = if hits_after = hits_before + 1 then ()
        else error "Admitted Entry smoke request did not take exactly one direct projection"
    in () end
  val valid_cases = [(0,1,0), (1,1,98), (923,9,0), (0,9,98)]
  val _ = List.app check_valid valid_cases
  val valid_hits = #direct_entry_hits endpoint_kernel ()
  val _ = if valid_hits = length valid_cases then ()
    else error "Not every admitted Entry smoke request used direct projection"

  val near = @{term
    "Comma_Near :: nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_finite_position"} $
      nat 1 $ nat 0 $ nat 1
  fun near_request r = target $ nat r $ near
  val canonical_request = near_request 0
  val canonical = require_some "canonical Near target"
    (#rewrite endpoint_kernel (Thm.cterm_of ctxt canonical_request))
  val endpoint_hits_before_rebase = #endpoint_hits endpoint_kernel ()
  val period_rebases_before = #target_period_rebases endpoint_kernel ()
  val rebased_request = near_request 1
  val rebased = require_some "period-normalized Near target"
    (#rewrite endpoint_kernel (Thm.cterm_of ctxt rebased_request))
  val _ = if Thm.term_of (Thm.lhs_of rebased) aconv rebased_request andalso
      Thm.term_of (Thm.rhs_of rebased) aconv Thm.term_of (Thm.rhs_of canonical) andalso
      Thm.nprems_of rebased = 0 andalso null (Thm.hyps_of rebased) andalso
      null (Thm.tpairs_of rebased) then ()
    else error "Period-normalized target did not retain its request equation"
  val _ = if #endpoint_hits endpoint_kernel () = endpoint_hits_before_rebase + 1 then ()
    else error "Period-normalized target did not reuse the canonical endpoint memo"
  val _ = if #target_period_rebases endpoint_kernel () = period_rebases_before + 1 then ()
    else error "Near target did not use its checked period equation"

  fun contains name term = Term.exists_subterm
    (fn Const (head, _) => head = name | _ => false) term
  fun check_invalid (f, x) =
    let
      val request_term = request 0 f x
      val request_ct = Thm.cterm_of ctxt request_term
      val hits_before = #direct_entry_hits endpoint_kernel ()
      val probe = #direct_entry_probe endpoint_kernel request_ct
      val _ = if is_none probe then ()
        else error "Unadmitted Entry request matched the direct projection"
      val root = Conv.rewrs_conv
        (map (fn rule => rule RS @{thm eq_reflection})
          @{thms comma_decisive_sector_target.simps}) request_ct
      val fallback = Thm.term_of (Thm.rhs_of root)
      val _ = if Thm.term_of (Thm.lhs_of root) aconv request_term andalso
          Thm.nprems_of root = 0 andalso
          contains @{const_name comma_entry_port_refined_locator} fallback then ()
        else error "Unadmitted Entry did not retain the total locator fallback"
      val after = #direct_entry_hits endpoint_kernel ()
      val _ = if hits_before = after andalso after = valid_hits then ()
        else error "Unadmitted Entry request incremented direct-projection hits"
    in () end
  val _ = List.app check_invalid [(0,0), (10,0), (1,99)]
\<close>
end
