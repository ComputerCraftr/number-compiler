theory Comma_Fast_Control
  imports Comma_Closed_Near.Comma_Closed_Near
begin

text \<open>The totality consumer needs only terminal control. This compiled
projection uses the checked short arithmetic and closed Near run; it never
constructs a weighted record or an occurrence proof for a concrete row.\<close>

fun comma_fast_step :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_move" where
  "comma_fast_step r (Comma_Entry f d x) =
    (if f<1 \<or> 9<f \<or> 98<x then Comma_Invalid
     else Comma_Next (Comma_Near f d (comma_finite_headroom_fast f r d x)))"
| "comma_fast_step r (Comma_Near f delta h) =
    (if f<1 \<or> 9<f \<or> h=0 \<or> 540<h then Comma_Invalid
     else let d=(10-h mod 10) mod 10 in
       if f<9 then let low=10*d+f in
         if low+1<h then Comma_Next (Comma_Near f delta (h-low))
         else if h=low+1 then Comma_Fork (f+1) delta
         else Comma_Next (Comma_Entry (f+1) delta (low+1-h))
       else if 10*d+9<h then Comma_Next (Comma_Near 9 delta (h-(10*d+9)))
         else if h\<le>10*d+1 then Comma_Next (Comma_Entry 1 (Suc delta) (10*d+1-h))
         else Comma_Landmine delta)"

lemma comma_fast_step_correct:
  "comma_fast_step r source = comma_finite_step r source"
proof (cases source)
  case (Comma_Entry f d x)
  show ?thesis
  proof (cases "f<1 \<or> 9<f \<or> 98<x")
    case True
    then show ?thesis
      by (auto simp: Comma_Entry comma_finite_step_def comma_weighted_step_def)
  next
    case False
    then have f: "1\<le>f" "f\<le>9" by auto
    have positive: "comma_finite_period f (x mod 10)\<noteq>0"
      using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] f
      by (auto simp: comma_cycle_displacements_def)
    show ?thesis using False positive comma_finite_headroom_fast_correct[OF f]
      by (simp add: Comma_Entry comma_finite_step_def comma_weighted_step_def Let_def)
  qed
next
  case (Comma_Near f d h)
  then show ?thesis by (simp add: comma_near_control_formula Let_def)
qed

fun comma_fast_sector :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<times> comma_finite_position" where
  "comma_fast_sector r (Comma_Near f d h) =
    (case comma_near_closed_germ f h of (n,t) \<Rightarrow> (n,Comma_Near f d t))"
| "comma_fast_sector r (Comma_Entry f d x) =
    (case comma_fast_step (r mod 924) (Comma_Entry f d x) of
       Comma_Next (Comma_Near g e h) \<Rightarrow>
         (case comma_near_closed_germ g h of (n,t) \<Rightarrow> (Suc n,Comma_Near g e t))
     | _ \<Rightarrow> (0,Comma_Entry f d x))"

text \<open>The control consumer demands only the sector endpoint. This
projection retains the original sector semantics and never changes its arithmetic.\<close>
fun comma_fast_sector_target :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position" where
  "comma_fast_sector_target r (Comma_Near f d h)=
    Comma_Near f d (snd (comma_near_closed_germ f h))"
| "comma_fast_sector_target r (Comma_Entry f d x)=
    (case comma_fast_step (r mod 924) (Comma_Entry f d x) of
       Comma_Next (Comma_Near g e h) \<Rightarrow>
         Comma_Near g e (snd (comma_near_closed_germ g h))
     | _ \<Rightarrow> Comma_Entry f d x)"

lemma comma_fast_sector_target_correct:
  "comma_fast_sector_target r source=snd (comma_fast_sector r source)"
  by (cases source)
    (auto split: comma_finite_move.splits comma_finite_position.splits prod.splits)

lemma comma_fast_sector_refines:
  assumes valid: "comma_round_admitted source"
  shows "comma_fast_sector r source = comma_sector_control r source"
proof (cases source)
  case (Comma_Near f d h)
  have germ: "comma_near_closed_germ f h=comma_near_germ f h"
    using valid by (intro comma_near_closed_germ_correct) (simp_all add: Comma_Near)
  show ?thesis by (simp add: Comma_Near germ comma_sector_control_evaluation)
next
  case (Comma_Entry f d x)
  have f: "1\<le>f" "f\<le>9" and x: "x\<le>98"
    using valid by (simp_all add: Comma_Entry)
  let ?h = "comma_finite_headroom f (r mod 924) d x"
  have positive: "comma_finite_period f (x mod 10)\<noteq>0"
    using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] f
    by (auto simp: comma_cycle_displacements_def)
  have move: "comma_finite_step (r mod 924) (Comma_Entry f d x)=
    Comma_Next (Comma_Near f d ?h)"
    using f x positive by (simp add: comma_finite_step_def comma_weighted_step_def Let_def)
  have near: "comma_round_admitted (Comma_Near f d ?h)"
    by (rule comma_round_next_admitted[OF _ move]) (use valid Comma_Entry in simp)
  have germ: "comma_near_closed_germ f ?h=comma_near_germ f ?h"
    by (rule comma_near_closed_germ_correct) (use near in simp_all)
  show ?thesis
    by (simp only: Comma_Entry comma_fast_sector.simps comma_fast_step_correct move
      comma_finite_move.case comma_finite_position.case germ
      comma_sector_control_evaluation Let_def)
qed

lemma comma_sector_control_admitted:
  assumes valid: "comma_round_admitted source"
    and sector: "comma_sector_control r source=(n,t)"
  shows "comma_round_admitted t"
proof -
  obtain a b entry units where germ: "comma_sector_germ r source=(a,b,entry,units)"
    by (cases "comma_sector_germ r source") auto
  have fields: "a=n" "b=t"
    using sector by (simp_all add: comma_sector_control_def germ)
  have weighted: "comma_round_weighted_prefix 0 r n source t
    (comma_sector_weight 0 entry units)"
    using comma_sector_germ_weighted[OF germ, of 0] fields by simp
  have prefix: "comma_round_prefix_steps n r source t"
    using weighted comma_round_weighted_prefix_erasure[of n r source t 0] by blast
  show ?thesis by (rule comma_round_prefix_admitted[OF prefix valid])
qed

fun comma_fast_round_aux :: "nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_round_result" where
  "comma_fast_round_aux 0 r source=Comma_Round_Invalid"
| "comma_fast_round_aux (Suc fuel) r source=
    (case comma_fast_sector r source of (n,t) \<Rightarrow>
      case comma_fast_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then Comma_Round_Cross target
          else comma_fast_round_aux fuel r target
      | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
      | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
      | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"

lemma comma_fast_round_aux_correct:
  assumes valid: "comma_round_admitted source"
    and enough: "Suc (9-comma_sector_number source)\<le>fuel"
  shows "comma_fast_round_aux fuel r source = snd (snd (comma_round_close r source))"
  using valid enough
proof (induction fuel arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  obtain n t where sector: "comma_sector_control r source=(n,t)"
    by (cases "comma_sector_control r source") auto
  have fast: "comma_fast_sector r source=(n,t)"
    using comma_fast_sector_refines[OF Suc.prems(1), of r] sector by simp
  have admitted: "comma_round_admitted t"
    by (rule comma_sector_control_admitted[OF Suc.prems(1) sector])
  note expand = comma_sector_control_expand[OF sector]
  note terminal = comma_round_close.simps[of r t]
  show ?case
  proof (cases "comma_finite_step (r mod 924) t")
    case (Comma_Next target)
    show ?thesis
    proof (cases "comma_round_crossing t target")
      case True
      show ?thesis using expand terminal
        by (simp only: comma_fast_round_aux.simps fast prod.case
          comma_fast_step_correct Comma_Next comma_finite_move.case True if_True snd_conv)
    next
      case False
      have target: "comma_round_admitted target"
        by (rule comma_round_next_admitted[OF admitted Comma_Next])
      have decrease: "Suc (9-comma_sector_number target)\<le>9-comma_sector_number source"
        by (rule comma_sector_call_budget[OF sector Comma_Next False])
      have enough: "Suc (9-comma_sector_number target)\<le>fuel"
        using decrease Suc.prems(2) by arith
      have ih: "comma_fast_round_aux fuel r target=snd(snd(comma_round_close r target))"
        by (rule Suc.IH[OF target enough])
      obtain k u event where tail: "comma_round_close r target=(k,u,event)"
        by (cases "comma_round_close r target") auto
      show ?thesis using expand terminal
        by (simp only: comma_fast_round_aux.simps fast prod.case comma_fast_step_correct
          Comma_Next comma_finite_move.case False if_False ih tail Let_def snd_conv)
    qed
  qed (use expand terminal fast in
    \<open>auto simp only: comma_fast_round_aux.simps comma_fast_step_correct
      prod.case comma_finite_move.case snd_conv\<close>)
qed

text \<open>Offset belongs to the occurrence, not the local round action.
Normalize it into the phase before evaluation, then restore the exact result.\<close>

lemma comma_fast_entry_round_phase_normalized:
  assumes "1\<le>f" "f\<le>9" "x\<le>98"
  shows "comma_fast_round_aux 9 r (Comma_Entry f d x)=
    comma_shift_round_result d
      (comma_fast_round_aux 9 ((r+d) mod 924) (Comma_Entry f 0 x))"
proof -
  have left: "comma_fast_round_aux 9 r (Comma_Entry f d x)=
      snd (snd (comma_round_close r (Comma_Entry f d x)))"
    by (rule comma_fast_round_aux_correct) (use assms in auto)
  have right: "comma_fast_round_aux 9 ((r+d) mod 924) (Comma_Entry f 0 x)=
      snd (snd (comma_round_close ((r+d) mod 924) (Comma_Entry f 0 x)))"
    by (rule comma_fast_round_aux_correct) (use assms in auto)
  obtain n t result where canonical:
    "comma_round_close ((r+d) mod 924) (Comma_Entry f 0 x)=(n,t,result)"
    by (cases "comma_round_close ((r+d) mod 924) (Comma_Entry f 0 x)") auto
  have transported: "comma_round_close r (Comma_Entry f d x)=
      (n,comma_shift_position d t,comma_shift_round_result d result)"
    using comma_round_close_phase_normalized[of r f d x]
    by (simp only: canonical comma_shift_round_close_def prod.case)
  show ?thesis by (simp only: left right transported canonical snd_conv)
qed

fun comma_fast_decade_control :: "comma_decade_state \<Rightarrow> comma_decade_outcome" where
  "comma_fast_decade_control (Comma_Decade r x)=
    comma_decade_decode r (comma_fast_round_aux 9 r (Comma_Entry 1 0 x))"

theorem comma_fast_decade_control_correct:
  assumes valid: "comma_decade_admitted s"
  shows "comma_fast_decade_control s=comma_decade_control s"
proof (cases s)
  case (Comma_Decade r x)
  have entry: "comma_round_admitted (Comma_Entry 1 0 x)"
    using valid by (simp add: Comma_Decade)
  have result: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=
    snd(snd(comma_round_close r (Comma_Entry 1 0 x)))"
    by (rule comma_fast_round_aux_correct[OF entry]) simp
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  show ?thesis
    by (simp only: Comma_Decade comma_fast_decade_control.simps result
      comma_decade_control.simps close prod.case snd_conv)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_entry_round_phase_normalized comma_fast_step_correct comma_fast_sector_target_correct comma_fast_sector_refines
      comma_fast_round_aux_correct comma_fast_decade_control_correct})
    then () else error "Fast comma control depends on an oracle";
\<close>
end
