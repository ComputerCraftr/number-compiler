theory Comma_Decade_Summary_Transport
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core Comma_Total_Macro.Comma_Total_Macro
begin

fun comma_shift_finite_outcome :: "nat \<Rightarrow> comma_finite_outcome \<Rightarrow> comma_finite_outcome" where
  "comma_shift_finite_outcome k (Comma_Fork_At a d)=Comma_Fork_At a (d+k)"
| "comma_shift_finite_outcome k (Comma_Landmine_At d)=Comma_Landmine_At (d+k)"

lemma comma_finite_run_shift_exact:
  "comma_finite_run fuel (r mod 924) (comma_shift_position k source) =
    map_option (comma_shift_finite_outcome k)
      (comma_finite_run fuel ((r+k) mod 924) source)"
proof (induction fuel arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
    by (simp only: comma_finite_run.simps comma_round_step_shift mod_mod_trivial;
      cases "comma_finite_step ((r+k) mod 924) source";
      simp add: Suc.IH)
qed

fun comma_summary_outcome :: "nat \<Rightarrow> comma_decade_terminal \<Rightarrow> comma_finite_outcome" where
  "comma_summary_outcome n (Comma_Terminal_Fork a)=Comma_Fork_At a n"
| "comma_summary_outcome n Comma_Terminal_Landmine=Comma_Landmine_At n"

lemma comma_summary_outcome_shift:
  "comma_shift_finite_outcome k (comma_summary_outcome n terminal)=
    comma_summary_outcome (n+k) terminal"
  by (cases terminal) simp_all

text \<open>Each continued decade contributes exactly one exponent increment.
The conclusion retains that exact gain; it is stronger than existence of an
unspecified successful evaluator result.\<close>

theorem comma_decade_exact_summary_run:
  assumes summary: "comma_decade_exact_summary s height terminal"
    and valid: "comma_decade_admitted s"
  shows "case s of Comma_Decade r x \<Rightarrow>
    \<exists>fuel. comma_finite_run fuel r (Comma_Entry 1 0 x)=
      Some (comma_summary_outcome height terminal)"
  using summary valid
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  obtain r x where source: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have decode: "comma_decade_decode r event=Comma_Decade_Fork a 0"
    using fork.hyps by (simp only: source comma_decade_control.simps close prod.case)
  have no_cross: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)\<noteq>Comma_Decade_Fork a 0"
    by (case_tac target) simp_all
  have event: "event=Comma_Round_Fork a 0"
    using decode no_cross by (cases event) auto
  have phase: "r mod 924=r" using fork.prems by (simp add: source)
  have terminal: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,Comma_Round_Fork a 0)"
    using close by (simp only: event)
  have run: "comma_finite_run (Suc n) r (Comma_Entry 1 0 x)=Some (Comma_Fork_At a 0)"
    using comma_round_close_fork_finite_run[OF terminal] by (simp only: phase)
  show ?case using run by (auto simp only: source comma_decade_state.case comma_summary_outcome.simps)
next
  case (landmine s)
  obtain r x where source: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have decode: "comma_decade_decode r event=Comma_Decade_Landmine 0"
    using landmine.hyps by (simp only: source comma_decade_control.simps close prod.case)
  have no_cross: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)\<noteq>Comma_Decade_Landmine 0"
    by (case_tac target) simp_all
  have event: "event=Comma_Round_Landmine 0"
    using decode no_cross by (cases event) auto
  have phase: "r mod 924=r" using landmine.prems by (simp add: source)
  have terminal: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,Comma_Round_Landmine 0)"
    using close by (simp only: event)
  have run: "comma_finite_run (Suc n) r (Comma_Entry 1 0 x)=Some (Comma_Landmine_At 0)"
    using comma_round_close_landmine_finite_run[OF terminal] by (simp only: phase)
  show ?case using run by (auto simp only: source comma_decade_state.case comma_summary_outcome.simps)
next
  case (crossing s q height terminal)
  obtain r x where source: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have entry: "comma_round_admitted (Comma_Entry 1 0 x)"
    and phase: "r mod 924=r" using crossing.prems by (simp_all add: source)
  have decode: "comma_decade_decode r event=Comma_Decade_Continue q"
    using crossing.hyps(1) by (simp only: source comma_decade_control.simps close prod.case)
  obtain target where event: "event=Comma_Round_Cross target"
    using decode by (cases event; auto split: comma_finite_position.splits if_splits)
  obtain y where y: "y\<le>90" "target=Comma_Entry 1 1 y"
    using comma_round_close_crossing_phase[of r "Comma_Entry 1 0 x" n t target]
      close event entry by auto
  have q: "q=Comma_Decade ((r+1) mod 924) y"
    using decode by (simp add: event y)
  have q_valid: "comma_decade_admitted q" by (simp add: q y)
  obtain fuel where suffix:
    "comma_finite_run fuel ((r+1) mod 924) (Comma_Entry 1 0 y)=
      Some (comma_summary_outcome height terminal)"
    using crossing.IH[OF q_valid] by (auto simp only: q comma_decade_state.case)
  have shifted: "comma_finite_run fuel (r mod 924) target=
      Some (comma_summary_outcome (Suc height) terminal)"
    using comma_finite_run_shift_exact[of fuel r 1 "Comma_Entry 1 0 y"]
    by (simp only: suffix; simp add: y comma_summary_outcome_shift)
  have terminal: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,Comma_Round_Cross target)"
    using close by (simp only: event)
  have prefix: "comma_round_prefix_steps (Suc n) r (Comma_Entry 1 0 x) target"
    by (rule comma_round_close_cross_prefix[OF terminal])
  have run: "comma_finite_run (Suc n+fuel) r (Comma_Entry 1 0 x)=
      Some (comma_summary_outcome (Suc height) terminal)"
    using comma_round_prefix_finite_run[OF prefix, of fuel] shifted by (simp only: phase)
  show ?case using run by (auto simp only: source comma_decade_state.case)
qed


fun comma_decade_summary_resume ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   nat \<Rightarrow> comma_round_result \<Rightarrow> comma_finite_outcome option" where
  "comma_decade_summary_resume height terminal r (Comma_Round_Fork a d)=Some (Comma_Fork_At a d)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Landmine d)=Some (Comma_Landmine_At d)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Cross (Comma_Entry f d x))=
    (let s=Comma_Decade ((r+d) mod 924) x in
      if f=1 \<and> comma_decade_admitted s then
        Some (comma_summary_outcome (height s+d) (terminal s)) else None)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Cross (Comma_Near f d h))=None"
| "comma_decade_summary_resume height terminal r Comma_Round_Invalid=None"

definition comma_fast_total_boundary ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_fast_total_boundary height terminal q =
    (if comma_boundary_valid q then
      comma_decade_summary_resume height terminal (snd (snd q))
        (comma_fast_round_aux 9 (snd (snd q)) (comma_finite_initial q))
     else None)"

theorem comma_fast_total_boundary_refines:
  assumes checked: "comma_decade_summary_checked height terminal"
    and valid: "comma_boundary_valid q"
  shows "\<exists>fuel outcome. comma_fast_total_boundary height terminal q=Some outcome \<and>
    comma_finite_macro fuel q=Some outcome"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  let ?source = "comma_finite_initial q"
  have admitted: "comma_round_admitted ?source"
    and delta: "comma_round_delta ?source=0"
    and phase: "r mod 924=r"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def comma_finite_initial_def)+
  obtain n t event where close: "comma_round_close r ?source=(n,t,event)"
    by (cases "comma_round_close r ?source") auto
  have budget: "Suc (9-comma_sector_number ?source)\<le>9"
    using admitted by (cases ?source) auto
  have fast: "comma_fast_round_aux 9 r ?source=event"
    using comma_fast_round_aux_correct[OF admitted budget, of r] close by simp
  have phase_key: "snd (snd q)=r" by (simp only: q snd_conv)
  have computed: "comma_fast_total_boundary height terminal q=
    comma_decade_summary_resume height terminal r event"
    by (simp only: comma_fast_total_boundary_def valid if_True phase_key fast)
  have result: "\<exists>fuel outcome. comma_decade_summary_resume height terminal r event=Some outcome \<and>
    comma_finite_run fuel r ?source=Some outcome"
  proof (cases event)
    case (Comma_Round_Fork b d)
    have run: "comma_finite_run (Suc n) r ?source=Some (Comma_Fork_At b d)"
      using comma_round_close_fork_finite_run[of r ?source n t b d] close
      by (simp only: Comma_Round_Fork phase)
    show ?thesis using run by (auto simp only: Comma_Round_Fork comma_decade_summary_resume.simps)
  next
    case (Comma_Round_Landmine d)
    have run: "comma_finite_run (Suc n) r ?source=Some (Comma_Landmine_At d)"
      using comma_round_close_landmine_finite_run[of r ?source n t d] close
      by (simp only: Comma_Round_Landmine phase)
    show ?thesis using run by (auto simp only: Comma_Round_Landmine comma_decade_summary_resume.simps)
  next
    case (Comma_Round_Cross target)
    obtain x where x: "x\<le>90" "target=Comma_Entry 1 1 x"
      using comma_round_close_crossing_phase[of r ?source n t target]
        close Comma_Round_Cross admitted delta by auto
    let ?s = "Comma_Decade ((r+1) mod 924) x"
    have state: "comma_decade_admitted ?s" using x by simp
    have summary: "comma_decade_exact_summary ?s (height ?s) (terminal ?s)"
      by (rule comma_decade_summary_checked_sound[OF checked state])
    obtain fuel where tail: "comma_finite_run fuel ((r+1) mod 924) (Comma_Entry 1 0 x)=
        Some (comma_summary_outcome (height ?s) (terminal ?s))"
      using comma_decade_exact_summary_run[OF summary state] by auto
    have shifted: "comma_finite_run fuel (r mod 924) target=
        Some (comma_summary_outcome (height ?s+1) (terminal ?s))"
      using comma_finite_run_shift_exact[of fuel r 1 "Comma_Entry 1 0 x"]
      by (simp only: tail; simp add: x comma_summary_outcome_shift)
    have prefix: "comma_round_prefix_steps (Suc n) r ?source target"
      by (rule comma_round_close_cross_prefix) (use close Comma_Round_Cross in simp)
    have run: "comma_finite_run (Suc n+fuel) r ?source=
        Some (comma_summary_outcome (height ?s+1) (terminal ?s))"
      using comma_round_prefix_finite_run[OF prefix, of fuel] shifted by (simp only: phase)
    have resume: "comma_decade_summary_resume height terminal r event=
        Some (comma_summary_outcome (height ?s+1) (terminal ?s))"
      using state by (simp only: Comma_Round_Cross x(2) comma_decade_summary_resume.simps Let_def if_True HOL.simp_thms)
    show ?thesis using resume run by blast
  next
    case Comma_Round_Invalid
    then show ?thesis using comma_round_close_admitted(2)[OF close admitted] by simp
  qed
  obtain fuel outcome where result:
    "comma_decade_summary_resume height terminal r event=Some outcome"
    "comma_finite_run fuel r ?source=Some outcome"
    using result by blast
  have macro: "comma_finite_macro fuel q=Some outcome"
    using result(2) valid by (simp add: comma_finite_macro_def q)
  show ?thesis
    apply (rule exI[of _ fuel])
    apply (rule exI[of _ outcome])
    using computed result(1) macro by simp
qed

theorem comma_fast_total_boundary_correct:
  assumes "comma_decade_summary_checked height terminal" "comma_boundary_valid q"
  shows "comma_fast_total_boundary height terminal q=Some (comma_total_macro q)"
  using comma_fast_total_boundary_refines[OF assms] comma_total_macro_agrees by metis

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_run_shift_exact comma_decade_exact_summary_run
      comma_fast_total_boundary_refines comma_fast_total_boundary_correct})
    then () else error "Decade summary transport depends on an oracle";
\<close>
end
