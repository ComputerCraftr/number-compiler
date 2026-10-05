theory Comma_Decade_Residual_Core
  imports Comma_Fast_Control.Comma_Fast_Control
    Comma_Decade_Helix.Comma_Decade_Helix
begin

text \<open>Canonical terminal and residual semantics depend only on the
admitted decade control and helix. A source classifier can establish their
local recurrence directly. Rank and rectangular regression checking are
consumers of this owner, never prerequisites for its definitions or soundness.\<close>

lemma comma_decade_rectangle:
  "list_all (\<lambda>r. list_all (\<lambda>x. P (Comma_Decade r x)) [0..<91]) [0..<924]
    = (\<forall>s. comma_decade_admitted s \<longrightarrow> P s)"
proof
  assume rows: "list_all (\<lambda>r. list_all (\<lambda>x. P (Comma_Decade r x)) [0..<91]) [0..<924]"
  show "\<forall>s. comma_decade_admitted s \<longrightarrow> P s"
  proof (intro allI impI)
    fix s assume "comma_decade_admitted s"
    then show "P s" using rows by (cases s) (auto simp: list_all_iff)
  qed
next
  assume "\<forall>s. comma_decade_admitted s \<longrightarrow> P s"
  then show "list_all (\<lambda>r. list_all (\<lambda>x. P (Comma_Decade r x)) [0..<91]) [0..<924]"
    by (auto simp: list_all_iff)
qed

datatype comma_decade_terminal =
    Comma_Terminal_Fork nat
  | Comma_Terminal_Landmine

fun comma_summary_outcome :: "nat \<Rightarrow> comma_decade_terminal \<Rightarrow> comma_finite_outcome" where
  "comma_summary_outcome n (Comma_Terminal_Fork a)=Comma_Fork_At a n"
| "comma_summary_outcome n Comma_Terminal_Landmine=Comma_Landmine_At n"

definition comma_fast_decade_summary_step ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   comma_decade_state \<Rightarrow> bool" where
  "comma_fast_decade_summary_step height terminal s =
    (case comma_fast_decade_control s of
       Comma_Decade_Continue t \<Rightarrow>
         comma_decade_admitted t \<and> height s = Suc (height t) \<and> terminal s = terminal t
     | Comma_Decade_Fork a d \<Rightarrow>
         d=0 \<and> height s=0 \<and> terminal s=Comma_Terminal_Fork a
     | Comma_Decade_Landmine d \<Rightarrow>
         d=0 \<and> height s=0 \<and> terminal s=Comma_Terminal_Landmine
     | Comma_Decade_Invalid \<Rightarrow> False)"

definition comma_decade_summary_checked ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow> bool" where
  "comma_decade_summary_checked height terminal =
    list_all (\<lambda>r. list_all
      (\<lambda>x. comma_fast_decade_summary_step height terminal (Comma_Decade r x))
      [0..<91]) [0..<924]"

definition comma_fast_decade_summary_range ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_decade_summary_range height terminal lo hi =
    list_all (\<lambda>r. list_all
      (\<lambda>x. comma_fast_decade_summary_step height terminal (Comma_Decade r x))
      [0..<91]) [lo..<hi]"

lemma comma_fast_decade_summary_range_join:
  assumes "lo\<le>mid" "mid\<le>hi"
  shows "comma_fast_decade_summary_range height terminal lo hi =
    (comma_fast_decade_summary_range height terminal lo mid \<and>
     comma_fast_decade_summary_range height terminal mid hi)"
  using assms by (auto simp: comma_fast_decade_summary_range_def list_all_iff)

lemma comma_fast_decade_summary_range_full:
  "comma_fast_decade_summary_range height terminal 0 924=comma_decade_summary_checked height terminal"
  by (simp only: comma_fast_decade_summary_range_def comma_decade_summary_checked_def)

lemma comma_decade_summary_row:
  assumes "comma_decade_summary_checked height terminal" "comma_decade_admitted s"
  shows "comma_fast_decade_summary_step height terminal s"
  using assms unfolding comma_decade_summary_checked_def comma_decade_rectangle by blast

text \<open>Height counts decade crossings. Terminal inspection is a further
round, so the existing finishes relation has count Suc height. The terminal
label contains no phase or literal weight; these must be transported separately.\<close>

inductive comma_decade_exact_summary ::
  "comma_decade_state \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> bool" where
  fork: "comma_decade_control s=Comma_Decade_Fork a 0 \<Longrightarrow>
    comma_decade_exact_summary s 0 (Comma_Terminal_Fork a)"
| landmine: "comma_decade_control s=Comma_Decade_Landmine 0 \<Longrightarrow>
    comma_decade_exact_summary s 0 Comma_Terminal_Landmine"
| crossing: "comma_decade_control s=Comma_Decade_Continue t \<Longrightarrow>
    comma_decade_exact_summary t n terminal \<Longrightarrow>
    comma_decade_exact_summary s (Suc n) terminal"

lemma comma_finite_fork_digit_bounds:
  assumes step: "comma_finite_step r position=Comma_Fork a d"
  shows "2\<le>a \<and> a\<le>9"
  using step
  by (cases position)
    (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)

lemma comma_decade_terminal_fork_bounds:
  assumes summary: "comma_decade_exact_summary s h terminal"
  shows "(case terminal of Comma_Terminal_Fork a \<Rightarrow> 2\<le>a \<and> a\<le>9
    | Comma_Terminal_Landmine \<Rightarrow> True)"
  using summary
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  obtain r x where state: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close:
    "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have decoded:
    "comma_decade_decode r event=Comma_Decade_Fork a 0"
    using fork.hyps by (simp only: state comma_decade_control.simps close prod.case)
  have event: "event=Comma_Round_Fork a 0"
  proof (cases event)
    case (Comma_Round_Fork fork_a fork_delta)
    then show ?thesis using decoded by simp
  next
    case (Comma_Round_Landmine delta)
    then show ?thesis using decoded by simp
  next
    case (Comma_Round_Cross target)
    then show ?thesis using decoded
      by (cases target) (auto simp: comma_decade_decode.simps split: if_splits)
  next
    case Comma_Round_Invalid
    then show ?thesis using decoded by simp
  qed
  have finite:
    "comma_finite_step (r mod 924) t=Comma_Fork a 0"
    using comma_round_close_refines_trace[OF close] event by simp
  have bounds: "2\<le>a \<and> a\<le>9"
    by (rule comma_finite_fork_digit_bounds[OF finite])
  show ?case using bounds by simp
next
  case (landmine s)
  then show ?case by simp
next
  case (crossing s t h terminal)
  then show ?case by simp
qed

text \<open>The induction consumes the local recurrence law directly. A domain
classifier may prove that law symbolically; enumerating the source rectangle
is only one optional way of establishing it. No rank premise is needed.\<close>

theorem comma_decade_summary_recurrence_sound:
  assumes recurrence: "\<And>s. comma_decade_admitted s \<Longrightarrow>
      comma_fast_decade_summary_step height terminal s"
    and valid: "comma_decade_admitted s"
  shows "comma_decade_exact_summary s (height s) (terminal s)"
  using valid
proof (induction "height s" arbitrary: s rule: less_induct)
  case less
  have row: "comma_fast_decade_summary_step height terminal s"
    by (rule recurrence[OF less.prems])
  have control: "comma_fast_decade_control s=comma_decade_control s"
    by (rule comma_fast_decade_control_correct[OF less.prems])
  show ?case
  proof (cases "comma_decade_control s")
    case (Comma_Decade_Continue t)
    have t: "comma_decade_admitted t" "height s=Suc (height t)" "terminal s=terminal t"
      using row by (simp_all add: comma_fast_decade_summary_step_def control Comma_Decade_Continue)
    have decrease: "height t<height s" using t by simp
    have ih: "comma_decade_exact_summary t (height t) (terminal t)"
      by (rule less.hyps[OF decrease t(1)])
    show ?thesis using comma_decade_exact_summary.crossing[OF Comma_Decade_Continue ih] t by simp
  next
    case (Comma_Decade_Fork a d)
    have d: "d=0" and h: "height s=0" and label: "terminal s=Comma_Terminal_Fork a"
      using row by (simp_all add: comma_fast_decade_summary_step_def control Comma_Decade_Fork)
    have actual: "comma_decade_control s=Comma_Decade_Fork a 0"
      using Comma_Decade_Fork d by simp
    have "comma_decade_exact_summary s 0 (Comma_Terminal_Fork a)"
      by (rule comma_decade_exact_summary.fork[OF actual])
    then show ?thesis by (simp only: h label)
  next
    case (Comma_Decade_Landmine d)
    have d: "d=0" and h: "height s=0" and label: "terminal s=Comma_Terminal_Landmine"
      using row by (simp_all add: comma_fast_decade_summary_step_def control Comma_Decade_Landmine)
    have actual: "comma_decade_control s=Comma_Decade_Landmine 0"
      using Comma_Decade_Landmine d by simp
    have "comma_decade_exact_summary s 0 Comma_Terminal_Landmine"
      by (rule comma_decade_exact_summary.landmine[OF actual])
    then show ?thesis by (simp only: h label)
  next
    case Comma_Decade_Invalid
    then show ?thesis using row by (simp add: comma_fast_decade_summary_step_def control)
  qed
qed

theorem comma_decade_summary_checked_sound:
  assumes "comma_decade_summary_checked height terminal" "comma_decade_admitted s"
  shows "comma_decade_exact_summary s (height s) (terminal s)"
  by (rule comma_decade_summary_recurrence_sound[OF _ assms(2)])
    (rule comma_decade_summary_row[OF assms(1)])

lemma comma_decade_exact_summary_finishes:
  "comma_decade_exact_summary s n terminal \<Longrightarrow> comma_decade_finishes s (Suc n)"
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have "comma_decade_finishes s 1"
    by (rule comma_decade_finishes.fork[OF fork.hyps])
  then show ?case by simp
next
  case (landmine s)
  have "comma_decade_finishes s 1"
    by (rule comma_decade_finishes.landmine[OF landmine.hyps])
  then show ?case by simp
next
  case (crossing s t n terminal)
  show ?case
    by (rule comma_decade_finishes.crossing[OF crossing.hyps(1) crossing.IH])
qed

corollary comma_decade_summary_checked_exact_height:
  assumes "comma_decade_summary_checked height terminal" "comma_decade_admitted s"
  shows "comma_decade_finishes s (Suc (height s))"
  by (rule comma_decade_exact_summary_finishes[OF comma_decade_summary_checked_sound[OF assms]])

text \<open>Live states retain the transported occurrence phase. Stops retain
exact crossing count and terminal kind. Invalid admission and nonzero terminal
deltas fail closed; neither is supplied by a candidate rank.\<close>

datatype comma_decade_block_result =
    Comma_Block_Live comma_decade_state
  | Comma_Block_Stop nat comma_decade_terminal
  | Comma_Block_Invalid

fun comma_decade_block_then ::
  "nat \<Rightarrow> comma_decade_block_result \<Rightarrow>
    (comma_decade_state \<Rightarrow> comma_decade_block_result) \<Rightarrow> comma_decade_block_result" where
  "comma_decade_block_then n (Comma_Block_Live s) right =
    (case right s of Comma_Block_Stop h t \<Rightarrow> Comma_Block_Stop (n+h) t | answer \<Rightarrow> answer)"
| "comma_decade_block_then n (Comma_Block_Stop h t) right=Comma_Block_Stop h t"
| "comma_decade_block_then n Comma_Block_Invalid right=Comma_Block_Invalid"

lemma comma_decade_block_then_associative:
  "comma_decade_block_then (n+m) (comma_decade_block_then n left middle) right =
    comma_decade_block_then n left (\<lambda>s. comma_decade_block_then m (middle s) right)"
  by (cases left; auto split: comma_decade_block_result.splits simp: add.assoc)

definition comma_decade_block_atom :: "comma_decade_state \<Rightarrow> comma_decade_block_result" where
  "comma_decade_block_atom s =
    (if comma_decade_admitted s then
      case comma_fast_decade_control s of
        Comma_Decade_Continue t \<Rightarrow>
          if comma_decade_admitted t then Comma_Block_Live t else Comma_Block_Invalid
      | Comma_Decade_Fork a d \<Rightarrow>
          if d=0 then Comma_Block_Stop 0 (Comma_Terminal_Fork a) else Comma_Block_Invalid
      | Comma_Decade_Landmine d \<Rightarrow>
          if d=0 then Comma_Block_Stop 0 Comma_Terminal_Landmine else Comma_Block_Invalid
      | Comma_Decade_Invalid \<Rightarrow> Comma_Block_Invalid
    else Comma_Block_Invalid)"

fun comma_decade_block_run :: "nat \<Rightarrow> comma_decade_state \<Rightarrow> comma_decade_block_result" where
  "comma_decade_block_run 0 s=Comma_Block_Live s"
| "comma_decade_block_run (Suc n) s=
    comma_decade_block_then 1 (comma_decade_block_atom s) (comma_decade_block_run n)"

lemma comma_decade_block_run_add:
  "comma_decade_block_run (n+m) s=
    comma_decade_block_then n (comma_decade_block_run n s) (comma_decade_block_run m)"
proof (induction n arbitrary: s)
  case 0
  then show ?case by (cases "comma_decade_block_run m s") simp_all
next
  case (Suc n)
  have tail: "comma_decade_block_run (n+m) =
    (\<lambda>t. comma_decade_block_then n (comma_decade_block_run n t) (comma_decade_block_run m))"
    by (rule ext; rule Suc.IH)
  have "comma_decade_block_run (Suc n+m) s =
    comma_decade_block_then 1 (comma_decade_block_atom s)
      (\<lambda>t. comma_decade_block_then n (comma_decade_block_run n t) (comma_decade_block_run m))"
    by (simp only: add_Suc comma_decade_block_run.simps tail)
  also have "... = comma_decade_block_then (1+n)
      (comma_decade_block_then 1 (comma_decade_block_atom s) (comma_decade_block_run n))
      (comma_decade_block_run m)"
    by (rule comma_decade_block_then_associative[symmetric])
  also have "... = comma_decade_block_then (Suc n)
      (comma_decade_block_run (Suc n) s) (comma_decade_block_run m)"
    by simp
  finally show ?case .
qed

fun comma_decade_block_power :: "nat \<Rightarrow> comma_decade_state \<Rightarrow> comma_decade_block_result" where
  "comma_decade_block_power 0 s=comma_decade_block_atom s"
| "comma_decade_block_power (Suc k) s=
    comma_decade_block_then (2^k) (comma_decade_block_power k s) (comma_decade_block_power k)"

lemma comma_decade_block_atom_run:
  "comma_decade_block_run 1 s=comma_decade_block_atom s"
  by (cases "comma_decade_block_atom s") simp_all

theorem comma_decade_block_square_refines:
  "comma_decade_block_power k s=comma_decade_block_run (2^k) s"
proof (induction k arbitrary: s)
  case 0
  show ?case by (simp only: comma_decade_block_power.simps power_0 comma_decade_block_atom_run)
next
  case (Suc k)
  have powered_functions: "comma_decade_block_power k=comma_decade_block_run (2^k)"
    by (rule ext; rule Suc.IH)
  show ?case
    by (simp only: comma_decade_block_power.simps powered_functions power_Suc
      mult_2 comma_decade_block_run_add)
qed

lemma comma_decade_block_atom_live:
  assumes "comma_decade_block_atom s=Comma_Block_Live t"
  shows "comma_decade_admitted s" "comma_decade_admitted t"
    "comma_decade_control s=Comma_Decade_Continue t"
  using assms comma_fast_decade_control_correct
  by (auto simp: comma_decade_block_atom_def split: if_splits comma_decade_outcome.splits)

lemma comma_decade_block_atom_stop:
  assumes "comma_decade_block_atom s=Comma_Block_Stop h terminal"
  shows "h=0" "comma_decade_admitted s" "comma_decade_exact_summary s 0 terminal"
  using assms comma_fast_decade_control_correct
  by (auto simp: comma_decade_block_atom_def
    split: if_splits comma_decade_outcome.splits intro: comma_decade_exact_summary.intros)

lemma comma_decade_block_run_stop:
  assumes "comma_decade_block_run n s=Comma_Block_Stop h terminal"
  shows "h<n \<and> comma_decade_exact_summary s h terminal"
  using assms
proof (induction n arbitrary: s h terminal)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "comma_decade_block_atom s")
    case (Comma_Block_Live t)
    obtain j where tail: "comma_decade_block_run n t=Comma_Block_Stop j terminal"
      and h: "h=Suc j"
      using Suc.prems by (auto simp: Comma_Block_Live split: comma_decade_block_result.splits)
    have ih: "j<n" "comma_decade_exact_summary t j terminal"
      using Suc.IH[OF tail] by auto
    have move: "comma_decade_control s=Comma_Decade_Continue t"
      by (rule comma_decade_block_atom_live(3)[OF Comma_Block_Live])
    have "comma_decade_exact_summary s (Suc j) terminal"
      by (rule comma_decade_exact_summary.crossing[OF move ih(2)])
    then show ?thesis using ih(1) h by simp
  next
    case (Comma_Block_Stop j kind)
    have h: "h=j" and label: "terminal=kind"
      using Suc.prems by (simp_all add: Comma_Block_Stop)
    have "j=0" "comma_decade_exact_summary s 0 kind"
      using comma_decade_block_atom_stop[OF Comma_Block_Stop] by auto
    then show ?thesis by (simp add: h label)
  next
    case Comma_Block_Invalid
    then show ?thesis using Suc.prems by simp
  qed
qed

theorem comma_decade_block_power_stop:
  assumes "comma_decade_block_power k s=Comma_Block_Stop h terminal"
  shows "h<2^k" "comma_decade_exact_summary s h terminal"
    "comma_decade_finishes s (Suc h)"
  using comma_decade_block_run_stop[of "2^k" s h terminal] assms
    comma_decade_exact_summary_finishes
  by (auto simp only: comma_decade_block_square_refines)

corollary comma_decade_block_B5_totality:
  assumes complete: "\<And>s. comma_decade_admitted s \<Longrightarrow>
    \<exists>h terminal. comma_decade_block_power 5 s=Comma_Block_Stop h terminal \<and> h\<le>26"
    and valid: "comma_decade_admitted s"
  shows "\<exists>n\<le>27. comma_decade_finishes s n"
proof -
  obtain h terminal where stop: "comma_decade_block_power 5 s=Comma_Block_Stop h terminal"
    and bound: "h\<le>26" using complete[OF valid] by blast
  have "comma_decade_finishes s (Suc h)" by (rule comma_decade_block_power_stop(3)[OF stop])
  then show ?thesis using bound by (intro exI[of _ "Suc h"]) simp
qed


lemma comma_decade_block_run_live_helix:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
    and live: "comma_decade_block_run n (Comma_Decade r x)=Comma_Block_Live (Comma_Decade r' x')"
  shows "r'=(r+n) mod 924 \<and> x'\<le>90"
  using valid live
proof (induction n arbitrary: r x r' x')
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain t where atom: "comma_decade_block_atom (Comma_Decade r x)=Comma_Block_Live t"
    and tail: "comma_decade_block_run n t=Comma_Block_Live (Comma_Decade r' x')"
    using Suc.prems(2)
    by (cases "comma_decade_block_atom (Comma_Decade r x)";
      auto split: comma_decade_block_result.splits)
  obtain a b where t: "t=Comma_Decade a b" by (cases t) auto
  have admitted: "comma_decade_admitted (Comma_Decade a b)"
    using comma_decade_block_atom_live(2)[OF atom] by (simp only: t)
  have move: "comma_decade_control (Comma_Decade r x)=Comma_Decade_Continue (Comma_Decade a b)"
    using comma_decade_block_atom_live(3)[OF atom] by (simp only: t)
  have a: "a=(r+1) mod 924" by (rule comma_decade_continue_helix(1)[OF Suc.prems(1) move])
  have ih: "r'=(a+n) mod 924 \<and> x'\<le>90"
    by (rule Suc.IH[OF admitted]) (use tail in \<open>simp only: t\<close>)
  show ?case using ih a by (simp add: mod_add_left_eq add.assoc)
qed

lemma comma_decade_block_power_live_helix:
  assumes "comma_decade_admitted (Comma_Decade r x)"
    "comma_decade_block_power k (Comma_Decade r x)=Comma_Block_Live (Comma_Decade r' x')"
  shows "r'=(r+2^k) mod 924 \<and> x'\<le>90"
  by (rule comma_decade_block_run_live_helix[OF assms(1)])
    (use assms(2) in \<open>simp only: comma_decade_block_square_refines\<close>)

text \<open>The existing exact-summary relation is already the temporal
residual R(height,terminal). A pair exposes that same object; no second
source classifier or eager temporal word is introduced. The terminal type
remains the existing type, and admission of its concrete channels is a
separate source-classification obligation.\<close>

type_synonym comma_decade_residual = "nat \<times> comma_decade_terminal"

datatype comma_residual_block_result =
    Comma_Residual_Live comma_decade_residual
  | Comma_Residual_Stop nat comma_decade_terminal

fun comma_residual_block :: "nat \<Rightarrow> comma_decade_residual \<Rightarrow> comma_residual_block_result" where
  "comma_residual_block D (h,tau)=
    (if h<D then Comma_Residual_Stop h tau else Comma_Residual_Live (h-D,tau))"

abbreviation comma_residual_step :: "comma_decade_residual \<Rightarrow> comma_residual_block_result" where
  "comma_residual_step R \<equiv> comma_residual_block 1 R"

lemma comma_residual_step_terminal [simp]:
  "comma_residual_step (0,tau)=Comma_Residual_Stop 0 tau"
  by simp

lemma comma_residual_step_continue [simp]:
  "comma_residual_step (Suc h,tau)=Comma_Residual_Live (h,tau)"
  by simp

fun comma_residual_then ::
  "nat \<Rightarrow> comma_residual_block_result \<Rightarrow>
    (comma_decade_residual \<Rightarrow> comma_residual_block_result) \<Rightarrow>
    comma_residual_block_result" where
  "comma_residual_then D (Comma_Residual_Live R) right=
    (case right R of Comma_Residual_Stop h tau \<Rightarrow> Comma_Residual_Stop (D+h) tau
     | Comma_Residual_Live S \<Rightarrow> Comma_Residual_Live S)"
| "comma_residual_then D (Comma_Residual_Stop h tau) right=Comma_Residual_Stop h tau"

lemma comma_residual_block_add:
  "comma_residual_block (D+E) R=
    comma_residual_then D (comma_residual_block D R) (comma_residual_block E)"
  by (cases R; auto split: if_splits; presburger)

corollary comma_residual_block_square:
  "comma_residual_block (2*D) R=
    comma_residual_then D (comma_residual_block D R) (comma_residual_block D)"
  by (simp only: mult_2 comma_residual_block_add)

corollary comma_residual_B32_totality:
  assumes "h\<le>26"
  shows "comma_residual_block 32 (h,tau)=Comma_Residual_Stop h tau"
  using assms by (auto; arith)

text \<open>Actual source runs reach exactly the stop of their summary as
soon as the block exceeds its height. This theorem evaluates no trajectory
and uses no finite enumeration as a premise.\<close>

lemma comma_decade_exact_summary_block_stop:
  assumes summary: "comma_decade_exact_summary s h tau"
    and valid: "comma_decade_admitted s" and width: "h<D"
  shows "comma_decade_block_run D s=Comma_Block_Stop h tau"
  using summary valid width
proof (induction arbitrary: D rule: comma_decade_exact_summary.induct)
  case (fork s a)
  obtain n where D: "D=Suc n" using fork.prems(2) by (cases D) auto
  have atom: "comma_decade_block_atom s=Comma_Block_Stop 0 (Comma_Terminal_Fork a)"
    using fork.hyps fork.prems(1) comma_fast_decade_control_correct[OF fork.prems(1)]
    by (simp add: comma_decade_block_atom_def)
  show ?case by (simp add: D atom)
next
  case (landmine s)
  obtain n where D: "D=Suc n" using landmine.prems(2) by (cases D) auto
  have atom: "comma_decade_block_atom s=Comma_Block_Stop 0 Comma_Terminal_Landmine"
    using landmine.hyps landmine.prems(1)
      comma_fast_decade_control_correct[OF landmine.prems(1)]
    by (simp add: comma_decade_block_atom_def)
  show ?case by (simp add: D atom)
next
  case (crossing s t h tau)
  obtain n where D: "D=Suc n" using crossing.prems(2) by (cases D) auto
  have admitted: "comma_decade_admitted t"
    by (rule comma_decade_control_closed(2)[OF crossing.prems(1) crossing.hyps(1) refl])
  have atom: "comma_decade_block_atom s=Comma_Block_Live t"
    using crossing.hyps(1) crossing.prems(1) admitted
      comma_fast_decade_control_correct[OF crossing.prems(1)]
    by (simp add: comma_decade_block_atom_def)
  have tail: "comma_decade_block_run n t=Comma_Block_Stop h tau"
    by (rule crossing.IH[OF admitted]) (use crossing.prems(2) D in simp)
  show ?case by (simp add: D atom tail)
qed


lemma comma_decade_exact_summary_block_live:
  assumes summary: "comma_decade_exact_summary s h tau"
    and valid: "comma_decade_admitted s" and width: "D\<le>h"
  shows "\<exists>t. comma_decade_block_run D s=Comma_Block_Live t \<and>
    comma_decade_admitted t \<and> comma_decade_exact_summary t (h-D) tau"
  using summary valid width
proof (induction arbitrary: D rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have "D=0" using fork.prems(2) by simp
  then show ?case using fork.prems(1) comma_decade_exact_summary.fork[OF fork.hyps] by auto
next
  case (landmine s)
  have "D=0" using landmine.prems(2) by simp
  then show ?case using landmine.prems(1)
    comma_decade_exact_summary.landmine[OF landmine.hyps] by auto
next
  case (crossing s t h tau)
  show ?case
  proof (cases D)
    case 0
    have "comma_decade_exact_summary s (Suc h) tau"
      by (rule comma_decade_exact_summary.crossing[OF crossing.hyps])
    then show ?thesis using crossing.prems(1) by (auto simp: 0)
  next
    case (Suc n)
    have admitted: "comma_decade_admitted t"
      by (rule comma_decade_control_closed(2)[OF crossing.prems(1) crossing.hyps(1) refl])
    have atom: "comma_decade_block_atom s=Comma_Block_Live t"
      using crossing.hyps(1) crossing.prems(1) admitted
        comma_fast_decade_control_correct[OF crossing.prems(1)]
      by (simp add: comma_decade_block_atom_def)
    obtain q where live: "comma_decade_block_run n t=Comma_Block_Live q"
      and q: "comma_decade_admitted q" "comma_decade_exact_summary q (h-n) tau"
      using crossing.IH[OF admitted] crossing.prems(2) Suc by auto
    show ?thesis using live q by (auto simp: Suc atom)
  qed
qed

theorem comma_decade_exact_summary_block:
  assumes "comma_decade_exact_summary s h tau" "comma_decade_admitted s"
  shows "if h<D then comma_decade_block_run D s=Comma_Block_Stop h tau
    else \<exists>t. comma_decade_block_run D s=Comma_Block_Live t \<and>
      comma_decade_admitted t \<and> comma_decade_exact_summary t (h-D) tau"
  using comma_decade_exact_summary_block_stop[OF assms]
    comma_decade_exact_summary_block_live[OF assms] by auto

text \<open>A candidate classifier is checked through the existing one-step
summary law, not through a rank table or an assumed stopping run. Admission,
terminal kind, zero terminal delta and successor height are all checked by
that law. This interface does not supply the missing compact candidate or a
proof that its source domains satisfy the law.\<close>

definition comma_decade_residual_classifier_ok ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual) \<Rightarrow> bool" where
  "comma_decade_residual_classifier_ok C =
    (\<forall>s. comma_decade_admitted s \<longrightarrow>
      comma_fast_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s)"

theorem comma_residual_classifier_sound:
  assumes classifier: "comma_decade_residual_classifier_ok C"
    and valid: "comma_decade_admitted s" and label: "C s=(h,tau)"
  shows "comma_decade_exact_summary s h tau"
proof -
  have summary: "comma_decade_exact_summary s (fst (C s)) (snd (C s))"
    by (rule comma_decade_summary_recurrence_sound[OF _ valid])
      (use classifier in \<open>auto simp: comma_decade_residual_classifier_ok_def\<close>)
  show ?thesis using summary by (simp only: label fst_conv snd_conv)
qed

corollary comma_residual_classifier_B32:
  assumes "comma_decade_residual_classifier_ok C" "comma_decade_admitted s"
    "C s=(h,tau)" "h\<le>26"
  shows "comma_decade_block_power 5 s=Comma_Block_Stop h tau"
proof -
  have summary: "comma_decade_exact_summary s h tau"
    by (rule comma_residual_classifier_sound[OF assms(1-3)])
  have "comma_decade_block_run 32 s=Comma_Block_Stop h tau"
    by (rule comma_decade_exact_summary_block_stop[OF summary assms(2)])
      (use assms(4) in arith)
  then show ?thesis by (simp add: comma_decade_block_square_refines)
qed

lemma comma_decade_finishes_exact_summary:
  assumes finish: "comma_decade_finishes s n" and valid: "comma_decade_admitted s"
  shows "\<exists>h tau. n=Suc h \<and> comma_decade_exact_summary s h tau"
  using finish valid
proof (induction rule: comma_decade_finishes.induct)
  case (fork s a d)
  have delta: "d=0"
    using comma_decade_terminal_delta(1) fork.hyps fork.prems by (cases s) blast
  have "comma_decade_exact_summary s 0 (Comma_Terminal_Fork a)"
    by (rule comma_decade_exact_summary.fork) (use fork.hyps delta in simp)
  then show ?case by auto
next
  case (landmine s d)
  have delta: "d=0"
    using comma_decade_terminal_delta(2) landmine.hyps landmine.prems by (cases s) blast
  have "comma_decade_exact_summary s 0 Comma_Terminal_Landmine"
    by (rule comma_decade_exact_summary.landmine) (use landmine.hyps delta in simp)
  then show ?case by auto
next
  case (crossing s t n)
  have admitted: "comma_decade_admitted t"
    by (rule comma_decade_control_closed(2)[OF crossing.prems crossing.hyps(1) refl])
  obtain h tau where count: "n=Suc h" and summary: "comma_decade_exact_summary t h tau"
    using crossing.IH[OF admitted] by blast
  have "comma_decade_exact_summary s (Suc h) tau"
    by (rule comma_decade_exact_summary.crossing[OF crossing.hyps(1) summary])
  then show ?case using count by auto
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_rectangle comma_decade_summary_recurrence_sound
      comma_decade_summary_checked_sound comma_decade_summary_checked_exact_height
      comma_decade_block_then_associative comma_decade_block_run_add
      comma_decade_block_square_refines comma_decade_block_power_stop
      comma_decade_block_B5_totality comma_decade_block_power_live_helix
      comma_residual_block_add comma_residual_block_square comma_residual_B32_totality
      comma_decade_exact_summary_block_stop comma_decade_exact_summary_block_live
      comma_decade_exact_summary_block comma_decade_finishes_exact_summary
      comma_residual_classifier_sound comma_residual_classifier_B32})
    then () else error "Rank-free decade residual core depends on an oracle";
\<close>
end
