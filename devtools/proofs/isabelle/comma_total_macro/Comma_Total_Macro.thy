theory Comma_Total_Macro
  imports Comma_Decade_Totality.Comma_Decade_Control
begin

declare comma_round_close.simps [simp del]
declare comma_weighted_step_def [simp del]

text \<open>Successful bounded evaluators are stable refinement witnesses.
No numerical fuel constant owns the semantic macro. Until a concrete decade
rank is checked, successful-domain assumptions remain explicit.\<close>

lemma comma_finite_run_success_unique:
  assumes left: "comma_finite_run f r source=Some x"
    and right: "comma_finite_run g r source=Some y"
  shows "x=y"
proof -
  have A: "comma_finite_run (f+g) r source=Some x"
    by (rule comma_finite_run_more[OF left])
  have B: "comma_finite_run (g+f) r source=Some y"
    by (rule comma_finite_run_more[OF right])
  show ?thesis using A B by (simp add: add.commute)
qed


lemma comma_finite_macro_success_unique:
  assumes "comma_finite_macro f q=Some x" "comma_finite_macro g q=Some y"
  shows "x=y"
proof -
  have left: "comma_finite_run f (snd (snd q)) (comma_finite_initial q)=Some x"
    and right: "comma_finite_run g (snd (snd q)) (comma_finite_initial q)=Some y"
    using assms by (cases q; auto simp: comma_finite_macro_def split: if_splits)+
  show ?thesis by (rule comma_finite_run_success_unique[OF left right])
qed


lemma comma_finite_weighted_run_more:
  assumes "comma_finite_weighted_run fuel p source=Some result"
  shows "comma_finite_weighted_run (fuel+extra) p source=Some result"
  using assms
proof (induction fuel arbitrary: source result)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "comma_weighted_step (p mod 924) source")
    case (Comma_WNext target weight)
    show ?thesis using Suc.prems Suc.IH[of target]
      by (cases "comma_finite_weighted_run fuel p target")
        (auto simp: Comma_WNext del: comma_weighted_step_def split: prod.splits)
  qed (use Suc.prems in \<open>auto simp del: comma_weighted_step_def\<close>)
qed


lemma comma_finite_weighted_run_success_unique:
  assumes left: "comma_finite_weighted_run f p source=Some x"
    and right: "comma_finite_weighted_run g p source=Some y"
  shows "x=y"
proof -
  have A: "comma_finite_weighted_run (f+g) p source=Some x"
    by (rule comma_finite_weighted_run_more[OF left])
  have B: "comma_finite_weighted_run (g+f) p source=Some y"
    by (rule comma_finite_weighted_run_more[OF right])
  show ?thesis using A B by (simp add: add.commute)
qed


lemma comma_finite_weighted_macro_more:
  assumes macro: "comma_finite_weighted_macro fuel p q=Some result"
  shows "comma_finite_weighted_macro (fuel+extra) p q=Some result"
proof -
  have admitted: "\<not>(p<5 \<or> \<not>comma_boundary_valid q \<or> p mod 924\<noteq>snd (snd q))"
    and run: "comma_finite_weighted_run fuel p (comma_finite_initial q)=Some result"
    using macro by (auto simp: comma_finite_weighted_macro_def split: if_splits)
  show ?thesis using comma_finite_weighted_run_more[OF run] admitted
    by (simp only: comma_finite_weighted_macro_def if_False)
qed


lemma comma_finite_weighted_macro_success_unique:
  assumes left: "comma_finite_weighted_macro f p q=Some x"
    and right: "comma_finite_weighted_macro g p q=Some y"
  shows "x=y"
proof -
  have A: "comma_finite_weighted_macro (f+g) p q=Some x"
    by (rule comma_finite_weighted_macro_more[OF left])
  have B: "comma_finite_weighted_macro (g+f) p q=Some y"
    by (rule comma_finite_weighted_macro_more[OF right])
  show ?thesis using A B by (simp add: add.commute)
qed


definition comma_macro_defined :: "comma_boundary_state \<Rightarrow> bool" where
  "comma_macro_defined q = (\<exists>fuel outcome. comma_finite_macro fuel q=Some outcome)"

definition comma_weighted_macro_defined :: "nat \<Rightarrow> comma_boundary_state \<Rightarrow> bool" where
  "comma_weighted_macro_defined p q =
    (\<exists>fuel result. comma_finite_weighted_macro fuel p q=Some result)"

definition comma_total_macro :: "comma_boundary_state \<Rightarrow> comma_finite_outcome" where
  "comma_total_macro q = (THE outcome. \<exists>fuel. comma_finite_macro fuel q=Some outcome)"

definition comma_total_weighted_macro ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    comma_finite_outcome \<times> nat \<times> comma_finite_position" where
  "comma_total_weighted_macro p q =
    (THE result. \<exists>fuel. comma_finite_weighted_macro fuel p q=Some result)"

lemma comma_total_macro_agrees:
  assumes run: "comma_finite_macro fuel q=Some outcome"
  shows "comma_total_macro q=outcome"
  unfolding comma_total_macro_def
  by (rule the_equality) (use run comma_finite_macro_success_unique in blast)+

lemma comma_total_weighted_macro_agrees:
  assumes run: "comma_finite_weighted_macro fuel p q=Some result"
  shows "comma_total_weighted_macro p q=result"
  unfolding comma_total_weighted_macro_def
  by (rule the_equality) (use run comma_finite_weighted_macro_success_unique in blast)+

lemma comma_total_macro_correct:
  assumes "comma_macro_defined q"
  shows "\<exists>fuel. comma_finite_macro fuel q=Some (comma_total_macro q)"
  using assms comma_total_macro_agrees unfolding comma_macro_defined_def by metis

lemma comma_total_weighted_macro_correct:
  assumes "comma_weighted_macro_defined p q"
  shows "\<exists>fuel. comma_finite_weighted_macro fuel p q=
    Some (comma_total_weighted_macro p q)"
  using assms comma_total_weighted_macro_agrees
  unfolding comma_weighted_macro_defined_def by metis

lemma comma_macro_defined_weighted:
  assumes defined: "comma_macro_defined q"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "comma_weighted_macro_defined p q"
proof -
  obtain fuel outcome where run: "comma_finite_macro fuel q=Some outcome"
    using defined unfolding comma_macro_defined_def by blast
  have erased: "map_option fst (comma_finite_weighted_macro fuel p q)=Some outcome"
    using comma_finite_weighted_macro_erasure[OF exponent phase] run by simp
  show ?thesis using erased unfolding comma_weighted_macro_defined_def
    by (cases "comma_finite_weighted_macro fuel p q") auto
qed

lemma comma_total_weighted_macro_erasure:
  assumes defined: "comma_macro_defined q"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "fst (comma_total_weighted_macro p q)=comma_total_macro q"
proof -
  obtain fuel where run: "comma_finite_weighted_macro fuel p q=
    Some (comma_total_weighted_macro p q)"
    using comma_total_weighted_macro_correct
      [OF comma_macro_defined_weighted[OF assms]] by blast
  have control: "comma_finite_macro fuel q=
    Some (fst (comma_total_weighted_macro p q))"
    using comma_finite_weighted_macro_erasure[OF exponent phase, of fuel] run by simp
  show ?thesis using comma_total_macro_agrees[OF control] by simp
qed

definition comma_total_children :: "comma_boundary_state \<Rightarrow> comma_boundary_state list" where
  "comma_total_children q =
    (case comma_total_macro q of
       Comma_Landmine_At d \<Rightarrow> []
     | Comma_Fork_At a d \<Rightarrow>
       [(Comma_N,a,(snd (snd q)+d) mod 924),
        (Comma_Z,a,(snd (snd q)+d) mod 924)])"

lemma comma_total_children_agree:
  assumes run: "comma_finite_macro fuel q=Some outcome"
  shows "comma_finite_children fuel q=Some (comma_total_children q)"
  using comma_total_macro_agrees[OF run] run
  by (cases q; cases outcome)
    (simp_all add: comma_finite_children_def comma_total_children_def)

lemma comma_finite_run_shift_exists:
  assumes run: "comma_finite_run fuel ((r+k) mod 924) source=Some outcome"
  shows "\<exists>shifted. comma_finite_run fuel (r mod 924)
    (comma_shift_position k source)=Some shifted"
  using run
proof (induction fuel arbitrary: source outcome)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "comma_finite_step ((r+k) mod 924) source")
    case (Comma_Next target)
    have tail: "comma_finite_run fuel ((r+k) mod 924) target=Some outcome"
      using Suc.prems by (simp only: comma_finite_run.simps Comma_Next comma_finite_move.case)
    obtain shifted where shifted:
      "comma_finite_run fuel (r mod 924) (comma_shift_position k target)=Some shifted"
      using Suc.IH[OF tail] by blast
    show ?thesis
      using comma_round_step_shift[of r k source] shifted
      by (simp add: Comma_Next)
  qed (use Suc.prems comma_round_step_shift[of r k source] in
    \<open>auto simp del: comma_weighted_step_def\<close>)
qed

lemma comma_round_success_from_cross:
  assumes close: "comma_round_close r source=(n,t,event)"
    and valid_event: "event\<noteq>Comma_Round_Invalid"
    and crossing: "\<And>target. event=Comma_Round_Cross target \<Longrightarrow>
      \<exists>fuel outcome. comma_finite_run fuel (r mod 924) target=Some outcome"
  shows "\<exists>fuel outcome. comma_finite_run fuel (r mod 924) source=Some outcome"
proof (cases event)
  case (Comma_Round_Fork a d)
  show ?thesis using comma_round_close_fork_finite_run close Comma_Round_Fork by blast
next
  case (Comma_Round_Landmine d)
  show ?thesis using comma_round_close_landmine_finite_run close Comma_Round_Landmine by blast
next
  case (Comma_Round_Cross target)
  have prefix: "comma_round_prefix_steps (Suc n) r source target"
    using comma_round_close_cross_prefix close Comma_Round_Cross by blast
  obtain fuel outcome where tail: "comma_finite_run fuel (r mod 924) target=Some outcome"
    using crossing[OF Comma_Round_Cross] by blast
  have "comma_finite_run (Suc n+fuel) (r mod 924) source=Some outcome"
    using comma_round_prefix_finite_run[OF prefix, of fuel] tail by simp
  then show ?thesis by blast
next
  case Comma_Round_Invalid
  then show ?thesis using valid_event by blast
qed

lemma comma_decade_finishes_run_exists:
  assumes finish: "comma_decade_finishes s rounds" and valid: "comma_decade_admitted s"
  shows "case s of Comma_Decade r x \<Rightarrow>
    \<exists>fuel outcome. comma_finite_run fuel r (Comma_Entry 1 0 x)=Some outcome"
  using finish valid
proof (induction rule: comma_decade_finishes.induct)
  case (fork s a d)
  obtain r x where source: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have decode: "comma_decade_decode r event=Comma_Decade_Fork a d"
    using fork.hyps by (simp only: source comma_decade_control.simps close prod.case)
  have no_cross: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)\<noteq>Comma_Decade_Fork a d"
    by (case_tac target) simp_all
  have event: "event=Comma_Round_Fork a d"
    using decode no_cross by (cases event) auto
  have phase: "r mod 924=r" using fork.prems by (simp add: source)
  have terminal: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,Comma_Round_Fork a d)"
    using close by (simp only: event)
  have run: "comma_finite_run (Suc n) r (Comma_Entry 1 0 x)=Some (Comma_Fork_At a d)"
    using comma_round_close_fork_finite_run[OF terminal] by (simp only: phase)
  show ?case using run by (auto simp only: source comma_decade_state.case)
next
  case (landmine s d)
  obtain r x where source: "s=Comma_Decade r x" by (cases s) auto
  obtain n t event where close: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have decode: "comma_decade_decode r event=Comma_Decade_Landmine d"
    using landmine.hyps by (simp only: source comma_decade_control.simps close prod.case)
  have no_cross: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)\<noteq>Comma_Decade_Landmine d"
    by (case_tac target) simp_all
  have event: "event=Comma_Round_Landmine d"
    using decode no_cross by (cases event) auto
  have phase: "r mod 924=r" using landmine.prems by (simp add: source)
  have terminal: "comma_round_close r (Comma_Entry 1 0 x)=(n,t,Comma_Round_Landmine d)"
    using close by (simp only: event)
  have run: "comma_finite_run (Suc n) r (Comma_Entry 1 0 x)=Some (Comma_Landmine_At d)"
    using comma_round_close_landmine_finite_run[OF terminal] by (simp only: phase)
  show ?case using run by (auto simp only: source comma_decade_state.case)
next
  case (crossing s q rounds)
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
  obtain fuel outcome where suffix:
    "comma_finite_run fuel ((r+1) mod 924) (Comma_Entry 1 0 y)=Some outcome"
    using crossing.IH[OF q_valid] by (auto simp only: q comma_decade_state.case)
  obtain shifted where shifted:
    "comma_finite_run fuel (r mod 924) target=Some shifted"
    using comma_finite_run_shift_exists[where r=r and k=1, OF suffix]
    by (auto simp: y)
  have "\<exists>fuel outcome. comma_finite_run fuel (r mod 924) (Comma_Entry 1 0 x)=Some outcome"
    by (rule comma_round_success_from_cross[OF close]) (use event shifted in auto)
  then show ?case by (simp only: source comma_decade_state.case phase)
qed

lemma comma_boundary_macro_exists:
  assumes checked: "comma_decade_rank_check rank"
    and valid: "comma_boundary_valid q"
  shows "comma_macro_defined q"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  let ?source = "comma_finite_initial q"
  have admitted: "comma_round_admitted ?source"
    and delta: "comma_round_delta ?source=0"
    and phase: "r mod 924=r"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def comma_finite_initial_def)+
  obtain n t event where close: "comma_round_close r ?source=(n,t,event)"
    by (cases "comma_round_close r ?source") auto
  have terminal: "event\<noteq>Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close admitted])
  have crossing: "\<And>target. event=Comma_Round_Cross target \<Longrightarrow>
    \<exists>fuel outcome. comma_finite_run fuel (r mod 924) target=Some outcome"
  proof -
    fix target assume event: "event=Comma_Round_Cross target"
    obtain x where x: "x\<le>90" "target=Comma_Entry 1 1 x"
      using comma_round_close_crossing_phase[of r ?source n t target]
        close event admitted delta by auto
    let ?state = "Comma_Decade ((r+1) mod 924) x"
    have state: "comma_decade_admitted ?state" using x by simp
    obtain rounds where finishes: "comma_decade_finishes ?state rounds"
      using comma_decade_checked_rank_totality[OF checked state] by blast
    obtain fuel outcome where suffix:
      "comma_finite_run fuel ((r+1) mod 924) (Comma_Entry 1 0 x)=Some outcome"
      using comma_decade_finishes_run_exists[OF finishes state] by auto
    show "\<exists>fuel outcome. comma_finite_run fuel (r mod 924) target=Some outcome"
      using comma_finite_run_shift_exists[where r=r and k=1, OF suffix]
      by (auto simp: x)
  qed
  obtain fuel outcome where run: "comma_finite_run fuel r ?source=Some outcome"
    using comma_round_success_from_cross[OF close terminal crossing] phase by auto
  have "comma_finite_macro fuel q=Some outcome"
    using run valid by (simp add: comma_finite_macro_def q)
  then show ?thesis unfolding comma_macro_defined_def by blast
qed

corollary comma_total_macro_from_checked_rank:
  assumes "comma_decade_rank_check rank" "comma_boundary_valid q"
  shows "\<exists>fuel. comma_finite_macro fuel q=Some (comma_total_macro q)"
  by (rule comma_total_macro_correct[OF comma_boundary_macro_exists[OF assms]])

corollary comma_total_weighted_macro_from_checked_rank:
  assumes "comma_decade_rank_check rank" "comma_boundary_valid q"
    "5\<le>p" "p mod 924=snd (snd q)"
  shows "\<exists>fuel. comma_finite_weighted_macro fuel p q=
    Some (comma_total_weighted_macro p q)"
  by (rule comma_total_weighted_macro_correct[OF comma_macro_defined_weighted
    [OF comma_boundary_macro_exists[OF assms(1,2)] assms(3,4)]])

text \<open>The total functions above are semantic descriptions. Their
correctness theorems require a successful domain; HOL's definite description
outside that domain is not admission evidence and is not an executable code
equation. No concrete all-boundary totality theorem is asserted here.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_run_success_unique comma_finite_macro_success_unique
      comma_finite_weighted_run_more comma_finite_weighted_run_success_unique
      comma_finite_weighted_macro_more comma_finite_weighted_macro_success_unique
      comma_total_macro_agrees comma_total_weighted_macro_agrees
      comma_total_macro_correct comma_total_weighted_macro_correct
      comma_macro_defined_weighted comma_total_weighted_macro_erasure
      comma_total_children_agree comma_finite_run_shift_exists
      comma_round_success_from_cross comma_decade_finishes_run_exists
      comma_boundary_macro_exists comma_total_macro_from_checked_rank
      comma_total_weighted_macro_from_checked_rank})
    then () else error "Comma total macro depends on an oracle";
\<close>
end
