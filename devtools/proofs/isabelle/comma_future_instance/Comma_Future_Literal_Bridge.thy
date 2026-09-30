theory Comma_Future_Literal_Bridge
  imports Comma_Future_Cycle_Check
    Comma_Literal_Bridge.Comma_Unique_Path
begin

text \<open>A selected boundary edge has a strictly positive literal length:
 the weighted chart run reaches the fork, then choosing either child adds one
 literal edge. Thus positivity does not require evaluating a gigantic decimal
 weight. Exact weight formulas remain a separate refinement interface.\<close>

lemma comma_indexed_trace_terminal_fork:
  assumes "comma_indexed_trace p source rows (Comma_Fork_At a d) terminal"
  shows "comma_weighted_step (p mod 924) terminal = Comma_WFork terminal a d"
  using assms by (induction p source rows "Comma_Fork_At a d" terminal
    rule: comma_indexed_trace.induct) auto

lemma comma_weighted_fork_literal_children:
  assumes exponent: "5 \<le> p"
    and fork: "comma_weighted_step (p mod 924) terminal = Comma_WFork terminal a d"
  shows "comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
    v = comma_near_boundary a (p+d) \<or> v = comma_zero_boundary a (p+d)"
proof -
  obtain f h where terminal: "terminal = Comma_Near f d h"
    and valid: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
    using fork by (cases terminal)
      (auto simp: comma_weighted_step_def Let_def split: if_splits)
  have step: "comma_finite_step (p mod 924) (Comma_Near f d h) = Comma_Fork a d"
    using fork by (simp add: terminal comma_finite_step_def)
  have sector: "comma_sector f (p+d) (comma_chart_value p (Comma_Near f d h))"
    by (rule comma_near_chart_checked_sector[OF valid(1,2) exponent valid(3,4)])
  have large: "2\<le>p+d" using exponent by arith
  have children: "comma_large_children f (p+d)
      (comma_chart_value p (Comma_Near f d h)) =
      [comma_near_boundary a (p+d),comma_zero_boundary a (p+d)]"
    by (rule comma_near_chart_fork(3)[OF sector large refl refl step])
  show ?thesis
    using comma_large_children_complete[OF sector large, of v]
    by (simp add: terminal children)
qed

lemma comma_total_macro_unique_fork_prefix:
  assumes defined: "comma_macro_defined q"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
    and outcome: "comma_total_macro q = Comma_Fork_At a d"
  shows "\<exists>weight terminal.
    comma_unique_literal_path weight (comma_boundary_value q p) terminal \<and>
    (\<forall>v. comma_child terminal v \<longleftrightarrow>
      v = comma_near_boundary a (p+d) \<or> v = comma_zero_boundary a (p+d))"
proof -
  obtain fuel where run: "comma_finite_weighted_macro fuel p q =
      Some (comma_total_weighted_macro p q)"
    using comma_total_weighted_macro_correct[OF
      comma_macro_defined_weighted[OF defined exponent phase]] by blast
  obtain weight terminal where weighted:
      "comma_total_weighted_macro p q = (Comma_Fork_At a d,weight,terminal)"
    using comma_total_weighted_macro_erasure[OF defined exponent phase] outcome
    by (cases "comma_total_weighted_macro p q") auto
  have finite: "comma_finite_weighted_run fuel p (comma_finite_initial q) =
      Some (Comma_Fork_At a d,weight,terminal)"
    using run valid exponent phase by (simp add: comma_finite_weighted_macro_def weighted)
  obtain rows where trace:
      "comma_indexed_trace p (comma_finite_initial q) rows (Comma_Fork_At a d) terminal"
    and weight: "sum_list (map fst rows) = weight"
    using comma_weighted_run_indexed_trace[OF finite] by blast
  have unique: "comma_unique_literal_path weight
      (comma_boundary_value q p) (comma_chart_value p terminal)"
    using comma_source_indexed_unique_path[OF trace exponent]
      comma_chart_initial_refines_boundary[OF valid, of p] weight by simp
  have children: "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      v = comma_near_boundary a (p+d) \<or> v = comma_zero_boundary a (p+d)"
    using comma_weighted_fork_literal_children[OF exponent
      comma_indexed_trace_terminal_fork[OF trace]] by blast
  show ?thesis using unique children by blast
qed

theorem comma_total_macro_selected_literal_path:
  assumes defined: "comma_macro_defined q"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
    and outcome: "comma_total_macro q = Comma_Fork_At a d"
    and selected: "target \<in> set (comma_total_children q)"
  shows "\<exists>weight>0. comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value target (p+d))"
    and "(p+d) mod 924 = snd (snd target)"
proof -
  have targets: "target = (Comma_N,a,(snd (snd q)+d) mod 924) \<or>
      target = (Comma_Z,a,(snd (snd q)+d) mod 924)"
    using selected by (simp add: comma_total_children_def outcome)
  obtain weight terminal where unique:
      "comma_unique_literal_path weight (comma_boundary_value q p) terminal"
    and children: "\<forall>v. comma_child terminal v \<longleftrightarrow>
      v = comma_near_boundary a (p+d) \<or> v = comma_zero_boundary a (p+d)"
    using comma_total_macro_unique_fork_prefix[OF defined valid exponent phase outcome]
    by blast
  have boundary: "comma_boundary_value target (p+d) = comma_near_boundary a (p+d) \<or>
      comma_boundary_value target (p+d) = comma_zero_boundary a (p+d)"
    using targets by (auto simp: comma_boundary_value_def
      comma_near_boundary_def comma_zero_boundary_def)
  have edge: "comma_child terminal (comma_boundary_value target (p+d))"
    by (rule iffD2[OF spec[OF children, of "comma_boundary_value target (p+d)"] boundary])
  have "comma_literal_path (Suc weight) (comma_boundary_value q p)
      (comma_boundary_value target (p+d))"
    by (rule comma_literal_path_snoc[OF comma_unique_literal_path_literal[OF unique] edge])
  then show "\<exists>weight>0. comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value target (p+d))" by blast
  have "(p+d) mod 924 = ((p mod 924)+d) mod 924"
    by (rule mod_add_left_eq[symmetric])
  also have "... = (snd (snd q)+d) mod 924"
    by (simp only: phase)
  also have "... = snd (snd target)"
    using targets by auto
  finally show "(p+d) mod 924 = snd (snd target)" .
qed

theorem comma_surviving_delta_path_literal:
  assumes path: "comma_surviving_delta_path rank steps q final_state delta"
    and closed: "\<And>q. comma_boundary_valid q \<Longrightarrow>
      set (comma_total_children q) \<subseteq> {r. comma_boundary_valid r}"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>weight\<ge>steps. comma_literal_path weight
      (comma_boundary_value q p) (comma_boundary_value final_state (p+delta))"
  using path valid exponent phase
proof (induction arbitrary: p rule: comma_surviving_delta_path.induct)
  case (empty q)
  then show ?case by (auto intro: comma_literal_path.zero)
next
  case (step q a d target steps final_state rest)
  obtain head where head: "0<head"
      "comma_literal_path head (comma_boundary_value q p)
        (comma_boundary_value target (p+d))"
    using comma_total_macro_selected_literal_path(1)
      [OF step.hyps(1) step.prems step.hyps(2,3)] by blast
  have target: "comma_boundary_valid target"
    using closed[OF step.prems(1)] step.hyps(3) by blast
  have large: "5\<le>p+d" using step.prems(2) by arith
  have phase: "(p+d) mod 924 = snd (snd target)"
    by (rule comma_total_macro_selected_literal_path(2)
      [OF step.hyps(1) step.prems step.hyps(2,3)])
  obtain tail where tail: "steps\<le>tail"
      "comma_literal_path tail (comma_boundary_value target (p+d))
        (comma_boundary_value final_state (p+d+rest))"
    using step.IH[OF target large phase] by blast
  have path: "comma_literal_path (head+tail) (comma_boundary_value q p)
      (comma_boundary_value final_state (p+(d+rest)))"
    using comma_literal_path_append[OF head(2) tail(2)] by (simp add: add.assoc)
  have "Suc steps\<le>head+tail" using head(1) tail(1) by arith
  then show ?case using path by blast
qed

corollary comma_checked_cycle_literal_returns:
  assumes cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>weight\<ge>k*314. comma_literal_path weight
    (comma_boundary_value q p) (comma_boundary_value q (p+k*924))"
proof -
  have closed: "\<And>q. comma_boundary_valid q \<Longrightarrow>
      set (comma_total_children q) \<subseteq> {r. comma_boundary_valid r}"
  proof -
    fix q assume valid: "comma_boundary_valid q"
    have state: "q \<in> set comma_boundary_states"
      using valid by (simp add: comma_boundary_states_set)
    have closure: "set (comma_total_children q) \<subseteq> set comma_boundary_states"
      by (rule comma_rank_witness_closed[OF cert state])
    show "set (comma_total_children q) \<subseteq> {r. comma_boundary_valid r}"
      using closure by (simp only: comma_boundary_states_set)
  qed
  show ?thesis by (rule comma_surviving_delta_path_literal
    [OF comma_surviving_cycle_repeats[OF cycle] closed valid exponent phase])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_total_macro_unique_fork_prefix
      comma_total_macro_selected_literal_path comma_surviving_delta_path_literal
      comma_checked_cycle_literal_returns})
    then () else error "Comma literal future bridge depends on an oracle";
\<close>
end
