theory Comma_Decade_Occurrence_Semantic
  imports Comma_Terminal_Event.Comma_Terminal_Event
begin

text \<open>
Direct terminal rounds retain a literal prefix and the complete child
relation. These lemmas reuse the checked terminal-event arithmetic without
macro fuel, a total-macro outcome or candidate rows. Crossing into a later
decade still requires induction over the exact residual summary; these
terminal lemmas alone are not the complete occurrence cutover.
\<close>

lemma comma_terminal_event_near_shape:
  assumes terminal_valid: "comma_round_admitted terminal"
    and move:
      "(\<exists>a. comma_finite_step residue terminal = Comma_Fork a d) \<or>
       comma_finite_step residue terminal = Comma_Landmine d"
  shows "\<exists>f delta h.
      terminal = Comma_Near f delta h \<and>
      1 \<le> f \<and> f \<le> 9 \<and> 1 \<le> h \<and> h \<le> 540"
proof (cases terminal)
  case (Comma_Entry f delta offset)
  have f_bounds: "1 \<le> f" "f \<le> 9"
    using terminal_valid by (simp_all add: Comma_Entry)
  have offset: "offset \<le> 98"
    using terminal_valid by (simp_all add: Comma_Entry)
  have positive: "comma_finite_period f (offset mod 10) \<noteq> 0"
    using comma_finite_period_in_catalog[rule_format, of f "offset mod 10"]
      f_bounds by (auto simp: comma_cycle_displacements_def)
  have advance:
      "comma_finite_step residue (Comma_Entry f delta offset) =
        Comma_Next (Comma_Near f delta
          (comma_finite_headroom f residue delta offset))"
    using f_bounds offset positive
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def)
  then show ?thesis using move Comma_Entry by auto
next
  case (Comma_Near f delta h)
  have bounds: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
    using terminal_valid by (simp_all add: Comma_Near)
  show ?thesis
    by (rule exI[of _ f], rule exI[of _ delta], rule exI[of _ h])
      (use bounds in \<open>simp add: Comma_Near\<close>)
qed

lemma comma_boundary_fork_occurrence:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (n,terminal,Comma_Round_Fork a d)"
  shows "\<exists>weight.
      comma_literal_path weight (comma_boundary_value q p)
        (comma_chart_value p terminal) \<and>
      (\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
        v = comma_near_boundary a (p+d) \<or>
        v = comma_zero_boundary a (p+d))"
proof -
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases q) (auto simp: comma_boundary_valid_def
      comma_finite_initial_def split: if_splits)
  have residue: "snd (snd q) mod 924 = p mod 924"
  proof -
    have bounded: "snd (snd q) < 924"
      using valid by (cases q) (auto simp: comma_boundary_valid_def)
    with phase show ?thesis by simp
  qed
  obtain weight where prefix:
      "comma_literal_path weight
        (comma_chart_value p (comma_finite_initial q))
        (comma_chart_value p terminal)"
    using comma_round_close_literal_prefix[OF close residue exponent source_valid]
    by blast
  have boundary:
      "comma_chart_value p (comma_finite_initial q) = comma_boundary_value q p"
    by (rule comma_chart_initial_refines_boundary[OF valid])
  have terminal_valid: "comma_round_admitted terminal"
    using comma_round_close_admitted(1)[OF close source_valid] .
  have move:
      "comma_finite_step (p mod 924) terminal = Comma_Fork a d"
  proof -
    have raw: "comma_finite_step (snd (snd q) mod 924) terminal =
        Comma_Fork a d"
      using comma_round_close_refines_trace[OF close] by simp
    with residue show ?thesis by simp
  qed
  have event_move:
      "(\<exists>a. comma_finite_step (p mod 924) terminal = Comma_Fork a d) \<or>
       comma_finite_step (p mod 924) terminal = Comma_Landmine d"
    by (simp add: move)
  obtain f delta h where terminal_shape:
      "terminal = Comma_Near f delta h"
    and f_bounds: "1 \<le> f" "f \<le> 9"
    and h_bounds: "1 \<le> h" "h \<le> 540"
    using comma_terminal_event_near_shape[OF terminal_valid event_move] by blast
  have move_shape:
      "comma_finite_step (p mod 924) (Comma_Near f delta h) =
        Comma_Fork a d"
    using move terminal_shape by simp
  have delta_eq: "d = delta"
    using move_shape f_bounds h_bounds
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  have germ_move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta h) =
        Comma_Fork a delta"
    using move_shape delta_eq
    by (simp add: comma_terminal_event_germ_def Let_def)
  have large:
      "comma_large_children f (p+delta)
        (comma_chart_value p (Comma_Near f delta h)) =
        [comma_near_boundary a (p+delta),
         comma_zero_boundary a (p+delta)]"
    by (rule comma_terminal_fork_children[OF f_bounds exponent h_bounds germ_move])
  have sector:
      "comma_sector f (p+delta)
        (comma_chart_value p (Comma_Near f delta h))"
    by (rule comma_near_chart_checked_sector[OF f_bounds exponent h_bounds])
  have chart_exponent: "2 \<le> p+delta" using exponent by arith
  have children:
      "comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
        v = comma_near_boundary a (p+delta) \<or>
        v = comma_zero_boundary a (p+delta)" for v
    using comma_large_children_complete[OF sector chart_exponent, of v]
    by (simp add: terminal_shape large; arith)
  show ?thesis
    by (rule exI[of _ weight])
      (use prefix boundary children delta_eq in simp)
qed

lemma comma_boundary_landmine_occurrence:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (n,terminal,Comma_Round_Landmine d)"
  shows "\<exists>weight.
      comma_literal_path weight (comma_boundary_value q p)
        (comma_chart_value p terminal) \<and>
      (\<nexists>v. comma_child (comma_chart_value p terminal) v)"
proof -
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases q) (auto simp: comma_boundary_valid_def
      comma_finite_initial_def split: if_splits)
  have residue: "snd (snd q) mod 924 = p mod 924"
  proof -
    have bounded: "snd (snd q) < 924"
      using valid by (cases q) (auto simp: comma_boundary_valid_def)
    with phase show ?thesis by simp
  qed
  obtain weight where prefix:
      "comma_literal_path weight
        (comma_chart_value p (comma_finite_initial q))
        (comma_chart_value p terminal)"
    using comma_round_close_literal_prefix[OF close residue exponent source_valid]
    by blast
  have boundary:
      "comma_chart_value p (comma_finite_initial q) = comma_boundary_value q p"
    by (rule comma_chart_initial_refines_boundary[OF valid])
  have terminal_valid: "comma_round_admitted terminal"
    using comma_round_close_admitted(1)[OF close source_valid] .
  have move:
      "comma_finite_step (p mod 924) terminal = Comma_Landmine d"
  proof -
    have raw: "comma_finite_step (snd (snd q) mod 924) terminal =
        Comma_Landmine d"
      using comma_round_close_refines_trace[OF close] by simp
    with residue show ?thesis by simp
  qed
  have event_move:
      "(\<exists>a. comma_finite_step (p mod 924) terminal = Comma_Fork a d) \<or>
       comma_finite_step (p mod 924) terminal = Comma_Landmine d"
    by (simp add: move)
  obtain f delta h where terminal_shape:
      "terminal = Comma_Near f delta h"
    and f_bounds: "1 \<le> f" "f \<le> 9"
    and h_bounds: "1 \<le> h" "h \<le> 540"
    using comma_terminal_event_near_shape[OF terminal_valid event_move] by blast
  have move_shape:
      "comma_finite_step (p mod 924) (Comma_Near f delta h) =
        Comma_Landmine d"
    using move terminal_shape by simp
  have delta_eq: "d = delta"
    using move_shape f_bounds h_bounds
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  have germ_move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta h) =
        Comma_Landmine delta"
    using move_shape delta_eq
    by (simp add: comma_terminal_event_germ_def Let_def)
  have large:
      "comma_large_children f (p+delta)
        (comma_chart_value p (Comma_Near f delta h)) = []"
    by (rule comma_terminal_landmine_children[OF f_bounds exponent h_bounds germ_move])
  have sector:
      "comma_sector f (p+delta)
        (comma_chart_value p (Comma_Near f delta h))"
    by (rule comma_near_chart_checked_sector[OF f_bounds exponent h_bounds])
  have chart_exponent: "2 \<le> p+delta" using exponent by arith
  have no_child: "\<nexists>v. comma_child (comma_chart_value p terminal) v"
  proof
    assume "\<exists>v. comma_child (comma_chart_value p terminal) v"
    then obtain v where child: "comma_child (comma_chart_value p terminal) v"
      by blast
    have member:
        "v \<in> set (comma_large_children f (p+delta)
          (comma_chart_value p (Comma_Near f delta h)))"
      using comma_large_children_complete[OF sector chart_exponent, of v] child
      by (simp add: terminal_shape; arith)
    then show False by (simp add: large)
  qed
  show ?thesis
    by (rule exI[of _ weight])
      (use prefix boundary no_child in simp)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_terminal_event_near_shape comma_boundary_fork_occurrence
      comma_boundary_landmine_occurrence})
    then () else error "Literal boundary occurrence depends on an oracle";
\<close>
end
