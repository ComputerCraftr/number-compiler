theory Comma_Decade_Occurrence_Lift
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
    Comma_Decade_Occurrence_Semantic.Comma_Decade_Occurrence_Semantic
begin

ML_file "../shared/proof_profile.ML"
ML \<open>val comma_occurrence_lift_checkpoint =
  Comma_Proof_Profile.timer "Occurrence lift"\<close>

text \<open>Lift the inductive decade summary to physical occurrences, retaining
its exact exponent gain. This proof uses neither a fuelled macro evaluator nor
a finite candidate table. Existence of a native summary for every admitted
input is a separate constructor obligation. A macro edge includes its literal
prefix: it is not a single literal child edge from the source boundary.\<close>

fun comma_summary_terminal_move :: "comma_decade_terminal \<Rightarrow> comma_finite_move" where
  "comma_summary_terminal_move (Comma_Terminal_Fork a) = Comma_Fork a 0"
| "comma_summary_terminal_move Comma_Terminal_Landmine = Comma_Landmine 0"

ML \<open>comma_occurrence_lift_checkpoint "entered theorem proofs"\<close>

lemma comma_round_terminal_occurrence:
  assumes close: "comma_round_close r source = (n,t,event)"
    and valid: "comma_round_admitted source"
    and zero: "comma_round_delta source = 0"
    and phase: "r mod 924 = p mod 924"
    and exponent: "5 \<le> p"
    and terminal: "event = (case tau of Comma_Terminal_Fork a \<Rightarrow>
      Comma_Round_Fork a 0 | Comma_Terminal_Landmine \<Rightarrow> Comma_Round_Landmine 0)"
  shows "\<exists>w. comma_literal_path w (comma_chart_value p source)
      (comma_chart_value p t) \<and> comma_round_admitted t \<and>
      comma_round_delta t = 0 \<and>
      comma_finite_step (p mod 924) t = comma_summary_terminal_move tau"
proof -
  obtain w where path: "comma_literal_path w (comma_chart_value p source)
      (comma_chart_value p t)"
    using comma_round_close_literal_prefix[OF close phase exponent valid] by blast
  have admitted: "comma_round_admitted t"
    using comma_round_close_admitted(1)[OF close valid] .
  have delta: "comma_round_delta t = 0"
    using comma_round_close_delta[OF close valid] zero by simp
  have move: "comma_finite_step (p mod 924) t = comma_summary_terminal_move tau"
    using comma_round_close_refines_trace[OF close] terminal phase
    by (cases tau) auto
  show ?thesis using path admitted delta move by blast
qed

ML \<open>comma_occurrence_lift_checkpoint "terminal round"\<close>

lemma comma_decade_direct_occurrence:
  assumes admitted: "comma_decade_admitted (Comma_Decade r x)"
    and phase: "p mod 924 = r" and exponent: "5 \<le> p"
    and control: "comma_decade_control (Comma_Decade r x) =
      (case tau of Comma_Terminal_Fork a \<Rightarrow> Comma_Decade_Fork a 0
        | Comma_Terminal_Landmine \<Rightarrow> Comma_Decade_Landmine 0)"
  shows "\<exists>w t. comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value p t) \<and> comma_round_admitted t \<and>
      comma_round_delta t = 0 \<and>
      comma_finite_step (p mod 924) t = comma_summary_terminal_move tau"
proof -
  obtain n t event where close:
    "comma_round_close r (Comma_Entry 1 0 x) = (n,t,event)"
    by (metis surj_pair)
  have decode: "comma_decade_decode r event =
      (case tau of Comma_Terminal_Fork a \<Rightarrow> Comma_Decade_Fork a 0
        | Comma_Terminal_Landmine \<Rightarrow> Comma_Decade_Landmine 0)"
    using control by (simp only: comma_decade_control.simps close prod.case)
  have no_cross_fork: "\<And>target a. comma_decade_decode r (Comma_Round_Cross target) \<noteq> Comma_Decade_Fork a 0"
    by (case_tac target) simp_all
  have no_cross_landmine: "\<And>target. comma_decade_decode r (Comma_Round_Cross target) \<noteq> Comma_Decade_Landmine 0"
    by (case_tac target) simp_all
  have event: "event = (case tau of Comma_Terminal_Fork a \<Rightarrow>
      Comma_Round_Fork a 0 | Comma_Terminal_Landmine \<Rightarrow> Comma_Round_Landmine 0)"
    using decode no_cross_fork no_cross_landmine by (cases tau; cases event) auto
  have valid: "comma_round_admitted (Comma_Entry 1 0 x)" using admitted by simp
  have residue: "r mod 924 = p mod 924" using phase by simp
  show ?thesis
    using comma_round_terminal_occurrence[OF close valid _ residue exponent event]
    by auto
qed

ML \<open>comma_occurrence_lift_checkpoint "direct decade terminal"\<close>

lemma comma_decade_continue_occurrence:
  assumes admitted: "comma_decade_admitted (Comma_Decade r x)"
    and phase: "p mod 924 = r" and exponent: "5 \<le> p"
    and control: "comma_decade_control (Comma_Decade r x) = Comma_Decade_Continue q"
  obtains y w where "y \<le> 90" "q = Comma_Decade ((r+1) mod 924) y"
    "comma_literal_path (Suc w) (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (Suc p) (Comma_Entry 1 0 y))"
proof -
  obtain n t event where close:
    "comma_round_close r (Comma_Entry 1 0 x) = (n,t,event)"
    by (metis surj_pair)
  have decode: "comma_decade_decode r event = Comma_Decade_Continue q"
    using control by (simp only: comma_decade_control.simps close prod.case)
  obtain target where event: "event = Comma_Round_Cross target"
    using decode by (cases event; auto split: comma_finite_position.splits if_splits)
  have valid: "comma_round_admitted (Comma_Entry 1 0 x)" using admitted by simp
  have cross: "comma_round_close r (Comma_Entry 1 0 x) = (n,t,Comma_Round_Cross target)"
    using close event by simp
  obtain y where y: "y \<le> 90" "target = Comma_Entry 1 1 y"
    using comma_round_close_crossing_phase[OF cross valid] by auto
  have q: "q = Comma_Decade ((r+1) mod 924) y"
    using decode by (simp add: event y)
  have residue: "r mod 924 = p mod 924" using phase by simp
  obtain w where path: "comma_literal_path (w+1)
      (comma_chart_value p (Comma_Entry 1 0 x)) (comma_chart_value p target)"
    using comma_round_crossing_literal_prefix[OF cross residue exponent valid] by blast
  have rebase: "comma_chart_value p target = comma_chart_value (Suc p) (Comma_Entry 1 0 y)"
    by (simp add: y comma_chart_value_def)
  show thesis by (rule that[OF y(1) q]) (use path rebase in simp)
qed

ML \<open>comma_occurrence_lift_checkpoint "crossing decade"\<close>

theorem comma_decade_summary_occurrence_exact:
  assumes summary: "comma_decade_exact_summary s h tau"
    and admitted: "comma_decade_admitted s"
    and exponent: "5 \<le> p"
    and binding: "s = Comma_Decade (p mod 924) x"
  shows "\<exists>w t. comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t) \<and> comma_round_admitted t \<and>
      comma_round_delta t = 0 \<and>
      comma_finite_step ((p+h) mod 924) t = comma_summary_terminal_move tau"
  using summary admitted exponent binding
proof (induction arbitrary: p x rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have valid: "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using fork.prems by simp
  have move: "comma_decade_control (Comma_Decade (p mod 924) x) = Comma_Decade_Fork a 0"
    using fork.hyps fork.prems by simp
  show ?case using comma_decade_direct_occurrence[OF valid refl fork.prems(2),
      where tau="Comma_Terminal_Fork a"] move by simp
next
  case (landmine s)
  have valid: "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using landmine.prems by simp
  have move: "comma_decade_control (Comma_Decade (p mod 924) x) = Comma_Decade_Landmine 0"
    using landmine.hyps landmine.prems by simp
  show ?case using comma_decade_direct_occurrence[OF valid refl landmine.prems(2),
      where tau=Comma_Terminal_Landmine] move by simp
next
  case (crossing s q h tau)
  have valid: "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using crossing.prems by simp
  have move: "comma_decade_control (Comma_Decade (p mod 924) x) = Comma_Decade_Continue q"
    using crossing.hyps(1) crossing.prems by simp
  obtain y w where y: "y \<le> 90" "q = Comma_Decade (((p mod 924)+1) mod 924) y"
    and path: "comma_literal_path (Suc w) (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (Suc p) (Comma_Entry 1 0 y))"
    by (rule comma_decade_continue_occurrence[OF valid refl crossing.prems(2) move]) blast
  have next_valid: "comma_decade_admitted q" using y by simp
  have next_exponent: "5 \<le> Suc p" using crossing.prems by simp
  have shift: "(p mod 924 + 1) mod 924 = (p+1) mod 924"
    by (rule mod_add_left_eq)
  have next_binding: "q = Comma_Decade ((Suc p) mod 924) y"
    using y(2) shift by simp
  obtain v t where tail: "comma_literal_path v (comma_chart_value (Suc p) (Comma_Entry 1 0 y))
      (comma_chart_value (Suc p+h) t)"
    and terminal: "comma_round_admitted t" "comma_round_delta t = 0"
      "comma_finite_step ((Suc p+h) mod 924) t = comma_summary_terminal_move tau"
    using crossing.IH[OF next_valid next_exponent next_binding] by blast
  have joined: "comma_literal_path (Suc w+v)
      (comma_chart_value p (Comma_Entry 1 0 x)) (comma_chart_value (Suc p+h) t)"
    by (rule comma_literal_path_append[OF path tail])
  show ?case using joined terminal by auto
qed

ML \<open>comma_occurrence_lift_checkpoint "recursive exact summary"\<close>

lemma comma_c1_crossing_chart_rebase:
  assumes close:
    "comma_round_close r position =
      (steps,terminal,Comma_Round_Cross q)"
    and valid: "comma_round_admitted position"
    and physical_phase: "p mod 924 = r"
  shows "\<exists>x\<le>90.
      q = Comma_Entry 1 (Suc (comma_round_delta position)) x \<and>
      comma_normalize_position r q =
        Comma_Entry 1 ((p + comma_round_delta position + 1) mod 924) x \<and>
      comma_chart_value p q =
        comma_chart_value (p + comma_round_delta position + 1)
          (Comma_Entry 1 0 x)"
proof -
  obtain x where x_bound: "x \<le> 90"
    and q_shape: "q = Comma_Entry 1 (Suc (comma_round_delta position)) x"
    and normalized:
      "comma_normalize_position r q =
        Comma_Entry 1 ((r + comma_round_delta position + 1) mod 924) x"
    using comma_round_close_crossing_phase[OF close valid] by blast
  have residue:
    "(r + comma_round_delta position + 1) mod 924 =
      (p + comma_round_delta position + 1) mod 924"
  proof -
    have "(r + comma_round_delta position + 1) mod 924 =
        ((p mod 924) + comma_round_delta position + 1) mod 924"
      using physical_phase by simp
    also have "... = (p + comma_round_delta position + 1) mod 924"
      by (simp only: add.assoc mod_add_left_eq)
    finally show ?thesis .
  qed
  have normalized_physical:
    "comma_normalize_position r q =
      Comma_Entry 1 ((p + comma_round_delta position + 1) mod 924) x"
    using normalized residue by simp
  have chart:
    "comma_chart_value p q =
      comma_chart_value (p + comma_round_delta position + 1)
        (Comma_Entry 1 0 x)"
    using q_shape by (simp add: comma_chart_value_def add.assoc)
  show ?thesis
    using x_bound q_shape normalized_physical chart by blast
qed

ML \<open>comma_occurrence_lift_checkpoint "crossing chart rebase"\<close>

fun comma_summary_ordered_children :: "comma_decade_terminal \<Rightarrow> nat \<Rightarrow> nat list" where
  "comma_summary_ordered_children (Comma_Terminal_Fork a) p =
    [comma_near_boundary a p, comma_zero_boundary a p]"
| "comma_summary_ordered_children Comma_Terminal_Landmine p = []"

lemma comma_summary_terminal_children_exact:
  assumes valid: "comma_round_admitted t" and zero: "comma_round_delta t = 0"
    and exponent: "5 \<le> p"
    and move: "comma_finite_step (p mod 924) t = comma_summary_terminal_move tau"
  shows "comma_large_children (comma_sector_number t) p (comma_chart_value p t)
      = comma_summary_ordered_children tau p"
    "comma_child (comma_chart_value p t) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children tau p)"
proof -
  have terminal: "(\<exists>a. comma_finite_step (p mod 924) t = Comma_Fork a 0) \<or>
      comma_finite_step (p mod 924) t = Comma_Landmine 0"
    using move by (cases tau) auto
  obtain f delta h where shape: "t = Comma_Near f delta h"
    and f: "1 \<le> f" "f \<le> 9" and h: "1 \<le> h" "h \<le> 540"
    using comma_terminal_event_near_shape[OF valid terminal] by blast
  have delta: "delta = 0" using zero shape by simp
  have sector: "comma_sector f p (comma_chart_value p t)"
    using comma_near_chart_checked_sector[OF f exponent h, of 0] by (simp add: shape delta)
  have germ: "terminal_move (comma_terminal_event_germ (p mod 924) f 0 h)
      = comma_summary_terminal_move tau"
    using move by (simp add: shape delta comma_terminal_event_germ_def Let_def)
  have children: "comma_large_children f p (comma_chart_value p t)
      = comma_summary_ordered_children tau p"
  proof (cases tau)
    case (Comma_Terminal_Fork a)
    have fork: "terminal_move (comma_terminal_event_germ (p mod 924) f 0 h) = Comma_Fork a 0"
      using germ Comma_Terminal_Fork by simp
    show ?thesis using comma_terminal_fork_children(1)[OF f exponent h fork]
      by (simp add: shape delta Comma_Terminal_Fork)
  next
    case Comma_Terminal_Landmine
    have dead: "terminal_move (comma_terminal_event_germ (p mod 924) f 0 h) = Comma_Landmine 0"
      using germ Comma_Terminal_Landmine by simp
    show ?thesis using comma_terminal_landmine_children(1)[OF f exponent h dead]
      by (simp add: shape delta Comma_Terminal_Landmine)
  qed
  show "comma_large_children (comma_sector_number t) p (comma_chart_value p t)
      = comma_summary_ordered_children tau p"
    using children by (simp add: shape)
  have large: "2 \<le> p" using exponent by arith
  show "comma_child (comma_chart_value p t) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children tau p)"
    using comma_large_children_complete[OF sector large, of v] children by simp
qed

ML \<open>comma_occurrence_lift_checkpoint "terminal children"\<close>

theorem comma_decade_summary_ordered_occurrence:
  assumes summary: "comma_decade_exact_summary s h tau"
    and admitted: "comma_decade_admitted s" and exponent: "5 \<le> p"
    and binding: "s = Comma_Decade (p mod 924) x"
  obtains w t where
    "comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
      = comma_summary_ordered_children tau (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children tau (p+h))"
proof -
  obtain w t where path: "comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    and valid: "comma_round_admitted t" and zero: "comma_round_delta t = 0"
    and move: "comma_finite_step ((p+h) mod 924) t = comma_summary_terminal_move tau"
    using comma_decade_summary_occurrence_exact[OF assms] by blast
  have large: "5 \<le> p+h" using exponent by arith
  show thesis by (rule that[OF path
      comma_summary_terminal_children_exact(1)[OF valid zero large move]
      comma_summary_terminal_children_exact(2)[OF valid zero large move]])
qed

ML \<open>comma_occurrence_lift_checkpoint "ordered summary theorem complete"\<close>

ML \<open>
  val comma_occurrence_lift_checked = @{thms
    comma_round_terminal_occurrence comma_decade_direct_occurrence
    comma_decade_continue_occurrence comma_decade_summary_occurrence_exact
    comma_c1_crossing_chart_rebase comma_summary_terminal_children_exact
    comma_decade_summary_ordered_occurrence}
  val _ = comma_occurrence_lift_checkpoint "oracle theorem list collected"
  val _ = if null (Thm_Deps.all_oracles comma_occurrence_lift_checked)
    then () else error "Decade occurrence lift depends on an oracle";
  val _ = comma_occurrence_lift_checkpoint "oracle dependencies validated";
\<close>
end
