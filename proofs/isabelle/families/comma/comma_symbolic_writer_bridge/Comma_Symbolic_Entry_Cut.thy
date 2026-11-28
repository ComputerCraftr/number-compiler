theory Comma_Symbolic_Entry_Cut
  imports Comma_C1_Occurrence.Comma_C1_First_Sector
begin

text \<open>Demanded Entry cut before the Near seam. The physical position is
computed from complete periods and a remainder, without an occurrence list.\<close>

definition comma_symbolic_entry_cut :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_symbolic_entry_cut f p delta offset j =
    (let L = comma_cycle_length f;
         P = comma_finite_period f (offset mod 10)
     in comma_chart_value p (Comma_Entry f delta offset) + (j div L)*P +
       comma_period_displacement f (offset mod 10) (j mod L))"

lemma comma_fixed_interval_literal:
  assumes edges: "\<forall>i<N. comma_child (comma_fixed_iter f i source)
    (comma_fixed_iter f (Suc i) source)"
    and bound: "j+n \<le> N"
  shows "comma_literal_path n (comma_fixed_iter f j source)
    (comma_fixed_iter f (j+n) source)"
  using bound
proof (induction n)
  case 0
  then show ?case by (simp add: comma_literal_path.zero)
next
  case (Suc n)
  have prefix: "comma_literal_path n (comma_fixed_iter f j source)
      (comma_fixed_iter f (j+n) source)"
    using Suc by simp
  have edge: "comma_child (comma_fixed_iter f (j+n) source)
      (comma_fixed_iter f (Suc (j+n)) source)"
    using edges Suc.prems by auto
  show ?case using comma_literal_path_snoc[OF prefix edge] by simp
qed

theorem comma_symbolic_entry_cut_exact:
  fixes f p delta offset j h P L steps :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div P) * L"
  assumes cut: "j \<le> steps"
  shows "j mod L < 10"
    and "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_symbolic_entry_cut f p delta offset j)"
    and "comma_literal_path (steps-j) (comma_symbolic_entry_cut f p delta offset j)
      (comma_chart_value p (Comma_Near f delta h))"
proof -
  let ?source = "comma_chart_value p (Comma_Entry f delta offset)"
  let ?c = "(10 ^ (p + delta) - offset - h) div P"
  have length: "0 < L" and closes: "10 dvd L*f"
    using comma_cycle_length_admitted[OF sector] by (simp_all add: L_def)
  have small: "L \<le> 10"
    using sector by (auto simp: L_def comma_cycle_length_def)
  have remainder: "j mod L < L" using length by simp
  show "j mod L < 10" using remainder small by arith
  have digit: "?source mod 10 = offset mod 10"
    using comma_entry_chart_digit[of p f delta offset] exponent by simp
  have period: "comma_period_displacement f (?source mod 10) L = P"
    using comma_finite_period_refines[OF sector, of "offset mod 10"] digit
    by (simp add: P_def L_def)
  have split: "j = (j div L)*L + j mod L" by (simp add: div_mult_mod_eq)
  have repeated: "comma_period_displacement f (?source mod 10) j =
      (j div L)*P + comma_period_displacement f (?source mod 10) (j mod L)"
    using comma_period_displacement_repeated[OF closes, of "?source mod 10" "j div L" "j mod L"]
      split period by simp
  have selected: "comma_fixed_iter f j ?source = comma_symbolic_entry_cut f p delta offset j"
    using comma_fixed_iter_displacement[of f j ?source] repeated digit
    by (simp add: comma_symbolic_entry_cut_def Let_def P_def L_def)
  have edges: "\<forall>i<steps. comma_child (comma_fixed_iter f i ?source)
      (comma_fixed_iter f (Suc i) ?source)"
    using comma_entry_chart_exact_literal_path(5)[OF sector exponent offset, of delta]
    by (simp add: h_def P_def L_def steps_def)
  have endpoint: "comma_fixed_iter f steps ?source = comma_chart_value p (Comma_Near f delta h)"
    using comma_fixed_iter_complete_cycles[OF closes, of ?c ?source]
      comma_entry_chart_exact_literal_path(3)[OF sector exponent offset, of delta] period
    by (simp add: h_def P_def L_def steps_def)
  show "comma_literal_path j ?source (comma_symbolic_entry_cut f p delta offset j)"
    using comma_fixed_interval_literal[OF edges, of 0 j] cut selected by simp
  show "comma_literal_path (steps-j) (comma_symbolic_entry_cut f p delta offset j)
      (comma_chart_value p (Comma_Near f delta h))"
    using comma_fixed_interval_literal[OF edges, of j "steps-j"] cut selected endpoint by simp
qed


lemma comma_symbolic_entry_cut_zero:
  "comma_symbolic_entry_cut f p delta offset 0 =
    comma_chart_value p (Comma_Entry f delta offset)"
  by (simp add: comma_symbolic_entry_cut_def Let_def comma_period_displacement_def)

lemma comma_symbolic_entry_cut_first_sample:
  "comma_symbolic_entry_cut 2 5 0 0 1 = 200002"
  by (simp add: comma_symbolic_entry_cut_def comma_cycle_length_def
      comma_period_displacement_def comma_chart_value_def Let_def)

lemma comma_symbolic_entry_cut_seam_sample:
  "comma_symbolic_entry_cut 2 5 0 0 2380 = 299960"
  by (simp add: comma_symbolic_entry_cut_def comma_cycle_length_def
      comma_finite_period_def comma_period_displacement_def comma_chart_value_def Let_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_fixed_interval_literal
    comma_symbolic_entry_cut_exact comma_symbolic_entry_cut_zero}) then ()
    else error "Symbolic Entry cut used an oracle";
  val _ = if Thm_Deps.has_skip_proof @{thms comma_fixed_interval_literal comma_symbolic_entry_cut_exact comma_symbolic_entry_cut_zero} then
    error "Symbolic writer theorem used a skipped proof" else ();
\<close>

end
