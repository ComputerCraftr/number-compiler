theory Comma_Normalized_Cycle
  imports Comma_Arithmetic.Comma_Finite_Period Comma_Arithmetic.Comma_Boundary_Primitives
begin

text \<open>Executable normal form used by cycle_actions.normalized_cycle.
The three fields are literal duration, displacement, and strict guard. An
occurrence value, index, and certificate binding are deliberately absent.
This theorem is about complete interior cycles, not future branch selection.
All copies are normalized before publication, without a temporal child tree.\<close>

definition comma_normalized_cycle :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "comma_normalized_cycle f d c =
    (let P = c * comma_finite_period f d
     in (c * comma_cycle_length f, P, P + (if f < 9 then 1 else 0)))"

lemma comma_finite_period_gcd_normalization:
  "comma_finite_period f d = comma_finite_period f (d mod gcd f 10)"
  unfolding comma_finite_period_def by (simp add: Let_def)

text \<open>The summary is unchanged when its incoming decimal displacement is
reduced modulo gcd(f,10). This equates only the normalized arithmetic cycle
record. It does not transfer future branch behavior across boundary seams.\<close>

lemma comma_normalized_cycle_gcd_normalization:
  "comma_normalized_cycle f d c =
    comma_normalized_cycle f (d mod gcd f 10) c"
  by (simp add: comma_normalized_cycle_def comma_finite_period_def Let_def)

lemma comma_normalized_cycle_refines:
  assumes sector: "1 \<le> f" "f \<le> 9" and phase: "d < 10"
    and copies: "0 < c"
  shows "comma_normalized_cycle f d c =
    (c * comma_cycle_length f,
     comma_period_displacement f d (c * comma_cycle_length f),
     comma_phase_max_guard f d (c * comma_cycle_length f))"
proof -
  have closes: "10 dvd comma_cycle_length f * f"
    using comma_cycle_length_admitted(2)[OF sector] .
  have positive: "0 < c * comma_cycle_length f"
    using copies comma_cycle_length_admitted(1)[OF sector] by simp
  have displacement: "comma_period_displacement f d (c * comma_cycle_length f) =
      c * comma_finite_period f d"
    using comma_period_displacement_repeated[OF closes, of d c 0]
      comma_finite_period_refines[OF sector phase]
    by (simp add: comma_period_displacement_def)
  show ?thesis
    using comma_phase_max_guard_closed[OF positive sector(2), of d] displacement
    by (simp add: comma_normalized_cycle_def Let_def)
qed

lemma comma_normalized_cycle_join:
  assumes "comma_normalized_cycle f d a = (ta,pa,ga)"
    "comma_normalized_cycle f d b = (tb,pb,gb)"
  shows "comma_normalized_cycle f d (a+b) = (ta+tb,pa+pb,pa+gb)"
  using assms by (auto simp: comma_normalized_cycle_def Let_def algebra_simps)

lemma comma_normalized_cycle_parenthesization:
  "comma_normalized_cycle f d ((a+b)+c) =
   comma_normalized_cycle f d (a+(b+c))"
  by (simp only: add.assoc)

lemma comma_normalized_cycle_receiving_guard:
  assumes sector: "1 \<le> f" "f \<le> 9" and phase: "d < 10"
    and copies: "0 < c"
    and action: "comma_normalized_cycle f d c = (steps, displacement, guard)"
    and admission: "guard < H" and prefix: "j < steps"
  shows "comma_phase_guard_at f d j < H"
proof -
  have fields: "steps = c * comma_cycle_length f"
    "guard = comma_phase_max_guard f d (c * comma_cycle_length f)"
    using action comma_normalized_cycle_refines[OF sector phase copies] by auto
  show ?thesis
    using comma_phase_guard_below_max[of j steps f d] prefix admission fields
    by simp
qed

text \<open>The guard is rebound at every receiving source. Equal arithmetic
summaries do not equate occurrences or authorize any branch at a seam. Zero
copies use the separate arena identity; this positive-copy normal form must
not be used as its guard. Construction uses a fixed number of integer
operations; their bit complexity still depends on the copy count.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_period_gcd_normalization
      comma_normalized_cycle_gcd_normalization comma_normalized_cycle_refines
      comma_normalized_cycle_join
      comma_normalized_cycle_parenthesization comma_normalized_cycle_receiving_guard})
    then () else error "Normalized comma cycle depends on an oracle";
\<close>

end
