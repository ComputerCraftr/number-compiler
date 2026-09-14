theory Antihydra_Source_Barrier
  imports Antihydra_Mahler_Skew
begin

text \<open>This theory states the source-bound barrier on the actual
source-generated Mahler orbit.  It proves the finite accounting equivalence;
it does not assume or claim the still-open all-time source-7 inequality.\<close>

fun mahler_orbit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_orbit D 0 = D"
| "mahler_orbit D (Suc n) = mahler_D_step (mahler_orbit D n)"

lemma mahler_orbit_shift:
  "mahler_orbit D (Suc n) = mahler_orbit (mahler_D_step D) n"
  by (induct n arbitrary: D) simp_all

theorem moving_source_cylinder:
  assumes "n \<le> N"
  shows "mahler_orbit (D + k * 2^N) n =
    mahler_orbit D n + k * 2^(N-n) * 3^n"
using assms
proof (induct n arbitrary: N D k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain M where Nform: "N = Suc M"
    by (cases N) auto
  have nM: "n \<le> M" using Suc.prems Nform by simp
  have first: "mahler_D_step (D + k * 2^N) =
      mahler_D_step D + (3*k) * 2^M"
    using Nform mahler_D_step_even_lift[of D "k*2^M"]
    by (simp add: power_Suc algebra_simps)
  have IH: "mahler_orbit (mahler_D_step D + (3*k) * 2^M) n =
      mahler_orbit (mahler_D_step D) n +
        (3*k) * 2^(M-n) * 3^n"
    by (rule Suc.hyps[OF nM])
  have orbit_eq: "mahler_orbit (mahler_D_step D) n =
      mahler_orbit D (Suc n)"
    by (rule sym, rule mahler_orbit_shift)
  have "mahler_orbit (D + k * 2^N) (Suc n) =
      mahler_orbit (mahler_D_step D + (3*k) * 2^M) n"
    by (simp only: mahler_orbit_shift first)
  also have "\<dots> = mahler_orbit (mahler_D_step D) n +
      (3*k) * 2^(M-n) * 3^n" by (rule IH)
  also have "\<dots> = mahler_orbit D (Suc n) +
      k * 2^(N-Suc n) * 3^(Suc n)"
    using Nform by (simp only: orbit_eq power_Suc Suc_diff_Suc)
      (simp add: algebra_simps)
  finally show ?case .
qed

fun odd_events :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "odd_events D 0 = 0"
| "odd_events D (Suc n) =
    odd_events D n + (mahler_orbit D n mod 2)"

fun ledger_at :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "ledger_at D 0 = 0"
| "ledger_at D (Suc n) = ledger_at D n +
    (if odd (mahler_orbit D n) then 2 else -1)"

lemma parity_indicator:
  "(if odd n then (2::int) else -1) = 3 * int (n mod 2) - 1"
proof (cases "n mod 2")
  case 0
  then show ?thesis by (simp add: odd_iff_mod_2_eq_one)
next
  case (Suc r)
  have "n mod 2 < 2" by simp
  with Suc have "n mod 2 = 1" by arith
  then show ?thesis by (simp add: odd_iff_mod_2_eq_one)
qed

theorem ledger_event_accounting:
  "ledger_at D n = 3 * int (odd_events D n) - int n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: parity_indicator algebra_simps)
qed

theorem source_bound_barrier_soundness:
  "0 \<le> ledger_at D n \<longleftrightarrow> n \<le> 3 * odd_events D n"
proof -
  have cast_product: "(3::int) * int (odd_events D n) =
      int (3 * odd_events D n)" by simp
  have cast_iff: "int n \<le> 3 * int (odd_events D n) \<longleftrightarrow>
      n \<le> 3 * odd_events D n"
    by (simp only: cast_product of_nat_le_iff)
  show ?thesis
    unfolding ledger_event_accounting[of D n]
    using cast_iff by simp
qed

corollary source_seven_all_time_barrier_exactly:
  "(\<forall>n. 0 \<le> ledger_at 7 n) \<longleftrightarrow>
    (\<forall>n. n \<le> 3 * odd_events 7 n)"
  by (simp add: source_bound_barrier_soundness)

definition source_seven_barrier_open :: bool where
  "source_seven_barrier_open \<longleftrightarrow> (\<forall>n. n \<le> 3 * odd_events 7 n)"

text \<open>No theorem below discharges @{term source_seven_barrier_open}.
Doing so requires an infinitary argument for the single compatible source,
not a finite cylinder census or a supplied safe itinerary.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms parity_indicator ledger_event_accounting
      mahler_orbit_shift moving_source_cylinder
      source_bound_barrier_soundness source_seven_all_time_barrier_exactly}) then ()
    else error "Antihydra source-barrier proof depends on an oracle";
\<close>

end
