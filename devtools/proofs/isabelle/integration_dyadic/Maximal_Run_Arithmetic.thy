theory Maximal_Run_Arithmetic
  imports Balanced_Dyadic_Families
begin

text \<open>Finite homogeneous runs underlying the production run quotient.
The Antihydra source coordinate is a=D+1. Its source parity is the
complement of the centered parity used by arithmetic_images.py.
These are arithmetic run and source-word refinements, not a bound on the
number of runs, a global safety assertion, or a Python constructor proof.\<close>

lemma antihydra_run_even_source_step:
  "antihydra_family_step (2*v) = 3*v"
  by (simp add: antihydra_family_step_def; arith)

lemma antihydra_run_odd_source_step:
  "antihydra_family_step (2*v+1) = 3*v+1"
  by (simp add: antihydra_family_step_def; arith)

lemma antihydra_centered_odd_run_orbit:
  "antihydra_family_orbit (2^k*u) k = 3^k*u"
proof (induction k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have step: "antihydra_family_step (2^Suc k*u) = 2^k*(3*u)"
    by (simp add: power_Suc antihydra_run_even_source_step mult.assoc mult.left_commute)
  show ?case
    by (simp only: antihydra_family_orbit.simps step Suc.IH; simp add: power_Suc algebra_simps)
qed

lemma antihydra_centered_odd_run_bits:
  "antihydra_family_bits (2^k*u) k = replicate k 0"
proof (induction k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have step: "antihydra_family_step (2^Suc k*u) = 2^k*(3*u)"
    by (simp add: power_Suc antihydra_run_even_source_step mult.assoc mult.left_commute)
  show ?case
    by (simp only: antihydra_family_bits.simps step Suc.IH replicate_Suc; simp add: power_Suc algebra_simps)
qed

lemmas antihydra_centered_odd_run =
  antihydra_centered_odd_run_orbit antihydra_centered_odd_run_bits

lemma antihydra_centered_even_run_orbit:
  "antihydra_family_orbit (2^k*u+1) k = 3^k*u+1"
proof (induction k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have step: "antihydra_family_step (2^Suc k*u+1) = 2^k*(3*u)+1"
    by (simp only: power_Suc mult.assoc antihydra_run_odd_source_step; simp add: algebra_simps)
  show ?case
    by (simp only: antihydra_family_orbit.simps step Suc.IH; simp add: power_Suc algebra_simps)
qed

lemma antihydra_centered_even_run_bits:
  "antihydra_family_bits (2^k*u+1) k = replicate k 1"
proof (induction k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have step: "antihydra_family_step (2^Suc k*u+1) = 2^k*(3*u)+1"
    by (simp only: power_Suc mult.assoc antihydra_run_odd_source_step; simp add: algebra_simps)
  have bit: "(2^Suc k*u+1) mod 2 = 1"
    by (simp only: power_Suc mult.assoc; presburger)
  show ?case
    by (simp only: antihydra_family_bits.simps step Suc.IH replicate_Suc bit)
qed

lemmas antihydra_centered_even_run =
  antihydra_centered_even_run_orbit antihydra_centered_even_run_bits

lemma homogeneous_ledger_zero:
  "ledger_word_delta (replicate k 0) = 2*int k"
  "ledger_word_minprefix (replicate k 0) = 0"
  by (induction k) (simp_all)

lemma homogeneous_ledger_one:
  "ledger_word_delta (replicate k 1) = -int k"
  "ledger_word_minprefix (replicate k 1) = -int k"
  by (induction k) (simp_all add: min_def)

corollary antihydra_centered_odd_run_ledger:
  "antihydra_family_balance (2^k*u) 0 k = 2*int k"
  "antihydra_family_minimum (2^k*u) 0 k = 0"
proof -
  show "antihydra_family_balance (2^k*u) 0 k = 2*int k"
    by (simp only: antihydra_family_balance_def antihydra_family_minimum_def
      antihydra_centered_odd_run homogeneous_ledger_zero; simp)
  show "antihydra_family_minimum (2^k*u) 0 k = 0"
    by (simp only: antihydra_family_balance_def antihydra_family_minimum_def
      antihydra_centered_odd_run homogeneous_ledger_zero; simp)
qed

corollary antihydra_centered_even_run_ledger:
  "antihydra_family_balance (2^k*u+1) 0 k = -int k"
  "antihydra_family_minimum (2^k*u+1) 0 k = -int k"
proof -
  show "antihydra_family_balance (2^k*u+1) 0 k = -int k"
    by (simp only: antihydra_family_balance_def antihydra_family_minimum_def
      antihydra_centered_even_run homogeneous_ledger_one; simp)
  show "antihydra_family_minimum (2^k*u+1) 0 k = -int k"
    by (simp only: antihydra_family_balance_def antihydra_family_minimum_def
      antihydra_centered_even_run homogeneous_ledger_one; simp)
qed

corollary antihydra_centered_run_endpoints:
  "antihydra_family_orbit (2^k*u+1) k - 1 = 3^k*u"
  "antihydra_family_orbit (2^k*u) k - 1 = 3^k*u-1"
proof -
  show "antihydra_family_orbit (2^k*u+1) k - 1 = 3^k*u"
    by (simp only: antihydra_centered_even_run antihydra_centered_odd_run; simp)
  show "antihydra_family_orbit (2^k*u) k - 1 = 3^k*u-1"
    by (simp only: antihydra_centered_even_run antihydra_centered_odd_run; simp)
qed

corollary antihydra_centered_run_guards:
  "antihydra_block_safe (2^k*u+1) initial k \<longleftrightarrow> int k \<le> initial"
  "antihydra_block_safe (2^k*u) initial k \<longleftrightarrow> 0 \<le> initial"
proof -
  show "antihydra_block_safe (2^k*u+1) initial k \<longleftrightarrow> int k \<le> initial"
    by (simp only: antihydra_block_safe_def antihydra_family_minimum_def
      antihydra_centered_even_run antihydra_centered_odd_run
      homogeneous_ledger_one homogeneous_ledger_zero; simp)
  show "antihydra_block_safe (2^k*u) initial k \<longleftrightarrow> 0 \<le> initial"
    by (simp only: antihydra_block_safe_def antihydra_family_minimum_def
      antihydra_centered_even_run antihydra_centered_odd_run
      homogeneous_ledger_one homogeneous_ledger_zero; simp)
qed

text \<open>At an odd Collatz source, one normalized odd symbol uses an
odd physical step followed by an even physical step. Positivity prevents
natural subtraction at the source boundary from saturating.\<close>

lemma collatz_odd_pair_run_step:
  assumes "0 < v"
  shows "physical_collatz (physical_collatz (2*v-1)) = 3*v-1"
proof -
  have source_odd: "odd (2*v-1)" using assms by presburger
  have first: "physical_collatz (2*v-1) = 2*(3*v-1)"
    using assms source_odd unfolding physical_collatz_def by presburger
  show ?thesis by (simp only: first; simp add: physical_collatz_def)
qed

lemma collatz_physical_odd_run:
  assumes "0 < u"
  shows "(physical_collatz ^^ (2*k)) (2^k*u-1) = 3^k*u-1"
  using assms
proof (induction k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have positive: "0 < 2^k*u" using Suc.prems by simp
  have pair: "physical_collatz (physical_collatz (2^Suc k*u-1)) =
      2^k*(3*u)-1"
    using collatz_odd_pair_run_step[OF positive]
    by (simp add: power_Suc algebra_simps)
  have ih: "(physical_collatz ^^ (2*k)) (2^k*(3*u)-1) = 3^k*(3*u)-1"
    using Suc.IH[of "3*u"] Suc.prems by simp
  have two: "(physical_collatz ^^ 2) (2^Suc k*u-1) = 2^k*(3*u)-1"
    using pair by (simp add: numeral_2_eq_2)
  have extent: "2*Suc k = 2*k+2" by simp
  have decompose: "(physical_collatz ^^ (2*Suc k)) (2^Suc k*u-1) =
      (physical_collatz ^^ (2*k)) ((physical_collatz ^^ 2) (2^Suc k*u-1))"
    by (simp only: extent funpow_add comp_apply)
  have endpoint: "(physical_collatz ^^ (2*Suc k)) (2^Suc k*u-1) = 3^k*(3*u)-1"
    by (simp only: decompose two ih)
  show ?case using endpoint by (simp only: power_Suc; simp add: algebra_simps)
qed

corollary collatz_physical_odd_run_boundary:
  assumes "x+1 = 2^k*u" "0 < u"
  shows "(physical_collatz ^^ (2*k)) x = 3^k*u-1"
proof -
  have source: "x = 2^k*u-1" using assms(1) by presburger
  show ?thesis unfolding source
    by (rule collatz_physical_odd_run[OF assms(2)])
qed

corollary collatz_physical_even_run:
  "(physical_collatz ^^ k) (2^k*u) = u"
  by (rule physical_collatz_removes_dyadic_prefix)

text \<open>An odd residual u certifies a parity switch at the endpoint;
thus a fully consumed dyadic factor is maximal. A truncated block need
not satisfy this residual hypothesis.\<close>

lemma antihydra_run_endpoint_parity:
  assumes "odd u"
  shows "odd (antihydra_family_orbit (2^k*u) k)"
    "even (antihydra_family_orbit (2^k*u+1) k)"
proof -
  show "odd (antihydra_family_orbit (2^k*u) k)"
    using assms by (simp only: antihydra_centered_odd_run; simp)
  show "even (antihydra_family_orbit (2^k*u+1) k)"
    using assms by (simp only: antihydra_centered_even_run; simp)
qed

text \<open>A named zero-to-one puncture contracts one even centered run
and its terminating odd step. The source is authenticated by its dyadic
factor, not by an anonymous harmonic fiber. These formulas refine the bounded
event branch in arithmetic_images.py; they do not bound the number of events.\<close>

lemma antihydra_punctured_event_bits:
  "antihydra_family_bits (2^k*(2*M+1)+1) (Suc k) =
    replicate k 1 @ [0]"
proof -
  have ending: "(3^k*(2*M+1)+1) mod 2 = 0" by simp
  show ?thesis
    by (simp only: antihydra_family_bits_Suc_right
      antihydra_centered_even_run_bits antihydra_centered_even_run_orbit ending)
qed

lemma antihydra_punctured_event_endpoint:
  "antihydra_family_orbit (2^k*(2*M+1)+1) (Suc k) - 1 =
    3^(Suc k)*M + (3^(Suc k)+1) div 2"
proof -
  have odd: "odd (3^k :: nat)" by simp
  obtain j :: nat where power: "3^k = 2*j+1"
    by (rule oddE[OF odd])
  have source: "3^k*(2*M+1)+1 = 2*((2*j+1)*M+j+1)"
    by (simp only: power; simp add: algebra_simps)
  have next_power: "3^(Suc k)+1 = 2*(3*j+2)"
    by (simp only: power_Suc power; simp add: algebra_simps)
  have half: "(3^(Suc k)+1) div 2 = 3*j+2"
    by (simp only: next_power; simp)
  have endpoint: "antihydra_family_orbit (2^k*(2*M+1)+1) (Suc k) =
      3*((2*j+1)*M+j+1)"
    by (simp only: antihydra_family_orbit_Suc_right
      antihydra_centered_even_run_orbit source antihydra_run_even_source_step)
  have centered: "3*((2*j+1)*M+j+1) = Suc (3*(2*j+1)*M+3*j+2)"
    by (simp add: algebra_simps)
  have target: "3^(Suc k)*M + (3^(Suc k)+1) div 2 =
      3*(2*j+1)*M+3*j+2"
    by (simp only: half; simp only: power_Suc power; simp add: algebra_simps)
  show ?thesis
    by (simp only: endpoint centered target; simp)
qed

lemma antihydra_punctured_event_ledger:
  "antihydra_family_balance (2^k*(2*M+1)+1) 0 (Suc k) = 2-int k"
  "antihydra_family_minimum (2^k*(2*M+1)+1) 0 (Suc k) = -int k"
proof -
  have delta: "ledger_word_delta (replicate k 1 @ [0]) = 2-int k"
    by (simp only: ledger_word_delta_append homogeneous_ledger_one;
      simp)
  have minimum: "ledger_word_minprefix (replicate k 1 @ [0]) = -int k"
    by (simp only: ledger_word_minprefix_append homogeneous_ledger_one;
      simp)
  show "antihydra_family_balance (2^k*(2*M+1)+1) 0 (Suc k) = 2-int k"
    by (simp only: antihydra_family_balance_def antihydra_punctured_event_bits delta;
      simp)
  show "antihydra_family_minimum (2^k*(2*M+1)+1) 0 (Suc k) = -int k"
    by (simp only: antihydra_family_minimum_def antihydra_punctured_event_bits minimum;
      simp)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms antihydra_centered_odd_run antihydra_centered_even_run
      antihydra_centered_odd_run_ledger antihydra_centered_even_run_ledger
      collatz_physical_odd_run collatz_physical_odd_run_boundary
      collatz_physical_even_run antihydra_run_endpoint_parity
      antihydra_centered_run_endpoints antihydra_centered_run_guards
      antihydra_punctured_event_bits antihydra_punctured_event_endpoint
      antihydra_punctured_event_ledger})
    then () else error "Maximal run arithmetic depends on an oracle";
\<close>

end
