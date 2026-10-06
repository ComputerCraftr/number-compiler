theory Shared_Affine_Birth_Tape
  imports Main
begin

text \<open>Generic affine source transport over a supplied event/birth tape.
This algebra composes occurrences; it does not select recurrence events or
construct source-dependent births.\<close>

definition harmonic_multiplier :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "harmonic_multiplier u y e = u ^ e * y"

lemma harmonic_multiplier_product:
  fixes u y :: "'a::comm_ring_1"
  shows "prod_list (map (harmonic_multiplier u y) es) =
    u ^ sum_list es * y ^ length es"
  by (induction es) (simp_all add: harmonic_multiplier_def power_add
      power_Suc algebra_simps)

theorem five_step_linear_harmonic_source_death:
  fixes u y :: "'a::comm_ring_1"
  assumes nilpotent: "y ^ 5 = 0"
      and five_events: "length es = 5"
  shows "prod_list (map (harmonic_multiplier u y) es) = 0"
  using harmonic_multiplier_product[of u y es] nilpotent five_events by simp

fun harmonic_run ::
    "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "harmonic_run u y [] source = source"
| "harmonic_run u y ((e,birth) # events) source =
    harmonic_run u y events (harmonic_multiplier u y e * source + birth)"

lemma harmonic_run_source_difference:
  fixes u y :: "'a::comm_ring_1"
  shows "harmonic_run u y events source - harmonic_run u y events other =
    prod_list (map (\<lambda>event. harmonic_multiplier u y (fst event)) events) *
      (source - other)"
proof (induction events arbitrary: source other)
  case Nil
  then show ?case by simp
next
  case (Cons event events)
  obtain e birth where event: "event = (e,birth)" by (cases event)
  let ?m = "harmonic_multiplier u y e"
  let ?tail =
    "prod_list (map (\<lambda>item. harmonic_multiplier u y (fst item)) events)"
  have difference:
      "harmonic_run u y events (?m * source + birth) -
        harmonic_run u y events (?m * other + birth) =
        ?tail * ((?m * source + birth) - (?m * other + birth))"
    by (rule Cons.IH)
  also have "... = (?m * ?tail) * (source - other)"
    by (simp add: algebra_simps)
  finally show ?case
    by (simp add: event algebra_simps)
qed

corollary five_step_same_birth_source_independence:
  fixes u y :: "'a::comm_ring_1"
  assumes nilpotent: "y ^ 5 = 0"
      and five_events: "length events = 5"
  shows "harmonic_run u y events source = harmonic_run u y events other"
proof -
  have exponents: "length (map fst events) = 5" using five_events by simp
  have zero: "prod_list (map (harmonic_multiplier u y) (map fst events)) = 0"
    using five_step_linear_harmonic_source_death[OF nilpotent exponents] .
  have zero_expanded:
      "prod_list (map (\<lambda>event. harmonic_multiplier u y (fst event)) events) = 0"
    using zero by (simp add: comp_def)
  have "harmonic_run u y events source - harmonic_run u y events other = 0"
    using harmonic_run_source_difference[of u y events source other]
      zero_expanded by simp
  then show ?thesis by simp
qed


lemma harmonic_run_append:
  "harmonic_run u y (prefix @ suffix) source =
    harmonic_run u y suffix (harmonic_run u y prefix source)"
  by (induction prefix arbitrary: source) (auto split: prod.splits)

corollary last_five_births_erase_earlier_jet:
  fixes u y :: "'a::comm_ring_1"
  assumes "y ^ 5 = 0" "length suffix = 5"
  shows "harmonic_run u y (prefix @ suffix) source =
    harmonic_run u y suffix 0"
  unfolding harmonic_run_append
  by (rule five_step_same_birth_source_independence[OF assms])

theorem at_least_five_births_source_independence:
  fixes u y :: "'a::comm_ring_1"
  assumes nilpotent: "y ^ 5 = 0" and enough: "5 \<le> length events"
  shows "harmonic_run u y events source = harmonic_run u y events other"
proof -
  have five: "length (take 5 events) = 5" using enough by simp
  have equal: "harmonic_run u y (take 5 events) source =
      harmonic_run u y (take 5 events) other"
    by (rule five_step_same_birth_source_independence[OF nilpotent five])
  have split: "events = take 5 events @ drop 5 events" by simp
  show ?thesis
    using equal by (subst (1 2) split) (simp only: harmonic_run_append)
qed

corollary annihilated_jet_future_consumer:
  fixes u y :: "'a::comm_ring_1"
  assumes "y ^ 5 = 0" "5 \<le> length events"
  shows "observe (harmonic_run u y (events @ future) source) =
    observe (harmonic_run u y (events @ future) other)"
  using at_least_five_births_source_independence[OF assms, of u source other]
  by (simp only: harmonic_run_append)

ML \<open>
  val checked = @{thms harmonic_multiplier_product
    five_step_linear_harmonic_source_death harmonic_run_source_difference
    five_step_same_birth_source_independence harmonic_run_append
    last_five_births_erase_earlier_jet at_least_five_births_source_independence
    annihilated_jet_future_consumer};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared affine birth-tape proof depends on an oracle";
\<close>

end
