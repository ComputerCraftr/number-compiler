theory Double_Reverse_Periodic_Ring_Action
  imports Double_Reverse_Temporal_Refinement
begin

text \<open>The NC15 periodic-core executor applies the exact T-squared local
digit law to a finite cyclic word after an external source certificate proves
that the demanded causal cones stay inside a periodic interior.  This theory
formalizes that finite action and its temporal powering.  A cycle premise is
an explicit certificate input: the finite ring itself does not prove that an
arbitrary integer source has a periodic interior or an indefinitely recurring
finite-source boundary.\<close>

definition double_reverse_ring_digit :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_ring_digit word i = word ! (i mod length word)"

definition double_reverse_ring_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_ring_step word =
    map (\<lambda>i. double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))) [0..<length word]"

lemma double_reverse_ring_step_length:
  "length (double_reverse_ring_step word) = length word"
  by (simp add: double_reverse_ring_step_def)

lemma double_reverse_ring_step_cell:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i =
    double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))"
  using assms
  by (simp add: double_reverse_ring_step_def double_reverse_ring_digit_def)

lemma double_reverse_ring_step_digits:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i < 10"
  using double_reverse_ring_step_cell[OF assms]
  by (simp add: double_reverse_t2_digit_def)

definition double_reverse_ring_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_ring_run steps word =
    (double_reverse_ring_step ^^ steps) word"

lemma double_reverse_ring_run_add:
  "double_reverse_ring_run (first + second) word =
    double_reverse_ring_run second (double_reverse_ring_run first word)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_ring_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

definition double_reverse_ring_cycle :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_ring_cycle period word \<longleftrightarrow>
    0 < period \<and> double_reverse_ring_run period word = word"

theorem double_reverse_ring_cycle_repeats:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (period * count) word = word"
proof (induction count)
  case 0
  then show ?case by (simp add: double_reverse_ring_run_def)
next
  case (Suc count)
  have cycle_step: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have arithmetic: "period * Suc count = period * count + period"
    by (simp add: algebra_simps)
  show ?case
    using Suc.IH cycle_step
    by (simp only: arithmetic double_reverse_ring_run_add Suc.IH cycle_step)
qed

theorem double_reverse_ring_cycle_future_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (time + period) word =
    double_reverse_ring_run time word"
proof -
  have state_cycle: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have reindex: "time + period = period + time" by (simp add: add.commute)
  have cyclic:
    "double_reverse_ring_run (period + time) word =
      double_reverse_ring_run time
        (double_reverse_ring_run period word)"
    by (rule double_reverse_ring_run_add)
  have final_state:
    "double_reverse_ring_run time
        (double_reverse_ring_run period word) =
      double_reverse_ring_run time word"
    using state_cycle by simp
  show ?thesis
    by (subst reindex; simp only: cyclic final_state)
qed

corollary double_reverse_ring_observation_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
      and coordinate: "i < length word"
  shows "double_reverse_ring_run (time + period) word ! i =
    double_reverse_ring_run time word ! i"
  using double_reverse_ring_cycle_future_periodic[OF cycle, of time]
  by simp

text \<open>Thus a certified ring cycle is a complete future quotient for the
ring's emitted digit word, and any projection of that word inherits the same
powered action.  Connecting a finite source interval to this ring remains a
separate causal-halo refinement obligation; the ring-period theorem alone is
not authority to publish digits outside that certified interval.\<close>

ML \<open>
  val checked = @{thms double_reverse_ring_step_length
    double_reverse_ring_step_cell double_reverse_ring_step_digits
    double_reverse_ring_run_add double_reverse_ring_cycle_repeats
    double_reverse_ring_cycle_future_periodic
    double_reverse_ring_observation_periodic};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse periodic ring action depends on an oracle";
\<close>

end
