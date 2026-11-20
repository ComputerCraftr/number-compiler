theory Five_Reverse
  imports Shared_Carry_Dynamics.Shared_Decimal_Reversal
    Shared_Carry_Dynamics.Shared_Closed_Arithmetic
begin

text \<open>
The source recurrence here is 5 times ordinary decimal reversal.  This
finite theorem certifies the four-step window beginning at seed 196,
generation 180.  It does not claim a periodic orbit or admit any later step.
\<close>

definition five_reverse_step :: "nat \<Rightarrow> nat" where
  "five_reverse_step n = 5 * decimal_reverse n"

fun five_reverse_orbit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_reverse_orbit 0 seed = seed"
| "five_reverse_orbit (Suc n) seed =
    five_reverse_step (five_reverse_orbit n seed)"

definition five_reverse_inlet :: "nat \<Rightarrow> nat" where
  "five_reverse_inlet n = ((n div 1000) mod 10) div 2"

definition five_reverse_border :: "nat \<Rightarrow> nat \<times> nat" where
  "five_reverse_border n =
    (n div 10^(decimal_digit_count n - 3), n mod 1000)"

definition five_reverse_window_port ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> (nat \<times> nat) \<times> (nat \<times> nat)" where
  "five_reverse_window_port seed generation =
    (five_reverse_inlet (five_reverse_orbit generation seed),
      five_reverse_border (five_reverse_orbit generation seed),
      five_reverse_border (five_reverse_orbit (Suc generation) seed))"

fun five_reverse_window_ports_from_states ::
    "nat list \<Rightarrow>
      (nat \<times> (nat \<times> nat) \<times> (nat \<times> nat)) list" where
  "five_reverse_window_ports_from_states [] = []"
| "five_reverse_window_ports_from_states [final_state] = []"
| "five_reverse_window_ports_from_states (source # target # rest) =
    (five_reverse_inlet source, five_reverse_border source,
      five_reverse_border target) #
        five_reverse_window_ports_from_states (target # rest)"

definition five_reverse_seed196_window_states :: "nat list" where
  "five_reverse_seed196_window_states =
    map (\<lambda>generation. five_reverse_orbit generation 196) [180..<185]"

definition five_reverse_seed196_window_generations :: "nat list" where
  "five_reverse_seed196_window_generations = [180..<184]"

lemma five_reverse_seed196_window_has_four_steps:
  "length five_reverse_seed196_window_generations = 4"
  by (simp add: five_reverse_seed196_window_generations_def)

ML \<open>
  val checked = @{thms five_reverse_step_def five_reverse_orbit.simps
    five_reverse_inlet_def five_reverse_border_def
    five_reverse_window_port_def five_reverse_window_ports_from_states.simps
    five_reverse_seed196_window_states_def
    five_reverse_seed196_window_generations_def
    five_reverse_seed196_window_has_four_steps};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse recurrence definitions depend on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse recurrence proof" else ();
\<close>

end
