theory Comma_Decade_Observation
  imports Comma_Weighted_Round.Comma_Weighted_Round
begin

text \<open>The demanded decade result is a projection of the weighted round.
This downstream bridge avoids an import cycle through the older decade
specification. It does not introduce a second transition implementation.\<close>

definition comma_decade_observed_control ::
  "comma_decade_state \<Rightarrow> comma_decade_outcome" where
  "comma_decade_observed_control s =
    (case s of Comma_Decade r x \<Rightarrow>
      case comma_round_observation r (Comma_Entry 1 0 x) of
        (n,t,result) \<Rightarrow> comma_decade_decode r result)"

lemma comma_decade_observed_control_eq:
  assumes "comma_decade_admitted s"
  shows "comma_decade_observed_control s = comma_decade_control s"
proof (cases s)
  case (Comma_Decade r x)
  have admitted: "comma_round_admitted (Comma_Entry 1 0 x)"
    using assms by (simp add: Comma_Decade)
  show ?thesis
    by (simp only: Comma_Decade comma_decade_observed_control_def
      comma_decade_state.case comma_decade_control.simps
      comma_round_observation_control[OF admitted])
qed

lemma comma_decade_observed_from_round:
  assumes "comma_round_observation r (Comma_Entry 1 0 x) = (n,t,event)"
  shows "comma_decade_observed_control (Comma_Decade r x) =
    comma_decade_decode r event"
  by (simp only: comma_decade_observed_control_def comma_decade_state.case
    assms prod.case)

definition comma_decade_observed_rank_step ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> comma_decade_state \<Rightarrow> bool" where
  "comma_decade_observed_rank_step rank s =
    (case comma_decade_observed_control s of
      Comma_Decade_Continue q \<Rightarrow> comma_decade_admitted q \<and> rank q < rank s
    | Comma_Decade_Invalid \<Rightarrow> False
    | _ \<Rightarrow> True)"

lemma comma_decade_observed_rank_check:
  "comma_decade_rank_check rank =
    (\<forall>s. comma_decade_admitted s \<longrightarrow> comma_decade_observed_rank_step rank s)"
  unfolding comma_decade_rank_check_def comma_decade_observed_rank_step_def
  by (simp add: comma_decade_observed_control_eq)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_observed_control_eq comma_decade_observed_from_round
      comma_decade_observed_rank_check}) then ()
    else error "Decade observation bridge depends on an oracle";
\<close>
end
