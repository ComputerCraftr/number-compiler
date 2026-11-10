theory Comma_Semantic_Initial_Prefix
  imports Comma_Semantic_Future.Comma_Semantic_Boundary
begin

text \<open>
The initial source prefix is determined by the admitted finite transition and
closed control germ. This contract retains exact calls, physical trace,
terminal event, and crossing phase; packet action authority is a separate
consumer concern.
\<close>

theorem comma_semantic_future_initial_round_prefix_closed:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
  obtains calls steps terminal event where
    "comma_round_control_germ_calls (snd (snd q))
      (comma_finite_initial q) calls"
    "calls \<le> 9"
    "comma_round_control_germ (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,terminal,event)"
    "comma_round_prefix_steps steps (snd (snd q))
      (comma_finite_initial q) terminal"
    "(\<exists>a d. event = Comma_Round_Fork a d) \<or>
      (\<exists>d. event = Comma_Round_Landmine d) \<or>
      (\<exists>x. x\<le>90 \<and>
        event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
        comma_normalize_position (snd (snd q)) (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((snd (snd q)+1) mod 924) x)"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  let ?initial = "comma_finite_initial q"
  have source_admitted: "comma_round_admitted ?initial"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  obtain calls where calls:
      "comma_round_control_germ_calls r ?initial calls"
    and calls_bound: "calls\<le>9"
    using comma_round_control_germ_at_most_nine_sectors[OF source_admitted]
    by blast
  obtain steps terminal event where close:
      "comma_round_close r ?initial=(steps,terminal,event)"
    by (cases "comma_round_close r ?initial") auto
  have trace:
      "comma_round_prefix_steps steps r ?initial terminal"
    using comma_round_close_refines_trace[OF close] by simp
  have germ:
      "comma_round_control_germ r ?initial=(steps,terminal,event)"
    using comma_round_control_germ_refines close by simp
  have close_at_q:
      "comma_round_close (snd (snd q)) ?initial=(steps,terminal,event)"
    using close q by simp
  have event_not_invalid: "event\<noteq>Comma_Round_Invalid"
    using comma_round_close_admitted(2)[OF close source_admitted] by simp
  have source_delta: "comma_round_delta ?initial=0"
    using q by (cases kind) (simp_all add: comma_finite_initial_def)
  have event_shape:
      "(\<exists>a' d'. event = Comma_Round_Fork a' d') \<or>
       (\<exists>d'. event = Comma_Round_Landmine d') \<or>
       (\<exists>x. x\<le>90 \<and>
         event=Comma_Round_Cross (Comma_Entry 1 1 x) \<and>
         comma_normalize_position r (Comma_Entry 1 1 x) =
           Comma_Entry 1 ((r+1) mod 924) x)"
  proof (cases event)
    case (Comma_Round_Fork fork delta)
    then show ?thesis by blast
  next
    case (Comma_Round_Landmine delta)
    then show ?thesis by blast
  next
    case (Comma_Round_Cross target)
    have crossing_close:
      "comma_round_close r ?initial =
        (steps,terminal,Comma_Round_Cross target)"
      using close Comma_Round_Cross by simp
    obtain x where x_bound: "x\<le>90"
      and target: "target=Comma_Entry 1 (Suc (comma_round_delta ?initial)) x"
      and normalized:
        "comma_normalize_position r target =
          Comma_Entry 1 ((r+comma_round_delta ?initial+1) mod 924) x"
      using comma_round_close_crossing_phase[OF crossing_close source_admitted]
      by blast
    have target_one: "target=Comma_Entry 1 1 x"
      using target source_delta by simp
    have normalized_one:
        "comma_normalize_position r (Comma_Entry 1 1 x) =
          Comma_Entry 1 ((r+1) mod 924) x"
      using normalized target_one source_delta by simp
    show ?thesis using Comma_Round_Cross x_bound target_one normalized_one
      by blast
  next
    case Comma_Round_Invalid
    then show ?thesis using event_not_invalid by blast
  qed
  show thesis
    using calls calls_bound germ close_at_q trace event_shape q
    by (intro that[of calls steps terminal event]) simp_all
qed


ML \<open>
  val published = @{thms comma_semantic_future_initial_round_prefix_closed}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "initial round prefix closure" published
\<close>

end
