theory Comma_Decade_Helix
  imports Comma_Fast_Control.Comma_Fast_Control
begin

text \<open>The phase is a chart coordinate, not an absolute exponent or a
literal transition count. Every continued decade advances it exactly once.
A terminal inspection has zero exponent increment.\<close>

lemma comma_decade_continue_helix:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
    and step: "comma_decade_control (Comma_Decade r x) =
      Comma_Decade_Continue (Comma_Decade r' x')"
  shows "r'=(r+1) mod 924" "x'\<le>90"
proof -
  obtain n t event where close:
    "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have entry: "comma_round_admitted (Comma_Entry 1 0 x)"
    using valid by simp
  have decode: "comma_decade_decode r event =
    Comma_Decade_Continue (Comma_Decade r' x')"
    using step by (simp only: comma_decade_control.simps close prod.case)
  obtain target where event: "event=Comma_Round_Cross target"
    using decode by (cases event; auto split: comma_finite_position.splits if_splits)
  obtain y where y: "y\<le>90" "target=Comma_Entry 1 1 y"
    using comma_round_close_crossing_phase[of r "Comma_Entry 1 0 x" n t target]
      close event entry by auto
  show "r'=(r+1) mod 924" "x'\<le>90"
    using decode y by (simp_all add: event)
qed

lemma comma_decade_terminal_delta:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
  shows "comma_decade_control (Comma_Decade r x)=Comma_Decade_Fork a d \<Longrightarrow> d=0"
    "comma_decade_control (Comma_Decade r x)=Comma_Decade_Landmine d \<Longrightarrow> d=0"
proof -
  obtain n t event where close:
    "comma_round_close r (Comma_Entry 1 0 x)=(n,t,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have entry: "comma_round_admitted (Comma_Entry 1 0 x)"
    using valid by simp
  have delta: "comma_round_delta t=0"
    using comma_round_close_delta[OF close entry] by simp
  have trace: "case event of
       Comma_Round_Fork a d \<Rightarrow> comma_finite_step (r mod 924) t=Comma_Fork a d
     | Comma_Round_Landmine d \<Rightarrow> comma_finite_step (r mod 924) t=Comma_Landmine d
     | _ \<Rightarrow> True"
    using comma_round_close_refines_trace[OF close] by (cases event) auto
  have local_delta:
    "\<And>a d. comma_finite_step (r mod 924) t=Comma_Fork a d \<Longrightarrow> d=0"
    "\<And>d. comma_finite_step (r mod 924) t=Comma_Landmine d \<Longrightarrow> d=0"
    using delta
    by (cases t; auto simp: comma_fast_step_correct[symmetric] Let_def
      split: if_splits)+
  have terminal: "case event of
       Comma_Round_Fork a d \<Rightarrow> d=0
     | Comma_Round_Landmine d \<Rightarrow> d=0
     | _ \<Rightarrow> True"
    using trace local_delta by (cases event) auto
  have decode: "comma_decade_control (Comma_Decade r x)=comma_decade_decode r event"
    by (simp only: comma_decade_control.simps close prod.case)
  have no_cross_fork: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)
      \<noteq>Comma_Decade_Fork a d"
    by (case_tac target) simp_all
  have no_cross_landmine: "\<And>target. comma_decade_decode r (Comma_Round_Cross target)
      \<noteq>Comma_Decade_Landmine d"
    by (case_tac target) simp_all
  have fork_shape: "comma_decade_decode r event=Comma_Decade_Fork a d \<Longrightarrow>
      event=Comma_Round_Fork a d"
    using no_cross_fork by (cases event) auto
  have landmine_shape: "comma_decade_decode r event=Comma_Decade_Landmine d \<Longrightarrow>
      event=Comma_Round_Landmine d"
    using no_cross_landmine by (cases event) auto
  show "comma_decade_control (Comma_Decade r x)=Comma_Decade_Fork a d \<Longrightarrow> d=0"
  proof -
    assume control: "comma_decade_control (Comma_Decade r x)=Comma_Decade_Fork a d"
    have shape: "event=Comma_Round_Fork a d"
      by (rule fork_shape) (use control in \<open>simp only: decode\<close>)
    show "d=0" using terminal by (simp only: shape comma_round_result.case)
  qed
  show "comma_decade_control (Comma_Decade r x)=Comma_Decade_Landmine d \<Longrightarrow> d=0"
  proof -
    assume control: "comma_decade_control (Comma_Decade r x)=Comma_Decade_Landmine d"
    have shape: "event=Comma_Round_Landmine d"
      by (rule landmine_shape) (use control in \<open>simp only: decode\<close>)
    show "d=0" using terminal by (simp only: shape comma_round_result.case)
  qed
qed

theorem comma_fast_decade_continue_helix:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
    and step: "comma_fast_decade_control (Comma_Decade r x)=
      Comma_Decade_Continue (Comma_Decade r' x')"
  shows "r'=(r+1) mod 924" "x'\<le>90"
proof -
  have control: "comma_decade_control (Comma_Decade r x)=
      Comma_Decade_Continue (Comma_Decade r' x')"
    using step by (simp only: comma_fast_decade_control_correct[OF valid])
  show "r'=(r+1) mod 924" "x'\<le>90"
    by (rule comma_decade_continue_helix[OF valid control])+
qed

theorem comma_fast_decade_terminal_delta:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
  shows "comma_fast_decade_control (Comma_Decade r x)=Comma_Decade_Fork a d \<Longrightarrow> d=0"
    "comma_fast_decade_control (Comma_Decade r x)=Comma_Decade_Landmine d \<Longrightarrow> d=0"
proof -
  show "comma_fast_decade_control (Comma_Decade r x)=Comma_Decade_Fork a d \<Longrightarrow> d=0"
    unfolding comma_fast_decade_control_correct[OF valid]
    by (rule comma_decade_terminal_delta(1)[OF valid])
  show "comma_fast_decade_control (Comma_Decade r x)=Comma_Decade_Landmine d \<Longrightarrow> d=0"
    unfolding comma_fast_decade_control_correct[OF valid]
    by (rule comma_decade_terminal_delta(2)[OF valid])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_decade_continue_helix comma_fast_decade_terminal_delta})
    then () else error "Decade helix depends on an oracle";
\<close>
end
