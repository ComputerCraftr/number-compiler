theory Comma_Return_Engine
  imports Comma_Return_Induction.Comma_Return_Induction
    Comma_Fast_Control.Comma_Fast_Kernel
begin

text \<open>One context-owned arithmetic engine serves both return and branch
proofs. Imported boundary traces are checked kernel theorems, not evaluated
rows or a second constructor. Their exact source keys retain the phase; the
existing phase-transport theorem alone changes an occurrence offset.\<close>

named_theorems comma_completed_boundary_traces
  "Closed source-bound boundary traces available before arithmetic discovery"

lemma comma_checked_return_edge:
  assumes valid: "comma_boundary_valid q"
    and defined: "comma_macro_defined q"
    and macro: "comma_total_macro q=Comma_Fork_At a d"
    and target: "comma_boundary_valid (kind,a,(snd (snd q)+d) mod 924)"
  shows "comma_return_path 1 q (kind,a,(snd (snd q)+d) mod 924) d"
proof -
  have child: "(kind,a,(snd (snd q)+d) mod 924)\<in>set (comma_total_children q)"
    using macro by (cases kind) (simp_all add: comma_total_children_def)
  show ?thesis
    using comma_return_path.step[OF valid defined macro child
      comma_return_path.empty[OF target]] by simp
qed

ML_file "return_check.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_round_reaches_macro comma_round_reaches_phase_transport
      comma_checked_return_edge})
    then () else error "Shared comma boundary engine depends on an oracle";
\<close>

end
