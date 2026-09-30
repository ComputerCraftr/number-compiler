theory Reverse_Contextual_Fixed_Point
  imports Reverse_Residuals
begin

text \<open>The observation option includes admissibility. Its payload denotes
the complete output/growth/alignment/extent/halo/cocycle record. The context and
residual edges both belong to the signature. This theorem is conditional on
stability for the entire state universe, not a bounded continuation sample.\<close>

definition contextual_signature where
  "contextual_signature q delta context obs x a =
    map_option (\<lambda>v. (v, q (context x a), q (delta x a))) (obs x a)"

fun continuation_trace where
  "continuation_trace delta obs [] x = []"
| "continuation_trace delta obs (a # w) x =
    (case obs x a of None \<Rightarrow> [None]
     | Some v \<Rightarrow> Some v # continuation_trace delta obs w (delta x a))"

lemma stable_signature_step:
  assumes "contextual_signature q delta context obs x a =
    contextual_signature q delta context obs y a"
  shows "obs x a = obs y a"
    "obs x a \<noteq> None \<Longrightarrow> q (context x a) = q (context y a)"
    "obs x a \<noteq> None \<Longrightarrow> q (delta x a) = q (delta y a)"
  using assms by (cases "obs x a"; cases "obs y a";
      auto simp: contextual_signature_def)+

theorem stable_contextual_all_continuations:
  assumes stable: "\<And>x y a. q x = q y \<Longrightarrow>
    contextual_signature q delta context obs x a =
    contextual_signature q delta context obs y a"
  and equal: "q x = q y"
  shows "continuation_trace delta obs w x = continuation_trace delta obs w y"
  using equal
proof (induction w arbitrary: x y)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  have sig: "contextual_signature q delta context obs x a =
      contextual_signature q delta context obs y a"
    by (rule stable[OF Cons.prems])
  have obs: "obs x a = obs y a" by (rule stable_signature_step(1)[OF sig])
  show ?case
  proof (cases "obs x a")
    case None
    then show ?thesis using obs by simp
  next
    case (Some v)
    have successor_eq: "q (delta x a) = q (delta y a)"
      by (rule stable_signature_step(3)[OF sig]) (simp add: Some)
    have tail: "continuation_trace delta obs w (delta x a) =
        continuation_trace delta obs w (delta y a)"
      by (rule Cons.IH[OF successor_eq])
    have other: "obs y a = Some v" using obs Some by metis
    show ?thesis by (simp only: continuation_trace.simps Some other option.case tail)
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms stable_signature_step stable_contextual_all_continuations}) then ()
    else error "Contextual stability proof depends on an oracle";
\<close>

end
