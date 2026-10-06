theory Comma_Compact_Decade_Classifier
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>
This theory supplies a bounded, option-valued residual evaluator parameterized
by a one-decade control function.  It is an interface only: it neither
constructs a Native19/core/reset action nor proves 27-step totality for any
particular control function.  A separate theorem relates every successful
run to the existing inductive residual semantics and block runner.
\<close>

fun comma_compact_residual_run ::
  "(comma_decade_state \<Rightarrow> comma_decade_outcome) \<Rightarrow>
    nat \<Rightarrow> comma_decade_state \<Rightarrow> comma_decade_residual option" where
  "comma_compact_residual_run K 0 s = None"
| "comma_compact_residual_run K (Suc n) s =
    (case K s of
       Comma_Decade_Continue t \<Rightarrow>
         (case comma_compact_residual_run K n t of
            None \<Rightarrow> None
          | Some (h,tau) \<Rightarrow> Some (Suc h,tau))
     | Comma_Decade_Fork a d \<Rightarrow>
         (if d=0 then Some (0,Comma_Terminal_Fork a) else None)
     | Comma_Decade_Landmine d \<Rightarrow>
         (if d=0 then Some (0,Comma_Terminal_Landmine) else None)
     | Comma_Decade_Invalid \<Rightarrow> None)"

lemma comma_compact_residual_run_stable_one:
  assumes hit: "comma_compact_residual_run K n s = Some residual"
  shows "comma_compact_residual_run K (Suc n) s = Some residual"
  using hit
proof (induction n arbitrary: s residual)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "K s")
    case (Comma_Decade_Continue t)
    then obtain h tau where
      tail: "comma_compact_residual_run K n t = Some (h,tau)"
      and residual: "residual=(Suc h,tau)"
      using Suc.prems by (cases "comma_compact_residual_run K n t") auto
    have stable: "comma_compact_residual_run K (Suc n) t = Some (h,tau)"
      by (rule Suc.IH[OF tail])
    show ?thesis using Comma_Decade_Continue stable residual by simp
  next
    case (Comma_Decade_Fork a d)
    then show ?thesis using Suc.prems by (cases "d=0") auto
  next
    case (Comma_Decade_Landmine d)
    then show ?thesis using Suc.prems by (cases "d=0") auto
  next
    case Comma_Decade_Invalid
    then show ?thesis using Suc.prems by simp
  qed
qed

lemma comma_compact_residual_run_height:
  assumes hit: "comma_compact_residual_run K n s = Some (h,tau)"
  shows "h<n"
  using hit
proof (induction n arbitrary: s h tau)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "K s")
    case (Comma_Decade_Continue t)
    then obtain h0 tau0 where
      tail: "comma_compact_residual_run K n t = Some (h0,tau0)"
      and fields: "h=Suc h0" "tau=tau0"
      using Suc.prems by (cases "comma_compact_residual_run K n t") auto
    have "h0<n" by (rule Suc.IH[OF tail])
    then show ?thesis using fields by simp
  next
    case (Comma_Decade_Fork a d)
    then show ?thesis using Suc.prems by (cases "d=0") auto
  next
    case (Comma_Decade_Landmine d)
    then show ?thesis using Suc.prems by (cases "d=0") auto
  next
    case Comma_Decade_Invalid
    then show ?thesis using Suc.prems by simp
  qed
qed

text \<open>
The following per-hit result is the semantic bridge.  It uses only refinement
of K on admitted states and successful option evaluation; it assumes no
global totality bound.
\<close>

theorem comma_compact_residual_run_exact:
  assumes refines: "\<And>q. comma_decade_admitted q \<Longrightarrow>
      K q = comma_fast_decade_control q"
    and valid: "comma_decade_admitted s"
    and hit: "comma_compact_residual_run K n s = Some (h,tau)"
  shows "comma_decade_exact_summary s h tau"
  using valid hit
proof (induction n arbitrary: s h tau)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "K s")
    case (Comma_Decade_Continue t)
    then obtain h0 where tail:
      "comma_compact_residual_run K n t = Some (h0,tau)"
      and h: "h=Suc h0"
      using Suc.prems(2) by (cases "comma_compact_residual_run K n t") auto
    have k_control: "K s=comma_fast_decade_control s"
      by (rule refines[OF Suc.prems(1)])
    have physical: "comma_decade_control s=Comma_Decade_Continue t"
      using comma_fast_decade_control_correct[OF Suc.prems(1)]
        k_control Comma_Decade_Continue by simp
    have target_valid: "comma_decade_admitted t"
      by (rule comma_decade_control_closed(2)[OF Suc.prems(1) physical])
        (rule refl)
    have exact_tail: "comma_decade_exact_summary t h0 tau"
      by (rule Suc.IH[OF target_valid tail])
    have "comma_decade_exact_summary s (Suc h0) tau"
      by (rule comma_decade_exact_summary.crossing[OF physical exact_tail])
    then show ?thesis using h by simp
  next
    case (Comma_Decade_Fork a d)
    have result: "d=0 \<and> h=0 \<and> tau=Comma_Terminal_Fork a"
      using Suc.prems(2) Comma_Decade_Fork by (cases "d=0") auto
    then have d: "d=0" and fields: "h=0" "tau=Comma_Terminal_Fork a" by auto
    have k_control: "K s=comma_fast_decade_control s"
      by (rule refines[OF Suc.prems(1)])
    have physical: "comma_decade_control s=Comma_Decade_Fork a 0"
      using comma_fast_decade_control_correct[OF Suc.prems(1)]
        k_control Comma_Decade_Fork d by simp
    have "comma_decade_exact_summary s 0 (Comma_Terminal_Fork a)"
      by (rule comma_decade_exact_summary.fork[OF physical])
    then show ?thesis using fields by simp
  next
    case (Comma_Decade_Landmine d)
    have result: "d=0 \<and> h=0 \<and> tau=Comma_Terminal_Landmine"
      using Suc.prems(2) Comma_Decade_Landmine by (cases "d=0") auto
    then have d: "d=0" and fields: "h=0" "tau=Comma_Terminal_Landmine" by auto
    have k_control: "K s=comma_fast_decade_control s"
      by (rule refines[OF Suc.prems(1)])
    have physical: "comma_decade_control s=Comma_Decade_Landmine 0"
      using comma_fast_decade_control_correct[OF Suc.prems(1)]
        k_control Comma_Decade_Landmine d by simp
    have "comma_decade_exact_summary s 0 Comma_Terminal_Landmine"
      by (rule comma_decade_exact_summary.landmine[OF physical])
    then show ?thesis using fields by simp
  next
    case Comma_Decade_Invalid
    then show ?thesis using Suc.prems(2) by simp
  qed
qed

corollary comma_compact_residual_run_block_stop:
  assumes refines: "\<And>q. comma_decade_admitted q \<Longrightarrow>
      K q = comma_fast_decade_control q"
    and valid: "comma_decade_admitted s"
    and hit: "comma_compact_residual_run K n s = Some (h,tau)"
  shows "comma_decade_block_run n s = Comma_Block_Stop h tau"
proof -
  have exact: "comma_decade_exact_summary s h tau"
    by (rule comma_compact_residual_run_exact[OF refines valid hit])
  have width: "h<n"
    by (rule comma_compact_residual_run_height[OF hit])
  show ?thesis
    by (rule comma_decade_exact_summary_block_stop[OF exact valid width])
qed

text \<open>
The total-function proof interface extracts an option only under a
successful-run or totality premise.  No terminal result is assigned to None.
The option-valued evaluator is the executable boundary; this adapter is not
production admission and is unspecified when that premise is unavailable.
\<close>

definition comma_compact_classifier_from ::
  "(comma_decade_state \<Rightarrow> comma_decade_outcome) \<Rightarrow>
    comma_decade_state \<Rightarrow> comma_decade_residual" where
  "comma_compact_classifier_from K s =
    the (comma_compact_residual_run K 27 s)"

lemma comma_compact_classifier_from_hit:
  assumes hit: "comma_compact_residual_run K 27 s = Some residual"
  shows "comma_compact_classifier_from K s = residual"
  using hit by (simp add: comma_compact_classifier_from_def)

theorem comma_compact_classifier_from_ok:
  assumes refines: "\<And>s. comma_decade_admitted s \<Longrightarrow>
      K s = comma_fast_decade_control s"
    and total: "\<And>s. comma_decade_admitted s \<Longrightarrow>
      \<exists>residual. comma_compact_residual_run K 27 s = Some residual"
  shows "comma_decade_residual_classifier_ok (comma_compact_classifier_from K)"
proof (unfold comma_decade_residual_classifier_ok_def, intro allI impI)
  fix s
  assume valid: "comma_decade_admitted s"
  obtain residual where hit:
    "comma_compact_residual_run K 27 s = Some residual"
    using total[OF valid] by blast
  note unroll = comma_compact_residual_run.simps(2)[of K 26 s, simplified]
  note step_hit = hit[unfolded unroll]
  have source: "comma_compact_classifier_from K s = residual"
    by (rule comma_compact_classifier_from_hit[OF hit])
  have control: "K s = comma_fast_decade_control s"
    by (rule refines[OF valid])
  show "comma_fast_decade_summary_step
      (\<lambda>s. fst (comma_compact_classifier_from K s))
      (\<lambda>s. snd (comma_compact_classifier_from K s)) s"
  proof (cases "K s")
    case (Comma_Decade_Continue t)
    obtain h tau where tail:
      "comma_compact_residual_run K 26 t = Some (h,tau)"
      and residual: "residual=(Suc h,tau)"
      using step_hit Comma_Decade_Continue
      by (cases "comma_compact_residual_run K 26 t") auto
    have tail27: "comma_compact_residual_run K 27 t = Some (h,tau)"
      using comma_compact_residual_run_stable_one[OF tail] by simp
    have target_classifier:
      "comma_compact_classifier_from K t=(h,tau)"
      by (rule comma_compact_classifier_from_hit[OF tail27])
    have physical: "comma_decade_control s=Comma_Decade_Continue t"
      using comma_fast_decade_control_correct[OF valid] control Comma_Decade_Continue
      by simp
    have target_valid: "comma_decade_admitted t"
      by (rule comma_decade_control_closed(2)[OF valid physical])
        (rule refl)
    show ?thesis
      using source residual target_classifier target_valid
      by (simp add: comma_fast_decade_summary_step_def control[symmetric]
        Comma_Decade_Continue)
  next
    case (Comma_Decade_Fork a d)
    have result: "d=0 \<and> residual=(0,Comma_Terminal_Fork a)"
      using step_hit Comma_Decade_Fork by (cases "d=0") auto
    then have d: "d=0" and residual: "residual=(0,Comma_Terminal_Fork a)" by auto
    show ?thesis
      using source residual d
      by (simp add: comma_fast_decade_summary_step_def control[symmetric]
        Comma_Decade_Fork)
  next
    case (Comma_Decade_Landmine d)
    have result: "d=0 \<and> residual=(0,Comma_Terminal_Landmine)"
      using step_hit Comma_Decade_Landmine by (cases "d=0") auto
    then have d: "d=0" and residual: "residual=(0,Comma_Terminal_Landmine)" by auto
    show ?thesis
      using source residual d
      by (simp add: comma_fast_decade_summary_step_def control[symmetric]
        Comma_Decade_Landmine)
  next
    case Comma_Decade_Invalid
    then show ?thesis using step_hit by simp
  qed
qed

lemma comma_compact_classifier_height_bound:
  assumes valid: "comma_decade_admitted s"
    and total: "\<And>q. comma_decade_admitted q \<Longrightarrow>
      \<exists>residual. comma_compact_residual_run K 27 q = Some residual"
    and label: "comma_compact_classifier_from K s=(h,tau)"
  shows "h\<le>26"
proof -
  obtain residual where hit0:
    "comma_compact_residual_run K 27 s=Some residual"
    using total[OF valid] by blast
  obtain h0 tau0 where fields: "residual=(h0,tau0)" by (cases residual) auto
  have hit: "comma_compact_residual_run K 27 s=Some (h0,tau0)"
    using hit0 fields by simp
  have classifier: "comma_compact_classifier_from K s=(h0,tau0)"
    by (rule comma_compact_classifier_from_hit[OF hit])
  have bound: "h0<27"
    by (rule comma_compact_residual_run_height[OF hit])
  show ?thesis using label classifier bound by simp
qed

ML \<open>
  val checked = @{thms comma_compact_residual_run_stable_one
    comma_compact_residual_run_height comma_compact_residual_run_exact
    comma_compact_residual_run_block_stop comma_compact_classifier_from_ok
    comma_compact_classifier_height_bound};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Compact decade classifier interface depends on an oracle";
\<close>

end
