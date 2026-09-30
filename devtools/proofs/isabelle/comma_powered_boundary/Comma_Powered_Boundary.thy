theory Comma_Powered_Boundary
  imports Comma_Decade_Blocks.Comma_Decade_Blocks
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
begin

declare comma_decade_block_power.simps [simp del]
declare comma_fast_round_aux.simps [simp del]

text \<open>The executable interface has no outer search budget. A crossing
consumes one guarded lookup from the checked B5 phase layer.
The executable consumer never invokes the recursive block-power specification. Live and invalid summaries fail closed until the
concrete all-state layer theorem establishes completeness. Existential fuel
below is only the already proved finite semantics, never a runtime argument.\<close>

fun comma_powered_boundary_resume ::
  "(nat \<Rightarrow> comma_decade_block_result list) \<Rightarrow> nat \<Rightarrow> comma_round_result \<Rightarrow> comma_finite_outcome option" where
  "comma_powered_boundary_resume layers r (Comma_Round_Fork a d)=Some (Comma_Fork_At a d)"
| "comma_powered_boundary_resume layers r (Comma_Round_Landmine d)=Some (Comma_Landmine_At d)"
| "comma_powered_boundary_resume layers r (Comma_Round_Cross (Comma_Entry f d x))=
    (let s=Comma_Decade ((r+d) mod 924) x in
      if f=1 \<and> comma_decade_admitted s then
        case comma_decade_layer_lookup (layers ((r+d) mod 924)) x of
          Comma_Block_Stop h terminal \<Rightarrow> Some (comma_summary_outcome (h+d) terminal)
        | _ \<Rightarrow> None
      else None)"
| "comma_powered_boundary_resume layers r (Comma_Round_Cross (Comma_Near f d h))=None"
| "comma_powered_boundary_resume layers r Comma_Round_Invalid=None"

definition comma_powered_total_boundary ::
  "(nat \<Rightarrow> comma_decade_block_result list) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_powered_total_boundary layers q =
    (if comma_boundary_valid q then
      comma_powered_boundary_resume layers (snd (snd q))
        (comma_fast_round_aux 9 (snd (snd q)) (comma_finite_initial q))
     else None)"

lemma comma_powered_boundary_resume_sound:
  assumes checked: "\<And>phase. phase<924 \<Longrightarrow>
      comma_decade_layer_correct 5 phase (layers phase)"
    and close: "comma_round_close r source=(n,t,event)"
    and phase: "r mod 924=r"
    and computed: "comma_powered_boundary_resume layers r event=Some outcome"
  shows "\<exists>fuel. comma_finite_run fuel r source=Some outcome"
proof (cases event)
  case (Comma_Round_Fork a d)
  have run: "comma_finite_run (Suc n) r source=Some (Comma_Fork_At a d)"
    using comma_round_close_fork_finite_run[of r source n t a d] close
    by (simp only: Comma_Round_Fork phase)
  have outcome: "outcome=Comma_Fork_At a d"
    using computed by (simp only: Comma_Round_Fork comma_powered_boundary_resume.simps option.inject)
  show ?thesis
    by (rule exI[of _ "Suc n"]) (simp only: outcome run)
next
  case (Comma_Round_Landmine d)
  have run: "comma_finite_run (Suc n) r source=Some (Comma_Landmine_At d)"
    using comma_round_close_landmine_finite_run[of r source n t d] close
    by (simp only: Comma_Round_Landmine phase)
  have outcome: "outcome=Comma_Landmine_At d"
    using computed by (simp only: Comma_Round_Landmine comma_powered_boundary_resume.simps option.inject)
  show ?thesis
    by (rule exI[of _ "Suc n"]) (simp only: outcome run)
next
  case (Comma_Round_Cross target)
  obtain d x h terminal where target: "target=Comma_Entry 1 d x"
    and admitted: "comma_decade_admitted (Comma_Decade ((r+d) mod 924) x)"
    and lookup: "comma_decade_layer_lookup (layers ((r+d) mod 924)) x=
      Comma_Block_Stop h terminal"
    and outcome: "outcome=comma_summary_outcome (h+d) terminal"
    using computed by (cases target;
      auto simp: Comma_Round_Cross Let_def split: if_splits comma_decade_block_result.splits)
  have bound: "x\<le>90" using admitted by simp
  have width: "x<91" using bound by arith
  have correct: "comma_decade_layer_correct 5 ((r+d) mod 924) (layers ((r+d) mod 924))"
    by (rule checked) simp
  have stop: "comma_decade_block_power 5 (Comma_Decade ((r+d) mod 924) x)=
      Comma_Block_Stop h terminal"
    using comma_decade_layer_lookup_correct[OF correct width] lookup by simp
  have summary: "comma_decade_exact_summary (Comma_Decade ((r+d) mod 924) x) h terminal"
    by (rule comma_decade_block_power_stop(2)[OF stop])
  obtain fuel where tail: "comma_finite_run fuel ((r+d) mod 924) (Comma_Entry 1 0 x)=
      Some (comma_summary_outcome h terminal)"
    using comma_decade_exact_summary_run[OF summary admitted] by auto
  have shifted: "comma_finite_run fuel (r mod 924) target=Some outcome"
    using comma_finite_run_shift_exact[of fuel r d "Comma_Entry 1 0 x"]
    by (simp only: tail; simp add: target outcome comma_summary_outcome_shift)
  have prefix: "comma_round_prefix_steps (Suc n) r source target"
    by (rule comma_round_close_cross_prefix) (use close Comma_Round_Cross in simp)
  have run: "comma_finite_run (Suc n+fuel) r source=Some outcome"
    using comma_round_prefix_finite_run[OF prefix, of fuel] shifted by (simp only: phase)
  show ?thesis using run by blast
next
  case Comma_Round_Invalid
  then show ?thesis using computed by simp
qed

theorem comma_powered_total_boundary_refines:
  assumes checked: "\<And>phase. phase<924 \<Longrightarrow>
      comma_decade_layer_correct 5 phase (layers phase)"
    and computed: "comma_powered_total_boundary layers q=Some outcome"
  shows "\<exists>fuel. comma_finite_macro fuel q=Some outcome"
proof -
  have valid: "comma_boundary_valid q"
    using computed by (auto simp: comma_powered_total_boundary_def split: if_splits)
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  let ?source = "comma_finite_initial q"
  have admitted: "comma_round_admitted ?source" and phase: "r mod 924=r"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def comma_finite_initial_def)+
  obtain n t event where close: "comma_round_close r ?source=(n,t,event)"
    by (cases "comma_round_close r ?source") auto
  have budget: "Suc (9-comma_sector_number ?source)\<le>9"
    using admitted by (cases ?source) auto
  have fast: "comma_fast_round_aux 9 r ?source=event"
    using comma_fast_round_aux_correct[OF admitted budget, of r] close by simp
  have phase_key: "snd (snd q)=r" by (simp only: q snd_conv)
  have resume: "comma_powered_boundary_resume layers r event=Some outcome"
    using computed by (simp only: comma_powered_total_boundary_def valid if_True phase_key fast)
  obtain fuel where run: "comma_finite_run fuel r ?source=Some outcome"
    using comma_powered_boundary_resume_sound[OF checked close phase resume] by blast
  show ?thesis using run valid by (auto simp: comma_finite_macro_def q)
qed

corollary comma_powered_total_boundary_agrees:
  assumes "\<And>phase. phase<924 \<Longrightarrow> comma_decade_layer_correct 5 phase (layers phase)"
    "comma_powered_total_boundary layers q=Some outcome"
  shows "outcome=comma_total_macro q"
  using comma_powered_total_boundary_refines[OF assms] comma_total_macro_agrees by metis

theorem comma_powered_total_boundary_complete:
  assumes checked: "\<And>phase. phase<924 \<Longrightarrow>
      comma_decade_layer_correct 5 phase (layers phase)"
    and complete: "\<And>phase. phase<924 \<Longrightarrow>
      comma_decade_layer_complete 26 (layers phase)"
    and valid: "comma_boundary_valid q"
  shows "comma_powered_total_boundary layers q=Some (comma_total_macro q)"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  let ?source = "comma_finite_initial q"
  have admitted: "comma_round_admitted ?source" and delta: "comma_round_delta ?source=0"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def comma_finite_initial_def)+
  obtain n t event where close: "comma_round_close r ?source=(n,t,event)"
    by (cases "comma_round_close r ?source") auto
  have budget: "Suc (9-comma_sector_number ?source)\<le>9"
    using admitted by (cases ?source) auto
  have fast: "comma_fast_round_aux 9 r ?source=event"
    using comma_fast_round_aux_correct[OF admitted budget, of r] close by simp
  have resume: "\<exists>outcome. comma_powered_boundary_resume layers r event=Some outcome"
  proof (cases event)
    case (Comma_Round_Cross target)
    obtain x where x: "x\<le>90" "target=Comma_Entry 1 1 x"
      using comma_round_close_crossing_phase[of r ?source n t target]
        close Comma_Round_Cross admitted delta by auto
    have state: "comma_decade_admitted (Comma_Decade ((r+1) mod 924) x)"
      using x by simp
    have width: "x<91" using x(1) by arith
    have correct: "comma_decade_layer_correct 5 ((r+1) mod 924) (layers ((r+1) mod 924))"
      by (rule checked) simp
    have complete_layer: "comma_decade_layer_complete 26 (layers ((r+1) mod 924))"
      by (rule complete) simp
    obtain h terminal where stop:
      "comma_decade_block_power 5 (Comma_Decade ((r+1) mod 924) x)=Comma_Block_Stop h terminal"
      using comma_decade_layer_complete_sound[OF correct complete_layer width] by blast
    have lookup: "comma_decade_layer_lookup (layers ((r+1) mod 924)) x=Comma_Block_Stop h terminal"
      using comma_decade_layer_lookup_correct[OF correct width] stop by simp
    show ?thesis
      by (simp only: Comma_Round_Cross x(2) comma_powered_boundary_resume.simps
        Let_def state lookup HOL.simp_thms if_True comma_decade_block_result.case; blast)
  next
    case Comma_Round_Invalid
    then show ?thesis using comma_round_close_admitted(2)[OF close admitted] by simp
  qed simp_all
  have phase_key: "snd (snd q)=r" by (simp only: q snd_conv)
  obtain outcome where computed: "comma_powered_total_boundary layers q=Some outcome"
    using resume by (auto simp only: comma_powered_total_boundary_def valid if_True phase_key fast)
  show ?thesis using computed comma_powered_total_boundary_agrees[OF checked computed] by simp
qed

text \<open>Completeness above remains conditional on the concrete B5 layer
check over all admitted states. It is not a checked future-branch certificate,
a literal-weight construction, or permission to remove production admission.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_powered_boundary_resume_sound comma_powered_total_boundary_refines
      comma_powered_total_boundary_agrees comma_powered_total_boundary_complete}) then ()
    else error "Powered boundary refinement depends on an oracle";
\<close>
end
