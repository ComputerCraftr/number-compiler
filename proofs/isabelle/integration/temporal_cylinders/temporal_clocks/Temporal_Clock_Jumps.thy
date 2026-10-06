theory Temporal_Clock_Jumps
  imports Main
begin

text \<open>Temporal laws for a supplied closed action. The quotient premise
below must be discharged for the actual state and every admitted context.
Function composition alone is not a bound on representation or evaluation cost.\<close>

locale temporal_quotient =
  fixes step :: "'s \<Rightarrow> 's"
    and project :: "'s \<Rightarrow> 'q"
    and advance :: "'q \<Rightarrow> 'q"
  assumes successor: "project (step x) = advance (project x)"
begin

theorem quotient_jump:
  "project ((step ^^ n) x) = (advance ^^ n) (project x)"
  by (induction n) (simp_all add: successor)

theorem quotient_jump_congruence:
  assumes "project x = project y"
  shows "project ((step ^^ n) x) = project ((step ^^ n) y)"
  using assms by (simp add: quotient_jump)

end

locale normalized_temporal_action =
  fixes step :: "'s \<Rightarrow> 's" and normalize :: "'s \<Rightarrow> 's"
  assumes idempotent: "normalize (normalize x) = normalize x"
      and consumes: "normalize (step (normalize x)) = normalize (step x)"
begin

definition normalized_step where "normalized_step = normalize \<circ> step"

lemma normalized_successor:
  "normalize (step x) = normalized_step (normalize x)"
  by (simp add: normalized_step_def consumes)

sublocale temporal_quotient step normalize normalized_step
  by unfold_locales (rule normalized_successor)

theorem normalize_at_every_seam:
  "normalize ((step ^^ (m+n)) x) =
    (normalized_step ^^ n) (normalize ((step ^^ m) x))"
proof -
  have swap: "m+n = n+m" by arith
  show ?thesis by (subst swap)
    (simp only: quotient_jump funpow_add comp_apply)
qed

text \<open>The consumes assumption is the exact rebase obligation. Merely
idempotent canonicalization cannot establish this theorem.\<close>
end

record ('p, 's) clock_section =
  section_phase :: 'p
  section_value :: 's

locale clocked_transition =
  fixes step :: "('p, 's) clock_section \<Rightarrow> ('p, 's) clock_section"
    and clock :: "'p \<Rightarrow> 'p"
  assumes phase_step: "section_phase (step x) = clock (section_phase x)"
begin

lemma jump_phase:
  "section_phase ((step ^^ n) x) = (clock ^^ n) (section_phase x)"
  by (induction n) (simp_all add: phase_step)

theorem typed_temporal_seam:
  "(step ^^ (n+n)) x = (step ^^ n) ((step ^^ n) x)"
  by (simp add: funpow_add)

end

section \<open>Closed affine effects with no midpoint record\<close>

type_synonym 'a affine_effect = "'a \<times> 'a"

definition apply_effect :: "'a::comm_ring_1 affine_effect \<Rightarrow> 'a \<Rightarrow> 'a" where
  "apply_effect A x = fst A * x + snd A"

definition then_effect :: "'a::comm_ring_1 affine_effect \<Rightarrow>
    'a affine_effect \<Rightarrow> 'a affine_effect" where
  "then_effect A B = (fst B * fst A, fst B * snd A + snd B)"

lemma then_effect_exact:
  "apply_effect (then_effect A B) x = apply_effect B (apply_effect A x)"
  by (simp add: apply_effect_def then_effect_def algebra_simps)

lemma then_effect_associative:
  "then_effect (then_effect A B) C = then_effect A (then_effect B C)"
  by (simp add: then_effect_def algebra_simps)

fun dyadic_effect :: "nat \<Rightarrow> 'a::comm_ring_1 affine_effect \<Rightarrow> 'a affine_effect" where
  "dyadic_effect 0 A = A"
| "dyadic_effect (Suc k) A =
    (let half = dyadic_effect k A in then_effect half half)"

theorem dyadic_effect_jump:
  "apply_effect (dyadic_effect k A) x = (apply_effect A ^^ (2^k)) x"
proof (induction k arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have twice: "(2::nat)^(Suc k) = 2^k + 2^k"
    by (simp add: power_Suc)
  show ?case by (simp only: dyadic_effect.simps Let_def then_effect_exact Suc.IH
    twice funpow_add comp_apply)
qed

fun dyadic_compositions :: "nat \<Rightarrow> nat" where
  "dyadic_compositions 0 = 0"
| "dyadic_compositions (Suc k) = Suc (dyadic_compositions k)"

lemma dyadic_compositions_exact: "dyadic_compositions k = k"
  by (induction k) simp_all

text \<open>The cost theorem counts one shared squaring per level. An affine
effect is two ring elements; their bit size and multiplication costs are not
asserted constant for an arbitrary ring. No new event is discovered here.\<close>

lemma killed_source_has_only_offset:
  assumes "fst A = 0"
  shows "apply_effect A x = snd A"
  using assms by (simp add: apply_effect_def)

lemma killed_source_stays_dead:
  assumes "fst A = 0"
  shows "fst (then_effect A B) = 0"
  using assms by (simp add: then_effect_def)

section \<open>Exact endpoint kernels\<close>

lemma endpoint_image_commutes:
  "(step ^^ n) (step x) = step ((step ^^ n) x)"
  by (induction n) simp_all

locale deterministic_endpoint_seam =
  fixes step :: "'s \<Rightarrow> 's" and duration :: nat
begin

sublocale temporal_quotient step "step ^^ duration" step
  by unfold_locales (rule endpoint_image_commutes)

text \<open>The image is an exact future occurrence. This discharges successor
congruence for deterministic endpoints without inventing a finite feature
observer. The image may lie outside the bounded set of audited source words.\<close>

end

theorem exact_endpoint_kernel_future:
  fixes step :: "'s \<Rightarrow> 's"
  assumes same: "(step ^^ n) x = (step ^^ n) y"
  shows "(step ^^ (n+m)) x = (step ^^ (n+m)) y"
  using same by (induction m) (simp_all add: funpow.simps comp_apply)

corollary exact_endpoint_kernel_doubling:
  fixes step :: "'s \<Rightarrow> 's"
  assumes "(step ^^ n) x = (step ^^ n) y"
  shows "(step ^^ (n+n)) x = (step ^^ (n+n)) y"
  by (rule exact_endpoint_kernel_future[OF assms])

lemma exact_endpoint_dyadic_composition:
  fixes step :: "'s \<Rightarrow> 's"
  shows "(step ^^ (2^(Suc k))) x = (step ^^ (2^k)) ((step ^^ (2^k)) x)"
proof -
  have twice: "(2::nat)^(Suc k) = 2^k + 2^k" by (simp add: power_Suc)
  show ?thesis by (simp only: twice funpow_add comp_apply)
qed

lemma endpoint_image_need_not_be_idempotent:
  "(Suc ^^ 1) ((Suc ^^ 1) 0) \<noteq> (Suc ^^ 1) 0"
  by simp

text \<open>These equations specify composition and permanent forgetting of
predecessor distinctions. They count no arithmetic work. An endpoint map
advances time and need not be an idempotent state normalizer. Constructing its
first image is a separate evaluator obligation.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms temporal_quotient.quotient_jump temporal_quotient.quotient_jump_congruence
      normalized_temporal_action.normalize_at_every_seam
      clocked_transition.jump_phase clocked_transition.typed_temporal_seam
      then_effect_exact then_effect_associative dyadic_effect_jump
      dyadic_compositions_exact killed_source_has_only_offset killed_source_stays_dead
      endpoint_image_commutes exact_endpoint_kernel_future exact_endpoint_kernel_doubling
      exact_endpoint_dyadic_composition endpoint_image_need_not_be_idempotent})
    then () else error "Temporal clock proof depends on an oracle";
\<close>
end
