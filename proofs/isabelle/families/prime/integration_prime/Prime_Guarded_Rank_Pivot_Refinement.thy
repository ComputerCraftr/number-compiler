theory Prime_Guarded_Rank_Pivot_Refinement
  imports Prime_Odd_Window_Selection_Refinement
begin

text \<open>The approximate estimate chooses a probe only. Exact rank responses own
both endpoints and decide which bracket is retained. A rank is a cumulative
count on odd-candidate offsets, with the lower endpoint excluded and the
upper endpoint included.\<close>

definition prime_rank_bracket ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "prime_rank_bracket rank target low high \<longleftrightarrow>
    low < high \<and> rank low \<le> target \<and> target < rank high"

definition prime_guarded_rank_pivot :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prime_guarded_rank_pivot low high estimate =
    (let guard = max 1 ((high - low) div 8)
     in min (high - guard) (max (low + guard) estimate))"

lemma prime_guarded_rank_pivot_inside:
  fixes low high estimate :: nat
  assumes "low + 1 < high"
  shows "low < prime_guarded_rank_pivot low high estimate \<and>
    prime_guarded_rank_pivot low high estimate < high"
proof -
  define guard where "guard = max 1 ((high - low) div 8)"
  have width: "1 < high - low" using assms by arith
  have quotient: "(high - low) div 8 < high - low" using width by simp
  have positive: "0 < guard" by (simp add: guard_def)
  have small: "guard < high - low" using width quotient by (simp add: guard_def)
  have lower: "low < high - guard" using small by arith
  have upper: "high - guard < high" using positive small by arith
  have first: "low < min (high - guard) (max (low + guard) estimate)"
    using lower positive by simp
  have second: "min (high - guard) (max (low + guard) estimate) < high"
    using upper by simp
  show ?thesis using first second
    by (simp only: prime_guarded_rank_pivot_def Let_def guard_def)
qed

theorem prime_guarded_rank_pivot_preserves_bracket:
  fixes rank :: "nat \<Rightarrow> nat" and estimate :: nat
  assumes bracket: "prime_rank_bracket rank target low high"
    and width: "low + 1 < high"
  defines "pivot \<equiv> prime_guarded_rank_pivot low high estimate"
  shows "(if target < rank pivot then prime_rank_bracket rank target low pivot
      else prime_rank_bracket rank target pivot high)"
    and "(if target < rank pivot then pivot - low else high - pivot) < high - low"
proof -
  have inside: "low < pivot" "pivot < high"
    using prime_guarded_rank_pivot_inside[OF width, of estimate] by (auto simp: pivot_def)
  show "(if target < rank pivot then prime_rank_bracket rank target low pivot
      else prime_rank_bracket rank target pivot high)"
    using bracket inside by (auto simp: prime_rank_bracket_def)
  show "(if target < rank pivot then pivot - low else high - pivot) < high - low"
    using inside by (auto; arith)
qed

lemma prime_guarded_rank_exact_probe:
  assumes odd: "odd start" and lower: "3 \<le> start" and inside: "low < pivot"
  shows "odd_window_count start pivot = odd_window_count start low +
    odd_window_count (start + 2 * low) (pivot - low)"
proof (cases "low = 0")
  case True
  then show ?thesis by (simp add: odd_window_count_def)
next
  case False
  have positive: "0 < low" using False by simp
  show ?thesis by (rule odd_prime_window_split[OF odd lower positive inside])
qed

corollary prime_guarded_window_consumer:
  fixes estimate pivot :: nat
  assumes odd: "odd start" and lower: "3 \<le> start"
    and bracket: "prime_rank_bracket (odd_window_count start) target low high"
    and width: "low + 1 < high"
  defines "pivot \<equiv> prime_guarded_rank_pivot low high estimate"
    and "probe \<equiv> odd_window_count (start + 2 * low) (pivot - low)"
  shows "(if target < odd_window_count start low + probe
      then prime_rank_bracket (odd_window_count start) target low pivot
      else prime_rank_bracket (odd_window_count start) target pivot high)"
    and "(if target < odd_window_count start low + probe
      then pivot - low else high - pivot) < high - low"
proof -
  have inside: "low < pivot"
    using prime_guarded_rank_pivot_inside[OF width, of estimate] by (simp add: pivot_def)
  have exact: "odd_window_count start pivot = odd_window_count start low + probe"
    using prime_guarded_rank_exact_probe[OF odd lower inside] by (simp add: probe_def)
  have bracket_step:
    "(if target < odd_window_count start pivot
      then prime_rank_bracket (odd_window_count start) target low pivot
      else prime_rank_bracket (odd_window_count start) target pivot high)"
    using prime_guarded_rank_pivot_preserves_bracket(1)[OF bracket width, of estimate]
    by (simp only: pivot_def)
  have progress_step:
    "(if target < odd_window_count start pivot
      then pivot - low else high - pivot) < high - low"
    using prime_guarded_rank_pivot_preserves_bracket(2)[OF bracket width, of estimate]
    by (simp only: pivot_def)
  show "(if target < odd_window_count start low + probe
      then prime_rank_bracket (odd_window_count start) target low pivot
      else prime_rank_bracket (odd_window_count start) target pivot high)"
    using bracket_step by (simp only: exact)
  show "(if target < odd_window_count start low + probe
      then pivot - low else high - pivot) < high - low"
    using progress_step by (simp only: exact)
qed

lemma prime_rank_singleton_target:
  assumes "prime_rank_bracket rank target low (Suc low)"
    and one: "rank (Suc low) \<le> rank low + 1"
  shows "target = rank low \<and> rank (Suc low) = Suc (rank low)"
  using assms by (auto simp: prime_rank_bracket_def; arith)

text \<open>No accuracy hypothesis is required of the density estimate, the
interpolation, or a forced midpoint: only the certified rank response is used
to update the bracket. The singleton conclusion additionally assumes that one
candidate changes rank by at most one.\<close>

ML \<open>
  val checked = @{thms prime_guarded_rank_pivot_inside
    prime_guarded_rank_pivot_preserves_bracket prime_guarded_rank_exact_probe
    prime_guarded_window_consumer prime_rank_singleton_target};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Prime guarded rank pivot refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped prime guarded rank pivot refinement" else ();
\<close>

end
