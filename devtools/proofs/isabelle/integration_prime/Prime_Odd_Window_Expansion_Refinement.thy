theory Prime_Odd_Window_Expansion_Refinement
  imports Prime_Odd_Window_Selection_Refinement
    "HOL-Library.While_Combinator"
begin

text \<open>This theory models production's doubling loop at
\<open>select.py:368-375\<close>.  The transition reads only the current exact
interval count.  A ranked target is ghost state used to prove preservation and
termination; it is not consulted by the executable guard or step.\<close>

record odd_expansion_state =
  expansion_start :: nat
  expansion_width :: nat
  expansion_remaining :: nat

definition odd_expansion_guard :: "odd_expansion_state \<Rightarrow> bool" where
  "odd_expansion_guard state \<longleftrightarrow>
    odd_window_count (expansion_start state) (expansion_width state) \<le>
      expansion_remaining state"

definition odd_expansion_step ::
    "odd_expansion_state \<Rightarrow> odd_expansion_state" where
  "odd_expansion_step state =
    \<lparr>expansion_start = expansion_start state + 2 * expansion_width state,
     expansion_width = 2 * expansion_width state,
     expansion_remaining = expansion_remaining state -
       odd_window_count (expansion_start state) (expansion_width state)\<rparr>"

definition odd_expansion_loop ::
    "odd_expansion_state \<Rightarrow> odd_expansion_state option" where
  "odd_expansion_loop state =
    while_option odd_expansion_guard odd_expansion_step state"

definition ranked_target_invariant ::
    "nat \<Rightarrow> odd_expansion_state \<Rightarrow> bool" where
  "ranked_target_invariant target state \<longleftrightarrow>
    prime target \<and>
    odd (expansion_start state) \<and>
    3 \<le> expansion_start state \<and>
    0 < expansion_width state \<and>
    expansion_start state \<le> target \<and>
    prime_block_count (expansion_start state) (target - 1) =
      expansion_remaining state"

lemma prime_rank_strict_at_prime:
  assumes prime: "prime p"
  shows "prime_rank p = Suc (prime_rank (p - 1))"
proof -
  have block: "prime_block_count p p = 1"
    using prime by (simp add: singleton_prime_block)
  have mono: "prime_rank (p - 1) \<le> prime_rank p"
    by (rule prime_rank_mono) simp
  show ?thesis using block mono
    unfolding prime_block_count_def by arith
qed

lemma odd_expansion_guard_places_target_after_window:
  assumes invariant: "ranked_target_invariant target state"
    and guard: "odd_expansion_guard state"
  shows "odd_window_high (expansion_start state) (expansion_width state) < target"
proof -
  let ?start = "expansion_start state"
  let ?width = "expansion_width state"
  let ?high = "odd_window_high ?start ?width"
  from invariant have target_prime: "prime target"
    and start_target: "?start \<le> target"
    and width_positive: "0 < ?width"
    and target_rank:
      "prime_block_count ?start (target - 1) = expansion_remaining state"
    by (auto simp: ranked_target_invariant_def)
  have start_high: "?start \<le> ?high"
    unfolding odd_window_high_def using width_positive by arith
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?high < target"
    then have target_high: "target \<le> ?high" by simp
    have base_rank: "prime_rank (?start - 1) \<le> prime_rank (target - 1)"
      by (rule prime_rank_mono) (use start_target in arith)
    have target_step: "prime_rank target = Suc (prime_rank (target - 1))"
      by (rule prime_rank_strict_at_prime[OF target_prime])
    have target_high_rank: "prime_rank target \<le> prime_rank ?high"
      by (rule prime_rank_mono[OF target_high])
    have window_count:
        "odd_window_count ?start ?width =
          prime_rank ?high - prime_rank (?start - 1)"
      using width_positive
      by (simp add: odd_window_count_def prime_block_count_def)
    have "expansion_remaining state < odd_window_count ?start ?width"
      using target_rank base_rank target_step target_high_rank window_count
      unfolding prime_block_count_def by arith
    with guard show False unfolding odd_expansion_guard_def by simp
  qed
qed

lemma odd_gap_next_start_le_target:
  fixes start width target :: nat
  assumes odd_start: "odd start" and width_positive: "0 < width"
    and target_prime: "prime target" and lower: "3 \<le> start"
    and after: "odd_window_high start width < target"
  shows "start + 2 * width \<le> target"
proof -
  have target_lower: "2 < target" using lower after
    unfolding odd_window_high_def by arith
  have target_odd: "odd target"
    using prime_odd_nat[OF target_prime] target_lower by auto
  have high_odd: "odd (odd_window_high start width)"
    using odd_start by (simp add: odd_window_high_def)
  have not_successor:
      "target \<noteq> Suc (odd_window_high start width)"
    using target_odd high_odd by auto
  have "Suc (Suc (odd_window_high start width)) \<le> target"
    using after not_successor by arith
  then show ?thesis
    unfolding odd_window_high_def using width_positive by arith
qed

lemma odd_expansion_skipped_prefix:
  fixes start width :: nat
  assumes odd: "odd start" and lower: "3 \<le> start"
    and positive: "0 < width"
  shows "prime_block_count start (start + 2 * width - 1) =
    odd_window_count start width"
proof -
  let ?seam = "start + 2 * width - 1"
  have seam_not_prime: "\<not> prime ?seam"
    by (rule odd_nat_ge_three_not_prime[OF odd lower positive])
  have window_endpoint: "odd_window_high start width = ?seam - 1"
    unfolding odd_window_high_def using positive by arith
  have start_seam: "start \<le> ?seam" using positive by arith
  have seam_exact:
      "prime_block_count start ?seam =
        card {p. prime p \<and> start \<le> p \<and> p \<le> ?seam}"
    by (rule prime_block_count_exact[OF start_seam])
  have window_exact:
      "odd_window_count start width =
        card {p. prime p \<and> start \<le> p \<and>
          p \<le> odd_window_high start width}"
    by (rule odd_window_count_exact_set[OF positive])
  have set_eq:
      "{p. prime p \<and> start \<le> p \<and> p \<le> ?seam} =
        {p. prime p \<and> start \<le> p \<and>
          p \<le> odd_window_high start width}"
    using prime_interval_drop_nonprime_endpoint[OF seam_not_prime, of start]
      window_endpoint by simp
  show ?thesis using seam_exact window_exact set_eq by simp
qed

theorem odd_expansion_step_preserves_ranked_target:
  assumes invariant: "ranked_target_invariant target state"
    and guard: "odd_expansion_guard state"
  shows "ranked_target_invariant target (odd_expansion_step state)"
    "target - expansion_start (odd_expansion_step state) <
      target - expansion_start state"
proof -
  let ?start = "expansion_start state"
  let ?width = "expansion_width state"
  let ?next = "?start + 2 * ?width"
  from invariant have target_prime: "prime target"
    and start_odd: "odd ?start" and start_lower: "3 \<le> ?start"
    and width_positive: "0 < ?width" and start_target: "?start \<le> target"
    and target_rank:
      "prime_block_count ?start (target - 1) = expansion_remaining state"
    by (auto simp: ranked_target_invariant_def)
  have after: "odd_window_high ?start ?width < target"
    by (rule odd_expansion_guard_places_target_after_window[OF invariant guard])
  have next_target: "?next \<le> target"
    by (rule odd_gap_next_start_le_target[OF start_odd width_positive
          target_prime start_lower after])
  have skipped:
      "prime_block_count ?start (?next - 1) = odd_window_count ?start ?width"
    by (rule odd_expansion_skipped_prefix[OF start_odd start_lower
          width_positive])
  have append:
      "prime_block_count ?start (target - 1) =
        prime_block_count ?start (?next - 1) +
          prime_block_count ?next (target - 1)"
    by (rule prime_block_count_append_before[OF _ next_target]) simp
  have count_le:
      "odd_window_count ?start ?width \<le> expansion_remaining state"
    using guard by (simp add: odd_expansion_guard_def)
  have next_rank:
      "prime_block_count ?next (target - 1) =
        expansion_remaining state - odd_window_count ?start ?width"
    using target_rank append skipped count_le by arith
  show "ranked_target_invariant target (odd_expansion_step state)"
    using target_prime start_odd start_lower width_positive next_target next_rank
    by (simp add: ranked_target_invariant_def odd_expansion_step_def)
  show "target - expansion_start (odd_expansion_step state) <
      target - expansion_start state"
    using width_positive start_target next_target
    by (simp add: odd_expansion_step_def; arith)
qed

theorem odd_expansion_loop_terminates:
  assumes invariant: "ranked_target_invariant target initial"
  shows "\<exists>final. odd_expansion_loop initial = Some final"
  unfolding odd_expansion_loop_def
  by (rule measure_while_option_Some[
        where P="ranked_target_invariant target"
          and f="\<lambda>state. target - expansion_start state"])
    (use odd_expansion_step_preserves_ranked_target invariant in blast)+

theorem odd_expansion_loop_reaches_ready_window:
  assumes invariant: "ranked_target_invariant target initial"
    and result: "odd_expansion_loop initial = Some final"
  shows "ranked_target_invariant target final"
    "expansion_remaining final <
      odd_window_count (expansion_start final) (expansion_width final)"
proof -
  have loop_result:
      "while_option odd_expansion_guard odd_expansion_step initial = Some final"
    using result unfolding odd_expansion_loop_def .
  have preserved: "ranked_target_invariant target final"
    by (rule while_option_rule[
          where P="ranked_target_invariant target"
            and b=odd_expansion_guard and c=odd_expansion_step
            and s=initial and t=final,
          OF _ loop_result invariant])
      (use odd_expansion_step_preserves_ranked_target in blast)
  have stopped: "\<not> odd_expansion_guard final"
    by (rule while_option_stop[OF loop_result])
  show "ranked_target_invariant target final" by (rule preserved)
  show "expansion_remaining final <
      odd_window_count (expansion_start final) (expansion_width final)"
    using stopped by (simp add: odd_expansion_guard_def)
qed

corollary odd_expansion_then_descent_returns_target:
  assumes invariant: "ranked_target_invariant target initial"
    and expansion: "odd_expansion_loop initial = Some final"
  shows "odd_window_descent (expansion_start final) (expansion_width final)
      (expansion_remaining final) = target"
proof -
  note ready = odd_expansion_loop_reaches_ready_window[OF invariant expansion]
  from ready(1) have target_prime: "prime target"
    and start_odd: "odd (expansion_start final)"
    and start_lower: "3 \<le> expansion_start final"
    and width_positive: "0 < expansion_width final"
    and start_target: "expansion_start final \<le> target"
    and target_rank:
      "prime_block_count (expansion_start final) (target - 1) =
        expansion_remaining final"
    by (auto simp: ranked_target_invariant_def)
  note selected = odd_window_descent_correct[OF start_odd start_lower
      width_positive ready(2)]
  have selected_prime:
      "prime (odd_window_descent (expansion_start final)
        (expansion_width final) (expansion_remaining final))"
    by (rule selected(1))
  have selected_rank:
      "prime_block_count (expansion_start final)
        (odd_window_descent (expansion_start final) (expansion_width final)
          (expansion_remaining final) - 1) = expansion_remaining final"
    by (rule selected(4))
  have selected_lower:
      "expansion_start final \<le>
        odd_window_descent (expansion_start final) (expansion_width final)
          (expansion_remaining final)"
    by (rule selected(2))
  have base_target:
      "prime_rank (expansion_start final - 1) \<le> prime_rank (target - 1)"
    by (rule prime_rank_mono) (use start_target in arith)
  have base_selected:
      "prime_rank (expansion_start final - 1) \<le>
        prime_rank (odd_window_descent (expansion_start final)
          (expansion_width final) (expansion_remaining final) - 1)"
    by (rule prime_rank_mono) (use selected_lower in arith)
  show ?thesis
  proof (rule ccontr)
    assume unequal:
      "odd_window_descent (expansion_start final) (expansion_width final)
        (expansion_remaining final) \<noteq> target"
    show False
    proof (cases "target < odd_window_descent (expansion_start final)
        (expansion_width final) (expansion_remaining final)")
      case True
      have strict: "prime_rank (target - 1) <
          prime_rank (odd_window_descent (expansion_start final)
            (expansion_width final) (expansion_remaining final) - 1)"
        using target_prime True prime_rank_strict_at_prime[OF target_prime]
          prime_rank_mono[of target
            "odd_window_descent (expansion_start final) (expansion_width final)
              (expansion_remaining final) - 1"]
        by arith
      show False using target_rank selected_rank strict base_target base_selected
        unfolding prime_block_count_def by arith
    next
      case False
      then have selected_before: "odd_window_descent (expansion_start final)
          (expansion_width final) (expansion_remaining final) < target"
        using unequal by arith
      have strict: "prime_rank
          (odd_window_descent (expansion_start final) (expansion_width final)
            (expansion_remaining final) - 1) < prime_rank (target - 1)"
        using selected_prime selected_before
          prime_rank_strict_at_prime[OF selected_prime]
          prime_rank_mono[of
            "odd_window_descent (expansion_start final) (expansion_width final)
              (expansion_remaining final)" "target - 1"]
        by arith
      show False using target_rank selected_rank strict base_target base_selected
        unfolding prime_block_count_def by arith
    qed
  qed
qed

text \<open>The loop is the exact deterministic transition used by production:
when the current interval count does not exceed the residual index, subtract
that count, advance by twice the candidate width, and double the width.  The
termination theorem uses a prime with the requested local rank as a proof
witness.  Establishing existence of that ranked target from prime infinitude,
and connecting the initial state's preprocessing of 2 and odd ceiling, remain
the next bounded obligations.  Runtime budgets, dynamic descriptor admission,
scheduler authority, publication, and counters remain outside this arithmetic
loop refinement.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms odd_expansion_step_preserves_ranked_target
      odd_expansion_loop_terminates odd_expansion_loop_reaches_ready_window
      odd_expansion_then_descent_returns_target}) then ()
    else error "Prime odd-window expansion refinement depends on an oracle";
\<close>

end
