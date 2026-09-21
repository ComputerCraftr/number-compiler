theory Prime_Selection_Initialization_Refinement
  imports "Prime_Deterministic_Refinement.Prime_Odd_Window_Expansion_Refinement"
begin

text \<open>This theory discharges the ranked-target witness used by the checked
expansion loop.  It also models production's special handling of 2, odd
ceiling, residual zero-based index, and initial width at
\<open>select.py:340-351\<close>.\<close>

fun ranked_prime_target :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ranked_prime_target start 0 = smallest_prime_beyond start"
| "ranked_prime_target start (Suc index) =
    next_prime_after (ranked_prime_target start index)"

lemma ranked_prime_target_prime [simp]:
  "prime (ranked_prime_target start index)"
  by (induction index) (simp_all add: next_prime_after_prime)

lemma ranked_prime_target_lower:
  "start \<le> ranked_prime_target start index"
proof (induction index)
  case 0
  show ?case by simp
next
  case (Suc index)
  have "ranked_prime_target start index <
      next_prime_after (ranked_prime_target start index)"
    by (rule next_prime_after_gt)
  with Suc.IH show ?case by simp
qed

lemma next_prime_after_open_interval_empty:
  assumes prime: "prime p"
  shows "{q. prime q \<and> p < q \<and> q < next_prime_after p} = {}"
proof (rule equals0I)
  fix q
  assume member:
    "q \<in> {q. prime q \<and> p < q \<and> q < next_prime_after p}"
  then have qprime: "prime q" and above: "p < q"
    and below: "q < next_prime_after p" by auto
  have "next_prime_after p \<le> q"
    by (rule next_prime_after_least[OF qprime above])
  with below show False by simp
qed

theorem ranked_prime_target_zero_based:
  "card {p. prime p \<and> start \<le> p \<and>
      p < ranked_prime_target start index} = index"
proof (induction index)
  case 0
  have no_earlier:
      "{p. prime p \<and> start \<le> p \<and>
          p < smallest_prime_beyond start} = {}"
  proof (rule equals0I)
    fix p
    assume member:
      "p \<in> {p. prime p \<and> start \<le> p \<and>
        p < smallest_prime_beyond start}"
    then have prime: "prime p" and lower: "start \<le> p"
      and upper: "p < smallest_prime_beyond start" by auto
    have "smallest_prime_beyond start \<le> p"
      by (rule smallest_prime_beyond_smallest[OF prime lower])
    with upper show False by simp
  qed
  show ?case using no_earlier by simp
next
  case (Suc index)
  let ?p = "ranked_prime_target start index"
  let ?q = "next_prime_after ?p"
  let ?old = "{r. prime r \<and> start \<le> r \<and> r < ?p}"
  let ?new = "{r. prime r \<and> start \<le> r \<and> r < ?q}"
  have pprime: "prime ?p" by simp
  have start_p: "start \<le> ?p" by (rule ranked_prime_target_lower)
  have split: "?new = insert ?p ?old"
  proof (rule Set.set_eqI)
    fix r
    show "r \<in> ?new \<longleftrightarrow> r \<in> insert ?p ?old"
    proof
      assume member: "r \<in> ?new"
      then have rprime: "prime r" and start_r: "start \<le> r"
        and r_q: "r < ?q" by auto
      show "r \<in> insert ?p ?old"
      proof (cases "r < ?p")
        case True
        with member show ?thesis by auto
      next
        case False
        then have p_r: "?p \<le> r" by simp
        have "r = ?p"
        proof (rule ccontr)
          assume "r \<noteq> ?p"
          with p_r have "?p < r" by simp
          then have "?q \<le> r"
            by (rule next_prime_after_least[OF rprime])
          with r_q show False by simp
        qed
        then show ?thesis by simp
      qed
    next
      assume member: "r \<in> insert ?p ?old"
      then show "r \<in> ?new"
        using pprime start_p next_prime_after_gt[of ?p] by auto
    qed
  qed
  have finite_old: "finite ?old"
    by (rule finite_subset[of _ "{..<?p}"]) auto
  have p_not_old: "?p \<notin> ?old" by simp
  show ?case using Suc.IH split finite_old p_not_old by simp
qed

lemma ranked_prime_target_block_count:
  assumes lower: "0 < start"
  shows "prime_block_count start (ranked_prime_target start index - 1) = index"
proof -
  have target_lower: "start \<le> ranked_prime_target start index"
    by (rule ranked_prime_target_lower)
  have exact:
      "prime_block_count start (ranked_prime_target start index - 1) =
        card {p. prime p \<and> start \<le> p \<and>
          p \<le> ranked_prime_target start index - 1}"
  proof (cases "ranked_prime_target start index = start")
    case True
    then have index_zero:
        "card {p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target start index} = 0" by simp
    then have "index = 0" using ranked_prime_target_zero_based[of start index]
      by simp
    have block_zero: "prime_block_count start (start - 1) = 0"
      unfolding prime_block_count_def
      using prime_rank_mono[of "start - 1" start] by simp
    have empty:
        "{p. prime p \<and> start \<le> p \<and> p \<le> start - 1} = {}"
      using lower by auto
    show ?thesis using True block_zero empty by simp
  next
    case False
    then have strict: "start < ranked_prime_target start index"
      using target_lower by arith
    show ?thesis by (rule prime_block_count_exact) (use strict in arith)
  qed
  have set_eq:
      "{p. prime p \<and> start \<le> p \<and>
          p \<le> ranked_prime_target start index - 1} =
       {p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target start index}"
    using lower by auto
  show ?thesis
    using exact set_eq ranked_prime_target_zero_based[of start index] by simp
qed

definition selection_odd_start :: "nat \<Rightarrow> nat" where
  "selection_odd_start start =
    (if start \<le> 2 then 3 else if odd start then start else Suc start)"

definition selection_remaining :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "selection_remaining start index =
    (if start \<le> 2 then index - 1 else index)"

definition selection_initial_width :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "selection_initial_width leaf remaining = max leaf (4 * (remaining + 1))"

definition selection_initial_state ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> odd_expansion_state" where
  "selection_initial_state start index leaf =
    (let odd_start = selection_odd_start start;
         remaining = selection_remaining start index
     in \<lparr>expansion_start = odd_start,
         expansion_width = selection_initial_width leaf remaining,
         expansion_remaining = remaining\<rparr>)"

definition arithmetic_prime_selection :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "arithmetic_prime_selection start index leaf =
    (if start \<le> 2 \<and> index = 0 then 2
     else
       (let initial = selection_initial_state start index leaf;
            final = the (odd_expansion_loop initial)
        in odd_window_descent (expansion_start final) (expansion_width final)
             (expansion_remaining final)))"

lemma selection_odd_start_properties:
  "odd (selection_odd_start start)"
  "3 \<le> selection_odd_start start"
  "start \<le> selection_odd_start start"
  by (auto simp: selection_odd_start_def)

lemma selection_local_rank:
  assumes active: "\<not> (start \<le> 2 \<and> index = 0)"
  defines "odd_start \<equiv> selection_odd_start start"
    and "remaining \<equiv> selection_remaining start index"
  shows "card {p. prime p \<and> start \<le> p \<and>
      p < ranked_prime_target odd_start remaining} = index"
proof (cases "start \<le> 2")
  case True
  with active have index_positive: "0 < index" by simp
  have odd_start_three: "odd_start = 3"
    using True by (simp add: odd_start_def selection_odd_start_def)
  have remaining_pred: "remaining = index - 1"
    using True by (simp add: remaining_def selection_remaining_def)
  have target_three: "3 \<le> ranked_prime_target odd_start remaining"
    using ranked_prime_target_lower[of odd_start remaining] odd_start_three by simp
  have prime_ge_three:
      "\<And>(p::nat). prime p \<Longrightarrow> p \<noteq> 2 \<Longrightarrow> 3 \<le> p"
  proof -
    fix p :: nat
    assume prime: "prime p" and not_two: "p \<noteq> 2"
    have "2 \<le> p" using prime_gt_1_nat[OF prime] by simp
    with not_two show "3 \<le> p" by arith
  qed
  have split:
      "{p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target odd_start remaining} =
        insert 2 {p. prime p \<and> odd_start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
    using True odd_start_three target_three prime_ge_three by auto
  have finite_tail:
      "finite {p. prime p \<and> odd_start \<le> p \<and>
        p < ranked_prime_target odd_start remaining}"
    by (rule finite_subset[of _ "{..<ranked_prime_target odd_start remaining}"])
      auto
  have two_not_tail:
      "2 \<notin> {p. prime p \<and> odd_start \<le> p \<and>
        p < ranked_prime_target odd_start remaining}"
    using odd_start_three by simp
  show ?thesis
    using split finite_tail two_not_tail
      ranked_prime_target_zero_based[of odd_start remaining]
      remaining_pred index_positive by simp
next
  case False
  have no_gap:
      "{p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target odd_start remaining} =
       {p. prime p \<and> odd_start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
  proof (cases "odd start")
    case True
    then show ?thesis
      using False by (simp add: odd_start_def selection_odd_start_def)
  next
    case even_start: False
    have start_above_two: "2 < start" using False by simp
    have start_not_prime: "\<not> prime start"
    proof
      assume prime: "prime start"
      have "odd start" by (rule prime_odd_nat[OF prime start_above_two])
      with even_start show False by simp
    qed
    have ceiling: "odd_start = Suc start"
      using False even_start
      by (simp add: odd_start_def selection_odd_start_def)
    show ?thesis
    proof (rule Set.set_eqI)
      fix p
      show "p \<in> {p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target odd_start remaining} \<longleftrightarrow>
        p \<in> {p. prime p \<and> odd_start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
      proof
        assume member: "p \<in> {p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
        then have pprime: "prime p" and start_p: "start \<le> p"
          and upper: "p < ranked_prime_target odd_start remaining" by auto
        have unequal: "p \<noteq> start" using pprime start_not_prime by auto
        have "Suc start \<le> p" using start_p unequal by arith
        with pprime upper ceiling show
          "p \<in> {p. prime p \<and> odd_start \<le> p \<and>
            p < ranked_prime_target odd_start remaining}"
          by simp
      next
        assume member: "p \<in> {p. prime p \<and> odd_start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
        then show "p \<in> {p. prime p \<and> start \<le> p \<and>
          p < ranked_prime_target odd_start remaining}"
          using ceiling by auto
      qed
    qed
  qed
  have remaining_index: "remaining = index"
    using False by (simp add: remaining_def selection_remaining_def)
  show ?thesis
    using no_gap remaining_index
      ranked_prime_target_zero_based[of odd_start remaining] by simp
qed

theorem selection_initial_state_has_ranked_target:
  fixes start index leaf :: nat
  assumes active: "\<not> (start \<le> 2 \<and> index = 0)"
  defines "initial \<equiv> selection_initial_state start index leaf"
    and "target \<equiv> ranked_prime_target (selection_odd_start start)
      (selection_remaining start index)"
  shows "ranked_target_invariant target initial"
proof -
  have odd: "odd (selection_odd_start start)"
    by (rule selection_odd_start_properties(1))
  have lower: "3 \<le> selection_odd_start start"
    by (rule selection_odd_start_properties(2))
  have width_positive:
      "0 < selection_initial_width leaf (selection_remaining start index)"
    by (simp add: selection_initial_width_def)
  have target_rank:
      "prime_block_count (selection_odd_start start) (target - 1) =
        selection_remaining start index"
    unfolding target_def
    by (rule ranked_prime_target_block_count) (use lower in arith)
  show ?thesis
    using odd lower width_positive target_rank ranked_prime_target_lower
    by (simp add: ranked_target_invariant_def initial_def
        selection_initial_state_def Let_def target_def)
qed

lemma arithmetic_prime_selection_correct_combined:
  shows "prime (arithmetic_prime_selection start index leaf) \<and>
    start \<le> arithmetic_prime_selection start index leaf \<and>
    card {p. prime p \<and> start \<le> p \<and>
      p < arithmetic_prime_selection start index leaf} = index"
proof (cases "start \<le> 2 \<and> index = 0")
  case True
  then show ?thesis
    by (auto simp: arithmetic_prime_selection_def dest: prime_gt_1_nat)
next
  case False
  let ?initial = "selection_initial_state start index leaf"
  let ?odd_start = "selection_odd_start start"
  let ?remaining = "selection_remaining start index"
  let ?target = "ranked_prime_target ?odd_start ?remaining"
  have invariant: "ranked_target_invariant ?target ?initial"
    by (rule selection_initial_state_has_ranked_target[OF False])
  obtain final where expansion:
      "odd_expansion_loop ?initial = Some final"
    using odd_expansion_loop_terminates[OF invariant] by blast
  have final_the: "the (odd_expansion_loop ?initial) = final"
    using expansion by simp
  have selected:
      "odd_window_descent (expansion_start final) (expansion_width final)
        (expansion_remaining final) = ?target"
    by (rule odd_expansion_then_descent_returns_target[OF invariant expansion])
  have condition_false: "(start \<le> 2 \<and> index = 0) = False"
    using False by simp
  have result_target: "arithmetic_prime_selection start index leaf = ?target"
    unfolding arithmetic_prime_selection_def
    by (simp only: condition_false if_False Let_def final_the selected)
  have local_rank:
      "card {p. prime p \<and> start \<le> p \<and> p < ?target} = index"
    by (rule selection_local_rank[OF False])
  have result_prime: "prime (arithmetic_prime_selection start index leaf)"
    using result_target by simp
  have start_odd_start: "start \<le> ?odd_start"
    by (rule selection_odd_start_properties(3))
  have odd_start_target: "?odd_start \<le> ?target"
    by (rule ranked_prime_target_lower)
  have start_target: "start \<le> ?target"
    using start_odd_start odd_start_target by (rule order_trans)
  have result_lower: "start \<le> arithmetic_prime_selection start index leaf"
    using result_target start_target by simp
  have result_rank: "card {p. prime p \<and> start \<le> p \<and>
      p < arithmetic_prime_selection start index leaf} = index"
    using result_target local_rank by simp
  show ?thesis using result_prime result_lower result_rank by blast
qed

theorem arithmetic_prime_selection_correct:
  shows "prime (arithmetic_prime_selection start index leaf)"
    "start \<le> arithmetic_prime_selection start index leaf"
    "card {p. prime p \<and> start \<le> p \<and>
      p < arithmetic_prime_selection start index leaf} = index"
  using arithmetic_prime_selection_correct_combined[of start index leaf]
  by blast+

text \<open>The public arithmetic theorem has no supplied target assumption.
The target is constructed by iterating Isabelle's least prime at or above the
requested lower bound and is proved to have the requested zero-based rank.
The initialized state exactly follows production's early 2 branch, odd
ceiling, residual index, and \<open>max(leaf, 4*(remaining+1))\<close> width.

This remains a mathematical refinement of successful execution.  The exact
interval-count provider is connected in the preceding prefix-image theory;
dynamic prefix admission, Python integer/type validation, configured budget
exceptions, scheduler authority, publication, and metrics remain separate
runtime obligations.  The arithmetic theorem permits every natural initial
leaf hint, while the Python entry point rejects hints below 8; source-level
correspondence therefore applies only after that runtime validation.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms ranked_prime_target_zero_based
      selection_initial_state_has_ranked_target
      arithmetic_prime_selection_correct}) then ()
    else error "Prime selection initialization refinement depends on an oracle";
\<close>

end
