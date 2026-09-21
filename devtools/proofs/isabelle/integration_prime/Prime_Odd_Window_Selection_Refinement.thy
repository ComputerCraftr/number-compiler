theory Prime_Odd_Window_Selection_Refinement
  imports Prime_Prefix_Image_Projection_Refinement
begin

text \<open>This theory models the second, shrinking loop of
\<open>nth_prime_at_or_after\<close>.  Its state fields are production's
\<open>(odd_start, length, remaining)\<close>, and every branch consumes the exact
half-open interval count established by the prefix-image theory.\<close>

definition odd_window_high :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "odd_window_high start width = start + 2 * (width - 1)"

definition odd_window_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "odd_window_count start width =
    (if width = 0 then 0 else prime_block_count start (odd_window_high start width))"

lemma odd_window_count_one [simp]:
  "odd_window_count start 1 = (if prime start then 1 else 0)"
  by (simp add: odd_window_count_def odd_window_high_def singleton_prime_block)

lemma odd_nat_ge_three_not_prime:
  fixes start width :: nat
  assumes odd: "odd start" and lower: "3 \<le> start" and positive: "0 < width"
  shows "\<not> prime (start + 2 * width - 1)"
proof -
  obtain m where start_shape: "start = 2 * m + 1"
    using odd by (rule oddE)
  have seam_shape: "start + 2 * width - 1 = 2 * (m + width)"
    using start_shape by simp
  have two_dvd: "2 dvd (start + 2 * width - 1)"
    unfolding seam_shape by simp
  have seam_not_two: "start + 2 * width - 1 \<noteq> 2"
    using lower positive by arith
  show ?thesis
  proof
    assume seam_prime: "prime (start + 2 * width - 1)"
    have "2 = start + 2 * width - 1"
      using two_is_prime_nat seam_prime two_dvd by (rule primes_dvd_imp_eq)
    with seam_not_two show False by simp
  qed
qed

lemma odd_window_count_exact_set:
  assumes positive: "0 < width"
  shows "odd_window_count start width =
    card {p. prime p \<and> start \<le> p \<and> p \<le> odd_window_high start width}"
  unfolding odd_window_count_def
  using positive prime_block_count_exact[of start "odd_window_high start width"]
  by (simp add: odd_window_high_def)

lemma prime_interval_drop_nonprime_endpoint:
  fixes start endpoint :: nat
  assumes endpoint: "\<not> prime endpoint"
  shows "{p. prime p \<and> start \<le> p \<and> p \<le> endpoint} =
    {p. prime p \<and> start \<le> p \<and> p \<le> endpoint - 1}"
proof (rule Set.set_eqI)
  fix p
  show "p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint} \<longleftrightarrow>
      p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint - 1}"
  proof
    assume member:
      "p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint}"
    then have prime: "prime p" and bound: "p \<le> endpoint" by auto
    have unequal: "p \<noteq> endpoint" using prime endpoint by auto
    have "p \<le> endpoint - 1" using bound unequal by arith
    with member show
      "p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint - 1}"
      by simp
  next
    assume member:
      "p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint - 1}"
    then show
      "p \<in> {p. prime p \<and> start \<le> p \<and> p \<le> endpoint}"
      by auto
  qed
qed

theorem odd_prime_window_split:
  assumes odd: "odd start" and lower: "3 \<le> start"
    and left_positive: "0 < left" and left_short: "left < width"
  shows "odd_window_count start width =
    odd_window_count start left +
      odd_window_count (start + 2 * left) (width - left)"
proof -
  let ?middle = "start + 2 * left - 1"
  let ?right = "start + 2 * left"
  let ?high = "odd_window_high start width"
  have start_middle: "start \<le> ?middle" using left_positive by arith
  have middle_high: "?middle < ?high"
    unfolding odd_window_high_def using left_positive left_short by arith
  have split:
      "prime_block_count start ?high =
        prime_block_count start ?middle + prime_block_count ?right ?high"
    using prime_block_bisection[OF start_middle middle_high] left_positive
    by simp
  have seam_not_prime: "\<not> prime ?middle"
    by (rule odd_nat_ge_three_not_prime[OF odd lower left_positive])
  have left_end:
      "prime_block_count start ?middle =
        prime_block_count start (odd_window_high start left)"
  proof -
    have left_high: "odd_window_high start left = ?middle - 1"
      using left_positive by (simp add: odd_window_high_def)
    have exact_middle:
        "prime_block_count start ?middle =
          card {p. prime p \<and> start \<le> p \<and> p \<le> ?middle}"
      by (rule prime_block_count_exact[OF start_middle])
    have exact_left:
        "prime_block_count start (odd_window_high start left) =
          card {p. prime p \<and> start \<le> p \<and>
            p \<le> odd_window_high start left}"
      by (rule prime_block_count_exact)
        (use left_positive in \<open>simp add: odd_window_high_def\<close>)
    have set_eq:
        "{p. prime p \<and> start \<le> p \<and> p \<le> ?middle} =
          {p. prime p \<and> start \<le> p \<and>
            p \<le> odd_window_high start left}"
      using prime_interval_drop_nonprime_endpoint[OF seam_not_prime,
          of start] left_high
      by simp
    show ?thesis using exact_middle exact_left set_eq by simp
  qed
  have right_positive: "0 < width - left" using left_short by simp
  have right_high:
      "odd_window_high ?right (width - left) = ?high"
    unfolding odd_window_high_def using left_positive left_short by arith
  show ?thesis
    using split left_end right_high left_positive right_positive
    by (simp add: odd_window_count_def)
qed

function odd_window_descent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "odd_window_descent start width remaining =
    (if width \<le> 1 then start
     else
       (let left = width div 2;
            left_count = odd_window_count start left
        in if remaining < left_count
           then odd_window_descent start left remaining
           else odd_window_descent (start + 2 * left) (width - left)
             (remaining - left_count)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(start,width,remaining). width)") auto

declare odd_window_descent.simps[simp del]

lemma odd_window_descent_equation:
  assumes width: "1 < width"
  defines "left \<equiv> width div 2"
  shows "odd_window_descent start width remaining =
    (if remaining < odd_window_count start left
     then odd_window_descent start left remaining
     else odd_window_descent (start + 2 * left) (width - left)
       (remaining - odd_window_count start left))"
  using width by (simp add: odd_window_descent.simps left_def Let_def)

lemma prime_block_count_append_before:
  assumes start_split: "start \<le> split" and split_result: "split \<le> result"
  shows "prime_block_count start (result - 1) =
    prime_block_count start (split - 1) +
      prime_block_count split (result - 1)"
proof -
  have first_mono: "prime_rank (start - 1) \<le> prime_rank (split - 1)"
    by (rule prime_rank_mono) (use start_split in arith)
  have second_mono: "prime_rank (split - 1) \<le> prime_rank (result - 1)"
    by (rule prime_rank_mono) (use split_result in arith)
  show ?thesis
    unfolding prime_block_count_def using first_mono second_mono by arith
qed

definition odd_window_descent_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "odd_window_descent_spec start width remaining \<longleftrightarrow>
    (let result = odd_window_descent start width remaining
     in prime result \<and> start \<le> result \<and>
        result \<le> odd_window_high start width \<and>
        prime_block_count start (result - 1) = remaining)"

theorem odd_window_descent_correct_state:
  assumes odd: "odd start" and lower: "3 \<le> start"
    and positive: "0 < width"
    and admitted: "remaining < odd_window_count start width"
  shows "odd_window_descent_spec start width remaining"
  using odd lower positive admitted
proof (induction width arbitrary: start remaining rule: less_induct)
  case (less width)
  show ?case
  proof (cases "width = 1")
    case True
    have count_one:
        "odd_window_count start width = (if prime start then 1 else 0)"
      using odd_window_count_one[of start] True by metis
    have start_prime: "prime start"
    proof (rule ccontr)
      assume "\<not> prime start"
      then show False using less.prems(4) count_one by simp
    qed
    have remaining_zero: "remaining = 0"
      using less.prems(4) count_one start_prime by simp
    have before_zero: "prime_block_count start (start - 1) = 0"
      unfolding prime_block_count_def
      using prime_rank_mono[of "start - 1" start] by simp
    show ?thesis
      using True start_prime remaining_zero before_zero
      by (simp add: odd_window_descent_spec_def odd_window_descent.simps
          odd_window_high_def)
  next
    case False
    with less.prems(3) have width_gt_one: "1 < width" by arith
    let ?left = "width div 2"
    let ?right_start = "start + 2 * ?left"
    let ?right_width = "width - ?left"
    have left_positive: "0 < ?left" using width_gt_one by simp
    have left_short: "?left < width" using width_gt_one by simp
    have right_positive: "0 < ?right_width" using left_short by simp
    have right_short: "?right_width < width"
      using left_positive by simp
    have split:
        "odd_window_count start width =
          odd_window_count start ?left +
            odd_window_count ?right_start ?right_width"
      by (rule odd_prime_window_split[OF less.prems(1,2) left_positive
            left_short])
    show ?thesis
    proof (cases "remaining < odd_window_count start ?left")
      case True
      note IH = less.IH[OF left_short less.prems(1,2) left_positive True]
      obtain result where result:
          "result = odd_window_descent start ?left remaining"
          "prime result" "start \<le> result"
          "result \<le> odd_window_high start ?left"
          "prime_block_count start (result - 1) = remaining"
        using IH unfolding odd_window_descent_spec_def Let_def by blast
      have current_result:
          "odd_window_descent start width remaining = result"
        using width_gt_one True result(1)
        by (simp add: odd_window_descent_equation)
      have result_high: "result \<le> odd_window_high start width"
        using result(4) left_positive left_short
        unfolding odd_window_high_def by arith
      show ?thesis
        using result current_result result_high
        by (simp add: odd_window_descent_spec_def)
    next
      case False
      have right_admitted:
          "remaining - odd_window_count start ?left <
            odd_window_count ?right_start ?right_width"
        using less.prems(4) split False by arith
      have right_odd: "odd ?right_start" using less.prems(1) by simp
      have right_lower: "3 \<le> ?right_start" using less.prems(2) by simp
      note IH = less.IH[OF right_short right_odd right_lower right_positive
          right_admitted]
      obtain result where result:
          "result = odd_window_descent ?right_start ?right_width
            (remaining - odd_window_count start ?left)"
          "prime result" "?right_start \<le> result"
          "result \<le> odd_window_high ?right_start ?right_width"
          "prime_block_count ?right_start (result - 1) =
            remaining - odd_window_count start ?left"
        using IH unfolding odd_window_descent_spec_def Let_def by blast
      have current_result:
          "odd_window_descent start width remaining = result"
        using width_gt_one False result(1)
        by (simp add: odd_window_descent_equation)
      have result_right: "?right_start \<le> result" using result by simp
      have left_before_right:
          "prime_block_count start (?right_start - 1) =
            odd_window_count start ?left"
      proof -
        have seam_not_prime: "\<not> prime (?right_start - 1)"
          using odd_nat_ge_three_not_prime[OF less.prems(1,2) left_positive]
            by simp
        have exact:
            "prime_block_count start (?right_start - 1) =
              card {p. prime p \<and> start \<le> p \<and> p \<le> ?right_start - 1}"
          by (rule prime_block_count_exact) (use left_positive in arith)
        have left_exact:
            "odd_window_count start ?left =
              card {p. prime p \<and> start \<le> p \<and>
                p \<le> odd_window_high start ?left}"
          by (rule odd_window_count_exact_set[OF left_positive])
        have endpoint:
            "?right_start - 1 - 1 = odd_window_high start ?left"
          unfolding odd_window_high_def using left_positive by arith
        have set_eq:
            "{p. prime p \<and> start \<le> p \<and> p \<le> ?right_start - 1} =
              {p. prime p \<and> start \<le> p \<and>
                p \<le> odd_window_high start ?left}"
          using prime_interval_drop_nonprime_endpoint[OF seam_not_prime,
              of start] endpoint
          by simp
        show ?thesis using exact left_exact set_eq by simp
      qed
      have before_split:
          "prime_block_count start (result - 1) =
            prime_block_count start (?right_start - 1) +
              prime_block_count ?right_start (result - 1)"
        by (rule prime_block_count_append_before) (use result_right in simp_all)
      have remaining_ge_left:
          "odd_window_count start ?left \<le> remaining" using False by simp
      have result_high: "result \<le> odd_window_high start width"
        using result(4) left_positive left_short
        unfolding odd_window_high_def by arith
      have result_rank: "prime_block_count start (result - 1) = remaining"
        using before_split left_before_right result(5) remaining_ge_left by arith
      show ?thesis
        using result current_result result_right result_high result_rank
        by (simp add: odd_window_descent_spec_def)
    qed
  qed
qed

theorem odd_window_descent_correct:
  assumes odd: "odd start" and lower: "3 \<le> start"
    and positive: "0 < width"
    and admitted: "remaining < odd_window_count start width"
  defines "result \<equiv> odd_window_descent start width remaining"
  shows "prime result"
    "start \<le> result"
    "result \<le> odd_window_high start width"
    "prime_block_count start (result - 1) = remaining"
  using odd_window_descent_correct_state[OF odd lower positive admitted]
  unfolding odd_window_descent_spec_def Let_def result_def by blast+

corollary odd_window_descent_returns_zero_based_selection:
  assumes odd: "odd start" and lower: "3 \<le> start"
    and positive: "0 < width"
    and admitted: "remaining < odd_window_count start width"
  defines "result \<equiv> odd_window_descent start width remaining"
  shows "prime result \<and> start \<le> result \<and>
    card {p. prime p \<and> start \<le> p \<and> p < result} = remaining"
proof -
  note correct = odd_window_descent_correct[OF odd lower positive admitted,
      folded result_def]
  have exact:
      "prime_block_count start (result - 1) =
        card {p. prime p \<and> start \<le> p \<and> p < result}"
  proof (cases "result = start")
    case True
    have block_zero: "prime_block_count start (start - 1) = 0"
      unfolding prime_block_count_def
      using prime_rank_mono[of "start - 1" start] by simp
    show ?thesis using True block_zero by simp
  next
    case False
    have start_before: "start < result" using correct(2) False by arith
    have exact_block:
        "prime_block_count start (result - 1) =
          card {p. prime p \<and> start \<le> p \<and> p \<le> result - 1}"
      by (rule prime_block_count_exact) (use start_before in arith)
    have set_eq:
        "{p. prime p \<and> start \<le> p \<and> p \<le> result - 1} =
          {p. prime p \<and> start \<le> p \<and> p < result}"
      using start_before by auto
    show ?thesis using exact_block set_eq by simp
  qed
  show ?thesis using correct exact by simp
qed

text \<open>The recursive equations are the production descent at
\<open>select.py:376-385\<close>, including its floor-halved left width, shifted
right start, and remaining-rank subtraction.  The theorem assumes only the
ready-loop condition returned by expansion: the target rank is below the exact
current interval count.  The prefix-image theorem supplies that count to the
runtime consumer.

This does not yet refine the preceding doubling loop, the special handling of
2, or the initial odd ceiling.  It also does not model configured budget
failures, dynamic prefix discovery, scheduler authentication, metrics, or
Python source execution.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms odd_prime_window_split odd_window_descent_correct
      odd_window_descent_returns_zero_based_selection}) then ()
    else error "Prime odd-window selection refinement depends on an oracle";
\<close>

end
