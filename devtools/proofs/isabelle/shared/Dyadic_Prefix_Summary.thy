theory Dyadic_Prefix_Summary
  imports Dyadic_Source_Lift
begin

text \<open>The finite signed-prefix consumer of a source label word.  The first
component is its total weight; the second includes the empty prefix and is
therefore always nonpositive.  Source admission remains in the dyadic source
action: this consumer does not choose a branch word.\<close>

fun prefix_summary :: "('label \<Rightarrow> int) \<Rightarrow> 'label list \<Rightarrow> int * int" where
  "prefix_summary weight [] = (0, 0)"
| "prefix_summary weight (x # xs) =
    (let tail = prefix_summary weight xs in
      (weight x + fst tail, min 0 (weight x + snd tail)))"

lemma prefix_summary_minimum_nonpositive [simp]:
  "snd (prefix_summary weight xs) \<le> 0"
  by (cases xs) (auto simp: Let_def)

lemma prefix_summary_min_shift:
  "min 0 (w + min a (d + b)) =
    min (min 0 (w + a)) ((w + d) + b)"
  for w a d b :: int
  by (auto simp: min_def; linarith)

lemma prefix_summary_append:
  "prefix_summary weight (xs @ ys) =
    (fst (prefix_summary weight xs) + fst (prefix_summary weight ys),
     min (snd (prefix_summary weight xs))
       (fst (prefix_summary weight xs) + snd (prefix_summary weight ys)))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: Let_def prefix_summary_min_shift algebra_simps)
qed

lemma prefix_summary_delta:
  "fst (prefix_summary weight xs) = sum_list (map weight xs)"
  by (induction xs) (simp_all add: Let_def)

definition prefix_guard ::
    "('label \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'label list \<Rightarrow> bool"
where
  "prefix_guard weight balance xs \<longleftrightarrow>
    (\<forall>k \<le> length xs.
      0 \<le> balance + sum_list (map weight (take k xs)))"

lemma prefix_guard_cons:
  "prefix_guard weight balance (x # xs) \<longleftrightarrow>
    0 \<le> balance \<and> prefix_guard weight (balance + weight x) xs"
proof
  assume guard: "prefix_guard weight balance (x # xs)"
  have initial: "0 \<le> balance"
  proof -
    have "0 \<le> balance + sum_list (map weight (take 0 (x # xs)))"
      using guard unfolding prefix_guard_def by blast
    then show ?thesis by simp
  qed
  have tail: "prefix_guard weight (balance + weight x) xs"
    unfolding prefix_guard_def
  proof (intro allI impI)
    fix k assume "k \<le> length xs"
    then have "Suc k \<le> length (x # xs)" by simp
    then have "0 \<le> balance +
        sum_list (map weight (take (Suc k) (x # xs)))"
      using guard unfolding prefix_guard_def by blast
    then show "0 \<le> balance + weight x +
        sum_list (map weight (take k xs))" by simp
  qed
  show "0 \<le> balance \<and> prefix_guard weight (balance + weight x) xs"
    using initial tail by simp
next
  assume guard: "0 \<le> balance \<and> prefix_guard weight (balance + weight x) xs"
  show "prefix_guard weight balance (x # xs)"
    unfolding prefix_guard_def
  proof (intro allI impI)
    fix k assume bound: "k \<le> length (x # xs)"
    show "0 \<le> balance + sum_list (map weight (take k (x # xs)))"
    proof (cases k)
      case 0
      with guard show ?thesis by simp
    next
      case (Suc j)
      with bound have "j \<le> length xs" by simp
      then have "0 \<le> (balance + weight x) +
          sum_list (map weight (take j xs))"
        using guard unfolding prefix_guard_def by blast
      with Suc show ?thesis by simp
    qed
  qed
qed

lemma prefix_summary_guard_iff:
  "prefix_guard weight balance xs \<longleftrightarrow>
    0 \<le> balance + snd (prefix_summary weight xs)"
proof (induction xs arbitrary: balance)
  case Nil
  then show ?case by (simp add: prefix_guard_def)
next
  case (Cons x xs)
  then show ?case
    by (simp add: prefix_guard_cons Let_def min_def; linarith)
qed

fun first_negative ::
    "('label \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'label list \<Rightarrow> nat option"
where
  "first_negative weight balance [] = None"
| "first_negative weight balance (x # xs) =
    (if balance + weight x < 0 then Some 0
     else map_option Suc (first_negative weight (balance + weight x) xs))"

lemma first_negative_none_iff:
  assumes "0 \<le> balance"
  shows "first_negative weight balance xs = None \<longleftrightarrow>
    prefix_guard weight balance xs"
  using assms
proof (induction xs arbitrary: balance)
  case Nil
  then show ?case by (simp add: prefix_guard_def)
next
  case (Cons x xs)
  show ?case
  proof (cases "balance + weight x < 0")
    case True
    have "\<not> prefix_guard weight (balance + weight x) xs"
      using True prefix_summary_minimum_nonpositive[of weight xs]
      by (simp add: prefix_summary_guard_iff; linarith)
    with True show ?thesis by (simp add: prefix_guard_cons)
  next
    case False
    then have next_balance: "0 \<le> balance + weight x" by simp
    from Cons.IH[OF next_balance] Cons.prems False
    show ?thesis by (simp add: prefix_guard_cons)
  qed
qed

lemma first_negative_append:
  "first_negative weight balance (xs @ ys) =
    (case first_negative weight balance xs of
      Some index \<Rightarrow> Some index
    | None \<Rightarrow>
        map_option (\<lambda>index. length xs + index)
          (first_negative weight
            (balance + fst (prefix_summary weight xs)) ys))"
proof (induction xs arbitrary: balance)
  case Nil
  then show ?case by (cases "first_negative weight balance ys") simp_all
next
  case (Cons x xs)
  let ?next = "balance + weight x"
  show ?case
  proof (cases "?next < 0")
    case True
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "first_negative weight ?next xs")
      case None
      with Cons.IH[of ?next] False show ?thesis
        by (cases "first_negative weight
            (?next + fst (prefix_summary weight xs)) ys")
          (simp_all add: Let_def algebra_simps)
    next
      case (Some index)
      with Cons.IH[of ?next] False show ?thesis
        by (simp add: Let_def)
    qed
  qed
qed

lemma first_negative_descent:
  assumes "0 \<le> balance"
  shows "first_negative weight balance (xs @ ys) =
    (if balance + snd (prefix_summary weight xs) < 0 then
       first_negative weight balance xs
     else map_option (\<lambda>index. length xs + index)
       (first_negative weight
         (balance + fst (prefix_summary weight xs)) ys))"
proof -
  have none_iff:
    "first_negative weight balance xs = None \<longleftrightarrow>
      0 \<le> balance + snd (prefix_summary weight xs)"
    using assms by (simp add: first_negative_none_iff prefix_summary_guard_iff)
  show ?thesis
  proof (cases "first_negative weight balance xs")
    case None
    with none_iff show ?thesis by (simp add: first_negative_append)
  next
    case (Some index)
    with none_iff show ?thesis by (simp add: first_negative_append)
  qed
qed

lemma (in dyadic_source_action) dyadic_source_prefix_summary_append:
  "prefix_summary weight (dyadic_source_word step label source (first + second)) =
    (let left = prefix_summary weight
         (dyadic_source_word step label source first);
         right = prefix_summary weight
         (dyadic_source_word step label
           (dyadic_source_orbit step source first) second)
     in (fst left + fst right, min (snd left) (fst left + snd right)))"
  by (simp add: dyadic_source_word_append prefix_summary_append Let_def)

lemma (in dyadic_source_action) dyadic_source_prefix_summary_high_fiber:
  "prefix_summary weight
      (dyadic_source_word step label (source + 2^n * lift_amount) n) =
    prefix_summary weight (dyadic_source_word step label source n)"
  using exact_precision_source_lift[of source n lift_amount] by simp

lemma (in dyadic_source_action) dyadic_source_prefix_summary_low_cylinder:
  "prefix_summary weight (dyadic_source_word step label source n) =
    prefix_summary weight
      (dyadic_source_word step label (source mod 2^n) n)"
  using source_residue_lift[of source n] by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms prefix_summary_minimum_nonpositive prefix_summary_min_shift
      prefix_summary_append prefix_summary_delta prefix_guard_cons
      prefix_summary_guard_iff first_negative_none_iff first_negative_append
      first_negative_descent
      dyadic_source_action.dyadic_source_prefix_summary_append
      dyadic_source_action.dyadic_source_prefix_summary_high_fiber
      dyadic_source_action.dyadic_source_prefix_summary_low_cylinder})
    then () else error "Dyadic prefix summary depends on an oracle";
\<close>

end
