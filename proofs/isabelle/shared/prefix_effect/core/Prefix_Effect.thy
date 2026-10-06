theory Prefix_Effect
  imports Main
begin

text \<open>The finite signed-prefix consumer of a source label word.  The first
component is its total weight; the second includes the empty prefix and is
therefore always nonpositive.  Source admission remains with the family action: this consumer does not
choose a branch word.\<close>

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

text \<open>The shared active-width ledger is the product of two prefix effects:
the lower walk uses each displacement, while the upper walk uses its
negation.  This keeps width extrema (including the initial and final width)
separate from any particular source's carry or borrow authority.  A ledger is
only a summary of an already authenticated row word.\<close>

record blank_ledger =
  blank_delta :: int
  blank_minimum :: int
  blank_maximum :: int

definition blank_ledger_admitted :: "blank_ledger \<Rightarrow> bool" where
  "blank_ledger_admitted L \<longleftrightarrow>
    blank_minimum L \<le> min 0 (blank_delta L) \<and>
    max 0 (blank_delta L) \<le> blank_maximum L"

definition blank_ledger_identity :: blank_ledger where
  "blank_ledger_identity = \<lparr>blank_delta=0, blank_minimum=0,
    blank_maximum=0\<rparr>"

definition blank_ledger_then :: "blank_ledger \<Rightarrow> blank_ledger \<Rightarrow> blank_ledger" where
  "blank_ledger_then A B = \<lparr>
    blank_delta=blank_delta A + blank_delta B,
    blank_minimum=min (blank_minimum A)
      (blank_delta A + blank_minimum B),
    blank_maximum=max (blank_maximum A)
      (blank_delta A + blank_maximum B)\<rparr>"

lemma blank_ledger_then_assoc:
  "blank_ledger_then (blank_ledger_then A B) C =
    blank_ledger_then A (blank_ledger_then B C)"
  by (cases A; cases B; cases C)
    (simp add: blank_ledger_then_def min.assoc max.assoc
      min_add_distrib_right max_add_distrib_right algebra_simps)

lemma blank_ledger_then_admitted:
  assumes "blank_ledger_admitted A" "blank_ledger_admitted B"
  shows "blank_ledger_admitted (blank_ledger_then A B)"
  using assms
  unfolding blank_ledger_admitted_def blank_ledger_then_def
  by (auto simp: min_def max_def; linarith)

lemma blank_ledger_then_identity:
  assumes "blank_ledger_admitted A"
  shows "blank_ledger_then blank_ledger_identity A = A"
    "blank_ledger_then A blank_ledger_identity = A"
proof -
  have bounds: "blank_minimum A \<le> 0 \<and>
      blank_minimum A \<le> blank_delta A \<and>
      0 \<le> blank_maximum A \<and>
      blank_delta A \<le> blank_maximum A"
    using assms
  proof (cases "0 \<le> blank_delta A")
    case True
    then show ?thesis using assms
      by (auto simp: blank_ledger_admitted_def min_def max_def; linarith)
  next
    case False
    then show ?thesis using assms
      by (auto simp: blank_ledger_admitted_def min_def max_def; linarith)
  qed
  show "blank_ledger_then blank_ledger_identity A = A"
    using bounds
    by (cases A; simp_all add: blank_ledger_identity_def blank_ledger_then_def
        min_def max_def)
  show "blank_ledger_then A blank_ledger_identity = A"
    using bounds
    by (cases A; simp_all add: blank_ledger_identity_def blank_ledger_then_def
        min_def max_def)
qed

definition blank_ledger_word :: "('label \<Rightarrow> int) \<Rightarrow> 'label list \<Rightarrow> blank_ledger" where
  "blank_ledger_word weight xs = \<lparr>
    blank_delta = fst (prefix_summary weight xs),
    blank_minimum = snd (prefix_summary weight xs),
    blank_maximum = - snd (prefix_summary (\<lambda>x. - weight x) xs)\<rparr>"

lemma prefix_summary_minimum_le_delta:
  "snd (prefix_summary weight xs) \<le> fst (prefix_summary weight xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail: "snd (prefix_summary weight xs) \<le>
      fst (prefix_summary weight xs)" using Cons.IH .
  show ?case
    using tail by (simp add: Let_def min_def; linarith)
qed

lemma sum_list_neg_map:
  fixes weight :: "'label \<Rightarrow> int"
  shows "sum_list (map (\<lambda>x. - weight x) xs) =
    - sum_list (map weight xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (simp add: algebra_simps)
qed

lemma int_neg_min_eq_max:
  "-(min a b::int) = max (-a) (-b)"
proof (cases "a \<le> b")
  case True
  then have "-b \<le> -a" by linarith
  then show ?thesis using True by (simp add: min_def max_def)
next
  case False
  then have "-a \<le> -b" by linarith
  then show ?thesis using False by (simp add: min_def max_def)
qed

lemma blank_ledger_word_admitted [simp]:
  "blank_ledger_admitted (blank_ledger_word weight xs)"
proof -
  have lower_zero: "snd (prefix_summary weight xs) \<le> 0"
    by simp
  have lower_delta: "snd (prefix_summary weight xs) \<le>
      fst (prefix_summary weight xs)"
    by (rule prefix_summary_minimum_le_delta)
  have upper_zero:
    "- snd (prefix_summary (\<lambda>x. - weight x) xs) \<ge> 0"
    using prefix_summary_minimum_nonpositive[of "\<lambda>x. - weight x" xs]
    by linarith
  have upper_delta:
    "- snd (prefix_summary (\<lambda>x. - weight x) xs) \<ge>
      fst (prefix_summary weight xs)"
    using prefix_summary_minimum_le_delta[of "\<lambda>x. - weight x" xs]
      prefix_summary_delta[of "\<lambda>x. - weight x" xs]
      prefix_summary_delta[of weight xs]
    by (simp add: sum_list_neg_map; linarith)
  show ?thesis
    using lower_zero lower_delta upper_zero upper_delta
    by (simp add: blank_ledger_admitted_def blank_ledger_word_def)
qed

lemma blank_ledger_word_append:
  "blank_ledger_word weight (xs @ ys) =
    blank_ledger_then (blank_ledger_word weight xs)
      (blank_ledger_word weight ys)"
proof -
  have neg_delta:
    "fst (prefix_summary (\<lambda>x. - weight x) xs) =
      - fst (prefix_summary weight xs)"
    by (simp add: prefix_summary_delta sum_list_neg_map)
  have upper:
    "- snd (prefix_summary (\<lambda>x. - weight x) (xs @ ys)) =
      max (- snd (prefix_summary (\<lambda>x. - weight x) xs))
        (fst (prefix_summary weight xs) -
          snd (prefix_summary (\<lambda>x. - weight x) ys))"
    using prefix_summary_append[of "\<lambda>x. - weight x" xs ys]
      neg_delta
    by (simp add: int_neg_min_eq_max algebra_simps)
  show ?thesis
    using prefix_summary_append[of weight xs ys] upper
    by (simp add: blank_ledger_word_def blank_ledger_then_def)
qed

fun blank_ledger_repeat :: "nat \<Rightarrow> blank_ledger \<Rightarrow> blank_ledger" where
  "blank_ledger_repeat 0 A = blank_ledger_identity"
| "blank_ledger_repeat (Suc n) A =
    blank_ledger_then (blank_ledger_repeat n A) A"

lemma blank_ledger_repeat_closed_form:
  assumes admitted: "blank_ledger_admitted A"
  shows "blank_ledger_repeat n A =
    (if n=0 then blank_ledger_identity else
      \<lparr>blank_delta = int n * blank_delta A,
       blank_minimum = blank_minimum A +
         min 0 ((int n - 1) * blank_delta A),
       blank_maximum = blank_maximum A +
         max 0 ((int n - 1) * blank_delta A)\<rparr>)"
  using admitted
proof (induction n)
  case 0
  then show ?case by (simp add: blank_ledger_identity_def)
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    have one: "blank_ledger_repeat (Suc 0) A =
        blank_ledger_then blank_ledger_identity A"
      by (simp add: blank_ledger_repeat.simps)
    have right: "blank_ledger_then blank_ledger_identity A = A"
      by (rule blank_ledger_then_identity(1)[OF Suc.prems])
    show ?thesis using 0 one right by (simp add: blank_ledger_identity_def)
  next
    case (Suc k)
    let ?d = "blank_delta A"
    let ?lo = "blank_minimum A"
    let ?hi = "blank_maximum A"
    have prior:
      "blank_ledger_repeat n A =
        \<lparr>blank_delta=int n * ?d,
          blank_minimum=?lo + min 0 ((int n - 1) * ?d),
          blank_maximum=?hi + max 0 ((int n - 1) * ?d)\<rparr>"
      using Suc.IH Suc.prems by (simp add: Suc)
    have min_offset:
      "min (min 0 (int k * ?d)) (int (Suc k) * ?d) =
        min 0 (int (Suc k) * ?d)"
    proof (cases "0 \<le> ?d")
      case True
      have k_nonneg: "0 \<le> int k" by simp
      have kd: "0 \<le> int k * ?d"
        by (rule mult_nonneg_nonneg[OF k_nonneg True])
      have m1: "min 0 (int k * ?d) = 0"
        using kd by (simp add: min_def)
      show ?thesis by (simp only: m1)
    next
      case False
      have d_nonpos: "?d \<le> 0" using False by linarith
      have k_nonneg: "0 \<le> int k" by simp
      have kd: "int k * ?d \<le> 0"
        by (rule mult_nonneg_nonpos[OF k_nonneg d_nonpos])
      have sk_nonneg: "0 \<le> int (Suc k)" by simp
      have sd: "int (Suc k) * ?d \<le> 0"
        by (rule mult_nonneg_nonpos[OF sk_nonneg d_nonpos])
      have step: "int (Suc k) * ?d = int k * ?d + ?d"
        by (simp add: algebra_simps)
      have le: "int (Suc k) * ?d \<le> int k * ?d"
        using step d_nonpos by linarith
      have m1: "min 0 (int k * ?d) = int k * ?d"
        using kd by (simp add: min_def)
      have m2: "min (int k * ?d) (int (Suc k) * ?d) =
          int (Suc k) * ?d"
        using le by (simp add: min_def)
      have m3: "min 0 (int (Suc k) * ?d) =
          int (Suc k) * ?d"
        using sd by (simp add: min_def)
      show ?thesis by (simp only: m1 m2 m3)
    qed
    have max_offset:
      "max (max 0 (int k * ?d)) (int (Suc k) * ?d) =
        max 0 (int (Suc k) * ?d)"
    proof (cases "0 \<le> ?d")
      case True
      have k_nonneg: "0 \<le> int k" by simp
      have sk_nonneg: "0 \<le> int (Suc k)" by simp
      have kd: "0 \<le> int k * ?d"
        by (rule mult_nonneg_nonneg[OF k_nonneg True])
      have sd: "0 \<le> int (Suc k) * ?d"
        by (rule mult_nonneg_nonneg[OF sk_nonneg True])
      have step: "int (Suc k) * ?d = int k * ?d + ?d"
        by (simp add: algebra_simps)
      have le: "int k * ?d \<le> int (Suc k) * ?d"
        using step True by linarith
      have m1: "max 0 (int k * ?d) = int k * ?d"
        using kd by (simp add: max_def)
      have m2: "max (int k * ?d) (int (Suc k) * ?d) =
          int (Suc k) * ?d"
        using le by (simp add: max_def)
      have m3: "max 0 (int (Suc k) * ?d) =
          int (Suc k) * ?d"
        using sd by (simp add: max_def)
      show ?thesis by (simp only: m1 m2 m3)
    next
      case False
      have d_nonpos: "?d \<le> 0" using False by linarith
      have k_nonneg: "0 \<le> int k" by simp
      have kd: "int k * ?d \<le> 0"
        by (rule mult_nonneg_nonpos[OF k_nonneg d_nonpos])
      have m1: "max 0 (int k * ?d) = 0"
        using kd by (simp add: max_def)
      show ?thesis by (simp only: m1)
    qed
    have repeat_next:
      "blank_ledger_repeat (Suc n) A = blank_ledger_then
        \<lparr>blank_delta=int n * ?d,
          blank_minimum=?lo + min 0 ((int n - 1) * ?d),
          blank_maximum=?hi + max 0 ((int n - 1) * ?d)\<rparr> A"
      using prior by (simp only: blank_ledger_repeat.simps prior)
    have min_translation:
      "min (?lo + min 0 (int k * ?d)) (int (Suc k) * ?d + ?lo) =
        ?lo + min 0 (int (Suc k) * ?d)"
      using arg_cong[OF min_offset, where f="\<lambda>x. ?lo + x"]
      by (simp add: min_add_distrib_right algebra_simps)
    have max_translation:
      "max (?hi + max 0 (int k * ?d)) (int (Suc k) * ?d + ?hi) =
        ?hi + max 0 (int (Suc k) * ?d)"
      using arg_cong[OF max_offset, where f="\<lambda>x. ?hi + x"]
      by (simp add: max_add_distrib_right algebra_simps)
    have combined:
      "blank_ledger_then
        \<lparr>blank_delta=int n * ?d,
          blank_minimum=?lo + min 0 ((int n - 1) * ?d),
          blank_maximum=?hi + max 0 ((int n - 1) * ?d)\<rparr> A =
       \<lparr>blank_delta=int (Suc n) * ?d,
          blank_minimum=?lo + min 0 ((int (Suc n) - 1) * ?d),
          blank_maximum=?hi + max 0 ((int (Suc n) - 1) * ?d)\<rparr>"
      using min_translation max_translation
      by (cases A; simp add: blank_ledger_then_def Suc algebra_simps)
    have calc:
      "blank_ledger_repeat (Suc n) A =
       \<lparr>blank_delta=int (Suc n) * ?d,
          blank_minimum=?lo + min 0 ((int (Suc n) - 1) * ?d),
          blank_maximum=?hi + max 0 ((int (Suc n) - 1) * ?d)\<rparr>"
      using repeat_next combined by (rule trans)
    have final_rhs:
      "\<lparr>blank_delta=int (Suc n) * ?d,
        blank_minimum=?lo + min 0 ((int (Suc n) - 1) * ?d),
        blank_maximum=?hi + max 0 ((int (Suc n) - 1) * ?d)\<rparr> =
       (if Suc n=0 then blank_ledger_identity else
        \<lparr>blank_delta=int (Suc n) * ?d,
          blank_minimum=?lo + min 0 ((int (Suc n) - 1) * ?d),
          blank_maximum=?hi + max 0 ((int (Suc n) - 1) * ?d)\<rparr>)"
      using Suc by simp
    show ?thesis using calc final_rhs by (rule trans)
  qed
qed

lemma blank_ledger_word_repeat:
  "blank_ledger_word weight (concat (replicate n xs)) =
    blank_ledger_repeat n (blank_ledger_word weight xs)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: blank_ledger_word_def blank_ledger_identity_def)
next
  case (Suc n)
  have word:
    "concat (replicate (Suc n) xs) =
      concat (replicate n xs) @ xs"
  proof -
    have replicate:
      "replicate (Suc n) xs = replicate n xs @ [xs]"
      using replicate_Suc[of n xs] replicate_append_same[of n xs]
      by simp
    show ?thesis using replicate by simp
  qed
  show ?case
    by (simp only: word blank_ledger_word_append Suc.IH
        blank_ledger_repeat.simps)
qed

lemma prefix_summary_nonpositive:
  assumes "\<forall>x\<in>set xs. weight x \<le> 0"
  shows "prefix_summary weight xs =
    (sum_list (map weight xs), sum_list (map weight xs))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail: "prefix_summary weight xs =
    (sum_list (map weight xs), sum_list (map weight xs))"
    using Cons.IH Cons.prems by simp
  have head: "weight x \<le> 0" using Cons.prems by simp
  have lower: "sum_list (map weight xs) \<le> 0"
    using prefix_summary_minimum_nonpositive[of weight xs] tail by simp
  show ?case using head lower
    by (simp add: Let_def tail min_def)
qed

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

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms prefix_summary_minimum_nonpositive prefix_summary_min_shift
      prefix_summary_append prefix_summary_delta prefix_summary_nonpositive prefix_guard_cons
      blank_ledger_then_assoc blank_ledger_then_admitted blank_ledger_then_identity
      prefix_summary_minimum_le_delta sum_list_neg_map int_neg_min_eq_max
      blank_ledger_word_admitted
      blank_ledger_word_append blank_ledger_repeat_closed_form
      blank_ledger_word_repeat
      prefix_summary_guard_iff first_negative_none_iff first_negative_append
      first_negative_descent})
    then () else error "Shared prefix effect depends on an oracle";
\<close>
end
