theory Overlap_Quarter
  imports Main
begin

text \<open>One-sided binary cellular action. Coordinates increase from left to
right, and every output consumes its own input and the next input.\<close>

fun overlap_run :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "overlap_run f 0 source i = source i"
| "overlap_run f (Suc n) source i =
    f (overlap_run f n source i) (overlap_run f n source (Suc i))"

lemma overlap_run_shift:
  "overlap_run f n (\<lambda>i. source (offset + i)) i =
    overlap_run f n source (offset + i)"
  by (induction n arbitrary: i) (simp_all add: add.assoc)

lemma overlap_run_add:
  "overlap_run f (a + b) source i =
    overlap_run f b (\<lambda>j. overlap_run f a source j) i"
  by (induction b arbitrary: i) (simp_all add: add_Suc)

lemma overlap_run_local:
  assumes "\<And>j. i \<le> j \<Longrightarrow> j \<le> i + n \<Longrightarrow> left j = right j"
  shows "overlap_run f n left i = overlap_run f n right i"
  using assms
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have first: "overlap_run f n left i = overlap_run f n right i"
    by (rule Suc.IH) (use Suc.prems in auto)
  have second: "overlap_run f n left (Suc i) = overlap_run f n right (Suc i)"
    by (rule Suc.IH) (use Suc.prems in auto)
  show ?case using first second by simp
qed

definition overlap_join :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "overlap_join width left right i =
    (if i < width then left i else right (i - width))"

lemma overlap_join_shift:
  "overlap_join q source (\<lambda>i. source (q+i)) = source"
  by (rule ext) (auto simp: overlap_join_def)

text \<open>The first half-time pass computes three overlapping windows at
offsets 0, q and 2q. The second pass consumes the two adjacent pairs.\<close>

theorem overlap_quarter_left:
  "overlap_run f q
      (overlap_join q (overlap_run f q source)
        (\<lambda>i. overlap_run f q source (q+i))) i =
    overlap_run f (q+q) source i"
  by (simp add: overlap_join_shift overlap_run_add)

theorem overlap_quarter_right:
  "overlap_run f q
      (overlap_join q (\<lambda>i. overlap_run f q source (q+i))
        (\<lambda>i. overlap_run f q source (2*q+i))) i =
    overlap_run f (q+q) source (q+i)"
proof -
  have joined:
    "overlap_join q (\<lambda>i. overlap_run f q source (q+i))
      (\<lambda>i. overlap_run f q source (2*q+i)) =
     (\<lambda>i. overlap_run f q source (q+i))"
    by (rule ext) (auto simp: overlap_join_def algebra_simps)
  show ?thesis
    by (simp only: joined overlap_run_add overlap_run_shift)
qed

theorem overlap_quarter_output:
  "map (overlap_run f q
      (overlap_join q (overlap_run f q source)
        (\<lambda>i. overlap_run f q source (q+i)))) [0..<q] @
   map (overlap_run f q
      (overlap_join q (\<lambda>i. overlap_run f q source (q+i))
        (\<lambda>i. overlap_run f q source (2*q+i)))) [0..<q] =
   map (overlap_run f (q+q) source) [0..<q+q]"
proof (rule nth_equalityI)
  show "length (map (overlap_run f q
      (overlap_join q (overlap_run f q source)
        (\<lambda>i. overlap_run f q source (q+i)))) [0..<q] @
    map (overlap_run f q
      (overlap_join q (\<lambda>i. overlap_run f q source (q+i))
        (\<lambda>i. overlap_run f q source (2*q+i)))) [0..<q]) =
    length (map (overlap_run f (q+q) source) [0..<q+q])"
    by simp
next
  fix i
  assume bound: "i < length (map (overlap_run f q
      (overlap_join q (overlap_run f q source)
        (\<lambda>i. overlap_run f q source (q+i)))) [0..<q] @
    map (overlap_run f q
      (overlap_join q (\<lambda>i. overlap_run f q source (q+i))
        (\<lambda>i. overlap_run f q source (2*q+i)))) [0..<q])"
  show "(map (overlap_run f q
      (overlap_join q (overlap_run f q source)
        (\<lambda>i. overlap_run f q source (q+i)))) [0..<q] @
    map (overlap_run f q
      (overlap_join q (\<lambda>i. overlap_run f q source (q+i))
        (\<lambda>i. overlap_run f q source (2*q+i)))) [0..<q]) ! i =
    map (overlap_run f (q+q) source) [0..<q+q] ! i"
    using bound
    by (cases "i < q")
      (auto simp: nth_append overlap_quarter_left overlap_quarter_right)
qed

text \<open>For q > 0 and i < q, the two output indices are i and q+i;
their complete initial halos end at i+2q and i+3q, both below 4q.\<close>

lemma overlap_quarter_halos:
  fixes q i :: nat
  assumes "q > 0" "i < q"
  shows "i + (q+q) < 4*q" "q+i + (q+q) < 4*q"
  using assms by arith+

fun overlap_recursive ::
  "nat \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "overlap_recursive 0 f source i = f (source i) (source (Suc i))"
| "overlap_recursive (Suc k) f source i =
    (let q = 2^k;
         u = overlap_recursive k f source;
         v = overlap_recursive k f (\<lambda>j. source (q+j));
         w = overlap_recursive k f (\<lambda>j. source (2*q+j))
     in if i < q then overlap_recursive k f (overlap_join q u v) i
        else overlap_recursive k f (overlap_join q v w) (i-q))"

theorem overlap_recursive_exact:
  "overlap_recursive k f source i = overlap_run f (2^k) source i"
proof (induction k arbitrary: source i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?q = "(2::nat)^k"
  have first: "overlap_recursive k f source = overlap_run f ?q source"
    by (rule ext) (rule Suc.IH)
  have second:
    "overlap_recursive k f (\<lambda>j. source (?q+j)) =
      (\<lambda>j. overlap_run f ?q source (?q+j))"
    by (rule ext) (simp only: Suc.IH overlap_run_shift)
  have third:
    "overlap_recursive k f (\<lambda>j. source (2*?q+j)) =
      (\<lambda>j. overlap_run f ?q source (2*?q+j))"
    by (rule ext) (simp only: Suc.IH overlap_run_shift)
  have duration: "2 ^ Suc k = ?q + ?q" by (simp add: power_Suc algebra_simps)
  show ?case
  proof (cases "i < ?q")
    case True
    show ?thesis
      using True by (simp only: overlap_recursive.simps Let_def if_True first second
          Suc.IH duration overlap_quarter_left)
  next
    case False
    have offset: "?q + (i - ?q) = i" using False by simp
    have "overlap_recursive (Suc k) f source i =
      overlap_recursive k f
        (overlap_join ?q (overlap_recursive k f (\<lambda>j. source (?q+j)))
          (overlap_recursive k f (\<lambda>j. source (2*?q+j)))) (i-?q)"
      using False by (simp only: overlap_recursive.simps Let_def if_False)
    also have "... = overlap_run f ?q
      (overlap_join ?q (overlap_recursive k f (\<lambda>j. source (?q+j)))
        (overlap_recursive k f (\<lambda>j. source (2*?q+j)))) (i-?q)"
      by (rule Suc.IH)
    also have "... = overlap_run f ?q
      (overlap_join ?q (\<lambda>j. overlap_run f ?q source (?q+j))
        (\<lambda>j. overlap_run f ?q source (2*?q+j))) (i-?q)"
      by (simp only: second third)
    also have "... = overlap_run f (?q+?q) source (?q+(i-?q))"
      by (rule overlap_quarter_right)
    also have "... = overlap_run f (2^Suc k) source i"
      by (simp only: offset duration)
    finally show ?thesis .
  qed
qed

end
