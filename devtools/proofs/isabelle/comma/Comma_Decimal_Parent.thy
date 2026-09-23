theory Comma_Decimal_Parent
  imports Comma_Child_Cylinder
begin

fun comma_leading_digit :: "nat \<Rightarrow> nat" where
  "comma_leading_digit n =
    (if n < 10 then n else comma_leading_digit (n div 10))"

declare comma_leading_digit.simps[simp del]

lemma comma_leading_sector:
  assumes "n > 0"
  shows "\<exists>p. comma_sector (comma_leading_digit n) p n"
  using assms
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have unfold: "comma_leading_digit n =
        (if n < 10 then n else comma_leading_digit (n div 10))"
      by (rule comma_leading_digit.simps)
    have lead: "comma_leading_digit n = n"
      using unfold True by simp
    have sector: "comma_sector n 0 n"
      using True less.prems by (simp add: comma_sector_def)
    have "comma_sector (comma_leading_digit n) 0 n"
      using lead sector by simp
    then show ?thesis by blast
  next
    case False
    let ?q = "n div 10"
    have qpos: "?q > 0" using False by simp
    have qless: "?q < n" using False by simp
    obtain p where sector: "comma_sector (comma_leading_digit ?q) p ?q"
      using less.IH[OF qless qpos] by blast
    have unfold: "comma_leading_digit n =
        (if n < 10 then n else comma_leading_digit (n div 10))"
      by (rule comma_leading_digit.simps)
    have f: "comma_leading_digit n = comma_leading_digit ?q"
      using unfold False by simp
    have qlo: "comma_leading_digit ?q * 10 ^ p \<le> ?q"
      and qhi: "?q < (comma_leading_digit ?q + 1) * 10 ^ p"
      using sector by (auto simp: comma_sector_def)
    have decomp: "n = 10 * ?q + n mod 10" by simp
    have rem: "n mod 10 < 10" by simp
    have lower: "comma_leading_digit ?q * 10 ^ (Suc p) \<le> n"
      using qlo decomp by (simp add: power_Suc; linarith)
    have upper: "n < (comma_leading_digit ?q + 1) * 10 ^ (Suc p)"
      using qhi decomp rem by (simp add: power_Suc; linarith)
    have next_sector: "comma_sector (comma_leading_digit ?q) (Suc p) n"
      using sector lower upper by (auto simp: comma_sector_def)
    have "comma_sector (comma_leading_digit n) (Suc p) n"
      using f next_sector by simp
    then show ?thesis by blast
  qed
qed

lemma comma_leading_bounds:
  assumes "n > 0"
  shows "1 \<le> comma_leading_digit n \<and> comma_leading_digit n \<le> 9"
  using comma_leading_sector[OF assms]
  by (auto simp: comma_sector_def)

definition comma_parent :: "nat \<Rightarrow> nat" where
  "comma_parent n =
    (let f = comma_leading_digit n;
         d = (n - f) mod 10
     in n - (10 * d + f))"

lemma comma_parent_smaller:
  assumes "n > 0"
  shows "comma_parent n < n"
proof -
  have positive: "0 < 10 * ((n - comma_leading_digit n) mod 10) +
      comma_leading_digit n"
    using comma_leading_bounds[OF assms] by linarith
  show ?thesis
    unfolding comma_parent_def Let_def
    using assms positive by linarith
qed

lemma comma_positive_parent_is_child:
  assumes positive: "n > 0" "comma_parent n > 0"
  shows "comma_child (comma_parent n) n"
proof -
  let ?f = "comma_leading_digit n"
  let ?d = "(n - ?f) mod 10"
  let ?k = "comma_parent n"
  have f: "1 \<le> ?f" "?f \<le> 9"
    using comma_leading_bounds positive by auto
  have diffpos: "0 < n - (10 * ?d + ?f)"
    using positive(2) by (simp only: comma_parent_def Let_def)
  have small: "10 * ?d + ?f \<le> n"
    using diffpos by arith
  have decomp: "n = ?k + 10 * ?d + ?f"
    using small by (simp add: comma_parent_def Let_def)
  have residue: "?k mod 10 = ?d"
  proof -
    have eq: "n - ?f = ?k + 10 * ?d" using decomp by arith
    have reduced: "(?k + 10 * ?d) mod 10 = ?k mod 10"
      by (rule mod_mult_self2)
    show ?thesis using eq reduced by simp
  qed
  obtain p where sector: "comma_sector ?f p n"
    using comma_leading_sector positive by auto
  show ?thesis using sector decomp residue
    by (auto simp: comma_child_def)
qed

lemma comma_parent_child:
  assumes "n \<ge> 100"
  shows "comma_parent n > 0 \<and> comma_child (comma_parent n) n"
proof -
  let ?f = "comma_leading_digit n"
  let ?d = "(n - ?f) mod 10"
  have f: "1 \<le> ?f" "?f \<le> 9"
    using comma_leading_bounds assms by auto
  have d: "?d \<le> 9" by simp
  have "10 * ?d + ?f \<le> 99" using f d by linarith
  then have positive: "comma_parent n > 0"
    using assms by (simp add: comma_parent_def Let_def)
  show ?thesis using positive comma_positive_parent_is_child assms by auto
qed

text \<open>For smaller nodes the same parent formula can be checked by
finite computation. The root list and excluded-tree instances are separate
certificates; no constructor theorem is inferred from these local lemmas.\<close>

definition comma_decimal_roots :: "nat set" where
  "comma_decimal_roots = set
    [1,2,3,4,5,6,7,8,9,10,13,14,15,16,17,18,19,20,21,25,26,27,
     28,29,30,31,32,37,38,39,40,41,42,43,49,50,51,52,53,54,62,63,
     64,65,74,75,76,86,87,98]"

lemma comma_small_root_classification:
  "{n. 1 \<le> n \<and> n < 100 \<and> comma_parent n = 0} =
    comma_decimal_roots"
proof -
  have computed: "filter (\<lambda>n. comma_parent n = 0) [1..<100] =
    [1,2,3,4,5,6,7,8,9,10,13,14,15,16,17,18,19,20,21,25,26,27,
     28,29,30,31,32,37,38,39,40,41,42,43,49,50,51,52,53,54,62,63,
     64,65,74,75,76,86,87,98]"
    by code_simp
  have domain: "{n. 1 \<le> n \<and> n < 100 \<and> comma_parent n = 0} =
      set (filter (\<lambda>n. comma_parent n = 0) [1..<100])"
    by auto
  have listed: "set (filter (\<lambda>n. comma_parent n = 0) [1..<100]) =
      comma_decimal_roots"
    using computed unfolding comma_decimal_roots_def by simp
  show ?thesis using domain listed by simp
qed

lemma comma_parent_zero_is_small:
  assumes "n > 0" "comma_parent n = 0"
  shows "n < 100"
proof (rule ccontr)
  assume "\<not> n < 100"
  then have large: "n \<ge> 100" by simp
  have "comma_parent n > 0" using comma_parent_child[OF large] by simp
  then show False using assms by simp
qed

lemma comma_every_positive_has_decimal_root:
  assumes "n > 0"
  shows "\<exists>root \<in> comma_decimal_roots. rtranclp comma_child root n"
  using assms
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "comma_parent n = 0")
    case True
    then have small: "n < 100"
      using comma_parent_zero_is_small less.prems by blast
    have member: "n \<in> {x. 1 \<le> x \<and> x < 100 \<and> comma_parent x = 0}"
      using True small less.prems by simp
    have "n \<in> comma_decimal_roots"
      using comma_small_root_classification member by metis
    then show ?thesis by blast
  next
    case False
    have ppos: "comma_parent n > 0" using False by simp
    have pless: "comma_parent n < n"
      using comma_parent_smaller less.prems by blast
    obtain root where root: "root \<in> comma_decimal_roots"
      and path: "rtranclp comma_child root (comma_parent n)"
      using less.IH[OF pless ppos] by blast
    have edge: "comma_child (comma_parent n) n"
      using comma_positive_parent_is_child less.prems ppos by blast
    show ?thesis using root path edge
      by (meson rtranclp.rtrancl_into_rtrancl)
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_leading_sector comma_leading_bounds comma_parent_smaller
      comma_positive_parent_is_child comma_parent_child
      comma_small_root_classification
      comma_parent_zero_is_small comma_every_positive_has_decimal_root})
    then () else error "Comma parent proof depends on an oracle";
\<close>
end
