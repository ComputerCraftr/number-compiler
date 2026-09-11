theory Radix64_Mirror_Correlation
  imports Five_Bit_Folded_Square
begin

text \<open>The radix-64 mirror leaf has a seven-valued Boolean correlation,
while its accumulated angular action is addition modulo 16.  The results below
are arithmetic carrier laws only; they do not assert an acceptance or
primality criterion.\<close>

definition add16 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add16 a b = (a + b) mod 16"

definition residue16 :: "nat set" where
  "residue16 = {0..<16}"

lemma add16_identity:
  assumes "a < 16"
  shows "add16 0 a = a" "add16 a 0 = a"
  using assms by (simp_all add: add16_def)

lemma add16_associative:
  "add16 (add16 a b) c = add16 a (add16 b c)"
  by (simp add: add16_def mod_add_left_eq mod_add_right_eq add.assoc)

lemma add16_closed: "add16 a b \<in> residue16"
  by (simp add: add16_def residue16_def)

lemma residue16_card: "card residue16 = 16"
  by (simp add: residue16_def)

lemma add16_sum_list_chunks:
  "sum_list (xs @ ys) mod 16 =
    add16 (sum_list xs mod 16) (sum_list ys mod 16)"
  by (simp add: add16_def mod_add_eq)

lemma add16_replicated_spatial_action:
  "sum_list (replicate copies a) mod 16 =
    (a * (copies mod 16)) mod 16"
  by (simp add: sum_list_replicate mod_mult_right_eq mult.commute)

definition leaf_correlation6 ::
  "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "leaf_correlation6 x y = (\<Sum>i<6. if x i \<and> y i then 1 else 0)"

lemma leaf_correlation6_bound: "leaf_correlation6 x y \<le> 6"
proof -
  have "leaf_correlation6 x y \<le> (\<Sum>i<(6::nat). (1::nat))"
    unfolding leaf_correlation6_def by (intro sum_mono) simp
  then show ?thesis by simp
qed

lemma leaf_correlation6_witness:
  assumes "n \<le> 6"
  shows "leaf_correlation6 (\<lambda>i. i < n) (\<lambda>i. i < n) = n"
proof -
  have "{..<6} \<inter> {i. i < n} = {..<n}" using assms by auto
  then show ?thesis by (simp add: leaf_correlation6_def sum.If_cases)
qed

lemma leaf_correlation6_range:
  "{leaf_correlation6 x y |x y. True} = {0..<7}"
proof
  show "{leaf_correlation6 x y |x y. True} \<subseteq> {0..<7}"
  proof
    fix n
    assume "n \<in> {leaf_correlation6 x y |x y. True}"
    then obtain x y where "n = leaf_correlation6 x y" by blast
    moreover have "leaf_correlation6 x y \<le> 6"
      by (rule leaf_correlation6_bound)
    ultimately show "n \<in> {0..<7}" by simp
  qed
  show "{0..<7} \<subseteq> {leaf_correlation6 x y |x y. True}"
  proof
    fix n :: nat
    assume "n \<in> {0..<7}"
    then have "n \<le> 6" by simp
    then have witness:
      "leaf_correlation6 (\<lambda>i. i < n) (\<lambda>i. i < n) = n"
      by (rule leaf_correlation6_witness)
    have exists: "\<exists>x y. n = leaf_correlation6 x y \<and> True"
      apply (rule exI[where x="\<lambda>i. i < n"])
      apply (rule exI[where x="\<lambda>i. i < n"])
      using witness by simp
    show "n \<in> {leaf_correlation6 x y |x y. True}"
      using exists by simp
  qed
qed

lemma leaf_correlation6_range_card:
  "card {leaf_correlation6 x y |x y. True} = 7"
  by (subst leaf_correlation6_range) simp

definition bounded_convolution ::
  "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "bounded_convolution x w k =
    (\<Sum>i<w. if i \<le> k \<and> k-i < w then x i * x (k-i) else 0)"

lemma mirror_correlation_reindex:
  assumes width: "6 \<le> w"
  shows
    "bounded_convolution x w (w + 5) =
      (\<Sum>u<w-6. x (u+6) * x (w-1-u))"
proof -
  have reduced:
    "bounded_convolution x w (w + 5) =
      (\<Sum>i\<in>{6..<w}. x i * x (w + 5 - i))"
  proof -
    have subset: "{6..<w} \<subseteq> {..<w}" by auto
    show ?thesis
      unfolding bounded_convolution_def
      using width subset
      by (intro sum.mono_neutral_cong_right) auto
  qed
  have shifted:
    "(\<Sum>i\<in>{6..<w}. x i * x (w + 5 - i)) =
      (\<Sum>u<w-6. x (u+6) * x (w-1-u))"
    using width
    by (intro sum.reindex_bij_witness[where
        j="\<lambda>i. i - 6" and i="\<lambda>u. u + 6"])
      (auto simp add: add.commute)
  show ?thesis using reduced shifted by simp
qed

lemma folded_mirror_component_five:
  assumes width: "6 \<le> w"
  shows
    "full_fold_coefficient c w s 5 = c 5 + s * c (w + 5)"
proof -
  have positive: "0 < w" and below: "5 < w" using width by arith+
  show ?thesis by (rule full_fold_coefficient_two_terms[OF positive below])
qed

lemma zero_word_has_zero_convolution:
  assumes zero: "\<And>i. i < w \<Longrightarrow> x i = 0"
  shows "bounded_convolution x w k = 0"
  unfolding bounded_convolution_def using zero by (intro sum.neutral) auto

theorem nonzero_folded_five_implies_nonzero_word:
  assumes width: "6 \<le> w"
      and nonzero:
        "full_fold_coefficient (bounded_convolution x w) w s 5 \<noteq> 0"
  shows "\<exists>i<w. x i \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>i<w. x i \<noteq> 0)"
  then have zero: "\<And>i. i < w \<Longrightarrow> x i = 0" by auto
  have all_zero: "\<And>k. bounded_convolution x w k = 0"
    using zero by (rule zero_word_has_zero_convolution)
  have "full_fold_coefficient (bounded_convolution x w) w s 5 =
      bounded_convolution x w 5 + s * bounded_convolution x w (w + 5)"
    by (rule folded_mirror_component_five[OF width])
  also have "... = 0" by (simp add: all_zero)
  finally show False using nonzero by contradiction
qed

corollary nonzero_reduced_folded_five_implies_nonzero_word:
  assumes width: "6 \<le> w"
      and reduced_nonzero:
        "full_fold_coefficient (bounded_convolution x w) w s 5 mod 16 \<noteq> 0"
  shows "\<exists>i<w. x i \<noteq> 0"
proof -
  have raw_nonzero:
    "full_fold_coefficient (bounded_convolution x w) w s 5 \<noteq> 0"
    using reduced_nonzero by auto
  show ?thesis
    by (rule nonzero_folded_five_implies_nonzero_word[OF width raw_nonzero])
qed

text \<open>The last theorem is only a rejection witness: nonzero folded
correlation proves that the orientation word was not zero.  Its converse and
any acceptance interpretation require additional family-specific theorems.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms add16_identity add16_associative add16_closed residue16_card
      add16_sum_list_chunks
      add16_replicated_spatial_action
      leaf_correlation6_bound leaf_correlation6_witness
      leaf_correlation6_range leaf_correlation6_range_card
      mirror_correlation_reindex folded_mirror_component_five
      zero_word_has_zero_convolution nonzero_folded_five_implies_nonzero_word
      nonzero_reduced_folded_five_implies_nonzero_word})
    then () else error "Radix-64 mirror-correlation proof depends on an oracle";
\<close>

end
