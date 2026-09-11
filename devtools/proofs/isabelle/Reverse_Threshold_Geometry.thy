theory Reverse_Threshold_Geometry
  imports Main
begin

text \<open>Whole-cell pruning laws for the decimal threshold at nine.  The
index set is arbitrary, so these statements apply to any spatial cell or
child cell.  They do not assert temporal closure or pointwise completeness
of a recursive value carrier.\<close>

definition cmp9 :: "int \<Rightarrow> nat" where
  "cmp9 x = (if x < 9 then 0 else if x = 9 then 1 else 2)"

definition threshold_agree_on ::
    "'a set \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> bool" where
  "threshold_agree_on R f g \<longleftrightarrow>
    (\<forall>i\<in>R. cmp9 (f i) = cmp9 (g i))"

lemma cmp9_below [simp]: "x < 9 \<Longrightarrow> cmp9 x = 0"
  by (simp add: cmp9_def)

lemma cmp9_equal [simp]: "x = 9 \<Longrightarrow> cmp9 x = 1"
  by (simp add: cmp9_def)

lemma cmp9_above [simp]: "9 < x \<Longrightarrow> cmp9 x = 2"
  by (simp add: cmp9_def)

theorem bounded_pair_field_all_LT:
  assumes f_upper: "\<And>i. i \<in> R \<Longrightarrow> f i \<le> uf"
      and g_upper: "\<And>i. i \<in> R \<Longrightarrow> g i \<le> ug"
      and separated: "uf + ug < 9"
  shows "\<forall>i\<in>R. cmp9 (f i + g i) = 0"
proof
  fix i
  assume in_R: "i \<in> R"
  have fi: "f i \<le> uf" using in_R by (rule f_upper)
  have gi: "g i \<le> ug" using in_R by (rule g_upper)
  have "f i + g i < 9" using fi gi separated by linarith
  then show "cmp9 (f i + g i) = 0" by simp
qed

theorem bounded_pair_field_all_GT:
  assumes f_lower: "\<And>i. i \<in> R \<Longrightarrow> lf \<le> f i"
      and g_lower: "\<And>i. i \<in> R \<Longrightarrow> lg \<le> g i"
      and separated: "9 < lf + lg"
  shows "\<forall>i\<in>R. cmp9 (f i + g i) = 2"
proof
  fix i
  assume in_R: "i \<in> R"
  have fi: "lf \<le> f i" using in_R by (rule f_lower)
  have gi: "lg \<le> g i" using in_R by (rule g_lower)
  have "9 < f i + g i" using fi gi separated by linarith
  then show "cmp9 (f i + g i) = 2" by simp
qed

theorem bounded_pair_field_all_EQ:
  assumes f_lower: "\<And>i. i \<in> R \<Longrightarrow> lf \<le> f i"
      and f_upper: "\<And>i. i \<in> R \<Longrightarrow> f i \<le> uf"
      and g_lower: "\<And>i. i \<in> R \<Longrightarrow> lg \<le> g i"
      and g_upper: "\<And>i. i \<in> R \<Longrightarrow> g i \<le> ug"
      and lower_sum: "lf + lg = 9"
      and upper_sum: "uf + ug = 9"
  shows "\<forall>i\<in>R. cmp9 (f i + g i) = 1"
proof
  fix i
  assume in_R: "i \<in> R"
  have f_lo: "lf \<le> f i" using in_R by (rule f_lower)
  have f_hi: "f i \<le> uf" using in_R by (rule f_upper)
  have g_lo: "lg \<le> g i" using in_R by (rule g_lower)
  have g_hi: "g i \<le> ug" using in_R by (rule g_upper)
  have "f i + g i = 9"
    using f_lo f_hi g_lo g_hi lower_sum upper_sum by linarith
  then show "cmp9 (f i + g i) = 1" by simp
qed

lemma threshold_agreement_restrict:
  assumes "threshold_agree_on R f g" "S \<subseteq> R"
  shows "threshold_agree_on S f g"
  using assms by (auto simp: threshold_agree_on_def)

lemma threshold_agreement_union:
  "threshold_agree_on (L \<union> R) f g \<longleftrightarrow>
    threshold_agree_on L f g \<and> threshold_agree_on R f g"
  by (auto simp: threshold_agree_on_def)

corollary threshold_agreement_spatial_children:
  assumes "C = L \<union> R"
  shows "threshold_agree_on C f g \<longleftrightarrow>
    threshold_agree_on L f g \<and> threshold_agree_on R f g"
  using assms threshold_agreement_union by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms bounded_pair_field_all_LT bounded_pair_field_all_GT
      bounded_pair_field_all_EQ threshold_agreement_restrict
      threshold_agreement_union threshold_agreement_spatial_children}) then ()
    else error "Threshold geometry proof depends on an oracle";
\<close>

end
