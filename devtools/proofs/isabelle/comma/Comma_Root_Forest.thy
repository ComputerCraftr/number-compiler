theory Comma_Root_Forest
  imports Comma_Decimal_Parent
begin

text \<open>These root lemmas state the exact missing bridge for the decimal
certificate. They do not treat an exhausted finite trace from one root as an
infinite-path witness. The executable sector forest still needs an instance
showing its compressed regions are closed under every literal child.\<close>

definition comma_descendants :: "nat \<Rightarrow> nat set" where
  "comma_descendants root = {n. rtranclp comma_child root n}"

lemma comma_finite_closed_region:
  assumes finite: "finite region"
    and initial: "root \<in> region"
    and closed: "\<And>x y. x \<in> region \<Longrightarrow> comma_child x y \<Longrightarrow> y \<in> region"
  shows "finite (comma_descendants root)"
proof -
  have "comma_descendants root \<subseteq> region"
    unfolding comma_descendants_def
    using initial closed by (auto elim: rtranclp_induct)
  then show ?thesis using finite by (rule finite_subset)
qed

lemma comma_compressed_region_sound:
  fixes entries :: "nat set" and region_of :: "nat \<Rightarrow> nat set"
  assumes finite_entries: "finite entries"
    and initial: "root \<in> entries"
    and finite_regions: "\<And>entry. entry \<in> entries \<Longrightarrow> finite (region_of entry)"
    and entry_in_region: "\<And>entry. entry \<in> entries \<Longrightarrow>
      entry \<in> region_of entry"
    and exact_exits: "\<And>entry x y. entry \<in> entries \<Longrightarrow>
      x \<in> region_of entry \<Longrightarrow> comma_child x y \<Longrightarrow>
      y \<in> region_of entry \<or> y \<in> entries"
  shows "finite (comma_descendants root)"
proof -
  let ?region = "\<Union>entry \<in> entries. region_of entry"
  have finite_region: "finite ?region"
    using finite_entries finite_regions by simp
  have root_in: "root \<in> ?region"
    using initial entry_in_region by blast
  have closed: "\<And>x y. x \<in> ?region \<Longrightarrow>
      comma_child x y \<Longrightarrow> y \<in> ?region"
  proof -
    fix x y
    assume member: "x \<in> ?region" and edge: "comma_child x y"
    obtain entry where entry: "entry \<in> entries"
      and x_region: "x \<in> region_of entry"
      using member by blast
    show "y \<in> ?region"
      using exact_exits[OF entry x_region edge] entry entry_in_region
      by blast
  qed
  show ?thesis
    by (rule comma_finite_closed_region[OF finite_region root_in closed])
qed

lemma comma_finite_right_forces_infinite_left:
  assumes fork_infinite: "infinite (comma_descendants fork)"
    and only_two: "\<And>child. comma_child fork child \<Longrightarrow>
      child = left \<or> child = right"
    and right_finite: "finite (comma_descendants right)"
  shows "infinite (comma_descendants left)"
proof
  assume left_finite: "finite (comma_descendants left)"
  let ?region = "insert fork
      (comma_descendants left \<union> comma_descendants right)"
  have finite_region: "finite ?region"
    using left_finite right_finite by simp
  have root_child: "\<And>child. comma_child fork child \<Longrightarrow>
      child \<in> ?region"
    using only_two by (auto simp: comma_descendants_def)
  have descendant_child: "\<And>source x child.
      x \<in> comma_descendants source \<Longrightarrow>
      comma_child x child \<Longrightarrow>
      child \<in> comma_descendants source"
  proof -
    fix source x child
    assume member: "x \<in> comma_descendants source"
      and edge: "comma_child x child"
    have path: "rtranclp comma_child source x"
      using member by (simp add: comma_descendants_def)
    have "rtranclp comma_child source child"
      using path edge by (meson rtranclp.rtrancl_into_rtrancl)
    then show "child \<in> comma_descendants source"
      by (simp add: comma_descendants_def)
  qed
  have closed: "\<And>x child. x \<in> ?region \<Longrightarrow>
      comma_child x child \<Longrightarrow> child \<in> ?region"
    using root_child descendant_child by auto
  have "finite (comma_descendants fork)"
    by (rule comma_finite_closed_region[OF finite_region _ closed]) simp
  then show False using fork_infinite by contradiction
qed

lemma comma_unique_unbounded_root:
  fixes roots :: "nat set"
  assumes finite_roots: "finite roots"
    and root20: "20 \<in> roots"
    and cover: "\<And>n. n > 0 \<Longrightarrow>
      \<exists>root \<in> roots. n \<in> comma_descendants root"
    and excluded: "\<And>root. root \<in> roots \<Longrightarrow> root \<noteq> 20 \<Longrightarrow>
      finite (comma_descendants root)"
  shows "infinite (comma_descendants 20)"
proof
  assume finite20: "finite (comma_descendants 20)"
  have every_root_finite: "\<And>root. root \<in> roots \<Longrightarrow>
      finite (comma_descendants root)"
    using finite20 excluded by auto
  have finite_union: "finite (\<Union>root \<in> roots. comma_descendants root)"
    using finite_roots every_root_finite by simp
  have "{n::nat. n > 0} \<subseteq>
      (\<Union>root \<in> roots. comma_descendants root)"
    using cover by auto
  then have finite_positive: "finite {n::nat. n > 0}"
    using finite_union by (rule finite_subset)
  have eq: "{n::nat. n > 0} = ({0<..} :: nat set)" by auto
  have "finite ({0<..} :: nat set)"
    using finite_positive eq by simp
  then show False using infinite_Ioi[of "0::nat"] by contradiction
qed

lemma comma_finite_other_regions_imply_root20_unbounded:
  fixes roots :: "nat set"
  assumes finite_roots: "finite roots"
    and root20: "20 \<in> roots"
    and cover: "\<And>n. n > 0 \<Longrightarrow>
      \<exists>root \<in> roots. n \<in> comma_descendants root"
    and certificates: "\<And>root. root \<in> roots \<Longrightarrow> root \<noteq> 20 \<Longrightarrow>
      \<exists>region. finite region \<and> root \<in> region \<and>
        (\<forall>x\<in>region. \<forall>y. comma_child x y \<longrightarrow> y \<in> region)"
  shows "infinite (comma_descendants 20)"
proof (rule comma_unique_unbounded_root[OF finite_roots root20 cover])
  fix root
  assume r: "root \<in> roots" "root \<noteq> 20"
  obtain region where finite: "finite region" and initial: "root \<in> region"
    and closed: "\<forall>x\<in>region. \<forall>y. comma_child x y \<longrightarrow> y \<in> region"
    using certificates[OF r] by blast
  show "finite (comma_descendants root)"
    using comma_finite_closed_region[OF finite initial] closed by blast
qed

lemma comma_decimal_finite_other_regions_imply_root20_unbounded:
  assumes certificates: "\<And>root. root \<in> comma_decimal_roots \<Longrightarrow>
      root \<noteq> 20 \<Longrightarrow>
      \<exists>region. finite region \<and> root \<in> region \<and>
        (\<forall>x\<in>region. \<forall>y. comma_child x y \<longrightarrow> y \<in> region)"
  shows "infinite (comma_descendants 20)"
proof -
  have finite_roots: "finite comma_decimal_roots"
    by (simp add: comma_decimal_roots_def)
  have root20: "20 \<in> comma_decimal_roots"
    by (simp add: comma_decimal_roots_def)
  have cover: "\<And>n. n > 0 \<Longrightarrow>
      \<exists>root \<in> comma_decimal_roots. n \<in> comma_descendants root"
  proof -
    fix n :: nat
    assume positive: "n > 0"
    obtain root where member: "root \<in> comma_decimal_roots"
      and path: "rtranclp comma_child root n"
      using comma_every_positive_has_decimal_root[OF positive] by blast
    show "\<exists>root \<in> comma_decimal_roots. n \<in> comma_descendants root"
      using member path by (auto simp: comma_descendants_def)
  qed
  show ?thesis
    by (rule comma_finite_other_regions_imply_root20_unbounded
        [OF finite_roots root20 cover certificates])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_closed_region comma_compressed_region_sound
      comma_finite_right_forces_infinite_left
      comma_unique_unbounded_root
      comma_finite_other_regions_imply_root20_unbounded
      comma_decimal_finite_other_regions_imply_root20_unbounded})
    then () else error "Comma root-forest proof depends on an oracle";
\<close>
end
