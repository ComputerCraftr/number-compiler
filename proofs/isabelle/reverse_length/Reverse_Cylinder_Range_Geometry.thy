theory Reverse_Cylinder_Range_Geometry
  imports Reverse_Cylinder_Length
begin

text \<open>
  Local affine geometry for source-cylinder range queries.  A chart is
  evaluated in one fixed extent/growth environment @{term "(M,G)"}; this
  theory proves only chart composition, interval reindexing, and the local
  palindrome equality.  It does not define temporal action normalization or
  a construction bound.
\<close>

record cylinder_chart =
  chart_slope :: int
  chart_offset :: int
  chart_extent_scale :: int
  chart_growth_scale :: int

definition chart_valid :: "cylinder_chart \<Rightarrow> bool" where
  "chart_valid c \<longleftrightarrow>
    chart_slope c = 1 \<or> chart_slope c = -1"

definition chart_shift :: "cylinder_chart \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "chart_shift c M G = chart_offset c + chart_extent_scale c * M
      + chart_growth_scale c * G"

definition chart_apply ::
    "cylinder_chart \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "chart_apply c M G i = chart_slope c * i + chart_shift c M G"

definition chart_then :: "cylinder_chart \<Rightarrow> cylinder_chart \<Rightarrow> cylinder_chart" where
  "chart_then c d =
    \<lparr>chart_slope = chart_slope d * chart_slope c,
     chart_offset = chart_slope d * chart_offset c + chart_offset d,
     chart_extent_scale = chart_slope d * chart_extent_scale c
       + chart_extent_scale d,
     chart_growth_scale = chart_slope d * chart_growth_scale c
       + chart_growth_scale d\<rparr>"

definition chart_identity :: cylinder_chart where
  "chart_identity =
    \<lparr>chart_slope = 1, chart_offset = 0,
     chart_extent_scale = 0, chart_growth_scale = 0\<rparr>"

definition chart_reflection :: cylinder_chart where
  "chart_reflection =
    \<lparr>chart_slope = -1, chart_offset = -1,
     chart_extent_scale = 1, chart_growth_scale = 1\<rparr>"

lemma chart_valid_identity [simp]: "chart_valid chart_identity"
  by (simp add: chart_valid_def chart_identity_def)

lemma chart_valid_reflection [simp]: "chart_valid chart_reflection"
  by (simp add: chart_valid_def chart_reflection_def)

theorem chart_then_apply:
  "chart_apply (chart_then c d) M G i =
     chart_apply d M G (chart_apply c M G i)"
  by (simp add: chart_apply_def chart_shift_def chart_then_def algebra_simps)

theorem chart_then_associative:
  "chart_then (chart_then a b) c = chart_then a (chart_then b c)"
  by (simp add: chart_then_def algebra_simps)

theorem chart_then_identity:
  "chart_then chart_identity c = c"
  "chart_then c chart_identity = c"
  by (cases c; simp add: chart_then_def chart_identity_def)+

theorem chart_reflection_twice:
  "chart_then chart_reflection chart_reflection = chart_identity"
  by (simp add: chart_reflection_def chart_identity_def chart_then_def)

theorem chart_reflection_apply:
  "chart_apply chart_reflection M G i = M + G - 1 - i"
  by (simp add: chart_apply_def chart_shift_def chart_reflection_def algebra_simps)

lemma chart_then_valid:
  assumes "chart_valid c" "chart_valid d"
  shows "chart_valid (chart_then c d)"
  using assms by (auto simp: chart_valid_def chart_then_def)

definition integer_interval :: "int \<Rightarrow> int \<Rightarrow> int set" where
  "integer_interval lo hi = {i. lo \<le> i \<and> i < hi}"

definition chart_image ::
    "cylinder_chart \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "chart_image c lo hi M G =
    (if chart_slope c = 1 then
       (lo + chart_shift c M G, hi + chart_shift c M G)
     else
       (chart_shift c M G - hi + 1, chart_shift c M G - lo + 1))"

definition chart_image_set ::
    "cylinder_chart \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int set" where
  "chart_image_set c lo hi M G =
    {chart_apply c M G i | i. i \<in> integer_interval lo hi}"

theorem chart_image_set_exact:
  assumes valid: "chart_valid c" and ordered: "lo \<le> hi"
  shows "chart_image_set c lo hi M G =
      integer_interval (fst (chart_image c lo hi M G))
        (snd (chart_image c lo hi M G))"
proof -
  have slopes: "chart_slope c = 1 \<or> chart_slope c = -1"
    using valid by (simp add: chart_valid_def)
  let ?target = "integer_interval (fst (chart_image c lo hi M G))
      (snd (chart_image c lo hi M G))"
  have pointwise: "\<And>i. i \<in> integer_interval lo hi \<longleftrightarrow>
      chart_apply c M G i \<in> ?target"
    using slopes
    by (auto simp: integer_interval_def chart_image_def chart_apply_def; linarith)
  have inverse: "\<And>x. chart_apply c M G
      (chart_slope c * (x - chart_shift c M G)) = x"
    using slopes by (auto simp: chart_apply_def algebra_simps)
  show ?thesis
    unfolding chart_image_set_def
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> {chart_apply c M G i |i. i \<in> integer_interval lo hi}"
    then show "x \<in> ?target" using pointwise by auto
  next
    fix x
    assume inside: "x \<in> ?target"
    let ?i = "chart_slope c * (x - chart_shift c M G)"
    have inverse_value: "chart_apply c M G ?i = x" by (rule inverse)
    have in_source: "?i \<in> integer_interval lo hi"
      using pointwise[of ?i] inverse_value inside by simp
    show "x \<in> {chart_apply c M G i |i. i \<in> integer_interval lo hi}"
      apply (rule CollectI)
      apply (rule exI[where x = "?i"])
      using inverse_value in_source by simp
  qed
qed

theorem chart_image_membership:
  assumes valid: "chart_valid c" and ordered: "lo \<le> hi"
  shows "x \<in> integer_interval (fst (chart_image c lo hi M G))
      (snd (chart_image c lo hi M G)) \<longleftrightarrow>
    (\<exists>i \<in> integer_interval lo hi. chart_apply c M G i = x)"
  by (subst chart_image_set_exact[OF valid ordered, symmetric];
      auto simp: chart_image_set_def)

text \<open>A completed spatial output branch routes its two child ranges with
  the same sibling-boundary functions as a point observation.  The functions
  below abstract already-published child images; no temporal callback or
  successor construction is part of this range law.\<close>

definition spatial_branch_point ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v)
    \<Rightarrow> (nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v)
    \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)
    \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)
    \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v" where
  "spatial_branch_point w left right right_boundary left_boundary i l r =
    (if i < w then left i l (right_boundary l r)
     else right (i-w) (left_boundary l r) r)"

definition spatial_branch_range ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v)
    \<Rightarrow> (nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v)
    \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)
    \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)
    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v list" where
  "spatial_branch_range w left right right_boundary left_boundary lo hi l r =
    (if lo < w then
       map (\<lambda>i. left i l (right_boundary l r)) [lo..<min hi w]
     else []) @
    (if w < hi then
       map (\<lambda>i. right i (left_boundary l r) r) [lo-w..<hi-w]
     else [])"

lemma spatial_branch_interval_split:
  assumes "lo \<le> hi"
  shows "[lo..<hi] =
    (if lo < w then [lo..<min hi w] else []) @
    (if w < hi then [max lo w..<hi] else [])"
proof (cases "hi \<le> w")
  case True
  then show ?thesis using assms by auto
next
  case False
  then have wh: "w < hi" by simp
  show ?thesis
  proof (cases "w \<le> lo")
    case True
    then show ?thesis using wh by auto
  next
    case False
    then have lw: "lo \<le> w" by simp
    have "hi = w + (hi-w)" using wh by simp
    then show ?thesis
      using upt_add_eq_append[OF lw, of "hi-w"] wh False by simp
  qed
qed

lemma spatial_branch_right_rebase:
  assumes "lo \<le> hi" "w < hi"
  shows "map (\<lambda>i. right (i-w) l r) [max lo w..<hi] =
    map (\<lambda>i. right i l r) [lo-w..<hi-w]"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. right (i-w) l r) [max lo w..<hi]) =
    length (map (\<lambda>i. right i l r) [lo-w..<hi-w])"
    using assms by simp
next
  fix k
  assume bound:
    "k < length (map (\<lambda>i. right (i-w) l r) [max lo w..<hi])"
  have left_bound: "k < hi - max lo w"
    using bound by simp
  have right_bound: "k < (hi-w) - (lo-w)"
    using left_bound assms by arith
  have offset: "max lo w + k - w = lo-w+k"
    by (simp add: max_def split: if_splits)
  then show "(map (\<lambda>i. right (i-w) l r) [max lo w..<hi]) ! k =
    (map (\<lambda>i. right i l r) [lo-w..<hi-w]) ! k"
    using left_bound right_bound by simp
qed

theorem spatial_branch_range_refines_point:
  assumes "lo \<le> hi"
  shows "spatial_branch_range w left right right_boundary left_boundary lo hi l r =
    map (\<lambda>i. spatial_branch_point w left right right_boundary left_boundary i l r)
      [lo..<hi]"
proof -
  let ?point =
    "\<lambda>i. spatial_branch_point w left right right_boundary left_boundary i l r"
  let ?left = "if lo < w then [lo..<min hi w] else []"
  let ?right = "if w < hi then [max lo w..<hi] else []"
  have left_map:
    "map ?point ?left =
      (if lo < w then
         map (\<lambda>i. left i l (right_boundary l r)) [lo..<min hi w]
       else [])"
  proof (cases "lo < w")
    case True
    have "map ?point [lo..<min hi w] =
      map (\<lambda>i. left i l (right_boundary l r)) [lo..<min hi w]"
      by (rule map_cong) (auto simp: spatial_branch_point_def)
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis by simp
  qed
  have right_map:
    "map ?point ?right =
      (if w < hi then
         map (\<lambda>i. right (i-w) (left_boundary l r) r) [max lo w..<hi]
       else [])"
  proof (cases "w < hi")
    case True
    have "map ?point [max lo w..<hi] =
      map (\<lambda>i. right (i-w) (left_boundary l r) r) [max lo w..<hi]"
      by (rule map_cong) (auto simp: spatial_branch_point_def)
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis by simp
  qed
  have right_rebased:
    "(if w < hi then
        map (\<lambda>i. right (i-w) (left_boundary l r) r) [max lo w..<hi]
      else []) =
     (if w < hi then
        map (\<lambda>i. right i (left_boundary l r) r) [lo-w..<hi-w]
      else [])"
    using spatial_branch_right_rebase[OF assms, of w right "left_boundary l r" r]
    by (cases "w < hi") simp_all
  have split: "[lo..<hi] = ?left @ ?right"
    by (rule spatial_branch_interval_split[OF assms])
  have "map ?point [lo..<hi] = map ?point ?left @ map ?point ?right"
    by (simp only: split map_append)
  also have "... = spatial_branch_range w left right right_boundary
      left_boundary lo hi l r"
    using left_map right_map right_rebased
    by (simp only: spatial_branch_range_def)
  finally show ?thesis by simp
qed

corollary spatial_branch_range_emission_count:
  assumes "lo \<le> hi"
  shows "length (spatial_branch_range w left right right_boundary left_boundary lo hi l r)
    = hi - lo"
  by (subst spatial_branch_range_refines_point[OF assms]) simp

lemma palindrome_range_coordinate:
  assumes palindrome: "rev xs = xs"
      and ordered: "lo \<le> hi" and bounded: "hi \<le> length xs"
      and position: "j < hi - lo"
  shows "xs ! (hi - Suc j) = xs ! (length xs - hi + j)"
proof -
  have jbound: "j < hi" using position by arith
  have ibound: "hi - Suc j < length xs" using jbound bounded by arith
  have index: "length xs - Suc (hi - Suc j) = length xs - hi + j"
    using jbound bounded by arith
  show ?thesis
    using palindrome_nth_reflect[OF palindrome ibound] index by simp
qed

theorem palindrome_range_sequence:
  assumes "rev xs = xs" "lo \<le> hi" "hi \<le> length xs"
  shows "map (\<lambda>j. xs ! (hi - Suc j)) [0..<hi-lo] =
    map (\<lambda>j. xs ! (length xs - hi + j)) [0..<hi-lo]"
  by (rule map_cong; auto intro: palindrome_range_coordinate[OF assms])

theorem palindrome_range_carry:
  assumes "rev xs = xs" "lo \<le> hi" "hi \<le> length xs"
  shows "carry_out c (map (\<lambda>j. xs ! (hi - Suc j)) [0..<hi-lo]) =
    carry_out c (map (\<lambda>j. xs ! (length xs - hi + j)) [0..<hi-lo])"
  by (rule arg_cong[where f="carry_out c", OF palindrome_range_sequence[OF assms]])

text \<open>An identity carry summary certifies every constituent transfer as
neutral.  Constant summaries do not have this property.  This is the exact
spatial reduction used to remove redundant children and inherit identity from
an admitted containing interval; it is not a temporal action quotient.\<close>

lemma carry_fold_identity_iff:
  "(fold carry_apply ds False = False \<and> fold carry_apply ds True = True)
    \<longleftrightarrow> (\<forall>d \<in> set ds. d = Equal)"
proof (induction ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case by (cases d; auto)
qed

lemma carry_fold_neutral:
  assumes "\<forall>d \<in> set ds. d = Equal"
  shows "fold carry_apply ds c = c"
  using assms by (induction ds; auto)

theorem identity_carry_restricts_to_identity:
  assumes "fold carry_apply ds False = False"
      and "fold carry_apply ds True = True"
  shows "fold carry_apply (take n (drop k ds)) c = c"
proof -
  have neutral: "\<forall>d \<in> set ds. d = Equal"
    using assms carry_fold_identity_iff[of ds] by blast
  have subset: "set (take n (drop k ds)) \<subseteq> set ds"
    by (meson set_drop_subset set_take_subset subset_trans)
  have "\<forall>d \<in> set (take n (drop k ds)). d = Equal"
    using neutral subset by blast
  then show ?thesis by (rule carry_fold_neutral)
qed

ML \<open>
  val checked = @{thms chart_valid_identity chart_valid_reflection
    chart_then_apply chart_then_associative chart_then_identity chart_then_valid
    chart_reflection_twice chart_reflection_apply
    chart_image_set_exact chart_image_membership
    palindrome_range_coordinate palindrome_range_sequence palindrome_range_carry
    carry_fold_identity_iff carry_fold_neutral identity_carry_restricts_to_identity};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse cylinder range geometry proof depends on an oracle";
\<close>

end
