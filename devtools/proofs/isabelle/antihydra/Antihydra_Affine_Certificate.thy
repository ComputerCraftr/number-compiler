theory Antihydra_Affine_Certificate
  imports Antihydra_Source_Barrier "HOL.Rat"
begin

text \<open>This is the arithmetic kernel for a finite affine-chart
certificate.  It proves checker soundness only.  Concrete chart coverage and
an accepted source-7 certificate remain separate obligations.\<close>

type_synonym affine_point = "rat \<times> rat"

record affine_constraint =
  coeff_x :: rat
  coeff_a :: rat
  coeff_0 :: rat

definition constraint_value :: "affine_constraint \<Rightarrow> affine_point \<Rightarrow> rat" where
  "constraint_value c p = coeff_x c * fst p + coeff_a c * snd p + coeff_0 c"

definition constraint_combination ::
    "(affine_constraint \<Rightarrow> rat) \<Rightarrow> affine_constraint set
      \<Rightarrow> affine_constraint" where
  "constraint_combination w S = \<lparr>
    coeff_x = (\<Sum>c\<in>S. w c * coeff_x c),
    coeff_a = (\<Sum>c\<in>S. w c * coeff_a c),
    coeff_0 = (\<Sum>c\<in>S. w c * coeff_0 c)\<rparr>"

definition farkas_certificate ::
    "affine_constraint set \<Rightarrow> (affine_constraint \<Rightarrow> rat)
      \<Rightarrow> affine_constraint \<Rightarrow> bool" where
  "farkas_certificate S w target \<longleftrightarrow>
    finite S \<and> (\<forall>c\<in>S. 0 \<le> w c) \<and>
    target = constraint_combination w S"

lemma constraint_combination_value:
  assumes "finite S"
  shows "constraint_value (constraint_combination w S) p =
    (\<Sum>c\<in>S. w c * constraint_value c p)"
using assms
proof (induct S rule: finite_induct)
  case empty
  then show ?case by (simp add: constraint_value_def constraint_combination_def)
next
  case (insert c S)
  then show ?case
    by (simp add: constraint_value_def constraint_combination_def algebra_simps)
qed

theorem farkas_certificate_sound:
  assumes cert: "farkas_certificate S w target"
    and source: "\<forall>c\<in>S. 0 \<le> constraint_value c p"
  shows "0 \<le> constraint_value target p"
proof -
  have finite: "finite S" and weights: "\<forall>c\<in>S. 0 \<le> w c"
    and target: "target = constraint_combination w S"
    using cert by (simp_all add: farkas_certificate_def)
  have nonnegative: "\<forall>c\<in>S. 0 \<le> w c * constraint_value c p"
    using weights source by (auto intro: mult_nonneg_nonneg)
  have "0 \<le> (\<Sum>c\<in>S. w c * constraint_value c p)"
    by (rule sum_nonneg) (use nonnegative in auto)
  then show ?thesis
    using target constraint_combination_value[OF finite, of w p]
    by simp
qed

definition indexed_constraint_combination ::
    "rat list \<Rightarrow> affine_constraint list \<Rightarrow> affine_constraint" where
  "indexed_constraint_combination ws cs = \<lparr>
    coeff_x = sum_list (map (\<lambda>(w,c). w * coeff_x c) (zip ws cs)),
    coeff_a = sum_list (map (\<lambda>(w,c). w * coeff_a c) (zip ws cs)),
    coeff_0 = sum_list (map (\<lambda>(w,c). w * coeff_0 c) (zip ws cs))\<rparr>"

definition indexed_farkas_certificate ::
    "affine_constraint list \<Rightarrow> rat list \<Rightarrow>
      affine_constraint \<Rightarrow> bool" where
  "indexed_farkas_certificate cs ws target \<longleftrightarrow>
    length ws = length cs \<and> (\<forall>w\<in>set ws. 0 \<le> w) \<and>
    target = indexed_constraint_combination ws cs"

lemma indexed_constraint_combination_value:
  "constraint_value (indexed_constraint_combination ws cs) p =
    sum_list (map (\<lambda>(w,c). w * constraint_value c p) (zip ws cs))"
proof (induct ws arbitrary: cs)
  case Nil
  then show ?case
    by (cases cs; simp_all add: indexed_constraint_combination_def
        constraint_value_def)
next
  case (Cons w ws)
  then show ?case
    by (cases cs; simp_all add: indexed_constraint_combination_def
        constraint_value_def algebra_simps)
qed

theorem indexed_farkas_certificate_sound:
  assumes cert: "indexed_farkas_certificate cs ws target"
    and source: "\<forall>c\<in>set cs. 0 \<le> constraint_value c p"
  shows "0 \<le> constraint_value target p"
proof -
  have lengths: "length ws = length cs"
    and weights: "\<forall>w\<in>set ws. 0 \<le> w"
    and target: "target = indexed_constraint_combination ws cs"
    using cert by (simp_all add: indexed_farkas_certificate_def)
  have terms: "\<forall>wc\<in>set (zip ws cs).
      0 \<le> fst wc * constraint_value (snd wc) p"
  proof (intro ballI)
    fix wc assume pair: "wc \<in> set (zip ws cs)"
    obtain w c where wc: "wc = (w,c)" by (cases wc) simp
    have win: "w \<in> set ws"
      using set_zip_leftD[of w c ws cs] pair wc by simp
    have cin: "c \<in> set cs"
      using set_zip_rightD[of w c ws cs] pair wc by simp
    have "0 \<le> w" using weights win by simp
    moreover have "0 \<le> constraint_value c p" using source cin by simp
    ultimately show "0 \<le> fst wc * constraint_value (snd wc) p"
      using wc by (simp add: mult_nonneg_nonneg)
  qed
  have "0 \<le> sum_list
      (map (\<lambda>(w,c). w * constraint_value c p) (zip ws cs))"
    by (rule sum_list_nonneg) (use terms in auto)
  then show ?thesis
    using target indexed_constraint_combination_value[of ws cs p] by simp
qed

record affine_branch =
  next_x_x :: rat
  next_x_a :: rat
  next_x_0 :: rat
  next_a_x :: rat
  next_a_a :: rat
  next_a_0 :: rat

definition apply_affine_branch :: "affine_branch \<Rightarrow> affine_point \<Rightarrow> affine_point" where
  "apply_affine_branch b p =
    (next_x_x b * fst p + next_x_a b * snd p + next_x_0 b,
     next_a_x b * fst p + next_a_a b * snd p + next_a_0 b)"

definition pullback_constraint :: "affine_branch \<Rightarrow> affine_constraint \<Rightarrow> affine_constraint" where
  "pullback_constraint b c = \<lparr>
    coeff_x = coeff_x c * next_x_x b + coeff_a c * next_a_x b,
    coeff_a = coeff_x c * next_x_a b + coeff_a c * next_a_a b,
    coeff_0 = coeff_x c * next_x_0 b + coeff_a c * next_a_0 b + coeff_0 c\<rparr>"

lemma pullback_constraint_value:
  "constraint_value (pullback_constraint b c) p =
    constraint_value c (apply_affine_branch b p)"
  by (simp add: constraint_value_def pullback_constraint_def
      apply_affine_branch_def algebra_simps)

definition chart_invariant :: "affine_constraint set \<Rightarrow> affine_point \<Rightarrow> bool" where
  "chart_invariant S p \<longleftrightarrow> (\<forall>c\<in>S. 0 \<le> constraint_value c p)"

definition branch_certificate :: "affine_constraint set \<Rightarrow> affine_branch \<Rightarrow> bool" where
  "branch_certificate S b \<longleftrightarrow>
    (\<forall>target\<in>S. \<exists>w. farkas_certificate S w (pullback_constraint b target))"

theorem certified_branch_preserves_chart:
  assumes inv: "chart_invariant S p" and cert: "branch_certificate S b"
  shows "chart_invariant S (apply_affine_branch b p)"
proof (simp add: chart_invariant_def, intro ballI)
  fix target assume target: "target \<in> S"
  obtain w where witness:
      "farkas_certificate S w (pullback_constraint b target)"
    using cert target by (auto simp: branch_certificate_def)
  have "0 \<le> constraint_value (pullback_constraint b target) p"
    by (rule farkas_certificate_sound[OF witness])
      (use inv in \<open>simp add: chart_invariant_def\<close>)
  then show "0 \<le> constraint_value target (apply_affine_branch b p)"
    by (simp only: pullback_constraint_value)
qed

fun certified_affine_orbit ::
    "(affine_point \<Rightarrow> affine_branch) \<Rightarrow> affine_point
      \<Rightarrow> nat \<Rightarrow> affine_point" where
  "certified_affine_orbit chooser p 0 = p"
| "certified_affine_orbit chooser p (Suc n) =
    apply_affine_branch (chooser (certified_affine_orbit chooser p n))
      (certified_affine_orbit chooser p n)"

theorem certified_affine_invariant_induction:
  assumes initial: "chart_invariant S p"
    and closed: "\<And>q. chart_invariant S q \<Longrightarrow>
      branch_certificate S (chooser q)"
  shows "chart_invariant S (certified_affine_orbit chooser p n)"
proof (induct n)
  case 0
  then show ?case using initial by simp
next
  case (Suc n)
  show ?case
    by (simp only: certified_affine_orbit.simps;
        rule certified_branch_preserves_chart[OF Suc closed[OF Suc]])
qed

text \<open>The theorem above cannot certify arbitrary integer inputs unless
the concrete chart family also proves exhaustive deterministic branch
coverage and contains the initial point.  No such source-7 certificate is
postulated in this theory.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms constraint_combination_value farkas_certificate_sound
      indexed_constraint_combination_value indexed_farkas_certificate_sound
      pullback_constraint_value certified_branch_preserves_chart
      certified_affine_invariant_induction}) then ()
    else error "Antihydra affine certificate proof depends on an oracle";
\<close>

end
