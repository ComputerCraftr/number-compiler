theory Reverse_Residuals
  imports Main
begin

text \<open>Exact definitions and proof obligations. No active 196 quotient is
assumed or admitted by this theory.\<close>

datatype carry_domain = Below | Equal | Above

definition domain :: "nat \<Rightarrow> carry_domain" where
  "domain s = (if s < 9 then Below else if s = 9 then Equal else Above)"

fun carry_apply :: "carry_domain \<Rightarrow> bool \<Rightarrow> bool" where
  "carry_apply Below c = False"
| "carry_apply Equal c = c"
| "carry_apply Above c = True"

definition carry_then ::
    "carry_domain \<Rightarrow> carry_domain \<Rightarrow> carry_domain" where
  "carry_then after before = (if after = Equal then before else after)"

lemma carry_then_apply:
  "carry_apply (carry_then after before) c =
    carry_apply after (carry_apply before c)"
  by (cases after; cases before; cases c; simp_all add: carry_then_def)

lemma carry_from_domain:
  "carry_apply (domain s) c = (10 \<le> s + (if c then 1 else 0))"
  by (cases c) (auto simp: domain_def)

definition carry_out :: "bool \<Rightarrow> nat list \<Rightarrow> bool" where
  "carry_out c ss = fold (\<lambda>s c. carry_apply (domain s) c) ss c"

lemma carry_depends_only_on_domains:
  assumes "map domain xs = map domain ys"
  shows "carry_out c xs = carry_out c ys"
proof -
  have "carry_out c xs = fold carry_apply (map domain xs) c"
    by (simp add: carry_out_def fold_map comp_def)
  also have "... = fold carry_apply (map domain ys) c" using assms by simp
  also have "... = carry_out c ys"
    by (simp add: carry_out_def fold_map comp_def)
  finally show ?thesis .
qed

fun emit :: "bool \<Rightarrow> nat list \<Rightarrow> nat list" where
  "emit c [] = []"
| "emit c (s # ss) = ((s + (if c then 1 else 0)) mod 10) #
    emit (carry_apply (domain s) c) ss"

definition digits :: "nat list \<Rightarrow> nat list" where
  "digits ss = emit False ss @ (if carry_out False ss then [1] else [])"

definition step :: "nat list \<Rightarrow> nat list" where
  "step ss = map (\<lambda>(a,b). a+b) (zip (digits ss) (rev (digits ss)))"

lemma example_steps [simp]:
  "step [10] = [1,1]" "step [1,1] = [2,2]" "step [2,2] = [4,4]"
  "step [12] = [3,3]" "step [3,3] = [6,6]" "step [6,6] = [12,12]"
  "step [14] = [5,5]" "step [5,5] = [10,10]" "step [10,10] = [1,2,1]"
  "step [16] = [7,7]" "step [7,7] = [14,14]" "step [14,14] = [5,10,5]"
  "step [18] = [9,9]" "step [9,9] = [18,18]" "step [18,18] = [9,18,9]"
  by (simp_all add: step_def digits_def carry_out_def domain_def)

definition observation where
  "observation ss = (map domain ss, carry_out False ss, length ss)"

definition key2 where
  "key2 ss = (observation ss, observation (step ss),
     observation (step (step ss)))"

lemma two_event_merge:
  "key2 [10] = key2 [12]"
  by (simp only: key2_def example_steps; simp add: observation_def carry_out_def domain_def)

lemma third_event_separates:
  "observation (step (step (step [10]))) \<noteq>
   observation (step (step (step [12])))"
  by (simp only: example_steps; simp add: observation_def carry_out_def domain_def)

lemma shifted_keys_separate:
  "key2 (step [10]) \<noteq> key2 (step [12])"
  by (simp only: key2_def example_steps; simp add: observation_def carry_out_def domain_def)

theorem two_event_key_has_no_total_successor:
  "\<not> (\<exists>u. \<forall>ss. u (key2 ss) = key2 (step ss))"
  using two_event_merge shifted_keys_separate by metis

definition key3 where
  "key3 ss = (key2 ss, observation (step (step (step ss))))"

theorem five_examples_separated_by_three_events:
  "inj_on key3 {[10], [12], [14], [16], [18]}"
  by (simp only: inj_on_def ball_simps;
      simp only: key3_def key2_def example_steps;
      simp add: observation_def carry_out_def domain_def)

text \<open>A complete factor-through criterion, including restricted domains.\<close>

theorem factor_through_iff:
  "(\<exists>h. \<forall>s\<in>A. h (q s) = r s) \<longleftrightarrow>
   (\<forall>s\<in>A. \<forall>t\<in>A. q s = q t \<longrightarrow> r s = r t)"
proof
  assume "\<exists>h. \<forall>s\<in>A. h (q s) = r s"
  then show "\<forall>s\<in>A. \<forall>t\<in>A. q s = q t \<longrightarrow> r s = r t"
    by metis
next
  assume congruence: "\<forall>s\<in>A. \<forall>t\<in>A. q s = q t \<longrightarrow> r s = r t"
  let ?h = "\<lambda>z. r (SOME s. s \<in> A \<and> q s = z)"
  have "?h (q s) = r s" if "s \<in> A" for s
  proof -
    have "\<exists>t. t \<in> A \<and> q t = q s" using that by blast
    then have "(SOME t. t \<in> A \<and> q t = q s) \<in> A \<and>
       q (SOME t. t \<in> A \<and> q t = q s) = q s"
      by (rule someI_ex)
    then show ?thesis using congruence that by blast
  qed
  then show "\<exists>h. \<forall>s\<in>A. h (q s) = r s"
    by (intro exI[of _ ?h]) blast
qed

corollary contextual_successor_iff:
  "(\<exists>h. \<forall>s\<in>A. h (F s) = G s) \<longleftrightarrow>
   (\<forall>s\<in>A. \<forall>t\<in>A.
      (\<forall>c. F s c = F t c) \<longrightarrow> (\<forall>c. G s c = G t c))"
  unfolding factor_through_iff by (auto simp: fun_eq_iff)

fun run :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "run f 0 s = s"
| "run f (Suc n) s = run f n (f s)"

theorem iterate_commutes:
  assumes closed: "\<And>s. s \<in> A \<Longrightarrow> T s \<in> A"
      and commute: "\<And>s. s \<in> A \<Longrightarrow> q (T s) = u (q s)"
      and initial: "s \<in> A"
  shows "q (run T n s) = run u n (q s)"
  using initial
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "T s \<in> A" using closed Suc.prems by blast
  then have "q (run T n (T s)) = run u n (q (T s))" by (rule Suc.IH)
  also have "... = run u n (u (q s))" using commute Suc.prems by simp
  finally show ?case by simp
qed

text \<open>The next theorem constructs a mathematical quotient successor from
an invariant and a proved congruence. Its assumptions must still be discharged
for a concrete 196 representation; a finite trace does not discharge them.\<close>

theorem invariant_quotient_exists:
  assumes closed: "\<And>s. s \<in> A \<Longrightarrow> T s \<in> A"
      and congruence: "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
          q s = q t \<Longrightarrow> q (T s) = q (T t)"
  shows "\<exists>u. \<forall>s\<in>A. \<forall>n. q (run T n s) = run u n (q s)"
proof -
  obtain u where commute: "\<forall>s\<in>A. u (q s) = q (T s)"
    using factor_through_iff[of A q "\<lambda>s. q (T s)"] congruence by blast
  have step_commutes: "q (T x) = u (q x)" if "x \<in> A" for x
  proof -
    from commute that have "u (q x) = q (T x)" by (rule bspec)
    then show ?thesis by (rule sym)
  qed
  have "q (run T n s) = run u n (q s)" if "s \<in> A" for s n
    by (rule iterate_commutes[where A=A and T=T and q=q and u=u,
          OF closed step_commutes that])
  then show ?thesis by (intro exI[of _ u]) blast
qed

ML \<open>
  val checked = @{thms carry_then_apply carry_from_domain carry_depends_only_on_domains
    two_event_key_has_no_total_successor five_examples_separated_by_three_events
    factor_through_iff contextual_successor_iff iterate_commutes invariant_quotient_exists};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Residual proof depends on an oracle";
\<close>

end
