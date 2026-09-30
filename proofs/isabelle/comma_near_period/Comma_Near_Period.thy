theory Comma_Near_Period
  imports Comma_Run_Germ.Comma_Run_Germ
begin

lemma comma_near_internal_iff:
  assumes "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
  shows "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 t) \<longleftrightarrow>
    10*((10-h mod 10) mod 10)+f+(if f<9 then 1 else 0)<h \<and>
    t=h-(10*((10-h mod 10) mod 10)+f)"
  using assms
  by (auto simp: comma_near_control_formula Let_def split: if_splits)

lemma comma_near_prefix_append:
  assumes "comma_near_prefix n f h u" "comma_near_prefix m f u t"
  shows "comma_near_prefix (n+m) f h t"
  using assms by (induction n arbitrary: h) auto

lemma comma_near_prefix_decisive_germ:
  assumes "comma_near_prefix n f h t" "comma_near_decisive f t"
  shows "comma_near_germ f h=(n,t)"
  using assms
proof (induction n arbitrary: h)
  case 0
  then show ?case
    by (cases "comma_finite_step 0 (Comma_Near f 0 h)")
      (auto simp: comma_near_germ.simps comma_near_decisive_def
        split: comma_finite_position.splits)
next
  case (Suc n)
  then obtain j where step:
    "comma_finite_step 0 (Comma_Near f 0 h)=Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t" by auto
  show ?case using Suc.IH[OF tail Suc.prems(2)]
    by (simp only: comma_near_germ.simps[of f h] step
      comma_finite_move.case comma_finite_position.case Let_def prod.case)
qed

lemmas comma_near_germ_unique = comma_near_prefix_decisive_germ

lemma comma_near_complement_digit:
  fixes x y :: nat
  assumes "(x+y) mod 10=0"
  shows "(10-x mod 10) mod 10=y mod 10"
proof -
  let ?a = "x mod 10"
  let ?b = "y mod 10"
  have bounds: "?a<10" "?b<10" by simp_all
  have zero: "(?a+?b) mod 10=0" using assms by (simp add: mod_add_eq)
  have divides: "10 dvd ?a+?b" using zero by (simp only: dvd_eq_mod_eq_0)
  obtain q where q: "?a+?b=10*q" using divides unfolding dvd_def by blast
  have "q=0 \<or> q=1" using q bounds by arith
  then have sum: "?a+?b=0 \<or> ?a+?b=10" using q by auto
  show ?thesis
  proof (cases "?a=0")
    case True
    have "?b=0" using sum bounds True by arith
    then show ?thesis using True by simp
  next
    case False
    have "10-?a=?b" using sum False by arith
    then show ?thesis by simp
  qed
qed

lemma comma_near_phase_headroom_digit:
  assumes digit: "d<10" and aligned: "(h+d) mod 10=0"
    and fits: "comma_period_displacement f d n\<le>h"
  shows "(10-(h-comma_period_displacement f d n) mod 10) mod 10 =
    comma_phase_digit f d n"
proof -
  have iter: "comma_fixed_iter f n d=d+comma_period_displacement f d n"
    using comma_fixed_iter_displacement[of f n d] digit by simp
  have sum: "(h-comma_period_displacement f d n)+comma_fixed_iter f n d=h+d"
    using fits iter by arith
  have "(10-(h-comma_period_displacement f d n) mod 10) mod 10 =
    comma_fixed_iter f n d mod 10"
    by (rule comma_near_complement_digit) (simp only: sum aligned)
  then show ?thesis using digit
    by (simp add: comma_fixed_iter_phase comma_phase_digit_def)
qed

text \<open>A single strict bound on final displacement certifies every
internal Near edge. The phase evolution is inherited from the existing
fixed-iteration displacement theorem.\<close>
lemma comma_near_prefix_from_displacement:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "h\<le>540"
    and digit: "d<10" and aligned: "(h+d) mod 10=0"
    and safe: "comma_period_displacement f d n+(if f<9 then 1 else 0)<h"
  shows "comma_near_prefix n f h (h-comma_period_displacement f d n)"
  using safe
proof (induction n)
  case 0
  then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc n)
  let ?D = "comma_period_displacement f d n"
  let ?a = "10*comma_phase_digit f d n+f"
  let ?e = "if f<9 then 1 else 0"
  have next_disp: "comma_period_displacement f d (Suc n)=?D+?a"
    by (simp add: comma_period_displacement_succ algebra_simps)
  have safe: "?D+?e<h" "?a+?e<h-?D" "?D\<le>h"
    using Suc.prems next_disp by arith+
  have prefix: "comma_near_prefix n f h (h-?D)"
    by (rule Suc.IH[OF safe(1)])
  have phase: "(10-(h-?D) mod 10) mod 10=comma_phase_digit f d n"
    by (rule comma_near_phase_headroom_digit[OF digit aligned safe(3)])
  have valid: "1\<le>h-?D" "h-?D\<le>540"
    using safe initial by arith+
  have step: "comma_finite_step 0 (Comma_Near f 0 (h-?D))=
    Comma_Next (Comma_Near f 0 (h-comma_period_displacement f d (Suc n)))"
    using safe(2)
    by (simp add: comma_near_internal_iff[OF sector valid] phase next_disp
      diff_diff_left)
  have tail: "comma_near_prefix 1 f (h-?D)
      (h-comma_period_displacement f d (Suc n))"
    using step by auto
  show ?case using comma_near_prefix_append[OF prefix tail] by simp
qed

lemma comma_near_complete_cycles_prefix:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "h\<le>540"
    and digit: "d<10" and aligned: "(h+d) mod 10=0"
    and closes: "10 dvd L*f"
    and safe: "q*comma_period_displacement f d L+(if f<9 then 1 else 0)<h"
  shows "comma_near_prefix (q*L) f h (h-q*comma_period_displacement f d L)"
proof -
  have displacement: "comma_period_displacement f d (q*L)=
      q*comma_period_displacement f d L"
    using comma_period_displacement_repeated[OF closes, of d q 0]
    by (simp add: comma_period_displacement_def)
  show ?thesis using comma_near_prefix_from_displacement
    [OF sector initial digit aligned, of "q*L"] safe
    by (simp only: displacement)
qed

lemma comma_near_initial_digit_aligned:
  fixes h :: nat
  shows "(h+(10-h mod 10) mod 10) mod 10=0"
proof -
  let ?a = "h mod 10"
  have bound: "?a<10" by simp
  have inner: "(?a+(10-?a) mod 10) mod 10=0"
  proof (cases "?a=0")
    case True
    then show ?thesis by simp
  next
    case False
    have small: "10-?a<10" using False by arith
    have sum: "?a+(10-?a)=10" using bound by arith
    show ?thesis by (simp only: mod_less[OF small] sum) simp
  qed
  show ?thesis using inner by (simp only: mod_add_left_eq)
qed


lemma comma_near_decisive_iff:
  assumes "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
  shows "comma_near_decisive f h \<longleftrightarrow>
    h\<le>10*((10-h mod 10) mod 10)+f+(if f<9 then 1 else 0)"
  using assms
  by (auto simp: comma_near_decisive_def comma_near_control_formula Let_def
    split: if_splits)

lemma comma_near_germ_from_maximal_displacement:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "h\<le>540"
    and digit: "d<10" and aligned: "(h+d) mod 10=0"
    and safe: "comma_period_displacement f d n+(if f<9 then 1 else 0)<h"
    and maximal: "h\<le>comma_period_displacement f d (Suc n)+(if f<9 then 1 else 0)"
  shows "comma_near_germ f h=(n,h-comma_period_displacement f d n)"
proof -
  let ?D = "comma_period_displacement f d n"
  have fits: "?D\<le>h" and valid: "1\<le>h-?D" "h-?D\<le>540"
    using safe initial by arith+
  have phase: "(10-(h-?D) mod 10) mod 10=comma_phase_digit f d n"
    by (rule comma_near_phase_headroom_digit[OF digit aligned fits])
  have bound: "h-?D\<le>10*comma_phase_digit f d n+f+(if f<9 then 1 else 0)"
    using maximal comma_period_displacement_succ[of f d n] by arith
  have decisive: "comma_near_decisive f (h-?D)"
    using bound by (simp add: comma_near_decisive_iff[OF sector valid] phase)
  show ?thesis
    by (rule comma_near_prefix_decisive_germ
      [OF comma_near_prefix_from_displacement[OF sector initial digit aligned safe]
        decisive])
qed

text \<open>The arithmetic certificate may use an arbitrary number of
complete periods and one residual position. Only the residual displacement
and its next guard remain to be checked; headrooms are never enumerated.\<close>
lemma comma_near_germ_from_period_residual:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "h\<le>540"
    and digit: "d<10" and aligned: "(h+d) mod 10=0"
    and closes: "10 dvd L*f"
    and safe: "q*comma_period_displacement f d L+
      comma_period_displacement f d j+(if f<9 then 1 else 0)<h"
    and maximal: "h\<le>q*comma_period_displacement f d L+
      comma_period_displacement f d (Suc j)+(if f<9 then 1 else 0)"
  shows "comma_near_germ f h=(q*L+j,h-(q*comma_period_displacement f d L+
    comma_period_displacement f d j))"
proof -
  have displacement: "comma_period_displacement f d (q*L+j)=
      q*comma_period_displacement f d L+comma_period_displacement f d j"
    by (rule comma_period_displacement_repeated[OF closes])
  have next_disp: "comma_period_displacement f d (Suc (q*L+j))=
      q*comma_period_displacement f d L+comma_period_displacement f d (Suc j)"
    using comma_period_displacement_repeated[OF closes, of d q "Suc j"] by simp
  show ?thesis using comma_near_germ_from_maximal_displacement
    [OF sector initial digit aligned, of "q*L+j"] safe maximal
    by (simp only: displacement next_disp)
qed


lemma comma_near_phase_tail:
  "comma_phase_digit f ((d+f) mod 10) n=comma_phase_digit f d (Suc n)"
  by (simp add: comma_phase_digit_def mod_add_left_eq mod_add_right_eq algebra_simps)

lemma comma_near_displacement_tail:
  assumes digit: "d<10"
  shows "comma_period_displacement f d (Suc n)=10*d+f+
    comma_period_displacement f ((d+f) mod 10) n"
proof (induction n)
  case 0
  then show ?case using digit
    by (simp add: comma_period_displacement_succ comma_period_displacement_def
      comma_phase_digit_def)
next
  case (Suc n)
  then show ?case
    by (simp add: comma_period_displacement_succ comma_near_phase_tail
      add.assoc)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_near_internal_iff comma_near_prefix_append
      comma_near_prefix_decisive_germ comma_near_complement_digit
      comma_near_phase_headroom_digit comma_near_prefix_from_displacement
      comma_near_complete_cycles_prefix comma_near_initial_digit_aligned
      comma_near_decisive_iff comma_near_germ_from_maximal_displacement
      comma_near_germ_from_period_residual comma_near_phase_tail
      comma_near_displacement_tail}) then ()
    else error "Near period bridge depends on an oracle";
\<close>

end
