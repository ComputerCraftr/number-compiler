theory Comma_Affine_Ray
  imports Comma_Boundary_Quotient
begin

text \<open>A macro fragment evaluates its integer-affine guards at
X = 10^p.  Checking one representative exponent is sound along an
unbounded exponent ray only with a suitable slope condition.  These
lemmas are the arithmetic part of that condition; they do not assert
that a table of macro fragments covers the comma graph.\<close>

definition comma_affine_ray :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "comma_affine_ray slope intercept p = slope * int (10 ^ p) + intercept"

lemma comma_affine_ray_increasing:
  assumes slope: "0 \<le> slope" and order: "initial \<le> p"
  shows "comma_affine_ray slope intercept initial \<le>
    comma_affine_ray slope intercept p"
proof -
  have powers: "(10::nat) ^ initial \<le> 10 ^ p"
    by (rule power_increasing[OF order]) simp
  have int_powers: "int ((10::nat) ^ initial) \<le> int (10 ^ p)"
    using powers by simp
  have product: "slope * int ((10::nat) ^ initial) \<le>
      slope * int (10 ^ p)"
    by (rule mult_left_mono[OF int_powers slope])
  show ?thesis using product
    by (simp add: comma_affine_ray_def)
qed

lemma comma_affine_ray_decreasing:
  assumes slope: "slope \<le> 0" and order: "initial \<le> p"
  shows "comma_affine_ray slope intercept p \<le>
    comma_affine_ray slope intercept initial"
proof -
  have nonnegative: "0 \<le> -slope" using slope by simp
  have increase: "comma_affine_ray (-slope) (-intercept) initial \<le>
      comma_affine_ray (-slope) (-intercept) p"
    by (rule comma_affine_ray_increasing[OF nonnegative order])
  show ?thesis using increase
    by (simp add: comma_affine_ray_def)
qed

lemma comma_affine_ray_positive_guard:
  assumes slope: "0 \<le> slope"
    and sample: "0 < comma_affine_ray slope intercept initial"
    and order: "initial \<le> p"
  shows "0 < comma_affine_ray slope intercept p"
proof -
  have monotone: "comma_affine_ray slope intercept initial \<le>
      comma_affine_ray slope intercept p"
    by (rule comma_affine_ray_increasing[OF slope order])
  show ?thesis using sample monotone by linarith
qed

lemma comma_affine_ray_nonnegative_guard:
  assumes slope: "0 \<le> slope"
    and sample: "0 \<le> comma_affine_ray slope intercept initial"
    and order: "initial \<le> p"
  shows "0 \<le> comma_affine_ray slope intercept p"
proof -
  have monotone: "comma_affine_ray slope intercept initial \<le>
      comma_affine_ray slope intercept p"
    by (rule comma_affine_ray_increasing[OF slope order])
  show ?thesis using sample monotone by linarith
qed

lemma comma_affine_ray_negative_guard:
  assumes slope: "slope \<le> 0"
    and sample: "comma_affine_ray slope intercept initial < 0"
    and order: "initial \<le> p"
  shows "comma_affine_ray slope intercept p < 0"
proof -
  have monotone: "comma_affine_ray slope intercept p \<le>
      comma_affine_ray slope intercept initial"
    by (rule comma_affine_ray_decreasing[OF slope order])
  show ?thesis using sample monotone by linarith
qed

lemma comma_affine_ray_nonpositive_guard:
  assumes slope: "slope \<le> 0"
    and sample: "comma_affine_ray slope intercept initial \<le> 0"
    and order: "initial \<le> p"
  shows "comma_affine_ray slope intercept p \<le> 0"
proof -
  have monotone: "comma_affine_ray slope intercept p \<le>
      comma_affine_ray slope intercept initial"
    by (rule comma_affine_ray_decreasing[OF slope order])
  show ?thesis using sample monotone by linarith
qed

lemma comma_affine_ray_zero_guard:
  assumes "slope = 0"
    "comma_affine_ray slope intercept initial = 0"
  shows "comma_affine_ray slope intercept p = 0"
  using assms by (simp add: comma_affine_ray_def)

definition comma_affine_ray_admitted :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_affine_ray_admitted slope intercept initial \<longleftrightarrow>
    (if 0 < comma_affine_ray slope intercept initial then 0 \<le> slope
     else if comma_affine_ray slope intercept initial < 0 then slope \<le> 0
     else slope = 0)"

lemma comma_affine_ray_admitted_sign:
  assumes admitted: "comma_affine_ray_admitted slope intercept initial"
    and order: "initial \<le> p"
  shows "sgn (comma_affine_ray slope intercept p) =
    sgn (comma_affine_ray slope intercept initial)"
proof (cases "0 < comma_affine_ray slope intercept initial")
  case True
  have slope: "0 \<le> slope"
    using admitted True by (simp add: comma_affine_ray_admitted_def)
  have future: "0 < comma_affine_ray slope intercept p"
    by (rule comma_affine_ray_positive_guard[OF slope True order])
  show ?thesis using future True by simp
next
  case False
  note nonpositive = False
  show ?thesis
  proof (cases "comma_affine_ray slope intercept initial < 0")
    case True
    have slope: "slope \<le> 0"
      using admitted nonpositive True
      by (simp add: comma_affine_ray_admitted_def)
    have future: "comma_affine_ray slope intercept p < 0"
      by (rule comma_affine_ray_negative_guard[OF slope True order])
    show ?thesis using future True by simp
  next
    case False
    have zero: "comma_affine_ray slope intercept initial = 0"
      using nonpositive False by linarith
    have slope: "slope = 0"
      using admitted nonpositive False
      by (simp add: comma_affine_ray_admitted_def)
    have future: "comma_affine_ray slope intercept p = 0"
      by (rule comma_affine_ray_zero_guard[OF slope zero])
    show ?thesis using future zero by simp
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_affine_ray_increasing comma_affine_ray_decreasing
      comma_affine_ray_positive_guard comma_affine_ray_nonnegative_guard
      comma_affine_ray_negative_guard comma_affine_ray_nonpositive_guard
      comma_affine_ray_zero_guard comma_affine_ray_admitted_sign})
    then () else error "Comma affine ray proof depends on an oracle";
\<close>
end
