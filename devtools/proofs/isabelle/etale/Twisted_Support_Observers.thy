theory Twisted_Support_Observers
  imports Skew_Cylinder_Observers
begin

lemma twisted_monomial_evaluation:
  fixes b s N :: int
  assumes twist: "b^w mod N = s mod N"
  shows "b^i mod N = (s^(i div w) * b^(i mod w)) mod N"
proof -
  have index: "w*(i div w) + i mod w = i" by (simp add: div_mult_mod_eq mult.commute)
  have split: "b^i = (b^w)^(i div w) * b^(i mod w)"
    by (simp only: power_mult[symmetric] power_add[symmetric] index)
  have powers: "(b^w)^(i div w) mod N = s^(i div w) mod N"
    using arg_cong[OF twist, of "\<lambda>x. x^(i div w) mod N"]
    by (simp only: power_mod)
  show ?thesis unfolding split by (rule mod_mult_cong[OF powers]) simp
qed

theorem twisted_evaluation_commutes:
  fixes a :: "nat \<Rightarrow> int"
  assumes twist: "b^w mod N = s mod N"
  shows "(\<Sum>i<L. a i*b^i) mod N =
    (\<Sum>i<L. a i*s^(i div w)*b^(i mod w)) mod N"
proof -
  have each: "(a i*b^i) mod N = (a i*s^(i div w)*b^(i mod w)) mod N" for i
    unfolding mult.assoc
    by (rule mod_mult_cong) (simp_all add: twisted_monomial_evaluation[OF twist])
  have sums: "(\<Sum>i<L. (a i*b^i) mod N) =
      (\<Sum>i<L. (a i*s^(i div w)*b^(i mod w)) mod N)"
    by (simp only: each)
  show ?thesis using arg_cong[OF sums, of "\<lambda>x. x mod N"]
    by (simp only: mod_sum_eq)
qed

lemma modular_affine_demand:
  fixes A A' B B' x R N :: int
  assumes "A mod N = A' mod N" "B mod N = B' mod N"
  shows "(A*x+B-R) mod N = (A'*x+B'-R) mod N"
  by (intro mod_diff_cong mod_add_cong mod_mult_cong) (simp_all add: assms)

lemma gcd_saturate_left:
  fixes N a b :: nat
  shows "gcd N (gcd N a * b) = gcd N (a*b)"
proof -
  have product: "gcd N a * b = gcd (N*b) (a*b)"
    by (simp add: gcd_mult_right gcd.commute mult.commute)
  show ?thesis by (simp add: product gcd.assoc[symmetric])
qed

lemma gcd_saturate_right:
  fixes N a b :: nat
  shows "gcd N (a * gcd N b) = gcd N (a*b)"
  using gcd_saturate_left[of N b a] by (simp only: mult.commute)

theorem tropical_product_observation:
  fixes N a b :: nat
  shows "gcd N (gcd N a * gcd N b) = gcd N (a*b)"
  by (simp only: gcd_saturate_left gcd_saturate_right)

lemma saturated_product_associative:
  fixes N a b c :: nat
  shows "gcd N (gcd N (a*b) * c) = gcd N (a * gcd N (b*c))"
  by (simp only: gcd_saturate_left gcd_saturate_right mult.assoc)

lemma tropical_meet_observation:
  fixes N a b :: nat
  shows "gcd (gcd N a) (gcd N b) = gcd N (gcd a b)"
  by (simp add: gcd.assoc gcd.left_commute gcd.commute)

lemma mirror_zero_has_zero_sheet:
  fixes d :: "nat \<Rightarrow> int"
  assumes mirror: "\<And>i. i<L \<Longrightarrow> d i=d (L-1-i)"
  shows "(\<Sum>i<L. (d i-d (L-1-i))*s^(i div w)*b^(i mod w)) = 0"
proof -
  have difference: "d i-d (L-1-i)=0" if "i<L" for i
    using mirror[OF that] by arith
  show ?thesis
  proof (rule sum.neutral, intro ballI)
    fix i assume "i \<in> {..<L}"
    then have i: "i<L" by simp
    show "(d i-d (L-1-i))*s^(i div w)*b^(i mod w)=0"
      by (simp only: difference[OF i] mult_zero_left)
  qed
qed

corollary nonzero_mirror_sheet_certifies_obstruction:
  fixes d :: "nat \<Rightarrow> int"
  assumes "(\<Sum>i<L. (d i-d (L-1-i))*s^(i div w)*b^(i mod w)) \<noteq> 0"
  shows "\<exists>i<L. d i \<noteq> d (L-1-i)"
  using assms mirror_zero_has_zero_sheet[of L d s w b] by blast

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms twisted_monomial_evaluation
   twisted_evaluation_commutes modular_affine_demand tropical_product_observation
   saturated_product_associative tropical_meet_observation
   nonzero_mirror_sheet_certifies_obstruction}) then ()
   else error "Twisted support observer oracle dependency";
\<close>
end
