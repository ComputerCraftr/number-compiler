theory Primary_Carry_Jet
  imports Main
begin

text \<open>The concrete integer-coordinate implementation of the first jet at
z=-1, reduced modulo 16. No support-separation premise is hidden in its algebra.\<close>

type_synonym carry_jet = "int \<times> int"

definition jet_reduce :: "carry_jet \<Rightarrow> carry_jet" where
  "jet_reduce x = (fst x mod 16, snd x mod 16)"

definition jet_defect :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> carry_jet \<Rightarrow> carry_jet" where
  "jet_defect L u v q = jet_reduce
    (3 * fst q - u + v * (-1)^L,
     3 * snd q - fst q - v * int L * (-1)^L)"

definition jet_recover :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> carry_jet \<Rightarrow> carry_jet" where
  "jet_recover L u v d = (let
     a = fst d + u - v * (-1)^L;
     b = snd d + v * int L * (-1)^L
   in jet_reduce (11*a, 11*b + 9*a))"

lemma mod16_add:
  "((a::int) mod 16 + b) mod 16 = (a+b) mod 16"
  by (simp add: mod_add_left_eq)

lemma mod16_sub:
  "((a::int) mod 16 - b) mod 16 = (a-b) mod 16"
  by (simp add: mod_diff_left_eq)

lemma mod16_mult:
  "(a * ((b::int) mod 16)) mod 16 = (a*b) mod 16"
  by (simp add: mod_mult_right_eq)

lemma jet_reduce_idempotent [simp]:
  "jet_reduce (jet_reduce q) = jet_reduce q"
  by (simp add: jet_reduce_def)

lemma recover_reduction:
  "jet_recover L u v (jet_reduce d) = jet_recover L u v d"
  unfolding jet_recover_def jet_reduce_def Let_def
  apply (simp only: fst_conv snd_conv prod.inject)
  apply (intro conjI mod_mult_cong mod_add_cong mod_diff_cong)
  by simp_all

lemma defect_reduction:
  "jet_defect L u v (jet_reduce q) = jet_defect L u v q"
  unfolding jet_defect_def jet_reduce_def
  apply (simp only: fst_conv snd_conv prod.inject)
  apply (intro conjI mod_mult_cong mod_add_cong mod_diff_cong)
  by simp_all

lemma defect_recover_exact:
  "jet_recover L u v (jet_defect L u v q) = jet_reduce q"
  unfolding jet_defect_def
  apply (simp only: recover_reduction)
  unfolding jet_recover_def jet_reduce_def Let_def
  by (simp add: mod_eq_dvd_iff algebra_simps)

lemma recover_defect_exact:
  "jet_defect L u v (jet_recover L u v d) = jet_reduce d"
  unfolding jet_recover_def Let_def
  apply (simp only: defect_reduction)
  unfolding jet_defect_def jet_reduce_def
  by (simp add: mod_eq_dvd_iff algebra_simps)

definition jet_shift :: "nat \<Rightarrow> carry_jet \<Rightarrow> carry_jet" where
  "jet_shift L q = ((-1)^L * fst q,
    (-1)^L * (snd q - int L * fst q))"

definition jet_add :: "carry_jet \<Rightarrow> carry_jet \<Rightarrow> carry_jet" where
  "jet_add a b = (fst a + fst b, snd a + snd b)"

lemma jet_shift_zero [simp]: "jet_shift 0 q = q"
  by (cases q) (simp add: jet_shift_def)

lemma jet_shift_compose:
  "jet_shift (L+M) q = jet_shift L (jet_shift M q)"
  by (simp add: jet_shift_def power_add algebra_simps)

lemma jet_shift_add:
  "jet_shift L (jet_add a b) = jet_add (jet_shift L a) (jet_shift L b)"
  by (simp add: jet_shift_def jet_add_def algebra_simps)


lemma jet_add_reduction:
  "jet_reduce (jet_add (jet_reduce a) (jet_reduce b)) = jet_reduce (jet_add a b)"
  by (simp add: jet_reduce_def jet_add_def mod_simps)

lemma jet_shift_reduction:
  "jet_reduce (jet_shift L (jet_reduce a)) = jet_reduce (jet_shift L a)"
  unfolding jet_reduce_def jet_shift_def
  apply (simp only: fst_conv snd_conv prod.inject)
  apply (intro conjI mod_mult_cong mod_add_cong mod_diff_cong)
  by simp_all

definition coefficient_jet :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> carry_jet" where
  "coefficient_jet a L = ((\<Sum>i<L. a i * (-1)^i),
    (\<Sum>i<L. - int i * a i * (-1)^i))"

lemma coefficient_jet_boundary:
  "coefficient_jet a (Suc L) = jet_add (coefficient_jet a L)
    (a L * (-1)^L, - int L * a L * (-1)^L)"
  by (simp add: coefficient_jet_def jet_add_def sum.lessThan_Suc)

record carry_jet_action =
  jet_span :: nat
  jet_endpoint :: "int \<Rightarrow> int"
  jet_emission :: "int \<Rightarrow> carry_jet"

definition jet_then :: "carry_jet_action \<Rightarrow> carry_jet_action \<Rightarrow> carry_jet_action" where
  "jet_then a b = \<lparr>jet_span = jet_span a + jet_span b,
    jet_endpoint = jet_endpoint b \<circ> jet_endpoint a,
    jet_emission = (\<lambda>u. jet_add (jet_emission a u)
      (jet_shift (jet_span a) (jet_emission b (jet_endpoint a u))))\<rparr>"

lemma jet_then_associative:
  "jet_then (jet_then a b) c = jet_then a (jet_then b c)"
  by (cases a; cases b; cases c)
    (simp add: jet_then_def fun_eq_iff jet_shift_def jet_add_def
      power_add algebra_simps)

text \<open>The normalized cochain identity follows from the digit recurrence,
including both seam scalars. It is valid for signed coefficient words as well.\<close>

definition polynomial_prefix :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "polynomial_prefix a L z = (\<Sum>i<L. a i * z^i)"

theorem carry_normalization_identity:
  assumes steps: "\<And>i. i < L \<Longrightarrow> a i + c i = r i + 2*c (Suc i)"
  shows "polynomial_prefix a L z - polynomial_prefix r L z =
    (2-z)*polynomial_prefix (\<lambda>i. c (Suc i)) L z - c 0 + c L*z^L"
  using steps
proof (induction L)
  case 0
  then show ?case by (simp add: polynomial_prefix_def)
next
  case (Suc L)
  have prior: "polynomial_prefix a L z - polynomial_prefix r L z =
    (2-z)*polynomial_prefix (\<lambda>i. c (Suc i)) L z - c 0 + c L*z^L"
    using Suc.IH Suc.prems by auto
  have edge: "a L + c L = r L + 2*c (Suc L)" using Suc.prems by simp
  have edge_diff: "a L - r L = 2*c (Suc L) - c L" using edge by linarith
  have expand: "polynomial_prefix a (Suc L) z - polynomial_prefix r (Suc L) z =
      (polynomial_prefix a L z - polynomial_prefix r L z) + (a L-r L)*z^L"
    by (simp add: polynomial_prefix_def sum.lessThan_Suc algebra_simps)
  show ?case
    unfolding expand prior edge_diff
    by (simp add: polynomial_prefix_def sum.lessThan_Suc power_Suc algebra_simps)
qed

theorem carry_coefficient_jet_identity:
  assumes steps: "\<And>i. i<L \<Longrightarrow> a i + c i = r i + 2*c (Suc i)"
  shows "coefficient_jet (\<lambda>i. a i-r i) L =
    (3 * fst (coefficient_jet (\<lambda>i. c (Suc i)) L) - c 0 + c L * (-1)^L,
     3 * snd (coefficient_jet (\<lambda>i. c (Suc i)) L) -
       fst (coefficient_jet (\<lambda>i. c (Suc i)) L) - c L * int L * (-1)^L)"
  using steps
proof (induction L)
  case 0
  then show ?case by (simp add: coefficient_jet_def)
next
  case (Suc L)
  have prior: "coefficient_jet (\<lambda>i. a i-r i) L =
    (3 * fst (coefficient_jet (\<lambda>i. c (Suc i)) L) - c 0 + c L * (-1)^L,
     3 * snd (coefficient_jet (\<lambda>i. c (Suc i)) L) -
       fst (coefficient_jet (\<lambda>i. c (Suc i)) L) - c L * int L * (-1)^L)"
    using Suc.IH Suc.prems by auto
  have edge: "a L-r L = 2*c (Suc L)-c L" using Suc.prems[of L] by auto
  show ?case
    by (simp only: coefficient_jet_boundary prior jet_add_def fst_conv snd_conv edge;
      simp add: power_Suc algebra_simps)
qed

corollary normalization_defect_is_carry_jet_action:
  assumes steps: "\<And>i. i<L \<Longrightarrow> a i + c i = r i + 2*c (Suc i)"
  shows "jet_defect L (c 0) (c L) (coefficient_jet (\<lambda>i. c (Suc i)) L) =
    jet_reduce (coefficient_jet (\<lambda>i. a i-r i) L)"
  unfolding jet_defect_def
  using carry_coefficient_jet_identity[where a=a and c=c and r=r and L=L, OF steps]
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms defect_recover_exact recover_defect_exact jet_shift_compose
      jet_shift_add jet_then_associative carry_normalization_identity
      carry_coefficient_jet_identity normalization_defect_is_carry_jet_action}) then ()
    else error "Primary carry jet proof depends on an oracle";
\<close>
end
