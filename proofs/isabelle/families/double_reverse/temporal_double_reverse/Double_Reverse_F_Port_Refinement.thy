theory Double_Reverse_F_Port_Refinement
  imports Double_Reverse_Periodic_Ring_Action
begin

definition double_reverse_f_port_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f_port_digit h x r =
    (4*x + 2*h + (if r = 3 \<or> r = 4 \<or> (r = 2 \<and> 5 \<le> x)
      then 1 else 0)) mod 10"

definition double_reverse_f_port_pair ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_f_port_pair h b c r =
    (double_reverse_f_port_digit h b (c mod 5),
     double_reverse_f_port_digit (if 5 \<le> b then 1 else 0) c r)"

theorem double_reverse_f_port_pair_exact:
  assumes "a < 10" "b < 10" "c < 10" "d < 10"
  shows "double_reverse_f_port_pair (if 5 \<le> a then 1 else 0) b c (d mod 5) =
    (double_reverse_t2_digit a b c, double_reverse_t2_digit b c d)"
proof -
  have port: "double_reverse_f_port_digit (if 5 \<le> x then 1 else 0) y (z mod 5)
      = double_reverse_t2_digit x y z" if "x < 10" "y < 10" "z < 10" for x y z
  proof -
    have carry: "(if z mod 5 = 3 \<or> z mod 5 = 4 \<or> z mod 5 = 2 \<and> 5 \<le> y
        then 1 else 0::nat) = (if z mod 5 = 3 \<or> z mod 5 = 4 then 1 else 0)
        + (if 5 \<le> y \<and> z mod 5 = 2 then 1 else 0)"
      by (cases "z mod 5 = 3"; cases "z mod 5 = 4"; cases "z mod 5 = 2"; simp)
    show ?thesis
      by (simp only: double_reverse_f_port_digit_def carry
          double_reverse_t2_open_stencil_exact[OF that] add.assoc)
  qed
  show ?thesis by (simp only: double_reverse_f_port_pair_def
      port[OF assms(1-3)] port[OF assms(2-4)])
qed

definition double_reverse_f_right_class :: "nat \<Rightarrow> nat" where
  "double_reverse_f_right_class r = (if r < 2 then 0 else if r = 2 then 1 else 2)"

definition double_reverse_f_row :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> bool" where
  "double_reverse_f_row h x = ((4*x + 2*h) mod 10, 5 \<le> x)"

lemma double_reverse_f_response_exact:
  assumes "r < 5"
  shows "double_reverse_f_port_digit h x r =
    fst (double_reverse_f_row h x) +
      (if double_reverse_f_right_class r = 2 \<or>
         (double_reverse_f_right_class r = 1 \<and> snd (double_reverse_f_row h x))
       then 1 else 0)"
proof -
  have scale: "(4*x + 2*h) mod 10 = 2*((2*x + h) mod 5)"
  proof -
    have A: "4*x + 2*h = 2*(2*x + h)" by (simp add: algebra_simps)
    show ?thesis unfolding A using mod_mult_mult1[of 2 "2*x+h" 5] by simp
  qed
  have rem: "(2*x+h) mod 5 < 5" by simp
  have bounded: "(4*x + 2*h) mod 10 + 1 < 10" using rem unfolding scale by linarith
  have carry: "(r = 3 \<or> r = 4 \<or> r = 2 \<and> 5 \<le> x) =
      (double_reverse_f_right_class r = 2 \<or> double_reverse_f_right_class r = 1 \<and> 5 \<le> x)"
    using assms by (auto simp: double_reverse_f_right_class_def split: if_splits)
  have odd: "(4*x + 2*h + 1) mod 10 = (4*x + 2*h) mod 10 + 1"
    using mod_add_left_eq[of "4*x + 2*h" 10 1] bounded by simp
  show ?thesis
    unfolding double_reverse_f_port_digit_def double_reverse_f_row_def
    by (cases "r = 3 \<or> r = 4 \<or> r = 2 \<and> 5 \<le> x";
        simp only: fst_conv snd_conv if_True if_False add_0 odd carry[symmetric]; simp)
qed

theorem double_reverse_f_row_minimal:
  "(\<forall>r<5. double_reverse_f_port_digit h x r = double_reverse_f_port_digit k y r)
    \<longleftrightarrow> double_reverse_f_row h x = double_reverse_f_row k y"
proof
  assume eq: "\<forall>r<5. double_reverse_f_port_digit h x r = double_reverse_f_port_digit k y r"
  have zero: "double_reverse_f_port_digit h x 0 = double_reverse_f_port_digit k y 0"
    using eq by simp
  have tie: "double_reverse_f_port_digit h x 2 = double_reverse_f_port_digit k y 2"
    using eq by simp
  have base: "fst (double_reverse_f_row h x) = fst (double_reverse_f_row k y)"
    using zero by (simp add: double_reverse_f_response_exact double_reverse_f_right_class_def)
  have bit_eq: "snd (double_reverse_f_row h x) = snd (double_reverse_f_row k y)"
    using tie by (cases "snd (double_reverse_f_row h x)"; cases "snd (double_reverse_f_row k y)";
      simp add: double_reverse_f_response_exact double_reverse_f_right_class_def base)
  show "double_reverse_f_row h x = double_reverse_f_row k y"
    by (rule prod_eqI[OF base bit_eq])

next
  assume "double_reverse_f_row h x = double_reverse_f_row k y"
  then show "\<forall>r<5. double_reverse_f_port_digit h x r = double_reverse_f_port_digit k y r"
    by (simp add: double_reverse_f_response_exact)
qed

theorem double_reverse_f_right_minimal:
  assumes "r < 5" "s < 5"
  shows "(\<forall>h<2. \<forall>x<10. double_reverse_f_port_digit h x r = double_reverse_f_port_digit h x s)
    \<longleftrightarrow> double_reverse_f_right_class r = double_reverse_f_right_class s"
proof
  assume eq: "\<forall>h<2. \<forall>x<10. double_reverse_f_port_digit h x r = double_reverse_f_port_digit h x s"
  have low: "double_reverse_f_port_digit 0 0 r = double_reverse_f_port_digit 0 0 s"
    using eq by simp
  have high: "double_reverse_f_port_digit 0 5 r = double_reverse_f_port_digit 0 5 s"
    using eq by simp
  show "double_reverse_f_right_class r = double_reverse_f_right_class s"
    using low high assms by (cases "r<2"; cases "s<2"; cases "r=2"; cases "s=2";
      simp add: double_reverse_f_response_exact double_reverse_f_right_class_def double_reverse_f_row_def)
next
  assume "double_reverse_f_right_class r = double_reverse_f_right_class s"
  with assms show "\<forall>h<2. \<forall>x<10. double_reverse_f_port_digit h x r = double_reverse_f_port_digit h x s"
    by (simp add: double_reverse_f_response_exact)
qed

ML \<open>
  val checked = @{thms double_reverse_f_port_pair_exact double_reverse_f_response_exact
    double_reverse_f_row_minimal double_reverse_f_right_minimal};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Unchecked double-reverse F-port refinement";
\<close>

end
