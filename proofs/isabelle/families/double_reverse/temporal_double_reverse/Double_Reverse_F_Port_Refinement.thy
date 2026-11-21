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

end
