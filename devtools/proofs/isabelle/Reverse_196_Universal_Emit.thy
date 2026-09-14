theory Reverse_196_Universal_Emit
  imports Reverse_196_Two_Port_Refinement
begin

text \<open>The two branches below are the exact consumers selected by the
global carry computed by the right port.  They expose the no-growth mirror
pair and the growth adjacent-pair stencil without assuming a successor value.
The final lemmas account separately for the appended publication blank.\<close>

definition carry_bit :: "bool \<Rightarrow> nat" where
  "carry_bit c = (if c then 1 else 0)"

theorem reverse_emit_no_growth_cell:
  assumes prefix: "\<forall>x\<in>set xs. x<19"
      and suffix: "\<forall>x\<in>set ys. x<19"
      and cell: "s<19"
      and no_growth:
        "\<not> carry_out
          (carry_apply (domain s) (carry_out False xs)) ys"
  shows "reverse_emit (reverse_left_fold xs) s (reverse_right_fold ys) =
    mirror_pair_step s (carry_bit (carry_out False xs))
      (carry_bit (carry_out False (rev ys)))"
proof -
  have left_carry:
      "rp_carry (reverse_left_fold xs) = carry_out False xs"
    using reverse_left_fold_valid_prefix(1)[OF prefix] .
  have live: "\<not> rp_sink (reverse_left_fold xs)"
    using reverse_left_fold_valid_prefix(4)[OF prefix] .
  have forward:
      "carry_apply (rp_forward (reverse_right_fold ys))
        (carry_apply (domain s) (carry_out False xs)) =
       carry_out (carry_apply (domain s) (carry_out False xs)) ys"
    using reverse_right_fold_valid_carries(1)[OF suffix] .
  have backward:
      "carry_apply (rp_backward (reverse_right_fold ys)) False =
       carry_out False (rev ys)"
    using reverse_right_fold_valid_carries(2)[OF suffix] .
  have not_blank: "s \<noteq> 19" using cell by arith
  show ?thesis
    using left_carry live forward backward no_growth not_blank
    by (simp add: reverse_emit_def reverse_operands_def mirror_pair_step_def
        carry_bit_def Let_def)
qed

theorem reverse_emit_growth_interior:
  assumes prefix: "\<forall>x\<in>set xs. x<19"
      and suffix: "\<forall>x\<in>set ys. x<19"
      and cell: "s<19"
      and interior: "xs \<noteq> []"
      and growth:
        "carry_out (carry_apply (domain s) (carry_out False xs)) ys"
  shows "reverse_emit (reverse_left_fold xs) s (reverse_right_fold ys) =
    growth_pair_step s (last xs) (carry_bit (carry_out False xs))
      (carry_bit
        (carry_apply (domain s) (carry_out False (rev ys))))"
proof -
  have left_carry:
      "rp_carry (reverse_left_fold xs) = carry_out False xs"
    using reverse_left_fold_valid_prefix(1)[OF prefix] .
  have previous:
      "rp_previous (reverse_left_fold xs) = Some (last xs)"
    using reverse_left_fold_valid_prefix(2)[OF prefix] interior by simp
  have live: "\<not> rp_sink (reverse_left_fold xs)"
    using reverse_left_fold_valid_prefix(4)[OF prefix] .
  have forward:
      "carry_apply (rp_forward (reverse_right_fold ys))
        (carry_apply (domain s) (carry_out False xs)) =
       carry_out (carry_apply (domain s) (carry_out False xs)) ys"
    using reverse_right_fold_valid_carries(1)[OF suffix] .
  have backward:
      "carry_apply (rp_backward (reverse_right_fold ys)) False =
       carry_out False (rev ys)"
    using reverse_right_fold_valid_carries(2)[OF suffix] .
  have not_blank: "s \<noteq> 19" using cell by arith
  show ?thesis
    using left_carry previous live forward backward growth not_blank
    by (simp add: reverse_emit_def reverse_operands_def growth_pair_step_def
        carry_bit_def carry_then_apply Let_def)
qed

theorem reverse_emit_growth_first_cell:
  assumes suffix: "\<forall>x\<in>set ys. x<19"
      and cell: "s<19"
      and growth: "carry_out (carry_apply (domain s) False) ys"
  shows "reverse_emit reverse_left_initial s (reverse_right_fold ys) =
    growth_pair_step s 1 0 0"
proof -
  have forward:
      "carry_apply (rp_forward (reverse_right_fold ys))
        (carry_apply (domain s) False) =
       carry_out (carry_apply (domain s) False) ys"
    using reverse_right_fold_valid_carries(1)[OF suffix] .
  have not_blank: "s \<noteq> 19" using cell by arith
  show ?thesis using forward growth not_blank
    by (simp add: reverse_left_initial_def reverse_emit_def
        reverse_operands_def growth_pair_step_def Let_def)
qed

theorem reverse_emit_terminal_blank_no_growth:
  assumes valid: "\<forall>x\<in>set ss. x<19"
      and no_growth: "\<not> carry_out False ss"
  shows "reverse_emit (reverse_left_fold ss) 19 reverse_right_initial = 19"
proof -
  have carry:
      "rp_carry (reverse_left_fold ss) = carry_out False ss"
    using reverse_left_fold_valid_prefix(1)[OF valid] .
  have no_blank: "\<not> rp_blank_seen (reverse_left_fold ss)"
    using reverse_left_fold_valid_prefix(3)[OF valid] .
  have live: "\<not> rp_sink (reverse_left_fold ss)"
    using reverse_left_fold_valid_prefix(4)[OF valid] .
  show ?thesis using carry no_blank live no_growth
    by (simp add: reverse_emit_def reverse_operands_def)
qed

theorem reverse_emit_terminal_blank_growth:
  assumes valid: "\<forall>x\<in>set ss. x<19"
      and nonempty: "ss \<noteq> []"
      and growth: "carry_out False ss"
  shows "reverse_emit (reverse_left_fold ss) 19 reverse_right_initial =
    (last ss mod 10)+1"
proof -
  have carry: "rp_carry (reverse_left_fold ss) = carry_out False ss"
    using reverse_left_fold_valid_prefix(1)[OF valid] .
  have previous: "rp_previous (reverse_left_fold ss) = Some (last ss)"
    using reverse_left_fold_valid_prefix(2)[OF valid] nonempty by simp
  have no_blank: "\<not> rp_blank_seen (reverse_left_fold ss)"
    using reverse_left_fold_valid_prefix(3)[OF valid] .
  have live: "\<not> rp_sink (reverse_left_fold ss)"
    using reverse_left_fold_valid_prefix(4)[OF valid] .
  show ?thesis using carry previous no_blank live growth
    by (simp add: reverse_emit_def reverse_operands_def)
qed

text \<open>These lemmas discharge the local no-growth, growth-interior,
growth-edge and blank-publication cases for every admitted finite pair field.
A whole-list equality with @{term step} additionally needs the palindrome
admission invariant that identifies the pair at each reflected position.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms reverse_emit_no_growth_cell reverse_emit_growth_interior
      reverse_emit_growth_first_cell reverse_emit_terminal_blank_no_growth
      reverse_emit_terminal_blank_growth}) then ()
    else error "Reverse 196 universal emission proof depends on an oracle";
\<close>

end
