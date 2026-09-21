theory Bilateral_Carry_Residual
  imports Bilateral_Cascade_Scan "Reverse_Residuals.Reverse_196_Two_Port_Refinement"
begin

text \<open>
  This theory binds the generic bilateral scan to the checked reverse/add
  left and right ports.  It proves finite append and projected carry-fold
  laws, plus a concrete rejection of reusing an unchanged right port at every
  cell.  It does not claim temporal normal-form closure or a powered
  construction bound. Physical decimal carry runs only from LSD to MSD.
  The right port is a summary of carry domains in the reflected coordinate
  chart, not a second physical carry stream. Both carry functions in that
  summary use the same forward physical carry law.
\<close>

definition reverse_bilateral_action ::
    "(nat, reverse_left_port, reverse_right_port) bilateral_action" where
  "reverse_bilateral_action =
    \<lparr>bilateral_left_initial = reverse_left_initial,
     bilateral_right_initial = reverse_right_initial,
     bilateral_left_step = reverse_left_advance,
     bilateral_right_step = reverse_right_advance,
     bilateral_emit = reverse_emit\<rparr>"

lemma reverse_right_fold_append:
  "bilateral_right_fold reverse_bilateral_action r (xs@ys) =
    bilateral_right_fold reverse_bilateral_action
      (bilateral_right_fold reverse_bilateral_action r ys) xs"
proof (induct xs arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by simp
qed

lemma reverse_left_fold_append:
  "bilateral_left_fold reverse_bilateral_action l (xs@ys) =
    bilateral_left_fold reverse_bilateral_action
      (bilateral_left_fold reverse_bilateral_action l xs) ys"
proof (induct xs arbitrary: l)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by simp
qed

theorem bilateral_emitted_word_append:
  "bilateral_emit_between reverse_bilateral_action l r (xs@ys) =
    bilateral_emit_between reverse_bilateral_action l
      (bilateral_right_fold reverse_bilateral_action r ys) xs @
    bilateral_emit_between reverse_bilateral_action
      (bilateral_left_fold reverse_bilateral_action l xs) r ys"
proof (induct xs arbitrary: l r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: reverse_right_fold_append)
qed

definition filtered_carry_fold :: "bool \<Rightarrow> nat list \<Rightarrow> bool" where
  "filtered_carry_fold c xs =
    carry_out c (filter (\<lambda>s. s \<noteq> 19) xs)"

theorem filtered_carry_fold_append:
  "filtered_carry_fold c (xs@ys) =
    filtered_carry_fold
      (filtered_carry_fold c xs) ys"
  by (simp add: filtered_carry_fold_def carry_out_def fold_append)

theorem bilateral_projected_carry_join:
  "filtered_carry_fold c
      (bilateral_emit_between reverse_bilateral_action l r (xs@ys)) =
    filtered_carry_fold
      (filtered_carry_fold c
        (bilateral_emit_between reverse_bilateral_action l
          (bilateral_right_fold reverse_bilateral_action r ys) xs))
      (bilateral_emit_between reverse_bilateral_action
        (bilateral_left_fold reverse_bilateral_action l xs) r ys)"
  using bilateral_emitted_word_append[of l r xs ys]
  by (simp add: filtered_carry_fold_append)

lemma reverse_bilateral_right_is_fold:
  "bilateral_right_fold reverse_bilateral_action reverse_right_initial ss =
    reverse_right_fold ss"
  by (induct ss; simp add: reverse_bilateral_action_def)

lemma reverse_bilateral_emit_between_is_scan:
  "bilateral_emit_between reverse_bilateral_action l
      reverse_right_initial ss =
    reverse_two_port_scan_from l ss"
  by (induct ss arbitrary: l;
      simp only: bilateral_emit_between.simps reverse_bilateral_right_is_fold
        reverse_two_port_scan_from.simps Let_def;
      simp add: reverse_bilateral_action_def)

lemma reverse_bilateral_run_is_two_port_scan:
  "bilateral_run reverse_bilateral_action ss =
    reverse_two_port_scan ss"
proof -
  have left: "bilateral_left_initial reverse_bilateral_action = reverse_left_initial"
    by (simp add: reverse_bilateral_action_def)
  have right: "bilateral_right_initial reverse_bilateral_action = reverse_right_initial"
    by (simp add: reverse_bilateral_action_def)
  show ?thesis
    by (simp only: bilateral_run_def reverse_two_port_scan_def left right
        reverse_bilateral_emit_between_is_scan)
qed

fun frozen_right_scan_from ::
    "reverse_left_port \<Rightarrow> nat list \<Rightarrow> nat list" where
  "frozen_right_scan_from l [] = []"
| "frozen_right_scan_from l (s#ss) =
    reverse_emit l s reverse_right_initial #
      frozen_right_scan_from (reverse_left_advance l s) ss"

definition frozen_right_scan :: "nat list \<Rightarrow> nat list" where
  "frozen_right_scan ss =
    frozen_right_scan_from reverse_left_initial ss"

lemma reflected_context_witness_correct:
  "reverse_two_port_scan [4,14,14,4,19] = [9,9,9,9,19]"
  by (simp add: reverse_two_port_scan_def reverse_left_initial_def
      reverse_two_port_scan_from.simps reverse_right_fold.simps
      reverse_right_initial_def reverse_right_advance_def
      reverse_left_advance_def reverse_operands_def reverse_emit_def
      carry_then_def domain_def carry_out_def Let_def)

lemma reflected_context_witness_frozen:
  "frozen_right_scan [4,14,14,4,19] = [8,9,10,9,19]"
  by (simp add: frozen_right_scan_def reverse_left_initial_def
      frozen_right_scan_from.simps reverse_left_advance_def
      reverse_operands_def reverse_emit_def reverse_right_initial_def
      carry_then_def domain_def Let_def)

lemma reflected_context_witness_carry:
  "filtered_carry_fold False [9,9,9,9,19] = False"
  "filtered_carry_fold False [8,9,10,9,19] = True"
  by (simp_all add: filtered_carry_fold_def carry_out_def domain_def)

text \<open>The following collision concerns only the unchanged original
primitive boundary at position zero. It is not a collision of the complete
source cylinder, nor an impossibility result for an enriched temporal type.
Both sources have the same local symbol and full original left/right ports,
and neither grows in either of the first two steps.\<close>

definition original_first_boundary where
  "original_first_boundary ss =
    (length ss, hd ss, reverse_left_initial, reverse_right_fold (tl ss),
      carry_out False ss, carry_out False (step ss))"

lemma unchanged_boundary_collision:
  "original_first_boundary [2,4,4,2] =
    original_first_boundary [2,5,5,2]"
  by (simp add: original_first_boundary_def reverse_right_initial_def
      reverse_right_advance_def carry_then_def domain_def
      step_def digits_def carry_out_def)

lemma two_step_first_carry_separates:
  "domain (hd (step (step [2,4,4,2]))) = Below"
  "domain (hd (step (step [2,5,5,2]))) = Equal"
  by (simp_all add: step_def digits_def carry_out_def domain_def)

theorem no_two_step_carry_on_unchanged_primitive_boundary:
  "\<not> (\<exists>f. \<forall>ss \<in> {[2,4,4,2], [2,5,5,2]}.
    f (original_first_boundary ss) = domain (hd (step (step ss))))"
  using unchanged_boundary_collision two_step_first_carry_separates
  by fastforce

ML \<open>
  val checked = @{thms reverse_right_fold_append reverse_left_fold_append
    bilateral_emitted_word_append filtered_carry_fold_append
    bilateral_projected_carry_join
    reverse_bilateral_right_is_fold reverse_bilateral_emit_between_is_scan
    reverse_bilateral_run_is_two_port_scan
    reflected_context_witness_correct reflected_context_witness_frozen
    reflected_context_witness_carry unchanged_boundary_collision
    two_step_first_carry_separates
    no_two_step_carry_on_unchanged_primitive_boundary};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Bilateral carry residual proof depends on an oracle";
\<close>

end
