theory Decimal_196_Terminal_Integration
  imports "Associated_Action_Core.Associated_Action_Pullback"
    "Temporal_Clock_Jumps.Decimal_Publisher_Constructor"
    "Reverse_Digit_Terminal.Reverse_Digit_Terminal_Refinement"
begin

text \<open>The decimal constructor publishes a residue digit together with
its carry domain.  On a pair of admitted decimal port digits, the domain
therefore reconstructs the coefficient consumed by the reverse-196 two-port
scan.  The blank value 19 remains outside the decimal constructor and follows
the existing scan's sink behavior.\<close>

definition decimal_published_coefficient :: "nat \<times> carry_domain \<Rightarrow> nat" where
  "decimal_published_coefficient p =
    fst p + (case snd p of Above \<Rightarrow> 10 | Equal \<Rightarrow> 0 | Below \<Rightarrow> 0)"

lemma decimal_domain_decodes_below_twenty:
  assumes "s < 20"
  shows "s mod 10 +
    (case domain s of Above \<Rightarrow> 10 | Equal \<Rightarrow> 0 | Below \<Rightarrow> 0) = s"
proof (cases "s < 10")
  case True
  then have remainder: "s mod 10 = s" by simp
  show ?thesis using True remainder
    by (cases "s < 9") (simp_all add: domain_def)
next
  case False
  then have lower: "10 \<le> s" by simp
  have difference: "s - 10 < 10" using assms by arith
  have decomposition: "s = 10 + (s-10)" using lower by arith
  have remainder: "s mod 10 = s-10"
    by (subst decomposition) (simp add: difference)
  show ?thesis using lower remainder by (simp add: domain_def)
qed

lemma decimal_published_coefficient_exact:
  assumes "x < 10" "y < 10"
  shows "decimal_published_coefficient (decimal_publisher x y) = x+y"
proof -
  have sum_bounded: "x+y < 20" using assms by arith
  show ?thesis
    unfolding decimal_publisher_exact_on_digits[OF assms]
      decimal_published_coefficient_def
    by (simp add: decimal_domain_decodes_below_twenty[OF sum_bounded])
qed

corollary decimal_open_published_coefficient_exact:
  "decimal_published_coefficient (decimal_open_publisher x y c1 c2) =
    decimal_port_digit x c1 + decimal_port_digit y c2"
  unfolding decimal_open_publisher_def
  by (rule decimal_published_coefficient_exact;
      rule decimal_port_digit_bounded)

definition reverse_decimal_emit ::
    "reverse_left_port \<Rightarrow> nat \<Rightarrow> reverse_right_port \<Rightarrow> nat" where
  "reverse_decimal_emit l s r =
    (case reverse_operands l s r of None \<Rightarrow> 19
     | Some (a,c,b,d) \<Rightarrow>
       decimal_published_coefficient (decimal_open_publisher a b c d))"

theorem reverse_decimal_emit_refines_two_port_emit:
  "reverse_decimal_emit l s r = reverse_emit l s r"
proof (cases "reverse_operands l s r")
  case None
  then show ?thesis
    by (simp add: reverse_decimal_emit_def reverse_emit_def)
next
  case (Some operands)
  then obtain a c b d where operands: "operands=(a,c,b,d)"
    by (cases operands) auto
  show ?thesis using Some operands decimal_open_published_coefficient_exact[of a b c d]
    by (simp add: reverse_decimal_emit_def reverse_emit_def
        decimal_port_digit_def decimal_nf_def)
qed

fun reverse_decimal_scan_from ::
    "reverse_left_port \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reverse_decimal_scan_from l [] = []"
| "reverse_decimal_scan_from l (s#ss) =
    reverse_decimal_emit l s (reverse_right_fold ss) #
      reverse_decimal_scan_from (reverse_left_advance l s) ss"

definition reverse_decimal_two_port_scan :: "nat list \<Rightarrow> nat list" where
  "reverse_decimal_two_port_scan ss =
    reverse_decimal_scan_from reverse_left_initial ss"

definition reverse_decimal_two_port_publisher :: "nat list \<Rightarrow> nat list" where
  "reverse_decimal_two_port_publisher ss =
    strip_blank_tail (reverse_decimal_two_port_scan (ss@[19]))"

lemma reverse_decimal_scan_from_refines_two_port_scan_from:
  "reverse_decimal_scan_from l ss = reverse_two_port_scan_from l ss"
  by (induct ss arbitrary: l)
    (simp_all add: reverse_decimal_emit_refines_two_port_emit)

theorem reverse_decimal_two_port_scan_refines_two_port_scan:
  "reverse_decimal_two_port_scan ss = reverse_two_port_scan ss"
  by (simp add: reverse_decimal_two_port_scan_def reverse_two_port_scan_def
      reverse_decimal_scan_from_refines_two_port_scan_from)

theorem reverse_decimal_two_port_publisher_refines_two_port_publisher:
  "reverse_decimal_two_port_publisher ss = reverse_two_port_publisher ss"
  by (simp add: reverse_decimal_two_port_publisher_def reverse_two_port_publisher_def
      reverse_decimal_two_port_scan_refines_two_port_scan)

theorem reverse_decimal_publisher_refines_valid_pair_step:
  assumes "valid_pair ss"
  shows "reverse_decimal_two_port_publisher ss = step ss"
  using reverse_decimal_two_port_publisher_refines_two_port_publisher
    reverse_two_port_publisher_refines_step[OF assms]
  by simp

theorem reverse_decimal_publisher_reaches_digit_terminal:
  assumes "valid_pair ss"
  shows "digit_terminal_normalize (reverse_decimal_two_port_publisher ss) =
    digits (step ss)"
  using reverse_decimal_two_port_publisher_refines_two_port_publisher
    digit_terminal_after_pair_publisher[OF assms]
  by simp

corollary reverse_196_decimal_publisher_terminal_chain:
  "reverse_decimal_two_port_publisher (run step n [7,18,7]) =
      reverse_two_port_publisher (run step n [7,18,7]) \<and>
    digit_terminal_normalize
      (reverse_decimal_two_port_publisher (run step n [7,18,7])) =
      digits (step (run step n [7,18,7]))"
  using reverse_decimal_two_port_publisher_refines_two_port_publisher
    reverse_decimal_publisher_reaches_digit_terminal
    all_196_pair_fields_valid
  by blast

corollary reverse_196_decimal_raw_scan_terminal_chain:
  "digit_terminal_normalize
      (reverse_decimal_two_port_scan (run step n [7,18,7] @ [19])) =
    digits (step (run step n [7,18,7]))"
  using reverse_decimal_two_port_scan_refines_two_port_scan
    digit_terminal_after_raw_pair_scan all_196_pair_fields_valid
  by simp

text \<open>The refinement above is a theorem about the checked Isabelle cell
map: @{const reverse_operands} supplies the two decimal endpoint digits,
@{const decimal_open_publisher} publishes their residue and carry domain, and
@{const decimal_published_coefficient} decodes exactly the coefficient consumed
by @{const reverse_two_port_scan}.  The final theorem then invokes the already
checked @{const digit_terminal_normalize} model.

It does not identify these list functions with the Python
\<open>ReverseFieldActionArena\<close>, its authenticated image scheduler, or
\<open>DigitNormalizeBlockEffect\<close>.  A production refinement still requires
a source theorem mapping an admitted scheduler leaf and its second-half image
to @{const reverse_operands}, followed by a terminal-effect refinement theorem.
Those source and scheduler obligations are deliberately not replaced by a new
abstract law here.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms decimal_published_coefficient_exact
      decimal_open_published_coefficient_exact
      reverse_decimal_emit_refines_two_port_emit
      reverse_decimal_scan_from_refines_two_port_scan_from
      reverse_decimal_two_port_scan_refines_two_port_scan
      reverse_decimal_two_port_publisher_refines_two_port_publisher
      reverse_decimal_publisher_refines_valid_pair_step
      reverse_decimal_publisher_reaches_digit_terminal
      reverse_196_decimal_publisher_terminal_chain
      reverse_196_decimal_raw_scan_terminal_chain}) then ()
    else error "Decimal 196 terminal integration depends on an oracle";
\<close>

end
