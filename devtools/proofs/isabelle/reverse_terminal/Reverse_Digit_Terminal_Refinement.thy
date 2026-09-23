theory Reverse_Digit_Terminal_Refinement
  imports Reverse_Residuals.Reverse_196_Publisher_Refinement
begin

text \<open>The decimal specialization of DigitNormalizeBlockEffect.  These
definitions retain its carry, first-blank and sink states, including invalid
input behavior.  The theorem below identifies this terminal consumer with
digits; it does not assume or prove a powered-image construction algorithm.\<close>

record digit_terminal_port =
  dt_carry :: bool
  dt_blank_seen :: bool
  dt_sink :: bool

definition digit_terminal_active :: "bool \<Rightarrow> digit_terminal_port" where
  "digit_terminal_active c =
    \<lparr>dt_carry=c, dt_blank_seen=False, dt_sink=False\<rparr>"

definition digit_terminal_advance ::
  "digit_terminal_port \<Rightarrow> nat \<Rightarrow> digit_terminal_port" where
  "digit_terminal_advance l s =
    (if dt_sink l then l
     else if s=19 then
       \<lparr>dt_carry=False, dt_blank_seen=True, dt_sink=False\<rparr>
     else if dt_blank_seen l \<or> 18<s then
       \<lparr>dt_carry=False, dt_blank_seen=True, dt_sink=True\<rparr>
     else digit_terminal_active (10 \<le> s + (if dt_carry l then 1 else 0)))"

definition digit_terminal_emit :: "digit_terminal_port \<Rightarrow> nat \<Rightarrow> nat" where
  "digit_terminal_emit l s =
    (if dt_sink l \<or> dt_blank_seen l then 19
     else if s=19 then (if dt_carry l then 1 else 19)
     else if 18<s then 19
     else (s + (if dt_carry l then 1 else 0)) mod 10)"

fun digit_terminal_scan :: "digit_terminal_port \<Rightarrow> nat list \<Rightarrow> nat list" where
  "digit_terminal_scan l [] = []"
| "digit_terminal_scan l (s#ss) =
    digit_terminal_emit l s # digit_terminal_scan (digit_terminal_advance l s) ss"

lemma digit_terminal_scan_admitted:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "digit_terminal_scan (digit_terminal_active c) (ss@[19]) =
    emit c ss @ [if carry_out c ss then 1 else 19]"
  using assms
  by (induct ss arbitrary: c)
    (auto simp: digit_terminal_active_def digit_terminal_advance_def
      digit_terminal_emit_def carry_out_def carry_from_domain)

lemma digit_terminal_scan_blanks:
  assumes "dt_blank_seen l"
  shows "digit_terminal_scan l (replicate k 19) = replicate k 19"
  using assms
  by (induct k arbitrary: l)
    (auto simp: digit_terminal_emit_def digit_terminal_advance_def
      digit_terminal_active_def)

lemma digit_terminal_scan_padded:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "digit_terminal_scan (digit_terminal_active c) (ss @ 19 # replicate k 19) =
    emit c ss @ (if carry_out c ss then 1 else 19) # replicate k 19"
  using assms
  by (induct ss arbitrary: c)
    (auto simp: digit_terminal_active_def digit_terminal_advance_def
      digit_terminal_emit_def carry_out_def carry_from_domain digit_terminal_scan_blanks)

lemma strip_blank_tail_extra:
  "strip_blank_tail (xs@[19]) = strip_blank_tail xs"
  by (induct xs) simp_all

definition digit_terminal_normalize :: "nat list \<Rightarrow> nat list" where
  "digit_terminal_normalize ss = strip_blank_tail
    (digit_terminal_scan (digit_terminal_active False) (ss@[19]))"

theorem digit_terminal_refines_digits:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "digit_terminal_normalize ss = digits ss"
proof -
  have bounded: "\<forall>x\<in>set (emit False ss). x<19"
    using emit_bounded by fastforce
  have grown: "\<forall>x\<in>set (emit False ss @ [1]). x<19"
    using bounded by auto
  show ?thesis
    using digit_terminal_scan_admitted[OF assms, of False]
      strip_blank_tail_append_blank[OF bounded]
      strip_blank_tail_identity[OF grown]
    by (auto simp: digit_terminal_normalize_def digits_def)
qed

text \<open>The production D1/D2 full-output iterator keeps one physical carry
and emits a terminal one directly. Its pair input may be an iterator: the list
below specifies the values supplied by that iterator, not a retained midpoint
word. This theorem does not construct a temporal pair-field provider.\<close>

fun streamed_digits :: "bool \<Rightarrow> nat list \<Rightarrow> nat list" where
  "streamed_digits c [] = (if c then [1] else [])"
| "streamed_digits c (s#ss) =
    (s + (if c then 1 else 0)) mod 10 #
      streamed_digits (10 \<le> s + (if c then 1 else 0)) ss"

lemma streamed_digits_fold:
  "streamed_digits c ss = emit c ss @ (if carry_out c ss then [1] else [])"
  by (induct ss arbitrary: c)
    (simp_all add: carry_out_def carry_from_domain)

theorem streamed_digits_refines_terminal:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "streamed_digits False ss = digit_terminal_normalize ss"
  using streamed_digits_fold[of False ss] digit_terminal_refines_digits[OF assms]
  by (simp add: digits_def)

lemma digit_terminal_normalize_padding:
  assumes "\<forall>s\<in>set ss. s<19"
  shows "digit_terminal_normalize (ss@[19]) = digits ss"
  using digit_terminal_scan_padded[OF assms, of False 1]
    digit_terminal_scan_admitted[OF assms, of False]
    digit_terminal_refines_digits[OF assms]
    strip_blank_tail_extra[of "emit False ss @ [if carry_out False ss then 1 else 19]"]
  by (simp add: digit_terminal_normalize_def append_assoc)

corollary digit_terminal_after_pair_publisher:
  assumes "valid_pair ss"
  shows "digit_terminal_normalize (reverse_two_port_publisher ss) = digits (step ss)"
  using reverse_two_port_publisher_refines_step[OF assms]
    digit_terminal_refines_digits step_bounded
  by fastforce

corollary digit_terminal_196_pair_output:
  "digit_terminal_normalize (run step n [7,18,7]) = digits (run step n [7,18,7])"
proof (rule digit_terminal_refines_digits)
  show "\<forall>s\<in>set (run step n [7,18,7]). s<19"
    using all_196_pair_fields_valid[of n] by (auto simp: valid_pair_def)
qed

theorem digit_terminal_after_raw_pair_scan:
  assumes "valid_pair ss"
  shows "digit_terminal_normalize (reverse_two_port_scan (ss@[19])) = digits (step ss)"
proof (cases "carry_out False ss")
  case True
  have bounded: "\<forall>s\<in>set (step ss). s<19" using step_bounded by fastforce
  show ?thesis using reverse_two_port_scan_growth[OF assms True]
    digit_terminal_refines_digits[OF bounded] by simp
next
  case False
  have bounded: "\<forall>s\<in>set (step ss). s<19" using step_bounded by fastforce
  show ?thesis using reverse_two_port_scan_no_growth[OF assms False]
    digit_terminal_normalize_padding[OF bounded] by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms digit_terminal_scan_admitted digit_terminal_refines_digits
      streamed_digits_fold streamed_digits_refines_terminal
      digit_terminal_after_pair_publisher digit_terminal_196_pair_output
      digit_terminal_after_raw_pair_scan digit_terminal_normalize_padding})
    then () else error "Digit terminal refinement depends on an oracle";
\<close>

end
