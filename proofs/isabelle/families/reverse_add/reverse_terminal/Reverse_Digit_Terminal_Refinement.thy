theory Reverse_Digit_Terminal_Refinement
  imports Reverse_Residuals.Reverse_196_Publisher_Refinement
    Reverse_Residuals.Mirror_Pair_Step
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

lemma digit_terminal_blank_advance_idempotent:
  "digit_terminal_advance (digit_terminal_advance l 19) 19 =
    digit_terminal_advance l 19"
  by (cases l) (simp add: digit_terminal_advance_def)

lemma digit_terminal_blank_emit_after_first:
  "digit_terminal_emit (digit_terminal_advance l 19) 19 = 19"
  by (cases l) (simp add: digit_terminal_advance_def digit_terminal_emit_def)

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

text \<open>For a symmetric pair field, the terminal carry can be obtained from
the first non-neutral coefficient at the LSD boundary.  A coefficient 9
preserves the incoming carry; the first coefficient below 9 resets it to
False, and the first coefficient above 9 resets it to True.  If every
coefficient is 9, the incoming carry is preserved.\<close>

fun digit_terminal_first_reset_carry :: "bool \<Rightarrow> nat list \<Rightarrow> bool" where
  "digit_terminal_first_reset_carry c [] = c"
| "digit_terminal_first_reset_carry c (s # ss) =
    (if s=9 then digit_terminal_first_reset_carry c ss else 10 \<le> s)"

lemma digit_terminal_first_reset_reverse_carry:
  "digit_terminal_first_reset_carry c ss = carry_out c (rev ss)"
proof (induct ss arbitrary: c)
  case Nil
  then show ?case by (simp add: carry_out_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "s=9")
    case True
    have step: "carry_out c (rev (s # ss)) = carry_out c (rev ss)"
      using True by (simp add: carry_out_append carry_out_def domain_def)
    show ?thesis using Cons.hyps[of c] step True by simp
  next
    case non_neutral: False
    show ?thesis
    proof (cases "s<9")
      case below: True
      have reset: "carry_out c (rev (s # ss)) = False"
        using below by (simp add: carry_out_append carry_out_def domain_def)
      show ?thesis
        using reset below non_neutral
        by (simp add: digit_terminal_first_reset_carry.simps; arith)
    next
      case not_below: False
      have above: "9<s" using not_below non_neutral by arith
      have reset: "carry_out c (rev (s # ss)) = True"
        using above by (simp add: carry_out_append carry_out_def domain_def)
      show ?thesis
        using reset above non_neutral
        by (simp add: digit_terminal_first_reset_carry.simps; arith)
    qed
  qed
qed

theorem digit_terminal_symmetric_first_reset_carry:
  assumes symmetric: "rev ss = ss"
  shows "carry_out c ss = digit_terminal_first_reset_carry c ss"
  using digit_terminal_first_reset_reverse_carry[of c ss] symmetric by simp

lemma digit_terminal_first_reset_after_nines:
  assumes "d \<noteq> 9"
  shows "digit_terminal_first_reset_carry c (replicate k 9 @ d # tail) =
    (10 \<le> d)"
  using assms by (induct k) simp_all

theorem digit_terminal_symmetric_reset_witness:
  assumes symmetric: "rev ss = ss"
      and witness: "ss = replicate k 9 @ d # tail"
      and reset: "d \<noteq> 9"
  shows "carry_out c ss = (10 \<le> d)"
proof -
  have first:
    "digit_terminal_first_reset_carry c (replicate k 9 @ d # tail) =
      (10 \<le> d)"
    by (rule digit_terminal_first_reset_after_nines[OF reset])
  show ?thesis
    using digit_terminal_symmetric_first_reset_carry[OF symmetric]
      first witness by simp
qed

corollary digit_terminal_valid_pair_first_reset_carry:
  assumes "valid_pair ss"
  shows "carry_out c ss = digit_terminal_first_reset_carry c ss"
proof -
  have symmetric: "rev ss = ss" using assms by (simp add: valid_pair_def)
  show ?thesis
    by (rule digit_terminal_symmetric_first_reset_carry[OF symmetric])
qed

lemma digit_terminal_first_reset_all_nines:
  assumes all_neutral: "\<forall>s\<in>set ss. s=9"
  shows "digit_terminal_first_reset_carry c ss = c"
  using all_neutral by (induct ss) auto

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

corollary digit_terminal_after_pair_publisher_blank_exterior:
  assumes "valid_pair ss"
  shows "digit_terminal_normalize
      (reverse_two_port_publisher (ss @ replicate n 19)) = digits (step ss)"
  using digit_terminal_after_pair_publisher[OF assms]
    reverse_two_port_publisher_active_blank_exterior[of ss n]
  by simp

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

text \<open>The finite width observer retains F5 position and parity only.
  Its growth argument is supplied by an admitted occurrence; these equations
  do not construct that occurrence or recover its exact extent.\<close>

definition reverse_width_phase :: "nat \<Rightarrow> nat" where
  "reverse_width_phase w = w mod 10"

definition reverse_width_action :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reverse_width_action r p = (p + r) mod 10"

lemma reverse_width_phase_transport:
  "reverse_width_action r (reverse_width_phase w) = reverse_width_phase (w+r)"
  unfolding reverse_width_action_def reverse_width_phase_def
  by (simp add: mod_add_left_eq)

lemma reverse_width_action_compose:
  "reverse_width_action s (reverse_width_action r p) =
    reverse_width_action (r+s) p"
  unfolding reverse_width_action_def by (simp add: mod_add_left_eq add.assoc)

lemma reverse_width_action_residue:
  "reverse_width_action (r mod 10) p = reverse_width_action r p"
  unfolding reverse_width_action_def by (simp add: mod_add_right_eq)

lemma reverse_width_phase_coordinates:
  "(reverse_width_phase w mod 5, reverse_width_phase w mod 2) =
    (w mod 5, w mod 2)"
  unfolding reverse_width_phase_def by simp

lemma reverse_width_phase_faithful:
  assumes "p < 10" "q < 10" "p mod 5 = q mod 5" "p mod 2 = q mod 2"
  shows "p = (q::nat)"
proof -
  have p: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4 \<or>
    p=5 \<or> p=6 \<or> p=7 \<or> p=8 \<or> p=9" using assms(1) by arith
  have q: "q=0 \<or> q=1 \<or> q=2 \<or> q=3 \<or> q=4 \<or>
    q=5 \<or> q=6 \<or> q=7 \<or> q=8 \<or> q=9" using assms(2) by arith
  show ?thesis using p q assms(3,4) by (elim disjE; simp_all)
qed

lemma reverse_width_reflection:
  assumes "0 < w"
  shows "(reverse_width_phase w + g + 9) mod 10 = (w+g-1) mod 10"
proof -
  have shift: "w+g+9 = (w+g-1)+10" using assms by arith
  have reduce: "(w mod 10 + g + 9) mod 10 = (w+g+9) mod 10"
    by (metis mod_add_left_eq)
  have target: "(w+g+9) mod 10 = (w+g-1) mod 10"
    by (subst shift) simp
  show ?thesis unfolding reverse_width_phase_def by (rule trans[OF reduce target])
qed

lemma reverse_width_phase_not_exact_extent:
  "reverse_width_phase (w+10) = reverse_width_phase w \<and> w+10 \<noteq> w"
  unfolding reverse_width_phase_def by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms reverse_width_phase_transport reverse_width_action_compose
      reverse_width_action_residue reverse_width_phase_coordinates
      reverse_width_phase_faithful reverse_width_reflection
      reverse_width_phase_not_exact_extent
      digit_terminal_scan_admitted digit_terminal_refines_digits
      streamed_digits_fold streamed_digits_refines_terminal
      digit_terminal_after_pair_publisher digit_terminal_196_pair_output
      digit_terminal_after_pair_publisher_blank_exterior
      digit_terminal_after_raw_pair_scan digit_terminal_normalize_padding
      digit_terminal_blank_advance_idempotent
      digit_terminal_blank_emit_after_first
      digit_terminal_first_reset_reverse_carry
      digit_terminal_symmetric_first_reset_carry
      digit_terminal_first_reset_after_nines
      digit_terminal_symmetric_reset_witness
      digit_terminal_valid_pair_first_reset_carry
      digit_terminal_first_reset_all_nines})
    then () else error "Digit terminal refinement depends on an oracle";
\<close>

end
