theory Collatz_Saturated_Threshold_Composition
  imports Associated_Action_Pullback
begin

text \<open>This is the finite, source-bound arithmetic of the executable
ThresholdEnvelope and SkewTransfer.  A line is a positive-slope inverse
threshold map.  The list is the unnormalized input to the hull constructor;
this theory does not infer an admitted source word or a hull-size bound.\<close>

fun option_max :: "rat option \<Rightarrow> rat option \<Rightarrow> rat option" where
  "option_max None y = y"
| "option_max (Some x) None = Some x"
| "option_max (Some x) (Some y) = Some (max x y)"

lemma option_max_assoc:
  "option_max (option_max x y) z = option_max x (option_max y z)"
  by (cases x; cases y; cases z; simp add: max.assoc)

lemma option_max_pull:
  fixes a b :: rat
  assumes "0 < a"
  shows "map_option (\<lambda>x. (x-b)/a) (option_max x y) =
    option_max (map_option (\<lambda>x. (x-b)/a) x)
      (map_option (\<lambda>x. (x-b)/a) y)"
  using assms by (cases x; cases y; simp add: inverse_affine_max)

definition line_value :: "(rat \<times> rat) \<Rightarrow> rat \<Rightarrow> rat" where
  "line_value line t = fst line * t + snd line"

fun envelope_value :: "(rat \<times> rat) list \<Rightarrow> rat \<Rightarrow> rat option" where
  "envelope_value [] t = None"
| "envelope_value (line # lines) t =
    option_max (Some (line_value line t)) (envelope_value lines t)"

lemma envelope_value_append:
  "envelope_value (xs @ ys) t =
    option_max (envelope_value xs t) (envelope_value ys t)"
  by (induct xs; simp add: option_max_assoc)

lemma envelope_value_empty_iff:
  "envelope_value lines t = None \<longleftrightarrow> lines = []"
proof (cases lines)
  case Nil
  then show ?thesis by simp
next
  case (Cons line rest)
  then show ?thesis by (cases "envelope_value rest t"; simp)
qed

lemma envelope_value_strict:
  "(\<exists>line\<in>set lines. x < line_value line t) \<longleftrightarrow>
    (case envelope_value lines t of None \<Rightarrow> False | Some bound \<Rightarrow> x < bound)"
  by (induct lines; auto split: option.splits simp: max_def)

lemma equal_slope_elimination:
  assumes "fst left = fst right" "snd left \<le> snd right"
  shows "option_max (Some (line_value left t)) (Some (line_value right t)) =
    Some (line_value right t)"
  using assms by (cases left; cases right;
    simp add: line_value_def max_def; linarith)

lemma middle_line_dominated:
  fixes a b c d e f t :: rat
  assumes ac: "a < c" and ce: "c < e"
    and crossing: "(d-f)/(e-c) \<le> (b-d)/(c-a)"
  shows "c*t+d \<le> max (a*t+b) (e*t+f)"
proof -
  let ?x = "(b-d)/(c-a)"
  let ?y = "(d-f)/(e-c)"
  have dx: "0 < c-a" using ac by simp
  have dy: "0 < e-c" using ce by simp
  have eqx: "(c-a)*?x = b-d" using dx by (simp add: field_simps)
  have eqy: "(e-c)*?y = d-f" using dy by (simp add: field_simps)
  show ?thesis
  proof (cases "t \<le> ?x")
    case True
    have "0 \<le> (c-a)*(?x-t)"
      using dx True by (intro mult_nonneg_nonneg) auto
    then have "(c-a)*t \<le> b-d"
      using eqx by (simp add: algebra_simps; linarith)
    then have "c*t+d \<le> a*t+b" by (simp add: algebra_simps)
    then show ?thesis by simp
  next
    case False
    have "?y \<le> t" using crossing False by simp
    then have "0 \<le> (e-c)*(t-?y)"
      using dy by (intro mult_nonneg_nonneg) auto
    then have "d-f \<le> (e-c)*t"
      using eqy by (simp add: algebra_simps; linarith)
    then have "c*t+d \<le> e*t+f" by (simp add: algebra_simps)
    then show ?thesis by simp
  qed
qed

definition line_pull :: "rat \<Rightarrow> rat \<Rightarrow> (rat \<times> rat) \<Rightarrow> (rat \<times> rat)" where
  "line_pull a b line = (fst line / a, (snd line - b) / a)"

lemma line_pull_value:
  fixes a b :: rat
  assumes "a \<noteq> 0"
  shows "line_value (line_pull a b line) t = (line_value line t - b) / a"
  using assms by (cases line; simp add: line_value_def line_pull_def
    diff_divide_distrib add_divide_distrib algebra_simps)

lemma envelope_value_pull:
  fixes a b :: rat
  assumes "0 < a"
  shows "envelope_value (map (line_pull a b) lines) t =
    map_option (\<lambda>x. (x-b)/a) (envelope_value lines t)"
  using assms
  by (induct lines; simp add: option_max_pull line_pull_value)

record saturated_threshold_action =
  endpoint_scale :: rat
  endpoint_offset :: rat
  threshold_lines :: "(rat \<times> rat) list"

definition saturated_admitted :: "saturated_threshold_action \<Rightarrow> bool" where
  "saturated_admitted A \<longleftrightarrow> 0 < endpoint_scale A"

definition saturated_endpoint :: "saturated_threshold_action \<Rightarrow> rat \<Rightarrow> rat" where
  "saturated_endpoint A x = endpoint_scale A * x + endpoint_offset A"

definition saturated_safety :: "saturated_threshold_action \<Rightarrow> rat \<Rightarrow> rat option" where
  "saturated_safety A t = envelope_value (threshold_lines A) t"

definition saturated_then ::
  "saturated_threshold_action \<Rightarrow> saturated_threshold_action \<Rightarrow>
    saturated_threshold_action" where
  "saturated_then A B =
    \<lparr>endpoint_scale = endpoint_scale B * endpoint_scale A,
     endpoint_offset = endpoint_scale B * endpoint_offset A + endpoint_offset B,
     threshold_lines = threshold_lines A @
       map (line_pull (endpoint_scale A) (endpoint_offset A))
         (threshold_lines B)\<rparr>"

lemma saturated_then_admitted:
  assumes "saturated_admitted A" "saturated_admitted B"
  shows "saturated_admitted (saturated_then A B)"
  using assms by (simp add: saturated_admitted_def saturated_then_def mult_pos_pos)

lemma saturated_endpoint_then:
  "saturated_endpoint (saturated_then A B) x =
    saturated_endpoint B (saturated_endpoint A x)"
  by (simp add: saturated_endpoint_def saturated_then_def algebra_simps)

theorem saturated_safety_then:
  assumes "saturated_admitted A"
  shows "saturated_safety (saturated_then A B) t =
    option_max (saturated_safety A t)
      (map_option (\<lambda>x. (x - endpoint_offset A) / endpoint_scale A)
        (saturated_safety B t))"
  using assms by (simp add: saturated_admitted_def saturated_safety_def
    saturated_then_def envelope_value_append envelope_value_pull)

lemma saturated_finite_descent:
  "(\<exists>line\<in>set (threshold_lines A). x < line_value line x) \<longleftrightarrow>
    (case saturated_safety A x of None \<Rightarrow> False | Some bound \<Rightarrow> x < bound)"
  by (simp add: saturated_safety_def envelope_value_strict)

text \<open>The retained threshold lines and endpoint are sufficient to evaluate
the finite consumer.  Any branch word used to discover them has been erased.
Equality here concerns the arithmetic observation, not source authority.\<close>

lemma saturated_observation_extensional:
  assumes "endpoint_scale A = endpoint_scale B"
    "endpoint_offset A = endpoint_offset B"
    "\<And>t. envelope_value (threshold_lines A) t =
      envelope_value (threshold_lines B) t"
  shows "saturated_endpoint A x = saturated_endpoint B x"
    "saturated_safety A t = saturated_safety B t"
  using assms by (simp_all add: saturated_endpoint_def saturated_safety_def)

text \<open>Given the supplied six-event high-fiber multiplication by 729,
the low six-bit deck is multiplication by 25.  This is a rechart law, not
a proof that a source follows those six events.\<close>

definition high_fiber_deck :: "nat \<Rightarrow> nat" where
  "high_fiber_deck d = (729 * d) mod 64"

lemma high_fiber_deck_25:
  "high_fiber_deck d = (25 * d) mod 64"
proof -
  have "(729*d) mod 64 = (((729::nat) mod 64)*d) mod 64"
    by (rule mod_mult_left_eq[symmetric])
  also have "... = (25*d) mod 64" by simp
  finally show ?thesis by (simp add: high_fiber_deck_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms envelope_value_append envelope_value_empty_iff
      envelope_value_strict equal_slope_elimination middle_line_dominated
      line_pull_value envelope_value_pull saturated_then_admitted
      saturated_endpoint_then saturated_safety_then saturated_finite_descent
      saturated_observation_extensional high_fiber_deck_25}) then ()
    else error "Saturated threshold composition depends on an oracle";
\<close>

end
