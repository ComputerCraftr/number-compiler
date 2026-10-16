theory Port_Valued_Mealy
  imports Main
begin

text \<open>A generic spatial Mealy action whose endpoint port and emission are
two views of one response.  The natural-number span acts on emissions through
an external additive clock shift.  This theory proves only spatial composition;
it does not assert closure under any arithmetic temporal successor.\<close>

record ('p, 'e) port_mealy =
  mealy_span :: nat
  mealy_endpoint :: "'p \<Rightarrow> 'p"
  mealy_emission :: "'p \<Rightarrow> 'e"

definition mealy_response :: "('p, 'e) port_mealy \<Rightarrow> 'p \<Rightarrow> 'p \<times> 'e" where
  "mealy_response action port =
    (mealy_endpoint action port, mealy_emission action port)"

definition endpoint_projection :: "('p, 'e) port_mealy \<Rightarrow> nat \<times> ('p \<Rightarrow> 'p)" where
  "endpoint_projection action = (mealy_span action, mealy_endpoint action)"

definition compose_endpoint ::
    "(nat \<times> ('p \<Rightarrow> 'p)) \<Rightarrow> (nat \<times> ('p \<Rightarrow> 'p)) \<Rightarrow>
      nat \<times> ('p \<Rightarrow> 'p)" where
  "compose_endpoint left right =
    (fst left + fst right, snd right \<circ> snd left)"

lemma carry_is_endpoint_view:
  "fst (mealy_response action port) = mealy_endpoint action port"
  by (simp add: mealy_response_def)

locale additive_shift_action =
  fixes shift :: "nat \<Rightarrow> 'e::monoid_add \<Rightarrow> 'e"
  assumes shift_zero [simp]: "shift 0 value = value"
      and shift_zero_value [simp]: "shift n 0 = 0"
      and shift_additive: "shift n (left + right) = shift n left + shift n right"
      and shift_compose: "shift (m + n) value = shift m (shift n value)"
begin

definition compose_mealy ::
    "('p, 'e) port_mealy \<Rightarrow> ('p, 'e) port_mealy \<Rightarrow>
      ('p, 'e) port_mealy" where
  "compose_mealy left right = \<lparr>
    mealy_span = mealy_span left + mealy_span right,
    mealy_endpoint = mealy_endpoint right \<circ> mealy_endpoint left,
    mealy_emission = (\<lambda>port.
      mealy_emission left port +
      shift (mealy_span left)
        (mealy_emission right (mealy_endpoint left port))) \<rparr>"

definition identity_mealy :: "('p, 'e) port_mealy" where
  "identity_mealy = \<lparr>
    mealy_span = 0,
    mealy_endpoint = id,
    mealy_emission = (\<lambda>_. 0) \<rparr>"

definition shift_mealy :: "nat \<Rightarrow> ('p, 'e) port_mealy \<Rightarrow> ('p, 'e) port_mealy" where
  "shift_mealy n action = action\<lparr>
    mealy_emission := shift n \<circ> mealy_emission action \<rparr>"

lemma shifted_actions_commute:
  "shift m (shift n value) = shift n (shift m value)"
proof -
  have "shift m (shift n value) = shift (m + n) value"
    using shift_compose by metis
  also have "... = shift (n + m) value" by (simp add: add.commute)
  also have "... = shift n (shift m value)"
    using shift_compose by metis
  finally show ?thesis .
qed

theorem compose_mealy_associative:
  "compose_mealy (compose_mealy first second) third =
    compose_mealy first (compose_mealy second third)"
  by (cases first; cases second; cases third)
    (simp add: compose_mealy_def fun_eq_iff add.assoc shift_additive
      shift_compose)

theorem identity_mealy_left [simp]:
  "compose_mealy identity_mealy action = action"
  by (cases action) (simp add: compose_mealy_def identity_mealy_def)

theorem identity_mealy_right [simp]:
  "compose_mealy action identity_mealy = action"
  by (cases action) (simp add: compose_mealy_def identity_mealy_def)

fun compose_mealy_power :: "nat \<Rightarrow> ('p, 'e) port_mealy \<Rightarrow>
    ('p, 'e) port_mealy" where
  "compose_mealy_power 0 action = identity_mealy"
| "compose_mealy_power (Suc n) action =
    compose_mealy (compose_mealy_power n action) action"

lemma compose_mealy_power_add:
  "compose_mealy_power (m+n) action =
    compose_mealy (compose_mealy_power m action)
      (compose_mealy_power n action)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have index: "m + Suc n = Suc (m+n)" by simp
  have reassociate:
    "compose_mealy
        (compose_mealy (compose_mealy_power m action)
          (compose_mealy_power n action)) action =
      compose_mealy (compose_mealy_power m action)
        (compose_mealy (compose_mealy_power n action) action)"
    by (rule compose_mealy_associative)
  show ?case
    by (simp only: index compose_mealy_power.simps Suc.IH)
      (simp only: reassociate compose_mealy_power.simps)
qed

corollary compose_mealy_power_square:
  "compose_mealy_power (n+n) action =
    compose_mealy (compose_mealy_power n action)
      (compose_mealy_power n action)"
  using compose_mealy_power_add[of n n action] by simp

theorem endpoint_projection_homomorphism:
  "endpoint_projection (compose_mealy left right) =
    compose_endpoint (endpoint_projection left) (endpoint_projection right)"
  by (simp add: endpoint_projection_def compose_endpoint_def compose_mealy_def)

theorem endpoint_application_homomorphism:
  "mealy_endpoint (compose_mealy left right) port =
    mealy_endpoint right (mealy_endpoint left port)"
  by (simp add: compose_mealy_def)

theorem external_shift_commutes_with_composition:
  "shift_mealy n (compose_mealy left right) =
    compose_mealy (shift_mealy n left) (shift_mealy n right)"
  by (cases left; cases right)
    (simp add: shift_mealy_def compose_mealy_def fun_eq_iff shift_additive
      shifted_actions_commute)

text \<open>Changing the emission view cannot change the endpoint/carry view.
The carry action therefore is a projection of the rich cylinder response, not
an additional peer field.\<close>

lemma endpoint_projection_ignores_emission:
  "endpoint_projection (action\<lparr>mealy_emission := emission\<rparr>) =
    endpoint_projection action"
  by (simp add: endpoint_projection_def)

end

text \<open>A partial count action has one exact finite-step count at each
admitted source, and explicit refusal elsewhere.  The count type is left
abstract so callers can use a product/vector monoid without duplicating the
partial-transition composition law.  This algebra does not authenticate an
input word or source; those remain obligations of a family publisher.\<close>

record ('s, 'c) partial_count_action =
  partial_count_steps :: nat
  partial_count_run :: "'s \<Rightarrow> ('s \<times> 'c) option"

definition partial_count_identity :: "'c \<Rightarrow> ('s, 'c) partial_count_action" where
  "partial_count_identity zero = \<lparr>
    partial_count_steps = 0,
    partial_count_run = (\<lambda>source. Some (source, zero)) \<rparr>"

definition partial_count_then :: "('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow>
    ('s, 'c) partial_count_action \<Rightarrow> ('s, 'c) partial_count_action \<Rightarrow>
      ('s, 'c) partial_count_action" where
  "partial_count_then add first after = \<lparr>
    partial_count_steps = partial_count_steps first + partial_count_steps after,
    partial_count_run = (\<lambda>source.
      case partial_count_run first source of None \<Rightarrow> None
      | Some (middle, first_count) \<Rightarrow>
          (case partial_count_run after middle of None \<Rightarrow> None
          | Some (target, after_count) \<Rightarrow>
              Some (target, add first_count after_count))) \<rparr>"

lemma partial_count_steps_then [simp]:
  "partial_count_steps (partial_count_then add first after) =
    partial_count_steps first + partial_count_steps after"
  by (simp add: partial_count_then_def)

lemma partial_count_run_then_admitted:
  assumes "partial_count_run first source = Some (middle, left_count)"
      and "partial_count_run after middle = Some (target, right_count)"
  shows "partial_count_run (partial_count_then add first after) source =
    Some (target, add left_count right_count)"
  using assms by (simp add: partial_count_then_def)

lemma partial_count_run_then_refuses_first:
  assumes "partial_count_run first source = None"
  shows "partial_count_run (partial_count_then add first after) source = None"
  using assms by (simp add: partial_count_then_def)

lemma partial_count_run_then_refuses_after:
  assumes "partial_count_run first source = Some (middle, count)"
      and "partial_count_run after middle = None"
  shows "partial_count_run (partial_count_then add first after) source = None"
  using assms by (simp add: partial_count_then_def)

theorem partial_count_then_associative:
  assumes add_assoc: "\<And>x y z. add (add x y) z = add x (add y z)"
  shows "partial_count_then add (partial_count_then add first second) third =
    partial_count_then add first (partial_count_then add second third)"
  using add_assoc
  by (cases first; cases second; cases third)
    (simp add: partial_count_then_def fun_eq_iff split: option.splits prod.splits)

theorem partial_count_identity_left:
  assumes left_zero: "\<And>x. add zero x = x"
  shows "partial_count_then add (partial_count_identity zero) action = action"
  using left_zero
  by (cases action) (simp add: partial_count_then_def partial_count_identity_def
      fun_eq_iff split: option.splits prod.splits)

theorem partial_count_identity_right:
  assumes right_zero: "\<And>x. add x zero = x"
  shows "partial_count_then add action (partial_count_identity zero) = action"
  using right_zero
  by (cases action) (simp add: partial_count_then_def partial_count_identity_def
      fun_eq_iff split: option.splits prod.splits)

theorem partial_count_then_chronological_counts:
  assumes first: "partial_count_run action source = Some (middle, left_count)"
      and after: "partial_count_run later middle = Some (target, right_count)"
  shows "partial_count_run (partial_count_then add action later) source =
      Some (target, add left_count right_count)"
    and "partial_count_steps (partial_count_then add action later) =
      partial_count_steps action + partial_count_steps later"
  using partial_count_run_then_admitted[OF first after]
  by (simp_all add: partial_count_then_def)

text \<open>A supplied finite word is interpreted by the chronological fold
below.  Its input letters are already-issued partial actions; an unsupported
letter therefore remains a refusal at the exact state where it is read.
This theorem concerns action composition and does not authorize a source
word that its family-specific issuer has not supplied.\<close>

fun partial_count_word :: "('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow>
    ('s, 'c) partial_count_action list \<Rightarrow> ('s, 'c) partial_count_action" where
  "partial_count_word add zero [] = partial_count_identity zero"
| "partial_count_word add zero (letter # rest) =
    partial_count_then add letter (partial_count_word add zero rest)"

theorem partial_count_word_append:
  assumes add_assoc: "\<And>x y z. add (add x y) z = add x (add y z)"
      and left_zero: "\<And>x. add zero x = x"
  shows "partial_count_word add zero (prefix @ suffix) =
    partial_count_then add (partial_count_word add zero prefix)
      (partial_count_word add zero suffix)"
proof (induction prefix)
  case Nil
  have identity:
    "partial_count_then add (partial_count_identity zero)
        (partial_count_word add zero suffix) = partial_count_word add zero suffix"
    by (rule partial_count_identity_left[where add = add and zero = zero
          and action = "partial_count_word add zero suffix", OF left_zero])
  show ?case
    using identity by simp
next
  case (Cons letter prefix)
  show ?case
    using Cons.IH
    by (simp add: partial_count_then_associative[OF add_assoc])
qed

theorem partial_count_word_append_admitted:
  assumes add_assoc: "\<And>x y z. add (add x y) z = add x (add y z)"
      and left_zero: "\<And>x. add zero x = x"
      and prefix: "partial_count_run (partial_count_word add zero prefix) source =
        Some (middle, prefix_count)"
      and suffix: "partial_count_run (partial_count_word add zero suffix) middle =
        Some (target, suffix_count)"
  shows "partial_count_run (partial_count_word add zero (prefix @ suffix)) source =
    Some (target, add prefix_count suffix_count)"
  using partial_count_word_append[OF add_assoc left_zero, of prefix suffix]
    partial_count_run_then_admitted[OF prefix suffix]
  by simp

theorem partial_count_word_append_refuses_prefix:
  assumes add_assoc: "\<And>x y z. add (add x y) z = add x (add y z)"
      and left_zero: "\<And>x. add zero x = x"
      and refused: "partial_count_run (partial_count_word add zero prefix) source = None"
  shows "partial_count_run (partial_count_word add zero (prefix @ suffix)) source = None"
  using partial_count_word_append[OF add_assoc left_zero, of prefix suffix]
    partial_count_run_then_refuses_first[OF refused]
  by simp

theorem partial_count_word_append_refuses_suffix:
  assumes add_assoc: "\<And>x y z. add (add x y) z = add x (add y z)"
      and left_zero: "\<And>x. add zero x = x"
      and prefix: "partial_count_run (partial_count_word add zero prefix) source =
        Some (middle, prefix_count)"
      and refused: "partial_count_run (partial_count_word add zero suffix) middle = None"
  shows "partial_count_run (partial_count_word add zero (prefix @ suffix)) source = None"
  using partial_count_word_append[OF add_assoc left_zero, of prefix suffix]
    partial_count_run_then_refuses_after[OF prefix refused]
  by simp

section \<open>Two Boolean ports and the three monotone endpoint rows\<close>

definition monotone_bool_endpoint :: "(bool \<Rightarrow> bool) \<Rightarrow> bool" where
  "monotone_bool_endpoint endpoint \<longleftrightarrow>
    (endpoint False \<longrightarrow> endpoint True)"

definition bool_endpoint_row :: "(bool \<Rightarrow> bool) \<Rightarrow> bool list" where
  "bool_endpoint_row endpoint = map endpoint [False, True]"

theorem monotone_bool_has_three_rows:
  assumes "monotone_bool_endpoint endpoint"
  shows "bool_endpoint_row endpoint = [False, False] \<or>
    bool_endpoint_row endpoint = [False, True] \<or>
    bool_endpoint_row endpoint = [True, True]"
  using assms
  by (cases "endpoint False"; cases "endpoint True")
    (simp_all add: monotone_bool_endpoint_def bool_endpoint_row_def)

lemma three_bool_rows_are_realized:
  "bool_endpoint_row (\<lambda>_. False) = [False, False]"
  "bool_endpoint_row id = [False, True]"
  "bool_endpoint_row (\<lambda>_. True) = [True, True]"
  by (simp_all add: bool_endpoint_row_def)

text \<open>These results are purely spatial.  In particular, equality of two
endpoint rows or even two full current emissions does not imply equality after
a recurrence-specific successor.  Temporal successor congruence requires a
separate proof for the chosen full consumer response.\<close>

ML \<open>
  val checked = @{thms additive_shift_action.compose_mealy_associative
    additive_shift_action.identity_mealy_left
    additive_shift_action.identity_mealy_right
    additive_shift_action.compose_mealy_power_add
    additive_shift_action.compose_mealy_power_square
    additive_shift_action.endpoint_projection_homomorphism
    additive_shift_action.endpoint_application_homomorphism
    additive_shift_action.external_shift_commutes_with_composition
    additive_shift_action.endpoint_projection_ignores_emission
    partial_count_steps_then partial_count_run_then_admitted
    partial_count_run_then_refuses_first partial_count_run_then_refuses_after
    partial_count_then_associative partial_count_identity_left
    partial_count_identity_right partial_count_then_chronological_counts
    partial_count_word_append partial_count_word_append_admitted
    partial_count_word_append_refuses_prefix partial_count_word_append_refuses_suffix
    monotone_bool_has_three_rows three_bool_rows_are_realized};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Port-valued Mealy proof depends on an oracle";
\<close>

end
