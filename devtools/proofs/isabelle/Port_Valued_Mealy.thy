theory Port_Valued_Mealy
  imports Reverse_Residuals
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

section \<open>Natural three-port Collatz endpoint projection\<close>

definition collatz_three_port_row :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list" where
  "collatz_three_port_row endpoint = map endpoint [0, 1, 2]"

lemma collatz_three_port_composition:
  "collatz_three_port_row (right \<circ> left) =
    map right (collatz_three_port_row left)"
  by (simp add: collatz_three_port_row_def)

lemma collatz_three_port_closure:
  assumes left: "\<forall>port<3. left port < 3"
      and right: "\<forall>port<3. right port < 3"
      and port: "port < 3"
  shows "(right \<circ> left) port < 3"
  using left right port by auto

text \<open>These results are purely spatial.  In particular, equality of two
endpoint rows or even two full current emissions does not imply equality after
a reverse-and-add or Collatz successor.  Temporal successor congruence requires
a separate proof for the chosen full consumer response.\<close>

ML \<open>
  val checked = @{thms additive_shift_action.compose_mealy_associative
    additive_shift_action.identity_mealy_left
    additive_shift_action.identity_mealy_right
    additive_shift_action.endpoint_projection_homomorphism
    additive_shift_action.endpoint_application_homomorphism
    additive_shift_action.external_shift_commutes_with_composition
    additive_shift_action.endpoint_projection_ignores_emission
    monotone_bool_has_three_rows
    three_bool_rows_are_realized collatz_three_port_composition
    collatz_three_port_closure};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Port-valued Mealy proof depends on an oracle";
\<close>

end
