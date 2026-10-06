theory Collatz_Three_Port_Projection
  imports Shared_Carry_Dynamics.Port_Valued_Mealy
begin

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
  val checked = @{thms collatz_three_port_composition collatz_three_port_closure};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz three-port projection depends on an oracle";
\<close>

end
