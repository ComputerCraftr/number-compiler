theory Comma_Branch_Instance
  imports Comma_Branch_Induction.Comma_Branch_Induction
    Comma_Return_Engine.Comma_Return_Engine
begin

text \<open>This instance certifies the complete finite losing subtree at the
zero-tail child of the first source-20 fork. Every macro outcome and both
children of every fork are obtained from the checked arithmetic constructor;
the local DFS is not a global forest or rank table. The resulting theorem is
uniform over all admitted exponents by the induction theorem imported above.\<close>

ML_file "branch_termination_check.ML"

local_setup \<open>fn lthy =>
  let
    val theorem = Comma_Branch_Termination_Check.check lthy
  in #2 (Local_Theory.note
    ((Binding.name "comma_zero_child_terminates", []), [theorem]) lthy) end\<close>

theorem comma_zero_child_has_no_infinite_literal_path:
  assumes "5\<le>p" "p mod 924=10"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value
    (Comma_Z,2,10) p \<and> (\<forall>j. comma_child (path j) (path (Suc j))))"
  by (rule comma_boundary_terminates_literal[OF comma_zero_child_terminates])
    (use assms in simp_all)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_zero_child_terminates comma_zero_child_has_no_infinite_literal_path})
    then () else error "Concrete first-sibling termination uses an oracle";
\<close>
end
