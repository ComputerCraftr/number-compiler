theory Comma_Branch_Period_Instance
  imports Comma_Selected_Return_Blocks.Comma_Selected_Return_Blocks
    Comma_Branch_Instance.Comma_Branch_Instance
    Comma_Return_Instance.Comma_Return_Instance
begin

text \<open>This concrete instance checks the complete 314-edge return and proves
termination for each of the 171 smaller N siblings at a selected Z choice.
The resulting theorem certifies this finite safe-choice return. The corollary
below establishes an infinite continuation from its initial value by unbounded
positive-weight repetition; it does not yet identify the produced literal path
with the recorded choice word or prove global lexicographic minimality.\<close>

ML_file "../comma_branch_period/branch_period_check.ML"

local_setup \<open>fn lthy =>
  let
    val (block,theorem) = Comma_Branch_Period_Check.check lthy
    val lthy = #2 (Local_Theory.note
      ((Binding.name "comma_nine_safe_block_checked", []), [block]) lthy)
  in #2 (Local_Theory.note
    ((Binding.name "comma_nine_safe_return_checked", []), [theorem]) lthy) end\<close>

theorem comma_nine_return_has_infinite_continuation:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=19999999999 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_earliest_return_path_has_infinite_continuation
      [OF comma_nine_safe_return_checked]) simp_all

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_nine_safe_block_checked comma_nine_safe_return_checked
      comma_nine_return_has_infinite_continuation})
    then () else error "The concrete comma branch-selection proof uses an oracle";
\<close>
end
