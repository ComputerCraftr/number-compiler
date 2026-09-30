theory Comma_Return_Instance
  imports Comma_Return_Engine.Comma_Return_Engine
begin

text \<open>The branch word is an untrusted witness, extracted from the old
candidate data. The checker proves its legal return directly from arithmetic;
no rank, forest, global-totality table or losing classification is imported.
This theorem establishes existence, not lexicographic branch uniqueness.\<close>

local_setup \<open>fn lthy =>
  let
    val (theorem,traces) = Comma_Return_Check.check lthy Comma_Return_Check.nine_choices
    val _ = Comma_Fast_Kernel.report "Return catalog: publishing checked traces"
    val _ = if length traces = 314 then ()
      else error "Return catalog did not retain all distinct boundary sources"
    val lthy = Local_Theory.declaration
      {syntax=false, pervasive=false, pos=\<^here>} (fn phi =>
        fold (Named_Theorems.add_thm @{named_theorems comma_completed_boundary_traces}
          o Morphism.thm phi) traces) lthy
    val _ = Comma_Fast_Kernel.report "Return catalog: traces published"
  in #2 (Local_Theory.note
    ((Binding.name "comma_nine_return_checked", []), [theorem]) lthy) end\<close>

theorem comma_nine_ray_returns:
  "\<exists>weight\<ge>k*314. comma_literal_path weight
    (comma_boundary_value (Comma_N,2,10) 10)
    (comma_boundary_value (Comma_N,2,10) (10+k*924))"
  by (rule comma_return_path_literal[OF
    comma_return_path_repeat[OF comma_nine_return_checked]]) simp_all

theorem comma_nine_ray_infinite:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=19999999999 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_nine_return_infinite[OF comma_nine_return_checked])

ML \<open>
  val _ = Comma_Fast_Kernel.report "Return instance: final oracle audit"
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_nine_return_checked comma_nine_ray_returns comma_nine_ray_infinite})
    then () else error "Concrete comma return depends on an oracle";
  val _ = Comma_Fast_Kernel.report "Return instance: oracle audit complete";
\<close>
end
