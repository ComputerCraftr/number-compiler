theory Comma_Run_Moore_Instance
  imports Comma_Run_Moore.Comma_Run_Moore
    Comma_Future_Structural_Instance.Comma_Future_Structural_Instance
begin

text \<open>
Concrete Moore-minimal source-20 run certificate.  The cyclic automaton is
anchored at the first maximal-run boundary after the physical source boundary,
(Comma_N,7,12).  It has 140 Moore states and emits 314 branch decisions per
cycle.  Every transition is checked through the certified decade summary and
future structural rank; no literal edge table and no rejected-sibling subtree
is reconstructed.
\<close>

ML_file "run_moore_check.ML"

local_setup \<open>fn lthy =>
  let
    val (entry,cycle) = Comma_Run_Moore_Instance_Check.check lthy
    val lthy = #2 (Local_Theory.note
      ((Binding.name "comma_nine_run_entry_expanded", []), [entry]) lthy)
  in #2 (Local_Theory.note
    ((Binding.name "comma_nine_run_safe_path_expanded", []), [cycle]) lthy) end\<close>

theorem comma_nine_run_entry_checked:
  "comma_safe_choice_path comma_rank_candidate_on_valid [False] 1
    (Comma_N,2,10) (Comma_N,7,12) 2"
  by (rule comma_nine_run_entry_expanded)

theorem comma_nine_run_safe_path_checked:
  "comma_safe_run_path comma_rank_candidate_on_valid comma_nine_run_cycle 314
    (Comma_N,7,12) (Comma_N,7,12) 924"
  using comma_nine_run_safe_path_expanded
  by (simp only: comma_nine_run_cycle_def)

theorem comma_nine_run_cycle_checked:
  "comma_surviving_delta_path comma_rank_candidate_on_valid 314
    (Comma_N,7,12) (Comma_N,7,12) 924"
  by (rule comma_safe_run_path_is_surviving_delta_path
    [OF comma_nine_run_safe_path_checked])

theorem comma_nine_run_cycle_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat.
    path 0=comma_boundary_value (Comma_N,7,12) 12 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_structural_descent_cycle_infinite_literal_path
      [OF comma_future_structural_candidate_descent comma_nine_run_cycle_checked])
    (simp_all add: comma_boundary_valid_def)

ML \<open>
  val checked = @{thms comma_nine_run_cycle_cyclic_moore_minimal
    comma_nine_run_entry_expanded comma_nine_run_entry_checked
    comma_nine_run_safe_path_expanded comma_nine_run_safe_path_checked
    comma_nine_run_cycle_checked comma_nine_run_cycle_infinite_literal_path}
  val _ = if null (Thm_Deps.all_oracles checked)
    then () else error "Concrete run-Moore certificate depends on an oracle";
  val _ = if List.all (fn th => Thm.nprems_of th=0 andalso null (Thm.hyps_of th)) checked
    then () else error "Concrete run-Moore certificate has hidden premises";
\<close>

end
