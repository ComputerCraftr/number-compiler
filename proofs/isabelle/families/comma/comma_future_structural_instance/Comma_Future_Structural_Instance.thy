theory Comma_Future_Structural_Instance
  imports Comma_Future_Structural_Check.Comma_Future_Structural_Check
    Comma_Decade_Summary_Checked.Comma_Decade_Summary_Checked
    Comma_Future_Rank_Data.Comma_Rank_Data
begin

text \<open>
Concrete forest-removal certificate.  Unlike the legacy future rank instance,
this checks only strict descent / unique-survivor structure against the already
certified one-step decade summary.  No 28-round boundary replay occurs here.
The numeric rank payload is only a well-founded measure.
\<close>

ML_file "../comma_entry_arithmetic/selected_list_conversion.ML"
ML_file "../comma_future_rank_data/rank_table_lookup.ML"
ML_file "future_structural_check.ML"

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Future_Structural_Instance_Check.make lthy
    fun nat n = HOLogic.mk_number @{typ nat} n
    fun certify r = (r,r+1,Comma_Future_Structural_Instance_Check.range lthy engine (r,r+1))
    fun join ((lo,mid,left),(mid',hi,right)) =
      if mid <> mid' then error "Nonadjacent future structural ranges" else
      let
        val rule = Drule.infer_instantiate lthy
          [(("height",0), @{cterm comma_decade_rank_candidate_on_valid}),
           (("terminal",0), @{cterm comma_decade_terminal_candidate_on_valid}),
           (("rank",0), @{cterm comma_rank_candidate_on_valid}),
           (("lo",0), Thm.cterm_of lthy (nat lo)),
           (("mid",0), Thm.cterm_of lthy (nat mid)),
           (("hi",0), Thm.cterm_of lthy (nat hi))]
          @{thm comma_future_descent_phase_range_join}
        val context = Comma_Entry_Arithmetic.natural_context lthy addsimps [left,right]
        val result = Simplifier.simplify context rule
      in (lo,hi,result) end
    fun reduce [item] = item
      | reduce items =
          let fun pairs (a::b::rest) = join(a,b) :: pairs rest
                | pairs rest = rest
          in reduce (pairs items) end
    val (_,_,checked_range) = reduce (map certify (0 upto 923))
    val full = Simplifier.simplify
      (Comma_Entry_Arithmetic.natural_context lthy addsimps [checked_range])
      @{thm comma_future_descent_phase_range_full}
    val expected = @{prop "comma_future_descent_check
      comma_decade_rank_candidate_on_valid comma_decade_terminal_candidate_on_valid comma_rank_candidate_on_valid"}
    val _ = if Thm.prop_of full aconv expected andalso Thm.nprems_of full=0
        andalso null (Thm.hyps_of full) andalso null (Thm_Deps.all_oracles [full])
      then () else error "Incomplete future structural coverage"
  in #2 (Local_Theory.note
    ((Binding.name "comma_future_structural_candidate_check", []), [full]) lthy) end\<close>

theorem comma_future_structural_candidate_checked:
  "comma_future_structural_witness comma_rank_candidate_on_valid"
  by (rule comma_future_descent_check_sound
    [OF comma_decade_summary_candidate_checked comma_future_structural_candidate_check])

corollary comma_future_structural_candidate_descent:
  "comma_descent_witness comma_total_children (set comma_boundary_states)
    comma_rank_candidate_on_valid"
  by (rule comma_future_structural_descent[OF comma_future_structural_candidate_checked])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_future_structural_candidate_check
      comma_future_structural_candidate_checked
      comma_future_structural_candidate_descent})
    then () else error "Concrete future structural certificate depends on an oracle";
\<close>

end
