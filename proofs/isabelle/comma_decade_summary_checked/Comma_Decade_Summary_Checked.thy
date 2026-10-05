theory Comma_Decade_Summary_Checked
  imports Comma_Decade_Summary_Kernel.Comma_Decade_Summary_Kernel
begin

text \<open>The release summary checks candidate labels for every admitted state, but evaluates
decade control once per offset-orbit representative and phase. The checked
control transport restores the exact original occurrence before publication.  It does not replay up to 27 rounds and it does not accept a generated
successor table.  The existing rank candidate is used here as exact crossing
height; the separate terminal candidate is propagated by the same checked local
recurrence.\<close>


local_setup \<open>fn lthy =>
  let
    val engine = Comma_Decade_Summary_Kernel.make lthy
    fun nat n = HOLogic.mk_number @{typ nat} n
    fun certify (lo,hi) = (lo,hi,Comma_Decade_Summary_Kernel.range lthy engine (lo,hi))
    fun join ((lo,mid,left),(mid',hi,right)) =
      if mid <> mid' then error "Nonadjacent decade summary ranges" else
      let
        val rule = Drule.infer_instantiate lthy
          [(("height",0), @{cterm comma_decade_rank_candidate_on_valid}),
           (("terminal",0), @{cterm comma_decade_terminal_candidate_on_valid}),
           (("lo",0), Thm.cterm_of lthy (nat lo)),
           (("mid",0), Thm.cterm_of lthy (nat mid)),
           (("hi",0), Thm.cterm_of lthy (nat hi))]
          @{thm comma_fast_decade_summary_range_join}
        val result = Simplifier.simplify
          (Comma_Entry_Arithmetic.natural_context lthy addsimps [left,right]) rule
      in (lo,hi,result) end
    fun reduce [item] = item
      | reduce items =
          let fun pairs (a::b::rest) = join(a,b) :: pairs rest
                | pairs rest = rest
          in reduce (pairs items) end
    val ranges = map (fn i => (i,i+1)) (0 upto 923)
    val (_,_,checked_range) = reduce (map certify ranges)
    val full = Simplifier.simplify
      (Comma_Entry_Arithmetic.natural_context lthy addsimps [checked_range])
      @{thm comma_fast_decade_summary_range_full}
    val expected = @{prop "comma_decade_summary_checked
      comma_decade_rank_candidate_on_valid comma_decade_terminal_candidate_on_valid"}
    val _ = if Thm.prop_of full aconv expected andalso Thm.nprems_of full=0
        andalso null (Thm.hyps_of full) andalso null (Thm_Deps.all_oracles [full])
      then () else error "Incomplete decade summary coverage"
  in #2 (Local_Theory.note
    ((Binding.name "comma_decade_summary_candidate_checked", []), [full]) lthy) end\<close>

corollary comma_decade_summary_candidate_exact:
  assumes "comma_decade_admitted s"
  shows "comma_decade_exact_summary s (comma_decade_rank_candidate_on_valid s)
    (comma_decade_terminal_candidate_on_valid s)"
  by (rule comma_decade_summary_checked_sound
    [OF comma_decade_summary_candidate_checked assms])

corollary comma_summary_boundary_candidate_correct:
  assumes "comma_boundary_valid q"
  shows "comma_fast_total_boundary comma_decade_rank_candidate_on_valid
    comma_decade_terminal_candidate_on_valid q = Some (comma_total_macro q)"
  by (rule comma_fast_total_boundary_correct
    [OF comma_decade_summary_candidate_checked assms])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_summary_candidate_checked comma_decade_summary_candidate_exact
      comma_summary_boundary_candidate_correct})
    then () else error "Concrete decade summary depends on an oracle";
\<close>

end
