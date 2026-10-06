theory Comma_Fast_Totality
  imports Comma_Fast_Rank_Check.Comma_Fast_Rank_Check
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
begin

text \<open>The release computation checks one actual decade successor and
one bound per admitted state. The old 27-round search is a separate regression;
it is not run here. Candidate ranks are definitions, never assumed facts.
All phase ranges share one evaluator and this session's unchanged time budget.\<close>

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Fast_Rank_Kernel.make lthy
    fun nat n = HOLogic.mk_number @{typ nat} n
    fun certify (lo, hi) = (lo, hi, Comma_Fast_Rank_Kernel.range lthy engine (lo, hi))
    fun join ((lo, mid, left), (mid', hi, right)) =
      if mid <> mid' then error "Nonadjacent fast rank ranges" else
      let
        val rule = Drule.infer_instantiate lthy
          [(("rank",0), @{cterm comma_decade_rank_candidate_on_valid}),
           (("bound",0), Thm.cterm_of lthy (nat 26)),
           (("lo",0), Thm.cterm_of lthy (nat lo)),
           (("mid",0), Thm.cterm_of lthy (nat mid)),
           (("hi",0), Thm.cterm_of lthy (nat hi))]
          @{thm comma_fast_decade_bounded_rank_range_join}
        val result = Simplifier.simplify
          (Comma_Entry_Arithmetic.natural_context lthy addsimps [left,right]) rule
      in (lo,hi,result) end
    fun reduce [item] = item
      | reduce items =
          let fun pairs (a::b::rest) = join (a,b) :: pairs rest
                | pairs rest = rest
          in reduce (pairs items) end
    val ranges = map (fn i => (i, i+1)) (0 upto 923)
    val (_, _, checked) = reduce (map certify ranges)
    val expected = @{prop "comma_fast_decade_bounded_rank_range
      comma_decade_rank_candidate_on_valid 26 0 924"}
    val _ = if Thm.prop_of checked aconv expected andalso
        Thm.nprems_of checked=0 andalso null (Thm.hyps_of checked) andalso
        null (Thm_Deps.all_oracles [checked]) then ()
      else error "Incomplete fast rank coverage"
  in #2 (Local_Theory.note
    ((Binding.name "comma_decade_bounded_rank_candidate_checked", []), [checked]) lthy) end\<close>

theorem comma_decade_rank_candidate_checked:
  "comma_decade_rank_check comma_decade_rank_candidate_on_valid"
  by (rule comma_fast_decade_bounded_rank_range_sound(1)
    [OF comma_decade_bounded_rank_candidate_checked])

theorem comma_decade_totality:
  assumes "comma_decade_admitted s"
  shows "\<exists>k\<le>27. comma_decade_finishes s k"
  using comma_fast_decade_bounded_rank_range_totality
    [OF comma_decade_bounded_rank_candidate_checked assms] by auto

theorem comma_boundary_macro_defined:
  assumes "comma_boundary_valid q"
  shows "comma_macro_defined q"
  by (rule comma_boundary_macro_exists_from_checked_rank
    [OF comma_decade_rank_candidate_checked assms])

corollary comma_total_macro_exists:
  assumes "comma_boundary_valid q"
  shows "\<exists>fuel. comma_finite_macro fuel q=Some (comma_total_macro q)"
  by (rule comma_total_macro_correct[OF comma_boundary_macro_defined[OF assms]])

corollary comma_total_weighted_macro_exists:
  assumes "comma_boundary_valid q" "5\<le>p" "p mod 924=snd (snd q)"
  shows "\<exists>fuel. comma_finite_weighted_macro fuel p q=
    Some (comma_total_weighted_macro p q)"
  by (rule comma_total_weighted_macro_correct[OF comma_macro_defined_weighted
    [OF comma_boundary_macro_defined[OF assms(1)] assms(2,3)]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_bounded_rank_candidate_checked comma_decade_rank_candidate_checked
      comma_decade_totality comma_boundary_macro_defined comma_total_macro_exists
      comma_total_weighted_macro_exists}) then ()
    else error "Concrete fast totality depends on an oracle";
\<close>
end
