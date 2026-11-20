(* Authenticated point evaluation follows only the demanded frozen MDD path. *)
structure Comma_CRT_MDD_Point_Eval =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove store phase root =
    let
      val ctxt = Store.context store
      val _ = if phase >= 0 then () else error "MDD point phase must be nonnegative"
      val radices = map (Utils.dest_nat "MDD point radix" natT)
        (HOLogic.dest_list (Store.radices store))
      fun visit id seen =
        if member (op =) seen id then error "MDD point path contains a cycle"
        else (case Store.node store id of
          Store.Leaf value => (value,rev (id :: seen))
        | Store.Branch (axis,children) =>
            let
              val radix = List.nth (radices,axis)
                handle Subscript => error "MDD point axis is outside the radix vector"
              val _ = if radix > 0 then () else error "MDD point radix is zero"
              val child = List.nth (children,phase mod radix)
                handle Subscript => error "MDD point child is outside its branch"
            in visit child (id :: seen) end)
      val (payload,path) = visit root []
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
        Store.radices store $ Store.table store $ nat phase $ nat root
      val some = @{term "Some :: nat => nat option"} $ nat payload
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval,some))
      val facts = maps (fn id => [Store.lookup store id,Store.bound store id]) path
      val context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps (Store.wellformed store :: facts)
        |> Simplifier.add_simps @{thms comma_crt_mdd_eval_phase_def
             comma_crt_mdd_eval_def comma_crt_mdd_eval_raw.simps
             comma_crt_mdd_node.case prod.case fst_conv snd_conv
             nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons' list.size option.simps Let_def}
      val theorem = Goal.prove ctxt [] [] expected (fn _ => simp_tac context 1)
        |> Utils.exact_prop ctxt "Frozen MDD point evaluation" expected
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Frozen MDD point evaluation" [theorem]
    in {payload=payload,theorem=theorem} end
end
