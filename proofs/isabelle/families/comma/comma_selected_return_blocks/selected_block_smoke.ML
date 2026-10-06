(* Exercise the production proof builder on two exact adjacent N choices.
   These finite checks assert neither a loop nor infinite branch safety. *)
val _ =
  let
    val ctxt = @{context}
    val engine = Comma_Return_Check.make_engine ctxt
    val builder = Comma_Selected_Block_Builder.make (#arithmetic engine) (#certify engine)
    fun nat n = HOLogic.mk_number @{typ nat} n
    val root = @{term "(Comma_N,2,10)::comma_boundary_state"}
    fun one q =
      let
        val {valid,defined,macro,finite_outcome,phase,...} = #boundary engine q
        val (head,args) = Term.strip_comb finite_outcome
        val _ = if head = @{term Comma_Fork_At} then ()
          else error "Selected-block smoke source reached a landmine"
        val a = hd args
        val delta = snd (HOLogic.dest_number (nth args 1))
        fun child kind = HOLogic.mk_prod
          (kind,HOLogic.mk_prod (a,nat ((phase+delta) mod 924)))
        val target = child @{term Comma_N}
        val ordered = #prove engine (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (@{term comma_total_children} $ q,
           HOLogic.mk_list @{typ comma_boundary_state}
             [target,child @{term Comma_Z}]))) [macro]
        val target_valid = #prove engine
          (HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ target)) []
        val block = #leaf builder false valid defined macro ordered target_valid @{thm TrueI}
      in (target,delta,block) end
    val (middle,d1,left) = one root
    val (target,d2,right) = one middle
    val before = #boundary_work engine ()
    val joined = #join builder left right
    val observed = #observe builder joined
    val expected = HOLogic.mk_Trueprop (@{term comma_earliest_return_path} $
      HOLogic.mk_list @{typ bool} [@{term False},@{term False}] $
      nat 2 $ root $ target $ nat (d1+d2))
    val _ = if #boundary_work engine () = before then ()
      else error "Block joining rediscovered its source"
    val _ = if Thm.prop_of observed aconv expected then ()
      else error ("Selected block observation mismatch: " ^
        Thm.string_of_thm ctxt observed ^ " EXPECTED " ^
        Syntax.string_of_term ctxt expected)
    val rejected = ((#join builder left left; false)
      handle ERROR message => String.isPrefix "Open cached theorem" message)
    val _ = if rejected then () else error "Mismatched block sources were accepted"

    val traces = #boundary_traces engine ()
    val warm_ctxt = Context.proof_map
      (fold (Named_Theorems.add_thm @{named_theorems comma_completed_boundary_traces})
        traces) ctxt
    val warm = Comma_Return_Check.make_engine warm_ctxt
    val _ = #boundary warm root
    val _ = #boundary warm middle
    val _ = if #boundary_work warm () = (2,0,0) then ()
      else error "Imported boundary facts did not bypass cold round construction"
    fun reject_catalog theorem =
      let
        val bad_ctxt = Context.proof_map
          (Named_Theorems.add_thm @{named_theorems comma_completed_boundary_traces}
            theorem) ctxt
        val rejected = ((Comma_Return_Check.make_engine bad_ctxt; false)
          handle ERROR message => String.isPrefix "Imported comma boundary trace" message)
      in if rejected then () else error "Malformed boundary catalog was accepted" end
    val _ = reject_catalog @{thm TrueI}
    val _ = reject_catalog (Thm.trivial @{cprop True})
    val _ = if null (Thm_Deps.all_oracles [joined,observed]) then ()
      else error "Selected-block smoke used a theorem oracle"
  in
    Comma_Fast_Kernel.report
      "Selected-block smoke: adjacent join checked; mismatched join rejected; warm boundaries=2, cold rounds=0"
  end;
