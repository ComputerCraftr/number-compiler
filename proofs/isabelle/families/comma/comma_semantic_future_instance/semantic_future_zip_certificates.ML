(* Kernel-checked, pair-state zip replay.  The three stores certify independent
   immutable tables; a caller supplies a checked leaf-combine equality. *)
signature COMMA_SEMANTIC_FUTURE_ZIP_CERTIFICATES =
sig
  type store = Comma_CRT_MDD_Certificate_Store.store
  type replay
  val make: Proof.context -> store -> store -> store -> term ->
    (int -> int -> int -> thm) -> replay
  val certify: replay -> int -> int -> int -> thm
  val proof_count: replay -> int
end

structure Comma_Semantic_Future_Zip_Certificates:
  COMMA_SEMANTIC_FUTURE_ZIP_CERTIFICATES =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Triple_Table = Table
  (
    type key = int * (int * int)
    val ord = prod_ord int_ord (prod_ord int_ord int_ord)
  )
  type store = Store.store
  val natT = @{typ nat}
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  val natListT = HOLogic.listT natT
  fun nat n = HOLogic.mk_number natT n
  fun proposition radices left right result combine l r z =
    HOLogic.mk_Trueprop
      (Const (@{const_name comma_crt_mdd_zip_certificate},
        natListT --> nodesT --> nodesT --> nodesT -->
        (natT --> natT --> natT) --> natT --> natT --> natT --> HOLogic.boolT) $
          radices $ left $ right $ result $ combine $ nat l $ nat r $ nat z)
  fun top (Store.Leaf _) = NONE | top (Store.Branch (axis,_)) = SOME axis
  fun child axis slot id (Store.Branch (other,children)) =
        if axis=other then List.nth (children,slot) else id
    | child _ _ id (Store.Leaf _) = id
  fun minimum [] = error "Zip split has no decision axis"
    | minimum (first::rest) = fold (fn value => fn current => Int.min (value,current)) rest first

  type replay = {certify_root: int -> int -> int -> thm,
    proof_count: unit -> int}

  fun make ctxt left right result combine leaf_equation =
    let
      fun check_store store =
        let
          val _ = if Context.subthy (Proof_Context.theory_of (Store.context store),
              Proof_Context.theory_of ctxt) then ()
            else error "Zip replay store belongs to an unrelated theory context"
          val _ = Utils.ensure_closed_context ctxt "Zip replay store wellformedness"
            (Store.wellformed store)
        in () end
      val _ = List.app check_store [left,right,result]
      val axes = Store.radices left
      val _ = if Store.radices right aconv axes andalso Store.radices result aconv axes
        then () else error "Zip replay store radices differ"
      val _ = if fastype_of combine = (natT --> natT --> natT) andalso Utils.closed combine
        then () else error "Zip replay needs a closed natural-payload operation"
      val widths = map (Utils.dest_nat "Zip radix" natT) (HOLogic.dest_list axes)
      val left_table = Store.table left
      val right_table = Store.table right
      val result_table = Store.table result
      fun require label tactic state =
        (case Seq.pull (tactic state) of
          NONE => error ("Future zip replay failed at " ^ label)
        | SOME (result,rest) => Seq.cons result rest)
      val memo = Unsynchronized.ref Triple_Table.empty
      fun exact x y w = proposition axes left_table right_table result_table combine x y w
      fun loop x y w =
        (case Triple_Table.lookup (!memo) (x,(y,w)) of
          SOME theorem => theorem
        | NONE =>
            let
              val xnode = Store.node left x
              val ynode = Store.node right y
              val wnode = Store.node result w
              val lookup_facts = [Store.lookup left x, Store.lookup right y,
                Store.lookup result w, Store.bound left x, Store.bound right y,
                Store.bound result w]
              val expected = exact x y w
              val theorem = (case (xnode,ynode,wnode) of
                (Store.Leaf a,Store.Leaf b,Store.Leaf c) =>
                  let
                    val equation = Utils.exact_prop ctxt "Future zip leaf combination"
                      (HOLogic.mk_Trueprop (HOLogic.mk_eq (Envir.beta_norm (combine $ nat a $ nat b),nat c)))
                      (leaf_equation a b c)
                    val node_type = @{typ "nat comma_crt_mdd_node"}
                    val leaf_constructor = Const (@{const_name Comma_CRT_MDD_Leaf},natT --> node_type)
                    val leaf_congruence = Thm.combination
                      (Thm.reflexive (Thm.cterm_of ctxt leaf_constructor))
                      (Thm.symmetric (equation RS @{thm eq_reflection}))
                    val result_leaf = Thm.transitive (Store.lookup result w) leaf_congruence
                      RS @{thm meta_eq_to_obj_eq}
                  in Utils.prove_exact ctxt "Future zip leaf" expected
                    (fn local_ctxt => require "leaf constructor" (resolve_tac local_ctxt
                      [@{thm comma_crt_mdd_zip_certificate.leaf}] 1) THEN
                      require "left bound" (resolve_tac local_ctxt [Store.bound left x] 1) THEN
                      require "right bound" (resolve_tac local_ctxt [Store.bound right y] 1) THEN
                      require "result bound" (resolve_tac local_ctxt [Store.bound result w] 1) THEN
                      require "left lookup" (resolve_tac local_ctxt [Store.lookup left x RS @{thm meta_eq_to_obj_eq}] 1) THEN
                      require "right lookup" (resolve_tac local_ctxt [Store.lookup right y RS @{thm meta_eq_to_obj_eq}] 1) THEN
                      require "result lookup" (resolve_tac local_ctxt [result_leaf] 1)) end
              | _ =>
                  let
                    val axis = minimum (map_filter top [xnode,ynode,wnode])
                    val _ = if axis >= 0 andalso axis < length widths then ()
                      else error "Zip replay found an invalid axis"
                    val width = List.nth (widths,axis)
                    val _ = if width > 0 then () else error "Zip replay axis is empty"
                    val slots = 0 upto (width-1)
                    val children = map (fn slot => loop
                      (child axis slot x xnode) (child axis slot y ynode)
                      (child axis slot w wnode)) slots
                    val intro = Drule.infer_instantiate ctxt
                      [(("axis",0),Thm.cterm_of ctxt (nat axis))]
                      @{thm comma_crt_mdd_zip_certificate.split}
                    val numeral_context = put_simpset HOL_basic_ss ctxt
                      |> Simplifier.add_simps @{thms One_nat_def}
                    val numeral_conversion = Simplifier.rewrite numeral_context
                    val id_conversion = Conv.arg_conv
                      (Conv.combination_conv
                        (Conv.combination_conv (Conv.arg_conv numeral_conversion) numeral_conversion)
                        numeral_conversion)
                    fun normalize_ids theorem = Thm.equal_elim
                      (id_conversion (Thm.cprop_of theorem)) theorem
                    val normalized_children = map normalize_ids children
                    fun normalize_lookup_index theorem =
                      let val change = Conv.arg_conv numeral_conversion (Thm.lhs_of theorem)
                      in Thm.transitive (Thm.symmetric change) theorem end
                    val lookup_aliases = map normalize_lookup_index
                      [Store.lookup left x, Store.lookup right y, Store.lookup result w]
                    val rules = lookup_facts @ lookup_aliases @ children @ normalized_children @
                      @{thms comma_crt_mdd_zip_child_def less_Suc_eq_0_disj
                        nth_Cons_0 nth_Cons_Suc nth_Cons' list.size
                        comma_crt_mdd_node.case}
                  in Utils.prove_exact ctxt "Future zip split" expected
                    (fn local_ctxt => require "split constructor" (resolve_tac local_ctxt [intro] 1) THEN
                      require "split left bound" (resolve_tac local_ctxt [Store.bound left x] 1) THEN
                      require "split right bound" (resolve_tac local_ctxt [Store.bound right y] 1) THEN
                      require "split result bound" (resolve_tac local_ctxt [Store.bound result w] 1) THEN
                      require "split slots" (auto_tac (Simplifier.add_simps rules local_ctxt))) end)
              val _ = memo := Triple_Table.update ((x,(y,w)),theorem) (!memo)
            in theorem end)
    in {certify_root=loop,proof_count=fn () => Triple_Table.size (!memo)} end

  fun certify ({certify_root,...}: replay) l r z = certify_root l r z
  fun proof_count ({proof_count,...}: replay) = proof_count ()
end
