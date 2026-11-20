(* Typed indexed publication: partial chunks, foreign roots and rejected indices. *)
structure Comma_Balanced_Table_Fixture =
struct
  structure Table = Comma_CRT_Balanced_Table
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun rejects label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error (label ^ " was accepted"))

  fun run lthy =
    let
      val rows = map (fn n => nat (n*n+1)) (0 upto 128)
      val (numbers,lthy1) = Table.make "typed_table_numbers" natT rows lthy
      val pairT = HOLogic.mk_prodT (natT,natT)
      val pairs = map (fn n => HOLogic.mk_prod (nat n,nat (129-n))) (0 upto 128)
      val (paired,lthy2) = Table.make "typed_table_pairs" pairT pairs lthy1
      val (foreign,lthy3) = Table.make "typed_table_foreign" natT rows lthy2
      val ctxt = Local_Theory.target_of lthy3
      fun selected table elementT index =
        Const (@{const_name nth},HOLogic.listT elementT --> natT --> elementT) $
          table $ nat index
      fun checked table elementT index value theorem =
        Utils.exact_prop ctxt "Typed table indexed equation"
          (Logic.mk_equals (selected table elementT index,value)) theorem
      val _ = List.app (fn index =>
        let
          val first = checked (#table numbers) natT index (List.nth (rows,index))
            (#lookup numbers index)
          val second = #lookup numbers index
          val _ = if Thm.prop_of first aconv Thm.prop_of second then ()
            else error "Repeated table selection changed its exact equation"
          val _ = checked (#table paired) pairT index (List.nth (pairs,index))
            (#lookup paired index)
        in () end) [0,63,127,128]
      fun size table elementT theorem =
        Utils.exact_prop ctxt "Typed table extent"
          (HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const (@{const_name size},HOLogic.listT elementT --> natT) $ table,nat 129)))
          theorem
      val _ = size (#table numbers) natT (#size numbers)
      val _ = size (#table paired) pairT (#size paired)
      val selected_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_proc (#procedure numbers)
      fun computed root index =
        Const (@{const_name nth},HOLogic.listT natT --> natT --> natT) $ root $
          (Const (@{const_name Suc},natT --> natT) $ nat index)
      val computed_request = computed (#table numbers) 127
      val computed_fact = Simplifier.rewrite selected_context
        (Thm.cterm_of ctxt computed_request)
      val _ = Utils.exact_prop ctxt "Computed index stays in selected owner"
        (Logic.mk_equals (computed_request,List.nth (rows,128))) computed_fact
      val foreign_request = computed (#table foreign) 127
      val foreign_fact = Simplifier.rewrite selected_context
        (Thm.cterm_of ctxt foreign_request)
      val _ = Utils.exact_prop ctxt "Foreign root is not selected"
        (Logic.mk_equals (foreign_request,foreign_request)) foreign_fact
      val _ = rejects "Computed upper boundary" (fn () =>
        Simplifier.rewrite selected_context (Thm.cterm_of ctxt (computed (#table numbers) 128)))
      val free_index = Free ("conditional_table_index",natT)
      val free_request = Const (@{const_name nth},HOLogic.listT natT --> natT --> natT) $
        #table numbers $ free_index
      val local_equality = Thm.assume (Thm.cterm_of ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (free_index,nat 0))))
      val conditional_context = selected_context |> Simplifier.add_simp local_equality
      val _ = (case #select numbers conditional_context (Thm.cterm_of ctxt free_request) of
          NONE => ()
        | SOME _ => error "Owner selected an open index from a local assumption")
      val closed_index = Const (@{const_name size},HOLogic.listT natT --> natT) $ #table numbers
      val assumed_closed = Thm.assume (Thm.cterm_of ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (closed_index,nat 0))))
      val assumed_context = selected_context |> Simplifier.add_simp assumed_closed
      val assumed_request = Const (@{const_name nth},HOLogic.listT natT --> natT --> natT) $
        #table numbers $ closed_index
      val _ = rejects "Closed index justified by a local assumption" (fn () =>
        #select numbers assumed_context (Thm.cterm_of ctxt assumed_request))
      val _ = (case #select numbers ctxt (Thm.cterm_of ctxt foreign_request) of
          NONE => ()
        | SOME _ => error "Owner selected a foreign table")
      val _ = rejects "Foreign named table proof" (fn () =>
        checked (#table foreign) natT 128 (List.nth (rows,128)) (#lookup numbers 128))
      val _ = rejects "Negative table index" (fn () => #lookup numbers (~1))
      val _ = rejects "Table upper boundary" (fn () => #lookup numbers 129)
      val _ = rejects "Empty table" (fn () => Table.make "bad_empty" natT [] lthy3)
      val _ = rejects "Wrong row type" (fn () => Table.make "bad_type" pairT rows lthy3)
      val _ = rejects "Open row" (fn () =>
        Table.make "bad_open" natT [Free ("untrusted_row",natT)] lthy3)
    in lthy3 end
end
