(* Exact structural transport for one phase shift of an issued zero-weight
   rank diagram.  The data arena computes the rotated child handles; Isabelle
   proves every shallow rotation and reuses child facts by owner identity. *)
structure Comma_Semantic_Phase_Class_Rank_Shift_Certificate =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Pair_Table = Table
  (
    type key = Data.identity * Data.identity
    val ord = prod_ord Data.identity_ord Data.identity_ord
  )

  val natT = @{typ nat}
  val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
  val shift = Const (@{const_name comma_weighted_crt_shift},
    natT --> rankT --> rankT)
  val one = HOLogic.mk_number natT 1

  fun make ctxt arena (named: Data.diagram -> Shallow.named_node) =
    let
      val proofs = Unsynchronized.ref (Pair_Table.empty: thm Pair_Table.table)
      val constructed = Unsynchronized.ref 0
      val scoped = Transport.make_scoped_checker ctxt "rank_shift"

      fun zero_view diagram =
        (case Data.view arena diagram of
          view as Data.View_Leaf {offset,...} =>
            if offset=0 then view
            else error "Rank shift certifier found a root offset"
        | view as Data.View_Branch {offset,children,...} =>
            if offset=0 andalso
                List.all (fn (weight,_) => weight=0) children then view
            else error "Rank shift certifier found a physical edge weight")

      fun prove source target child_equations =
        let
          val source_entry = named source
          val target_entry = named target
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (shift $ one $ #term source_entry,#term target_entry))
          val rules = [#definition source_entry,#definition target_entry] @
            child_equations @
            @{thms comma_weighted_crt_shift.simps rotate_Suc rotate0
              id_apply rotate1.simps list.map append_Nil append_Cons}
          val context = Transport.arithmetic_context ctxt
            |> Simplifier.del_simps @{thms One_nat_def[symmetric]}
            |> Simplifier.add_simps (Comma_Proof_Rewrite_Rules.nonreflexive_rules
              ([@{thm One_nat_def}] @ rules))
          val theorem = Goal.prove ctxt [] [] proposition
            (fn _ => HEADGOAL (simp_tac context))
        in #check scoped "Shallow rank phase shift" proposition theorem end

      fun certify source target =
        let
          val key = (Data.identity arena source,Data.identity arena target)
        in
          (case Pair_Table.lookup (!proofs) key of
            SOME theorem => theorem
          | NONE => Data.with_reservation arena (fn reservation =>
              let
                val _ = Data.reserve_external arena reservation
                val source_view = zero_view source
                val target_view = zero_view target
                val child_equations =
                  (case (source_view,target_view) of
                    (Data.View_Leaf {payload=left,...},
                     Data.View_Leaf {payload=right,...}) =>
                      if #value left aconv #value right then []
                      else error "Rank phase shift changed a leaf potential"
                  | (Data.View_Branch {axis=left_axis,children=left,...},
                     Data.View_Branch {axis=right_axis,children=right,...}) =>
                      let
                        val radix = Data.axis_radix left_axis
                        val _ = if left_axis=right_axis andalso
                            length left=radix andalso length right=radix then ()
                          else error "Rank phase shift changed its CRT schema"
                        fun selected slot =
                          let
                            val (_,source_child) =
                              List.nth (left,(slot+1) mod radix)
                            val (_,target_child) = List.nth (right,slot)
                            val _ = Data.reserve_external arena reservation
                          in certify source_child target_child end
                      in map selected (0 upto (radix-1)) end
                  | _ => error "Rank phase shift changed a leaf into a branch")
                val theorem = prove source target child_equations
                val _ = Data.retain_external arena reservation 1
                val _ = proofs := Pair_Table.update (key,theorem) (!proofs)
                val _ = constructed := !constructed+1
              in theorem end))
        end
    in {certify=certify,audit= #audit scoped,
      stats=fn () => {shift_proofs= !constructed,
        proof_audit= #stats scoped ()}} end
end
