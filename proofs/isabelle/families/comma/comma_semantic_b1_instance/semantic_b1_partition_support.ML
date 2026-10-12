(* Shared bounded diagnostics for the B1 partition proof drivers. *)
structure Comma_Semantic_B1_Partition_Support =
struct
  structure Node_Head_Key = Table(type key = int * int
    val ord = prod_ord int_ord int_ord)

  fun shape depth term =
    let
      fun label current =
        (case Term.head_of current of
          Const (name, _) => Long_Name.base_name name
        | Free _ => "Free"
        | Var _ => "Var"
        | Bound _ => "Bound"
        | Abs _ => "Abs")
      val head = label term
      val (_, arguments) = strip_comb term
    in
      if depth = 0 orelse null arguments then head
      else head ^ "(" ^ String.concatWith ","
        (map (shape (depth - 1)) (take 4 arguments)) ^
        (if length arguments > 4 then ",..." else "") ^ ")"
    end

  fun profile_message make_message =
    if Comma_Proof_Profile.enabled () then
      Comma_Proof_Profile.report (make_message ()) else ()

  fun profile_stage name phase elapsed = profile_message (fn () =>
    "B1 partition stage=" ^ name ^ " phase=" ^ phase ^
    (case elapsed of NONE => "" | SOME ms => " elapsed_ms=" ^ LargeInt.toString ms))

  (* Exact, short-circuiting conversion for the partition's per-level node
     predicate.  Only each visited head is simplified, using that CID's exact
     column equation; the list recursion itself is certified structurally. *)
  fun make_node_presence_prover ctxt
      {column_value: int -> term, step: int -> thm,
       base_context: Proof.context} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val column_listT = HOLogic.listT columnT
      val boolT = @{typ bool}
      val has_node = Const
        (@{const_name comma_semantic_b1_crt_partition_has_node_at},
          natT --> column_listT --> boolT)
      val has_node_nil =
        @{thm comma_semantic_b1_crt_partition_has_node_at.simps(1)} RS
          @{thm eq_reflection}
      val has_node_cons =
        @{thm comma_semantic_b1_crt_partition_has_node_at.simps(2)} RS
          @{thm eq_reflection}
      val head_facts = Unsynchronized.ref
        (Node_Head_Key.empty: thm Node_Head_Key.table)
      val head_builds = Unsynchronized.ref 0
      val head_hits = Unsynchronized.ref 0
      val head_refusals = Unsynchronized.ref 0

      fun clean theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun number n = HOLogic.mk_number natT n
      fun check_equation label lhs rhs theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso clean theorem
        then theorem
        else error ("B1 partition " ^ label ^
          " theorem changed its exact equation or is not closed")
      fun boolean_rhs theorem =
        (case Thm.term_of (Thm.rhs_of theorem) of
          Const (name, _) =>
            if name = @{const_name True} then true
            else if name = @{const_name False} then false
            else error "B1 partition node head did not reduce to a Boolean"
        | _ => error "B1 partition node head did not reduce to a Boolean")
      fun node_head_fact level cid head_ct =
        let
          val head_term = Thm.term_of head_ct
        in
          (case Node_Head_Key.lookup (!head_facts) (level, cid) of
            SOME theorem =>
              let
                val _ = head_hits := !head_hits + 1
                val _ = if Thm.term_of (Thm.lhs_of theorem) aconv head_term andalso
                    clean theorem then () else error
                  "B1 cached node-head equation changed its exact request"
                val _ = ignore (boolean_rhs theorem)
              in theorem end
          | NONE =>
              let
                val theorem = Simplifier.rewrite
                  (base_context addsimps
                    (step cid :: @{thms comma_crt_column.case})) head_ct
                val rhs = Thm.term_of (Thm.rhs_of theorem)
                val _ = ignore (boolean_rhs theorem)
                val theorem = check_equation "node head" head_term rhs theorem
                val _ = head_builds := !head_builds + 1
                val _ = if Node_Head_Key.size (!head_facts) < 8192 then
                  head_facts := Node_Head_Key.update ((level, cid), theorem)
                    (!head_facts)
                  else head_refusals := !head_refusals + 1
              in theorem end)
        end

      fun prove level ids =
        let
          val request = has_node $ number level $
            HOLogic.mk_list columnT (map column_value ids)
          val request_ct = Thm.cterm_of ctxt request
          val (has_node_level_ct, source_ct) = Thm.dest_comb request_ct
          fun derive [] source =
                (case Thm.term_of source of
                  Const (name, _) => if name = @{const_name Nil} then
                    Conv.rewr_conv has_node_nil
                      (Thm.apply has_node_level_ct source)
                    else error "B1 node-presence source ended before its IDs"
                | _ => error "B1 node-presence source ended before its IDs")
            | derive (cid :: rest) source =
                let
                  val (cons_head_ct, tail_ct) = Thm.dest_comb source
                  val (cons_ct, column_ct) = Thm.dest_comb cons_head_ct
                  val _ = (case Thm.term_of cons_ct of
                    Const (name, _) => if name = @{const_name Cons} then ()
                      else error "B1 node-presence source is not a literal list"
                  | _ => error "B1 node-presence source has a malformed cons")
                  val _ = if Thm.term_of column_ct aconv column_value cid then ()
                    else error "B1 node-presence source changed CID order"
                  val unfolded = Conv.rewr_conv has_node_cons
                    (Thm.apply has_node_level_ct source)
                  val rhs_ct = Thm.rhs_of unfolded
                  val (disj_head_ct, _) = Thm.dest_comb rhs_ct
                  val (disj_ct, head_ct) = Thm.dest_comb disj_head_ct
                  val _ = (case Thm.term_of disj_ct of
                    Const (name, _) => if name = @{const_name HOL.disj} then ()
                      else error "B1 node-presence rule did not expose a disjunction"
                  | _ => error "B1 node-presence rule exposed a malformed disjunction")
                  val head_fact = node_head_fact level cid head_ct
                  val head_is_true = boolean_rhs head_fact
                  val head_reduced = Conv.fun_conv
                    (Conv.arg_conv (Conv.rewr_conv head_fact)) rhs_ct
                  val boolean_rule =
                    (if head_is_true then
                       @{lemma "(True \<or> P) = True" by simp}
                     else @{lemma "(False \<or> P) = P" by simp}) RS
                      @{thm eq_reflection}
                  val simplified = Conv.rewr_conv boolean_rule
                    (Thm.rhs_of head_reduced)
                  val after_head = Thm.transitive head_reduced simplified
                  val rhs = Thm.term_of (Thm.rhs_of after_head)
                  val with_head = Thm.transitive unfolded after_head
                in
                  if rhs aconv @{term True} then with_head
                  else
                    let
                      val expected_tail = Thm.term_of
                        (Thm.apply has_node_level_ct tail_ct)
                      val _ = if rhs aconv expected_tail then () else error
                        "B1 false node head did not reduce to its exact tail request"
                      val tail_fact = derive rest tail_ct
                    in Thm.transitive with_head tail_fact end
                end
          val theorem = derive ids source_ct
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val _ = if rhs aconv @{term True} orelse rhs aconv @{term False} then ()
            else error "B1 node-presence recursion did not finish with a Boolean"
        in check_equation "node presence" request rhs theorem end
      fun counts () = (!head_builds, !head_hits, !head_refusals)
      fun stats () =
        " partition_node_head_builds=" ^ Int.toString (!head_builds) ^
        " partition_node_head_hits=" ^ Int.toString (!head_hits) ^
        " partition_node_head_refusals=" ^ Int.toString (!head_refusals)
    in {prove = prove, counts = counts, stats = stats} end
end
