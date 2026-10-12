(* Stable indexed compression and checked selector-embedding transport. *)
structure Comma_Semantic_B1_Indexed_Labels =
struct
  structure Embedding_Key = Table(type key = int list val ord = list_ord int_ord)

  fun make ctxt {column_value: int -> term, step: int -> thm,
      node_count: int, cache_limit: int} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val column_listT = HOLogic.listT columnT
      val nat_listT = HOLogic.listT natT
      val boolT = @{typ bool}
      (* Arithmetic normalization is applied only to a constructor's child
         offset.  The recursive source and occurrence lists are untouched. *)
      val scalar_context = Comma_Entry_Arithmetic.numeral_context ctxt
      val mask_const = Const
        (@{const_name comma_semantic_b1_crt_indexed_mask},
          natT --> HOLogic.listT boolT --> column_listT --> nat_listT -->
            column_listT --> boolT)
      val indexed_embedding_const = Const
        (@{const_name comma_semantic_b1_crt_indexed_embedding},
          nat_listT --> column_listT --> column_listT --> boolT)
      val false_column = Const (@{const_name Comma_CRT_Bool}, boolT --> columnT) $
        @{term False}
      val embedding_cache = Unsynchronized.ref
        (Embedding_Key.empty: (term * int list * term * thm) Embedding_Key.table)
      val zero_false_cache = Unsynchronized.ref (NONE: thm option)
      val cache_hits = Unsynchronized.ref 0
      val cache_refusals = Unsynchronized.ref 0
      val compression_builds = Unsynchronized.ref 0
      val false_test_builds = Unsynchronized.ref 0
      val false_test_hits = Unsynchronized.ref 0
      val false_test_refusals = Unsynchronized.ref 0
      val raw_occurrences = Unsynchronized.ref 0
      val zero_occurrences = Unsynchronized.ref 0
      val mask_constructor_steps = Unsynchronized.ref 0
      val mask_drop_steps = Unsynchronized.ref 0
      val proof_ms = Unsynchronized.ref (0: LargeInt.int)

      fun number n = HOLogic.mk_number natT n
      fun literal_columns ids = HOLogic.mk_list columnT (map column_value ids)
      fun argument_at index conversion cterm =
        if index = 0 then Conv.arg_conv conversion cterm
        else Conv.fun_conv (argument_at (index - 1) conversion) cterm
      fun measured elapsed work =
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val duration = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = elapsed := LargeInt.+ (!elapsed, duration)
        in Exn.release result end
      fun closed theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun check_theorem label proposition theorem =
        if Thm.prop_of theorem aconv proposition andalso closed theorem then theorem
        else error ("B1 indexed labels " ^ label ^
          " theorem changed authority or is not kernel-closed")
      fun check_equation label lhs rhs theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso closed theorem
        then theorem
        else error ("B1 indexed labels " ^ label ^ " equation changed")
      fun mask_proposition offset flags columns positions compact =
        HOLogic.mk_Trueprop (mask_const $ number offset $ flags $ columns $
          positions $ compact)
      fun list_cons label expected cterm =
        let
          val (head_function, tail_ct) = Thm.dest_comb cterm
          val (constructor, head_ct) = Thm.dest_comb head_function
          val constructor_term = Thm.term_of constructor
          val head = Thm.term_of head_ct
          val _ = (case constructor_term of
            Const (name, _) => if name = @{const_name Cons} then ()
              else error ("B1 indexed mask expected a cons " ^ label ^ " list")
          | _ => error ("B1 indexed mask expected a cons " ^ label ^ " list"))
          val _ = if head aconv expected then ()
            else error ("B1 indexed mask changed its " ^ label ^ " head")
        in (head_ct, tail_ct) end
      fun require_nil label cterm =
        (case Thm.term_of cterm of
          Const (name, _) => if name = @{const_name Nil} then ()
            else error ("B1 indexed mask ended its " ^ label ^ " list early")
        | _ => error ("B1 indexed mask has a nonempty " ^ label ^ " suffix"))
      fun zero_false_equation () =
        (case !zero_false_cache of
          SOME theorem => (false_test_hits := !false_test_hits + 1; theorem)
        | NONE =>
            let
              val value = column_value 0
              val zero_step = step 0
              val _ = check_equation "CID-zero column" value false_column zero_step
              val theorem = zero_step RS @{thm meta_eq_to_obj_eq}
              val proposition = HOLogic.mk_Trueprop
                (HOLogic.mk_eq (value, false_column))
              val theorem = check_theorem "CID-zero false occurrence" proposition theorem
              val _ = false_test_builds := !false_test_builds + 1
              val _ = zero_false_cache := SOME theorem
            in theorem end)
      fun mask_rule offset flags columns positions compact column keep =
        let
          val instances =
            [(("offset", 0), Thm.cterm_of ctxt (number offset)),
             (("flags", 0), flags),
             (("columns", 0), columns),
             (("positions", 0), positions),
             (("compact", 0), compact),
             (("column", 0), column)]
          val theorem = Drule.infer_instantiate ctxt instances
            (if keep then @{thm comma_semantic_b1_crt_indexed_mask_keep}
             else @{thm comma_semantic_b1_crt_indexed_mask_drop})
          val child_offset = Simplifier.rewrite scalar_context
          val relation_offset = Conv.arg_conv
            (argument_at 4 child_offset)
          val offset_conv =
            if keep then argument_at 1 relation_offset
            else Conv.arg_conv (argument_at 1 relation_offset)
        in Conv.fconv_rule offset_conv theorem end
      fun check_tail_offset expected premises index =
        let
          val premise = nth premises index
          val proposition = HOLogic.dest_Trueprop premise
          val (head, args) = strip_comb proposition
          val _ = (case head of
            Const (name, _) => if name = @{const_name comma_semantic_b1_crt_indexed_mask}
              then () else error "B1 indexed mask child has another relation"
          | _ => error "B1 indexed mask child relation is malformed")
          val _ = if length args = 5 then ()
            else error "B1 indexed mask child relation has the wrong arity"
          val (typ, actual) = HOLogic.dest_number (hd args)
        in if typ = natT andalso actual = expected then ()
          else error "B1 indexed mask constructor changed its child offset" end
      fun derive_mask offset ids flags columns positions compact =
        (case ids of
            [] =>
              let
                val expected = mask_proposition offset (Thm.term_of flags)
                  (Thm.term_of columns) (Thm.term_of positions)
                  (Thm.term_of compact)
                val _ = require_nil "flag" flags
                val _ = require_nil "source" columns
                val _ = require_nil "position" positions
                val _ = require_nil "compact" compact
                val theorem = Drule.infer_instantiate ctxt
                  [(("offset", 0), Thm.cterm_of ctxt (number offset))]
                  @{thm comma_semantic_b1_crt_indexed_mask_nil}
              in check_theorem "empty occurrence mask" expected theorem end
          | cid :: rest =>
              let
                val keep = cid <> 0
                val (flag_head, flags_tail) = list_cons "flag"
                  (if keep then @{term True} else @{term False}) flags
                val (head, columns_tail) = list_cons "source"
                  (column_value cid) columns
                val (positions_tail, compact_tail) =
                  if keep then
                    (#2 (list_cons "position" (number offset) positions),
                     #2 (list_cons "compact" (Thm.term_of head) compact))
                  else (positions, compact)
                val tail = derive_mask (offset + 1) rest flags_tail
                  columns_tail positions_tail compact_tail
                val rule = mask_rule offset flags_tail columns_tail
                  positions_tail compact_tail head keep
                val _ = mask_constructor_steps := !mask_constructor_steps + 1
                val _ = if keep then ()
                  else mask_drop_steps := !mask_drop_steps + 1
                val premises = Thm.prems_of rule
                val tail_index = if keep then 0 else 1
                val _ = if (if keep then Thm.term_of flag_head aconv @{term True}
                    else Thm.term_of flag_head aconv @{term False}) then ()
                  else error "B1 indexed mask changed its source keep flag"
                val _ = if length premises > tail_index then
                    check_tail_offset (offset + 1) premises tail_index
                  else error "B1 indexed mask constructor lost its child premise"
                val derived =
                  if keep then Thm.implies_elim rule tail
                  else
                    let
                      val equality_expected = HOLogic.mk_Trueprop
                        (HOLogic.mk_eq (Thm.term_of head, false_column))
                      val _ = if hd premises aconv equality_expected then ()
                        else error "B1 indexed mask dropped a non-false source head"
                      val with_false = Thm.implies_elim rule (zero_false_equation ())
                    in Thm.implies_elim with_false tail end
              in derived end)
      fun compression_embedding_uncached raw_ids =
        let
          val _ = if forall (fn cid => cid >= 0 andalso cid < node_count) raw_ids
              then () else error "B1 compression received a foreign CID"
          val indexed_occurrences =
            map_index (fn (position, cid) => (position, cid)) raw_ids
          val retained = filter (fn (_, cid) => cid <> 0) indexed_occurrences
          val positions = map (number o #1) retained
          val positions_term = HOLogic.mk_list natT positions
          val compact_ids = map #2 retained
          val flags = HOLogic.mk_list boolT
            (map (fn cid => if cid = 0 then @{term False} else @{term True}) raw_ids)
          val raw_columns = literal_columns raw_ids
          val compact_columns = literal_columns compact_ids
          val flags_ct = Thm.cterm_of ctxt flags
          val raw_columns_ct = Thm.cterm_of ctxt raw_columns
          val positions_ct = Thm.cterm_of ctxt positions_term
          val compact_columns_ct = Thm.cterm_of ctxt compact_columns
          val mask = derive_mask 0 raw_ids flags_ct raw_columns_ct positions_ct
            compact_columns_ct
          val mask_expected = mask_proposition 0 flags raw_columns positions_term
            compact_columns
          val mask = check_theorem "exact mask/positions/raw/compact" mask_expected mask
          val embedded = @{thm comma_semantic_b1_crt_indexed_mask_embedding}
            OF [mask]
          val expected = HOLogic.mk_Trueprop (indexed_embedding_const $
            positions_term $ compact_columns $ raw_columns)
          val embedded = check_theorem "exact compression embedding" expected embedded
          val _ = compression_builds := !compression_builds + 1
        in (positions_term, compact_ids, compact_columns, embedded) end
      fun compress raw_ids =
        let
          val _ = raw_occurrences := !raw_occurrences + length raw_ids
          val result =
            (case Embedding_Key.lookup (!embedding_cache) raw_ids of
              SOME embedding => (cache_hits := !cache_hits + 1; embedding)
            | NONE =>
                let
                  val embedding = measured proof_ms
                    (fn () => compression_embedding_uncached raw_ids)
                  val _ = if Embedding_Key.size (!embedding_cache) < cache_limit then
                      embedding_cache := Embedding_Key.update (raw_ids, embedding)
                        (!embedding_cache)
                    else cache_refusals := !cache_refusals + 1
                in embedding end)
          val (_, compact_ids, _, _) = result
          val _ = zero_occurrences := !zero_occurrences +
            (length raw_ids - length compact_ids)
        in result end
      fun proof_counts () = (!compression_builds, !false_test_builds,
        !false_test_hits, !false_test_refusals, !proof_ms)
      fun occurrence_counts () = (!raw_occurrences, !zero_occurrences)
      fun stats () =
        " labelled_zip_compression_proof_ms=" ^ LargeInt.toString (!proof_ms) ^
        " labelled_zip_embedding_cache_hits=" ^ Int.toString (!cache_hits) ^
        " labelled_zip_embedding_cache_refusals=" ^ Int.toString (!cache_refusals) ^
        " labelled_zip_raw_state_column_occurrences=" ^ Int.toString (!raw_occurrences) ^
        " labelled_zip_compressed_zero_occurrences=" ^ Int.toString (!zero_occurrences) ^
        " labelled_zip_compression_embeddings=" ^ Int.toString (!compression_builds) ^
        " labelled_zip_false_test_builds=" ^ Int.toString (!false_test_builds) ^
        " labelled_zip_false_test_hits=" ^ Int.toString (!false_test_hits) ^
        " labelled_zip_false_test_refusals=" ^ Int.toString (!false_test_refusals) ^
        " labelled_zip_mask_constructor_steps=" ^
          Int.toString (!mask_constructor_steps) ^
        " labelled_zip_mask_drop_steps=" ^ Int.toString (!mask_drop_steps)
    in {compress = compress, proof_counts = proof_counts,
        occurrence_counts = occurrence_counts, cache_hits = fn () => !cache_hits,
        stats = stats} end
end
