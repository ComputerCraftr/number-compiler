(* Certify the distinct used-template catalogue, then transport its exact
   theorem to the named occurrence catalogue. No source chooses a fresh
   arithmetic proof after this boundary. *)
structure Comma_Semantic_B1_Used_Templates =
struct
  fun fold_exact_list_all ctxt pred elements facts =
    let
      val natT = @{typ nat}
      val list_all_function =
        @{term "list_all :: (nat => bool) => nat list => bool"} $ pred
      val predicate_ct = Thm.cterm_of ctxt list_all_function
      fun proposition_equation equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
      val _ = if length elements = length facts then ()
        else error "B1 used-template list fold has mismatched item facts"
      val nil_ids = HOLogic.mk_list natT []
      val nil_equation = Conv.rewr_conv
        (@{thm list_all_Nil_iff} RS @{thm eq_reflection})
        (Thm.apply predicate_ct (Thm.cterm_of ctxt nil_ids))
      val nil_fact = Thm.equal_elim
        (Thm.symmetric (proposition_equation nil_equation)) @{thm TrueI}
      fun add (element, head_fact) (tail_ids, tail_fact) =
        let
          val ids = HOLogic.cons_const natT $ element $ tail_ids
          val equation = Conv.rewr_conv
            (@{thm list_all_Cons_iff} RS @{thm eq_reflection})
            (Thm.apply predicate_ct (Thm.cterm_of ctxt ids))
          val fact = Thm.equal_elim
            (Thm.symmetric (proposition_equation equation))
            (@{thm conjI} OF [head_fact, tail_fact])
        in (ids, fact) end
      val pairs = ListPair.zip (elements, facts)
      val (ids, fact) = fold_rev add pairs (nil_ids, nil_fact)
      val expected = HOLogic.mk_Trueprop (list_all_function $ ids)
      val _ = if Thm.prop_of fact aconv expected andalso
          Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact) andalso
          null (Thm.tpairs_of fact) then ()
        else error "B1 used-template list fold changed its exact theorem"
    in (ids, fact) end

  fun check_fold ctxt =
    let
      val predicate = @{term "(\<le>) (0::nat)"}
      val ids = [@{term "0::nat"}, @{term "1::nat"}]
      fun prove element = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (predicate $ element))
        (fn _ => simp_tac ctxt 1)
      val (folded_ids, _) = fold_exact_list_all ctxt predicate ids (map prove ids)
      val _ = if folded_ids aconv HOLogic.mk_list @{typ nat} ids then ()
        else error "B1 used-template early list-fold fixture changed its result"
    in Comma_Proof_Profile.report "B1 used-template load-time fold fixture checked" end

  fun prove ctxt context prove_item predicate range =
    let
      fun stage name = Comma_Proof_Profile.report
        ("B1 used-template stage=" ^ name)
      val _ = stage "start"
      val expected_range =
        @{term "remdups (map fst comma_semantic_b1_crt_descriptors)"}
      val expected_predicate =
        @{term "comma_semantic_b1_crt_template_mass_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids"}
      val _ = if range aconv expected_range andalso
          predicate aconv expected_predicate then ()
        else error "B1 used-template proof has foreign catalogue authority"
      val extent = Simplifier.rewrite context
        (Thm.cterm_of ctxt @{term "length comma_semantic_b1_crt_descriptors"})
      val (_, bound) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of extent))
      val _ = if bound >= 0 andalso bound <= 1024 then ()
        else error "B1 used-template catalogue exceeds its admitted extent"
      val _ = stage "range-start"

      (* The descriptor rows carry large binding payloads.  Do not turn their
         projection into indexed lookups: nth conversion revisits every
         remaining payload for each CID.  Rewrite the exact owner definition
         once and fold map/fst over its certified list spine instead. *)
      val descriptor_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_descriptors_def")
      val descriptor_table = @{term comma_semantic_b1_crt_descriptors}
      val descriptor_definition =
        Comma_Selected_List_Conversion.validate_equation descriptor_table
          descriptor_definition
      val descriptor_listT = fastype_of descriptor_table
      val descriptorT = (case descriptor_listT of
        Type (@{type_name list}, [entryT]) => entryT
      | _ => error "B1 occurrence descriptors are not a list")
      val descriptor_rhs = Thm.rhs_of descriptor_definition
      val descriptor_entries = HOLogic.dest_list (Thm.term_of descriptor_rhs)
      val _ = if length descriptor_entries = bound then ()
        else error "B1 descriptor definition disagrees with its checked extent"
      val _ = stage "range-complete"
      val _ = stage "descriptors-complete"

      val natT = @{typ nat}
      val nat_listT = HOLogic.listT natT
      val fst_const = Const (@{const_name fst}, descriptorT --> natT)
      val map_const = Const (@{const_name map},
        (descriptorT --> natT) --> descriptor_listT --> nat_listT)
      val map_function = map_const $ fst_const
      val map_function_ct = Thm.cterm_of ctxt map_function
      val fst_ct = Thm.cterm_of ctxt fst_const
      val nat_cons_ct = Thm.cterm_of ctxt
        (Const (@{const_name Cons}, natT --> nat_listT --> nat_listT))
      val map_nil = @{thm list.map(1)} RS @{thm eq_reflection}
      val map_cons = @{thm list.map(2)} RS @{thm eq_reflection}
      val fst_pair = @{thm fst_conv} RS @{thm eq_reflection}

      fun project_list source =
        let
          val map_request = Thm.apply map_function_ct source
          fun fold_spine current remaining =
            let
              val source_term = Thm.term_of current
            in
              (case source_term of
                Const (name, _) =>
                  if name = @{const_name Nil} andalso remaining = 0 then
                    Conv.rewr_conv map_nil (Thm.apply map_function_ct current)
                  else error "B1 descriptor projection ended at a malformed list"
              | _ =>
                  if remaining <= 0 then
                    error "B1 descriptor projection exceeded its checked extent"
                  else
                    let
                      val (cons_head, tail) = Thm.dest_comb current
                      val (cons_ct, head) = Thm.dest_comb cons_head
                      val _ = (case Thm.term_of cons_ct of
                        Const (name, _) => if name = @{const_name Cons} then ()
                          else error "B1 descriptor projection found a non-cons spine"
                      | _ => error "B1 descriptor projection found a malformed spine")
                      val (descriptor_first, _) =
                        (case try HOLogic.dest_prod (Thm.term_of head) of
                          SOME pair => pair
                        | NONE => error "B1 descriptor row is not a literal pair")
                      val _ = (case try HOLogic.dest_number descriptor_first of
                        SOME (typ, value) => if typ = natT andalso value >= 0 then ()
                          else error "B1 descriptor has a non-natural template ID"
                      | NONE => error "B1 descriptor template ID is not a numeral")
                      val head_request = Thm.apply fst_ct head
                      val head_equation = Conv.rewr_conv fst_pair head_request
                      val _ = if Thm.term_of (Thm.rhs_of head_equation) aconv
                          descriptor_first then ()
                        else error "B1 descriptor projection changed its template ID"
                      val tail_equation = fold_spine tail (remaining - 1)
                      val map_equation = Conv.rewr_conv map_cons
                        (Thm.apply map_function_ct current)
                      val cons_head_equation = Thm.combination
                        (Thm.reflexive nat_cons_ct) head_equation
                      val target_cons_equation = Thm.combination
                        cons_head_equation tail_equation
                    in Thm.transitive map_equation target_cons_equation end)
            end
          val result = fold_spine source (length descriptor_entries)
          val _ = if Thm.term_of (Thm.lhs_of result) aconv
              Thm.term_of map_request then ()
            else error "B1 structural descriptor projection changed its request"
        in result end

      val descriptor_map_equation = Thm.combination
        (Thm.reflexive map_function_ct) descriptor_definition
      val projected_literal = project_list descriptor_rhs
      val mapped = Thm.transitive descriptor_map_equation projected_literal
      val map_request = map_function $ descriptor_table
      val mapped = Comma_Selected_List_Conversion.validate_equation
        map_request mapped
      val _ = stage "map-complete"

      val range_ct = Thm.cterm_of ctxt range
      val (remdups_ct, _) = Thm.dest_comb range_ct
      val remdups_map = Thm.combination (Thm.reflexive remdups_ct) mapped
      val range_equation = Comma_Selected_List_Conversion.validate_equation range
        remdups_map
      val literal_ids = Thm.term_of (Thm.rhs_of mapped)
      val entries = HOLogic.dest_list literal_ids
      fun numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = @{typ nat} andalso value >= 0
        | NONE => false)
      val _ = if length entries = bound andalso forall numeral entries then ()
        else error "B1 projected template IDs disagree with their checked extent"
      val unique_entries = distinct (op aconv) entries
      val _ = if length unique_entries <= bound then ()
        else error "B1 used-template catalogue exceeds its admitted extent"

      (* The remdups theorem transports the checked occurrence list to the
         published range.  Prove each distinct ID once, then reuse its exact
         theorem at each matching occurrence instead of proving a large set
         inclusion over the two closed lists. *)
      val list_all = Const (@{const_name list_all},
        @{typ "(nat => bool) => nat list => bool"}) $ predicate
      val remdups_all = Drule.infer_instantiate ctxt
        [( ("P", 0), Thm.cterm_of ctxt predicate),
         (("xs", 0), Thm.cterm_of ctxt literal_ids)]
        @{thm comma_semantic_b1_crt_list_all_remdups} RS @{thm eq_reflection}
      val remdups_all_prop = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) remdups_all
      val _ = stage "deduplicate-complete"

      fun check_item entry =
        let
          val request = predicate $ entry
          val head = prove_item request
          val _ = if Thm.prop_of head aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of head = 0 andalso null (Thm.hyps_of head) andalso
              null (Thm.tpairs_of head) then ()
            else error "B1 used-template item changed its exact theorem"
        in head end
      val _ = stage ("template-items-start distinct=" ^ Int.toString
        (length unique_entries) ^ " occurrences=" ^ Int.toString (length entries))
      fun check_items [] _ facts = rev facts
        | check_items (entry :: rest) index facts =
            let
              val item_started = Time.now ()
              val _ = stage ("template-item-start index=" ^ Int.toString index ^
                " cid=" ^ Int.toString (#2 (HOLogic.dest_number entry)))
              val fact = check_item entry
              val elapsed = Time.toMilliseconds (Time.- (Time.now (), item_started))
              val _ = stage ("template-item-done index=" ^ Int.toString index ^
                " cid=" ^ Int.toString (#2 (HOLogic.dest_number entry)) ^
                " elapsed_ms=" ^ LargeInt.toString elapsed)
            in check_items rest (index + 1) (fact :: facts) end
      val item_facts = check_items unique_entries 0 []
      val _ = stage "distinct-item-proofs-complete"
      val _ = if length unique_entries = length item_facts then ()
        else error "B1 used-template distinct cache has mismatched proof count"
      val item_pairs = ListPair.zip (unique_entries, item_facts)
      val item_facts_by_id = fold (fn (entry, fact) => fn table =>
        if Termtab.defined table entry then
          error "B1 used-template distinct cache contains a duplicate ID"
        else Termtab.update (entry, fact) table) item_pairs Termtab.empty
      val occurrence_fact_lookups = Unsynchronized.ref 0
      val occurrence_fact_hits = Unsynchronized.ref 0
      fun occurrence_item entry =
        let
          val _ = occurrence_fact_lookups := !occurrence_fact_lookups + 1
          val request = predicate $ entry
          val fact = (case Termtab.lookup item_facts_by_id entry of
            SOME checked => checked
          | NONE => error "B1 used-template occurrence has no distinct item proof")
          val _ = if Thm.prop_of fact aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact) andalso
              null (Thm.tpairs_of fact) then
            occurrence_fact_hits := !occurrence_fact_hits + 1
          else error "B1 used-template occurrence changed its cached item theorem"
        in fact end
      val occurrence_facts = map occurrence_item entries
      val (folded_occurrence_ids, literal_fact) =
        fold_exact_list_all ctxt predicate entries occurrence_facts
      val literal_request = HOLogic.mk_Trueprop (list_all $ literal_ids)
      val _ = if folded_occurrence_ids aconv literal_ids andalso
          Thm.prop_of literal_fact aconv literal_request andalso
          Thm.nprems_of literal_fact = 0 andalso null (Thm.hyps_of literal_fact)
          andalso null (Thm.tpairs_of literal_fact) then ()
        else error "B1 used-template occurrence fold changed its theorem"
      val _ = stage ("occurrence-list-transport-complete refs=" ^
        Int.toString (!occurrence_fact_lookups) ^ " hits=" ^
        Int.toString (!occurrence_fact_hits))
      val deduplicated_fact = Thm.equal_elim
        (Thm.symmetric remdups_all_prop) literal_fact
      val equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt list_all)) range_equation
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
      val result = Thm.equal_elim
        (Thm.symmetric proposition_equation) deduplicated_fact
      val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop (list_all $ range)
          andalso Thm.nprems_of result = 0 andalso null (Thm.hyps_of result)
          andalso null (Thm.tpairs_of result) then ()
        else error "B1 used-template publication changed its exact theorem"
      val _ = Comma_Proof_Profile.report
        ("B1 used-template publication distinct=" ^ Int.toString (length unique_entries) ^
          " occurrences=" ^ Int.toString bound)
    in result end
end

val _ = Comma_Semantic_B1_Used_Templates.check_fold @{context}
