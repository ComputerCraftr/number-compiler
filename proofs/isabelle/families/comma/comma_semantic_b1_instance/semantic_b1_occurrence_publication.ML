(* Publish the online CRT templates and occurrence descriptors as HOL data.
   Candidate construction is untrusted; the importing theory certifies the
   published values with the structural CRT checker. *)
structure Comma_Semantic_B1_Occurrence_Publication =
struct

  structure Candidate = Comma_Semantic_B1_Template_Constructor

  (* Keep executable constructor fixtures with the publication boundary; the
     candidate fold itself contains only production construction logic. *)
  fun check_candidate_examples () =
    let
      val even_one = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_True, Candidate.MDD_False, Candidate.MDD_False])
      val slot_two = Candidate.scope_column_key [(4, 2)]
      val shifted = Candidate.lift_template_slot 4 2 3 [even_one]
      val _ = if length shifted = 1 andalso
          Candidate.mdd_eval_phase (hd shifted) 2 andalso
          not (Candidate.mdd_eval_phase (hd shifted) 1) then ()
        else error "B1 occurrence lift has the wrong positive net-shift sign"
      val _ = if slot_two = hd shifted then ()
        else error "B1 slot lift did not intersect the shifted child geometry"
      val phase_one = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_True, Candidate.MDD_False, Candidate.MDD_False])
      val phase_two = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_False])
      val geometry = sort Candidate.compare_mdd [phase_one, phase_two]
      val first_binding = Candidate.binding_outputs geometry [phase_one, phase_two]
        [Candidate.Live 7, Candidate.Stop 3]
      val swapped_binding = Candidate.binding_outputs geometry [phase_two, phase_one]
        [Candidate.Live 7, Candidate.Stop 3]
      val full = Candidate.check_mdd_partition [(Candidate.Live 0, Candidate.MDD_True)]
      val half = Candidate.MDD_Node (0, [Candidate.MDD_True, Candidate.MDD_True,
        Candidate.MDD_False, Candidate.MDD_False])
      val other_half = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_True])
      val complementary = Candidate.check_mdd_partition
        [(Candidate.Live 0, half), (Candidate.Stop 1, other_half)]
      fun rejected expected columns =
        (case Exn.capture (fn () => Candidate.check_mdd_partition columns) () of
          Exn.Exn (ERROR message) => message = expected
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => false)
      val overlap = rejected "B1 symbolic source columns overlap"
        [(Candidate.Live 0, half), (Candidate.Stop 1, half)]
      val missing = rejected "B1 symbolic source table does not cover the clock"
        [(Candidate.Stop 0, Candidate.MDD_False)]
      val _ = if first_binding = [Candidate.Stop 3, Candidate.Live 7] andalso
          swapped_binding = [Candidate.Live 7, Candidate.Stop 3] andalso
          first_binding <> swapped_binding andalso full = [Candidate.MDD_True] andalso
          complementary = [half, other_half] andalso overlap andalso missing then ()
        else error "B1 compact geometry/binding or partition regression failed"
    in () end

  (* Serialize one template row as a closed HOL Let-DAG.  The candidate MDD
     already hash-conses nodes structurally; reuse that exact equality while
     binding each non-leaf node once.  The selected geometry checker unfolds
     only the row it consumes, so publication does not expand 10k column
     trees before a concrete row is selected. *)
  fun compress_template_row (keys: Candidate.mdd list) =
    let
      fun collect key (known, reverse_order) =
        (case key of
          Candidate.MDD_False => (known, reverse_order)
        | Candidate.MDD_True => (known, reverse_order)
        | Candidate.MDD_Node (_, children) =>
            if Candidate.MDDtab.defined known key then (known, reverse_order)
            else
              let
                val (with_children, child_order) =
                  fold collect children (known, reverse_order)
                val with_key = Candidate.MDDtab.update (key, ()) with_children
              in (with_key, key :: child_order) end)
      val (_, reverse_nodes) =
        fold collect keys (Candidate.MDDtab.empty, [])
      val nodes = rev reverse_nodes
      val node_indexes = fold_index (fn (index, key) =>
        Candidate.MDDtab.update (key, index))
        nodes Candidate.MDDtab.empty
      fun reference _ Candidate.MDD_False = @{term "Comma_CRT_Bool False"}
        | reference _ Candidate.MDD_True = @{term "Comma_CRT_Bool True"}
        | reference depth (key as Candidate.MDD_Node _) =
            (case Candidate.MDDtab.lookup node_indexes key of
              SOME index =>
                if index < depth then
                  Bound (depth - index - 1)
                else error "B1 compact template has a forward MDD reference"
            | NONE => error "B1 compact template omitted an MDD subnode")
      fun node_value depth (Candidate.MDD_Node (level, children)) =
            @{term Comma_CRT_Node} $ Candidate.nat level $
              HOLogic.mk_list Candidate.columnT
                (map (reference depth) children)
        | node_value _ _ = error "B1 compact template bound a Boolean leaf"
      val row_type = HOLogic.listT Candidate.columnT
      val let_term = Const (@{const_name Let},
        Candidate.columnT --> (Candidate.columnT --> row_type) --> row_type)
      fun bind (index, key) body =
        let_term $ node_value index key $ Abs ("", Candidate.columnT, body)
      val body = HOLogic.mk_list Candidate.columnT
        (map (reference (length nodes)) keys)
      val columns_term = fold bind (rev (map_index I nodes)) body
      val _ = if not (Term.is_open columns_term) andalso
          null (Term.add_frees columns_term []) andalso
          null (Term.add_vars columns_term []) then ()
        else error "B1 compact template is not closed"
      val row_metrics =
        if getenv "COMMA_PROFILE_LOG" = "" then NONE
        else
          let
            val expanded_weights = fold (fn key => fn weights =>
              (case key of
                Candidate.MDD_Node (level, children) =>
                  let
                    fun child_weight Candidate.MDD_False = 3
                      | child_weight Candidate.MDD_True = 3
                      | child_weight child =
                          (case Candidate.MDDtab.lookup weights child of
                            SOME weight => weight
                          | NONE => error "B1 compact MDD order is not bottom-up")
                    val child_nodes =
                      fold (fn child => fn total => total + child_weight child)
                        children 0
                    val weight = 4 + Term.size_of_term (Candidate.nat level) +
                      3 * length children + child_nodes
                  in Candidate.MDDtab.update (key, weight) weights end
              | Candidate.MDD_False => weights
              | Candidate.MDD_True => weights))
              nodes Candidate.MDDtab.empty
            fun expanded_size Candidate.MDD_False = 3
              | expanded_size Candidate.MDD_True = 3
              | expanded_size key =
                  (case Candidate.MDDtab.lookup expanded_weights key of
                    SOME weight => weight
                  | NONE => error "B1 compact MDD weight table is incomplete")
            val expanded_nodes = 1 + 3 * length keys +
              fold (fn key => fn total => total + expanded_size key) keys 0
          in
            SOME {expanded_nodes = expanded_nodes,
              unique_mdd_nodes = length nodes,
              compact_nodes = Term.size_of_term columns_term}
          end
    in
      {columns_term = columns_term, metrics = row_metrics}
    end

  fun compress_templates (templates: Candidate.mdd list list) =
    let
      val profile = getenv "COMMA_PROFILE_LOG" <> ""
      val rows = map compress_template_row templates
      val row_type = HOLogic.listT Candidate.columnT
      val term = HOLogic.mk_list row_type (map #columns_term rows)
      fun metric field =
        fold (fn row => fn total =>
          (case #metrics row of
            SOME values => total + field values
          | NONE => total)) rows 0
      val metrics = if not profile then NONE else
        SOME ("b1_template_expanded_row_term_nodes=" ^
          Int.toString (metric #expanded_nodes) ^
          " b1_template_unique_mdd_nodes=" ^
          Int.toString (metric #unique_mdd_nodes) ^
          " b1_template_compact_row_term_nodes=" ^
          Int.toString (metric #compact_nodes))
    in (term, metrics) end

  fun define_data name body lthy =
    let
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report ("B1 publication start=" ^ name)
      val ((_, (_, _)), next) = Local_Theory.define
        ((Binding.name name, NoSyn),
          ((Binding.name (name ^ "_def"), []), body)) lthy
      val _ = Comma_Proof_Profile.report
        ("B1 publication complete=" ^ name ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
    in next end

  fun serialize_lift_ref reference =
    let
      val natT = @{typ nat}
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
    in
      (case reference of
        Candidate.Terminal_Ref (slot, parent) =>
          Const (@{const_name Comma_B1_Lift_Terminal_Ref}, natT --> natT --> refT) $
            Candidate.nat slot $ Candidate.nat parent
      | Candidate.Goto_Ref (slot, child, lift_cid) =>
          Const (@{const_name Comma_B1_Lift_Goto_Ref},
            natT --> natT --> natT --> refT) $
            Candidate.nat slot $ Candidate.nat child $ Candidate.nat lift_cid)
    end

  fun serialize_lift_refs rows =
    let
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
    in
      HOLogic.mk_list (HOLogic.listT refT)
        (map (fn refs => HOLogic.mk_list refT (map serialize_lift_ref refs)) rows)
    end

  fun serialize_lift_descriptor
      ({period, slot, template_cid, net_shift}: Candidate.lift_descriptor) =
    let
      val natT = @{typ nat}
      val descriptorT = @{typ comma_semantic_b1_crt_lift_descriptor}
      val makeT = natT --> natT --> natT --> natT --> descriptorT
      val make = Const
        (@{const_name comma_semantic_b1_crt_lift_descriptor.make}, makeT)
    in
      make $ Candidate.nat period $ Candidate.nat slot $
        Candidate.nat template_cid $ Candidate.nat net_shift
    end

  fun serialize_lift_descriptors descriptors =
    HOLogic.mk_list @{typ comma_semantic_b1_crt_lift_descriptor}
      (map serialize_lift_descriptor descriptors)

  fun lift_publication_metrics artifact lift_term refs_term =
    #stats artifact () ^
    " b1_template_lift_descriptor_term_nodes=" ^
      Int.toString (Term.size_of_term lift_term) ^
    " b1_template_compact_ref_term_nodes=" ^
      Int.toString (Term.size_of_term refs_term)

  fun publish lthy =
    let
      val (artifact, generated_lthy) =
        Comma_Semantic_B1_Template_Constructor.make lthy
      val lift_descriptors_term =
        serialize_lift_descriptors (#lift_descriptors artifact)
      val lift_refs_term = serialize_lift_refs (#lift_refs artifact)
      val _ = if getenv "COMMA_PROFILE_LOG" = "" then ()
        else Comma_Proof_Profile.report
          ("B1 compact lift artifact " ^
            lift_publication_metrics artifact lift_descriptors_term lift_refs_term)
      val compression_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 publication stage=template-let-compression-start"
      val (template_columns_term, compression_metrics) =
        compress_templates (#template_keys artifact)
      val _ = (case compression_metrics of
          NONE => ()
        | SOME metrics => Comma_Proof_Profile.report
            ("B1 publication stage=template-let-compression-complete " ^
             metrics ^ " elapsed_ms=" ^
             Comma_Proof_Profile.elapsed_ms compression_started))
      val _ = Comma_Proof_Profile.report "B1 publication artifact ready"
      val next = generated_lthy
        |> define_data "comma_semantic_b1_crt_templates"
          template_columns_term
        |> define_data "comma_semantic_b1_crt_descriptors"
          (#occurrence_descriptors_term artifact)
        |> define_data "comma_semantic_b1_crt_sources"
          (#normalized_sources_term artifact)
        |> define_data "comma_semantic_b1_crt_root_occurrence_indices"
          (#root_occurrence_indices_term artifact)
        |> define_data "comma_semantic_b1_crt_lift_descriptors"
          lift_descriptors_term
        |> define_data "comma_semantic_b1_crt_lift_refs"
          lift_refs_term
    in next end

end
