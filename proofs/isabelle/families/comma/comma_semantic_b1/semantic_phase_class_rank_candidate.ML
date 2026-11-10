(* Candidate only: the resulting roots have no authority until the shallow
   HOL node equations, exact source-action equation, and final joint rank
   checker have all been kernel-certified.  No phase grid is enumerated. *)
structure Comma_Semantic_Phase_Class_Rank_Candidate =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  type diagram = Data.diagram
  type arena = Data.arena

  val natT = @{typ nat}
  val rankT = Type (@{type_name option}, [natT])

  datatype action_label =
      Invalid | Terminal | Continue of int
  datatype jump_label =
      Jump_Invalid | Jump_Terminal of int | Jump_Continue of int

  val jumpT = HOLogic.mk_prodT (natT,natT)

  fun dest_nat label term =
    let val (typ,value) = HOLogic.dest_number term
    in
      if typ = natT andalso value >= 0 then value
      else error ("Phase-rank " ^ label ^ " is not a natural numeral")
    end
    handle TERM _ => error ("Phase-rank " ^ label ^ " is not a natural numeral")

  fun action_label ({value,...}: Data.payload) =
    (case Term.strip_comb value of
      (Const (name,_),[]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Invalid} then Invalid
        else error "Phase-rank action leaf is not a static constructor"
    | (Const (name,_),[_,_]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Fork} then Terminal
        else error "Phase-rank action fork has the wrong constructor"
    | (Const (name,_),[child]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Landmine} then Terminal
        else if name = @{const_name Comma_Phase_Rank_Mask_Continue} then
          Continue (dest_nat "successor class" child)
        else error "Phase-rank action leaf has the wrong constructor"
    | _ => error "Phase-rank action leaf is not a closed constructor")

  fun rank_value ({value,...}: Data.payload) =
    (case Term.strip_comb value of
      (Const (name,_),[]) =>
        if name = @{const_name None} then NONE
        else error "Phase-rank leaf is not an option numeral"
    | (Const (name,_),[rank]) =>
        if name = @{const_name Some} then
          SOME (dest_nat "leaf potential" rank)
        else error "Phase-rank leaf is not an option numeral"
    | _ => error "Phase-rank leaf is not an option numeral")

  fun rank_payload NONE : Data.payload =
        {key="phase-rank-option:none",
         value=Const (@{const_name None},rankT)}
    | rank_payload (SOME rank) =
        {key="phase-rank-option:" ^ Int.toString rank,
         value=Const (@{const_name Some},natT --> rankT) $
           HOLogic.mk_number natT rank}

  fun jump_payload label : Data.payload =
    let
      val (tag, value, key) = (case label of
          Jump_Invalid => (0,0,"invalid")
        | Jump_Terminal height => (1,height,"terminal:" ^ Int.toString height)
        | Jump_Continue child => (2,child,"continue:" ^ Int.toString child))
    in
      {key="phase-rank-jump:" ^ key,
       value=HOLogic.mk_prod (HOLogic.mk_number natT tag,
         HOLogic.mk_number natT value)}
    end

  fun jump_label ({value,...}: Data.payload) =
    let
      val _ = if fastype_of value = jumpT then ()
        else error "Phase-rank jump leaf has an unexpected payload type"
      val (tag_term,value_term) = HOLogic.dest_prod value
      val tag = IntInf.toInt (dest_nat "jump tag" tag_term)
      val payload = IntInf.toInt (dest_nat "jump value" value_term)
    in
      (case tag of
        0 => Jump_Invalid
      | 1 => Jump_Terminal payload
      | 2 => Jump_Continue payload
      | _ => error "Phase-rank jump leaf has an unknown tag")
    end

  fun shifted_terminal_payload span payload =
    (case jump_label payload of
      Jump_Invalid => jump_payload Jump_Invalid
    | Jump_Terminal height => jump_payload (Jump_Terminal (span+height))
    | Jump_Continue child => jump_payload (Jump_Continue child))

  fun plain_rank_payload payload : Data.payload =
    (case rank_value payload of
      SOME rank =>
        {key="phase-rank-plain:" ^ Int.toString rank,
         value=HOLogic.mk_number natT rank}
    | NONE => error "Cannot publish an unresolved phase-rank leaf")

  fun check_roots arena actions =
    if length actions <> 46 then
      error "Phase-rank candidate requires exactly 46 admitted action roots"
    else List.app (Data.check_diagram arena) actions

  fun initial_summary arena projected_action =
    Data.normalize arena
      (Data.map_leaves arena
        (fn payload =>
          case action_label payload of
            Terminal => jump_payload (Jump_Terminal 0)
          | Invalid => jump_payload Jump_Invalid
          | Continue child => jump_payload (Jump_Continue child))
        projected_action)

  fun successor_square arena span previous =
    Data.with_reservation arena (fn reservation => let
      val prior = Vector.fromList previous
      val advanced = Unsynchronized.ref (Inttab.empty: diagram Inttab.table)
      fun successor child =
        if child < 0 orelse child >= Vector.length prior then
          error "Phase-rank summary names a foreign successor class"
        else (case Inttab.lookup (!advanced) child of
          SOME result => result
        | NONE =>
            let
              val result = Data.normalize arena
                (Data.map_leaves arena (shifted_terminal_payload span)
                  (Data.shift arena span (Vector.sub (prior,child))))
              val _ = Data.reserve_external arena reservation
              val _ = advanced := Inttab.update (child,result) (!advanced)
            in result end)
      fun next summary =
        Data.normalize arena
          (Data.bind arena
            (fn payload => fn offset =>
              if offset <> 0 then
                error "Phase-rank jump summary acquired a physical weight"
              else case jump_label payload of
                  Jump_Terminal height =>
                    Data.leaf arena (jump_payload (Jump_Terminal height))
                | Jump_Invalid => Data.leaf arena (jump_payload Jump_Invalid)
                | Jump_Continue child => successor child)
            summary)
    in map next previous end)

  fun rank_summary arena summary =
    Data.normalize arena
      (Data.map_leaves arena
        (fn payload =>
          (case jump_label payload of
            Jump_Terminal height => rank_payload (SOME height)
          | Jump_Invalid => rank_payload NONE
          | Jump_Continue _ => rank_payload NONE))
        summary)

  structure Identity_Table = Table
  (
    type key = Data.identity
    val ord = Data.identity_ord
  )
  type named_node = {term: term, definition: thm}
  datatype transaction_status =
      Transaction_Open
    | Transaction_Committed
    | Transaction_Aborted
  type shallow_transaction =
    {arena: arena, reservation: Data.reservation,
     current_lthy: local_theory option Unsynchronized.ref,
     status: transaction_status Unsynchronized.ref,
     abort_cleanups: (unit -> unit) list Unsynchronized.ref}
  type shallow_publisher =
    {transaction: shallow_transaction, arena: arena, payloadT: typ, prefix: string,
     entries: named_node Identity_Table.table Unsynchronized.ref,
     published: thm list Unsynchronized.ref,
     next_name: int Unsynchronized.ref}

  fun require_open_transaction (transaction: shallow_transaction) =
    (case !(#status transaction) of
      Transaction_Open =>
        Data.check_reservation (#arena transaction) (#reservation transaction)
    | Transaction_Committed =>
        error "Shallow publication transaction is already committed"
    | Transaction_Aborted =>
        error "Shallow publication transaction was aborted")

  fun abort_shallow_transaction (transaction: shallow_transaction) =
    (case !(#status transaction) of
      Transaction_Open =>
        (#status transaction := Transaction_Aborted;
         List.app (fn cleanup => cleanup ()) (!(#abort_cleanups transaction));
         #abort_cleanups transaction := [];
         #current_lthy transaction := NONE)
    | _ => ())

  (* The callback includes construction, naming, and the root proof.  Thus
     retained proof entries commit only after the callback returns normally;
     on every exception, child publishers are invalidated before the exact
     scratch/pending-proof reservation is rolled back. *)
  fun with_shallow_transaction arena initial_lthy work =
    Data.with_reservation arena (fn reservation =>
      let
        val transaction: shallow_transaction =
          {arena=arena,reservation=reservation,
           current_lthy=Unsynchronized.ref (SOME initial_lthy),
           status=Unsynchronized.ref Transaction_Open,
           abort_cleanups=Unsynchronized.ref []}
        val outcome = Exn.capture (fn () => work transaction) ()
      in
        (case outcome of
          Exn.Res result =>
            (require_open_transaction transaction;
             let
               val final_lthy = (case !(#current_lthy transaction) of
                   SOME lthy => lthy
                 | NONE => error "Shallow transaction lost its local-theory cursor")
             in (#status transaction := Transaction_Committed;
               #abort_cleanups transaction := [];
               #current_lthy transaction := NONE;
               (result,final_lthy)) end)
        | Exn.Exn failure =>
            (abort_shallow_transaction transaction; Exn.reraise failure))
      end)

  fun current_local_theory (transaction: shallow_transaction) =
    (require_open_transaction transaction;
     case !(#current_lthy transaction) of
       SOME lthy => lthy
     | NONE => error "Shallow transaction lost its local-theory cursor")

  fun note_in_shallow_transaction (transaction: shallow_transaction) binding facts =
    let
      val _ = require_open_transaction transaction
      val lthy = (case !(#current_lthy transaction) of
          SOME current => current
        | NONE => error "Shallow transaction lost its local-theory cursor")
      val outcome = Exn.capture (fn () =>
        Local_Theory.note ((binding,[]),facts) lthy) ()
    in
      (case outcome of
        Exn.Res ((_,theorems),next_lthy) =>
          (#current_lthy transaction := SOME next_lthy; theorems)
      | Exn.Exn failure =>
          (abort_shallow_transaction transaction; Exn.reraise failure))
    end

  (* Define one aggregate term on the transaction's owned context cursor.
     This is deliberately narrower than exposing a Local_Theory callback:
     callers cannot switch contexts or morphisms, and the definition remains
     inside the same retained-proof reservation as its root proof. *)
  fun define_in_shallow_transaction (transaction: shallow_transaction)
      (binding: binding) rhs =
    let
      val _ = require_open_transaction transaction
      val arena = #arena transaction
      val reservation = #reservation transaction
      val lthy = (case !(#current_lthy transaction) of
          SOME current => current
        | NONE => error "Shallow transaction lost its local-theory cursor")
      val outcome = Exn.capture (fn () =>
        let
          val _ = Data.reserve_external arena reservation
          val ((constant,(_,local_definition)),next_lthy) =
            Data.with_reservation arena (fn workspace =>
              let val _ = Data.reserve_external arena workspace
              in Local_Theory.define
                ((binding,NoSyn),
                  ((Binding.name (Binding.name_of binding ^ "_def"),[]),rhs))
                lthy
              end)
          val morphism = Local_Theory.target_morphism next_lthy
          val term = Morphism.term morphism constant
          val definition = Morphism.thm morphism local_definition
          val _ = Data.retain_external arena reservation 1
          val _ = #current_lthy transaction := SOME next_lthy
        in (term,definition) end) ()
    in
      (case outcome of
        Exn.Res defined => defined
      | Exn.Exn failure =>
          (abort_shallow_transaction transaction; Exn.reraise failure))
    end

  fun make_shallow_publisher (transaction: shallow_transaction) payloadT prefix:
      shallow_publisher =
    let
      val _ = require_open_transaction transaction
      val publisher: shallow_publisher =
        {transaction=transaction,arena= #arena transaction,
         payloadT=payloadT,prefix=prefix,
         entries=Unsynchronized.ref Identity_Table.empty,
         published=Unsynchronized.ref [],next_name=Unsynchronized.ref 0}
      fun clear_publisher () =
        (#entries publisher := Identity_Table.empty;
         #published publisher := [];
         #next_name publisher := 0)
      val _ = #abort_cleanups transaction :=
        clear_publisher :: !(#abort_cleanups transaction)
    in publisher end

  (* Publish nodes through the transaction-owned Local_Theory cursor.  No
     caller can substitute a sibling context or another target morphism. *)
  fun publish_shallow_roots (publisher: shallow_publisher) roots =
    let
      val transaction = #transaction publisher
      val _ = require_open_transaction transaction
      val arena = #arena publisher
      val reservation = #reservation transaction
      val payloadT = #payloadT publisher
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT])
      val edgeT = HOLogic.mk_prodT (natT,dagT)
      val leaf_const =
        Const (@{const_name Comma_Weighted_CRT_Leaf},payloadT --> dagT)
      val branch_const =
        Const (@{const_name Comma_Weighted_CRT_Branch},
          natT --> HOLogic.listT edgeT --> dagT)
      fun define action lthy =
        let val identity = Data.identity arena action
        in
          (case Identity_Table.lookup (!(#entries publisher)) identity of
            SOME cached => (cached,lthy)
          | NONE =>
              let
                val view = Data.view arena action
                val _ = (case view of
                    Data.View_Leaf {offset,...} =>
                      if offset=0 then () else
                        error "Shallow rank/action root retains an offset"
                  | Data.View_Branch {offset,children,...} =>
                      if offset=0 andalso
                          List.all (fn (weight,_) => weight=0) children then ()
                      else error "Shallow rank/action branch retains physical weights")
                val (rhs,children_lthy) =
                  (case view of
                    Data.View_Leaf {payload,...} =>
                      (leaf_const $ #value payload,lthy)
                  | Data.View_Branch {axis,children,...} =>
                      let
                        val (rows,children_lthy) =
                          fold_map (fn (_,child) => fn context =>
                            let val (child_data,next_context) = define child context
                            in ((HOLogic.mk_number natT 0,#term child_data),
                              next_context) end) children lthy
                        val rhs = branch_const $ HOLogic.mk_number natT axis $
                          HOLogic.mk_list edgeT
                            (map (fn (weight,child_term) =>
                              HOLogic.mk_prod (weight,child_term)) rows)
                      in (rhs,children_lthy) end)
                val serial = !(#next_name publisher)
                val _ = #next_name publisher := serial+1
                val name = #prefix publisher ^ "_node_" ^ Int.toString serial
                val _ = Data.reserve_external arena reservation
                val ((local_term,(_,local_definition)),defined_lthy) =
                  Data.with_reservation arena (fn workspace =>
                    let
                      val _ = Data.reserve_external arena workspace
                    in
                      Local_Theory.define
                        ((Binding.name name,NoSyn),
                          ((Binding.name (name ^ "_def"),[]),rhs))
                        children_lthy
                    end)
                val morphism = Local_Theory.target_morphism defined_lthy
                val entry: named_node = {term=Morphism.term morphism local_term,
                  definition=Morphism.thm morphism local_definition}
                val _ = Data.retain_external arena reservation 1
                val _ = #entries publisher :=
                  Identity_Table.update (identity,entry) (!(#entries publisher))
                val _ = #published publisher :=
                  #definition entry :: !(#published publisher)
              in (entry,defined_lthy) end)
        end
      val initial_lthy = (case !(#current_lthy transaction) of
          SOME lthy => lthy
        | NONE => error "Shallow transaction lost its local-theory cursor")
      val outcome = Exn.capture (fn () => fold_map define roots initial_lthy) ()
    in
      (case outcome of
        Exn.Res (entries,lthy) =>
          (#current_lthy transaction := SOME lthy; entries)
      | Exn.Exn failure =>
          (abort_shallow_transaction transaction; Exn.reraise failure))
    end

  fun shallow_publisher_lookup (publisher: shallow_publisher) action =
    (require_open_transaction (#transaction publisher);
     Identity_Table.lookup (!(#entries publisher))
       (Data.identity (#arena publisher) action))

  fun shallow_publisher_definitions (publisher: shallow_publisher) =
    (require_open_transaction (#transaction publisher);
     rev (!(#published publisher)))

  fun shallow_publisher_node_count (publisher: shallow_publisher) =
    (require_open_transaction (#transaction publisher);
     !(#next_name publisher))

  fun require_closed_rank arena roots =
    Data.with_reservation arena (fn reservation => let
      val seen = Unsynchronized.ref Identity_Table.empty
      fun visit action =
        let
          val identity = Data.identity arena action
        in
          if Identity_Table.defined (!seen) identity then ()
          else
            (Data.reserve_external arena reservation;
             seen := Identity_Table.update (identity, ()) (!seen);
             case Data.view arena action of
               Data.View_Leaf {offset,payload} =>
                 (if offset = 0 then () else
                    error "Phase-rank leaf retains physical edge weight";
                  case rank_value payload of
                    SOME rank =>
                      if rank <= 26 then () else
                        error "Phase-rank candidate exceeds height 26"
                  | NONE =>
                      error "Phase-rank candidate has an unresolved continuation")
             | Data.View_Branch {offset,children,...} =>
                 (if offset = 0 andalso
                       List.all (fn (weight,_) => weight = 0) children then ()
                  else error "Phase-rank candidate retains physical edge weight";
                  List.app (fn (_,child) => visit child) children))
        end
    in
      List.app visit roots;
      Identity_Table.size (!seen)
    end)

  fun construct arena actions =
    let
      val _ = check_roots arena actions
      val projected_actions =
        map (fn action => Data.normalize arena
          (Data.erase_weights arena action)) actions
      val initial_roots = map (initial_summary arena) projected_actions
      fun square_levels 0 _ current = current
        | square_levels levels span current =
            square_levels (levels-1) (2*span)
              (successor_square arena span current)
      val final_summaries = square_levels 5 1 initial_roots
      val final_roots = map (rank_summary arena) final_summaries
      val rank_nodes = require_closed_rank arena final_roots
      val plain_roots = map (fn root => Data.normalize arena
        (Data.map_leaves arena plain_rank_payload root)) final_roots
    in {actions=projected_actions,ranks=plain_roots,
      composition_levels=5,covered_span=32,rank_nodes=rank_nodes} end

  (* One shallow constant per admitted node.  A definition mentions only its
     already-published child constants, so no recursive tree quotation enters
     a proof term.  These definitions are construction evidence, not the
     source-equivalence or rank certificate.  Every publisher belongs to the
     same root-proof transaction and shares its exact local-theory cursor. *)
  fun finish_candidate (transaction: shallow_transaction) candidate
      action_publisher =
    let
      val arena = #arena transaction
      val stats_before = Data.stats arena
      val view_before = Data.view_stats arena
      val referenced = Data.with_reservation arena (fn reservation =>
        let
          fun add_referenced payload _ seen =
            (case action_label payload of
              Continue child =>
                if Inttab.defined seen child then seen
                else (Data.reserve_external arena reservation;
                  Inttab.update (child,()) seen)
            | _ => seen)
        in fold (fn action => fn seen =>
          Data.fold_leaves arena add_referenced seen action)
          (#actions candidate) Inttab.empty end)
      val referenced_children = Inttab.keys referenced
      val rank_vector = Vector.fromList (#ranks candidate)
      val shifted_diagrams = map (fn child =>
        (child,Data.shift arena 1 (Vector.sub (rank_vector,child))))
        referenced_children
      val action_entries = map (fn diagram =>
        (case shallow_publisher_lookup action_publisher diagram of
          SOME entry => entry
        | NONE => error "Completed source-action root was not published by its producer"))
        (#actions candidate)
      val actions = {roots=map #term action_entries,
        definitions=shallow_publisher_definitions action_publisher,
        lookup_named=(fn diagram => shallow_publisher_lookup action_publisher diagram),
        node_count=shallow_publisher_node_count action_publisher,
        lthy=current_local_theory transaction}
      val rank_publisher = make_shallow_publisher transaction natT "comma_phase_rank"
      val rank_entries = publish_shallow_roots rank_publisher
        (#ranks candidate @ map #2 shifted_diagrams)
      val rank_root_terms = map #term (take 46 rank_entries)
      val shifted_root_terms = map #term (drop 46 rank_entries)
      val shifted_rank_roots = map2 (fn (child,diagram) => fn term =>
        (child,diagram,term)) shifted_diagrams shifted_root_terms
      val stats_after = Data.stats arena
      val view_after = Data.view_stats arena
    in
      {action_roots= #roots actions,rank_roots=rank_root_terms,
       action_diagrams= #actions candidate,rank_diagrams= #ranks candidate,
       shifted_rank_roots=shifted_rank_roots,
       action_definitions= #definitions actions,
       rank_definitions=shallow_publisher_definitions rank_publisher,
       action_lookup= #lookup_named actions,
       rank_lookup=(fn diagram => shallow_publisher_lookup rank_publisher diagram),
       action_nodes= #node_count actions,
       rank_nodes=shallow_publisher_node_count rank_publisher,
       composition_levels= #composition_levels candidate,
       covered_span= #covered_span candidate,
       new_arena_nodes= #nodes stats_after - #nodes stats_before,
       retained_proof_entries=
         #proof_entries stats_after - #proof_entries stats_before,
       shallow_node_visits=
         #node_visits view_after - #node_visits view_before,
       shallow_edge_visits=
         #edge_visits view_after - #edge_visits view_before,
       lthy=current_local_theory transaction}
    end

  fun construct_and_define_with_publisher (transaction: shallow_transaction)
      action_publisher action_roots =
    finish_candidate transaction
      (construct (#arena transaction) action_roots) action_publisher

  fun construct_and_define (transaction: shallow_transaction) action_roots =
    let
      val arena = #arena transaction
      val candidate = construct arena action_roots
      val publisher = make_shallow_publisher transaction
        @{typ comma_phase_rank_mask_action} "comma_phase_action"
      val _ = publish_shallow_roots publisher action_roots
    in finish_candidate transaction candidate publisher end
end
