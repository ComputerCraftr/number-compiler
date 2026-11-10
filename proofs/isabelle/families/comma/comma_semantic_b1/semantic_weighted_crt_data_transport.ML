(* Proof-only term transport for the shared weighted CRT data arena.
   Arena ownership, interning, proof caches, and budget accounting remain in
   semantic_weighted_crt_data.ML. *)
structure Comma_Semantic_Weighted_CRT_Data_Transport =
struct
  val natT = @{typ nat}
  val radices = [4,3,7,11]
  val clock_weights = [693,616,792,672]

  (* The rule database is immutable and contains no source or occurrence
     facts. Install it into the receiving context rather than rebuilding its
     arithmetic rules for every local proof or retaining a caller context. *)
  val arithmetic_simpset = Simplifier.simpset_of
    (Comma_Entry_Arithmetic.natural_context @{context})
  fun arithmetic_context ctxt = put_simpset arithmetic_simpset ctxt

  (* This record is created once by a single normalization publication and is
     passed only through its proof constructors.  It contains no theorem or
     cache authority.  Traces are sampled after the first 128 stages and then
     once per 64 stages; counters and elapsed times remain exact for the run. *)
  type proof_profile =
   {owner: string, stages: string list, enabled: bool,
    calls: int Unsynchronized.ref,
    active_stage: string option Unsynchronized.ref,
    totals: (int * Time.time) Symtab.table Unsynchronized.ref}

  fun make_profile owner stages: proof_profile =
    {owner=owner, stages=stages, enabled=Comma_Proof_Profile.enabled (),
     calls=Unsynchronized.ref 0,
     active_stage=Unsynchronized.ref NONE,
     totals=Unsynchronized.ref Symtab.empty}

  fun make_normalization_profile owner = make_profile owner
    ["data_wellformed", "data_cofactor", "branch_rows",
     "branch_normalize", "selector_admissibility", "selector_port",
     "selector_first_port_root", "selector_spine", "selector_family",
     "selector_diagonal", "selector_common", "closed_validation"]

  fun profile_stats (profile: proof_profile) =
    let
      val {owner,stages,enabled,calls,active_stage,totals} = profile
      fun fields stage =
        let
          val (count,elapsed) = (case Symtab.lookup (!totals) stage of
            SOME value => value
          | NONE => (0,Time.zeroTime))
        in owner ^ "_" ^ stage ^ "_calls=" ^ Int.toString count ^
          " " ^ owner ^ "_" ^ stage ^ "_ms=" ^
          LargeInt.toString (Time.toMilliseconds elapsed) end
    in
      if not enabled then ""
      else String.concatWith " "
        (map fields stages @ [owner ^ "_active_stage=" ^
          (case !active_stage of SOME stage => stage | NONE => "none"),
         owner ^ "_profile_calls=" ^ Int.toString (!calls)])
    end

  fun with_profile (profile: proof_profile) stage work =
    let
      val {owner,stages,enabled,calls,active_stage,totals} = profile
    in
      if not enabled then work ()
      else if not (member (op =) stages stage) then
        error ("unknown " ^ owner ^ " proof profile stage: " ^ stage)
      else
        let
          val ordinal = !calls
          val _ = calls := ordinal + 1
          val traced = ordinal < 128 orelse ordinal mod 64 = 0
          val started = Time.now ()
          val previous_stage = !active_stage
          val _ = active_stage := SOME stage
          val _ = if traced then Comma_Proof_Profile.report
            (owner ^ " stage=" ^ stage ^ "-start ordinal=" ^ Int.toString ordinal)
            else ()
          val result = Exn.capture work ()
          val elapsed = Time.- (Time.now (),started)
          val (count,prior) = (case Symtab.lookup (!totals) stage of
            SOME value => value
          | NONE => (0,Time.zeroTime))
          val _ = totals := Symtab.update
            (stage,(count+1,Time.+ (prior,elapsed))) (!totals)
          val _ = active_stage := previous_stage
          val status = (case result of Exn.Res _ => "complete" | Exn.Exn _ => "failed")
          val _ = if traced then Comma_Proof_Profile.report
            (owner ^ " stage=" ^ stage ^ "-" ^ status ^ " ordinal=" ^
              Int.toString ordinal ^ " elapsed_ms=" ^
              LargeInt.toString (Time.toMilliseconds elapsed)) else ()
        in Exn.release result end
    end

  fun prove_profiled profile stage ctxt fixes assumes proposition tactic =
    with_profile profile stage
      (fn () => Goal.prove ctxt fixes assumes proposition tactic)

  fun nat n = HOLogic.mk_number natT n

  fun diagnostic_term_in ctxt term =
    let
      val rendered = XML.content_of
        (YXML.parse_body (Syntax.string_of_term ctxt term))
      val limit = 240
    in
      if String.size rendered <= limit then rendered
      else String.substring (rendered,0,limit) ^ "..."
    end

  fun diagnostic_term term = diagnostic_term_in @{context} term

  fun diagnostic_head term =
    (case Term.head_of term of
      Const (name,_) => name
    | Free (name,_) => "free:" ^ name
    | Var ((name,index),_) => "var:" ^ name ^ "." ^ Int.toString index
    | Bound index => "bound:" ^ Int.toString index
    | Abs _ => "abstraction"
    | _ => "literal")

  fun report_counts label counts =
    if Comma_Proof_Profile.enabled () then
      Comma_Proof_Profile.report (label ^ " " ^ String.concatWith " "
        (map (fn (name,value) => name ^ "=" ^ Int.toString value) counts))
    else ()

  fun capture_with_failure_counts label counts work =
    (case Exn.capture work () of
      Exn.Res result => result
    | Exn.Exn failure => if Exn.is_interrupt failure then Exn.reraise failure
      else
        let val _ = Exn.capture (fn () => report_counts label (counts ())) ()
        in Exn.reraise failure end)

  (* Reverse a closed object equality by a theorem conversion.  The only
     accepted shape is a HOL-universal prefix ending in an object equality;
     this keeps symmetry transport structural and avoids rebuilding a proof
     with a simplifier for every normalized graph node. *)
  fun object_symmetric ctxt theorem =
    let
      val original = Thm.prop_of theorem
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
          andalso null (Thm.tpairs_of theorem)
          andalso not (Term.is_open original)
          andalso null (Term.add_frees original [])
          andalso null (Term.add_vars original [])
          andalso Context.subthy (Thm.theory_of_thm theorem,
            Proof_Context.theory_of ctxt) then ()
        else error "Cannot reverse an open or foreign weighted-action equality"
      val eq_commute = @{thm HOL.eq_commute} RS @{thm eq_reflection}
      fun reverse_body context current =
        (case Thm.term_of current of
          Const (name, _) $ Abs _ =>
            if name = @{const_name All} then
              Conv.arg_conv
                (Conv.abs_conv (fn (_, body_context) =>
                  reverse_body body_context) context) current
            else Conv.rewr_conv eq_commute current
        | _ => Conv.rewr_conv eq_commute current)
      val conversion = Conv.arg_conv (reverse_body ctxt)
        (Thm.cprop_of theorem)
      val reversed = Thm.equal_elim conversion theorem
      val expected = Thm.term_of (Thm.rhs_of conversion)
      val actual = Thm.prop_of reversed
      val _ = if Thm.nprems_of reversed = 0 andalso
          null (Thm.hyps_of reversed) andalso null (Thm.tpairs_of reversed) andalso
          not (Term.is_open actual) andalso
          null (Term.add_frees actual []) andalso null (Term.add_vars actual []) andalso
          actual aconv expected andalso
          Context.subthy (Thm.theory_of_thm reversed,
            Proof_Context.theory_of ctxt) then ()
        else error "Weighted-action symmetry conversion changed its theorem authority"
    in reversed end

  (* A local typed view of one checked literal vector.  Reuse its cterms for
     every selected cell so deep child payloads are not re-certified per row. *)
  datatype literal_vector = Literal_Vector of
   {rows_ct: cterm, nth_function_ct: cterm, cells: term list}

  fun make_literal_vector_cterm ctxt rows_ct =
    let
      val source_theory = Thm.theory_of_cterm rows_ct
      val current_theory = Proof_Context.theory_of ctxt
      val _ = if Context.subthy (source_theory,current_theory) then ()
        else error "Weighted CRT literal vector cterm belongs to a foreign or newer theory"
      val rows = Thm.term_of rows_ct
      val cells = HOLogic.dest_list rows
      val rowT = (case fastype_of rows of
          Type (name,[elementT]) =>
            if name = @{type_name list} then elementT
            else error "Weighted CRT selected row source is not a list"
        | _ => error "Weighted CRT selected row source has a malformed type")
      val _ = if fastype_of rows = HOLogic.listT rowT then ()
        else error "Weighted CRT literal vector has an inconsistent element type"
      val nth_function = Const (@{const_name nth},fastype_of rows --> natT --> rowT)
      val nth_function_ct = Thm.cterm_of ctxt nth_function
    in Literal_Vector {rows_ct=rows_ct,nth_function_ct=nth_function_ct,
      cells=cells} end

  fun make_literal_vector ctxt rows =
    make_literal_vector_cterm ctxt (Thm.cterm_of ctxt rows)

  fun literal_vector_rows_ct (Literal_Vector {rows_ct,...}) = rows_ct

  (* Select one cell from the validated spine without normalizing neighboring
     payloads.  The cached row cterm is applied directly to the nth function. *)
  fun literal_nth_conversion_cterm ctxt successor_equation index
      (Literal_Vector {rows_ct,nth_function_ct,cells}) =
    let
      val _ = if index >= 0 andalso index < length cells then ()
        else error "Weighted CRT selected row is outside its literal list"
      val request_ct = Thm.apply
        (Thm.apply nth_function_ct rows_ct) (Thm.cterm_of ctxt (nat index))
      val request = Thm.term_of request_ct
      val nth_zero = @{thm nth_Cons_0} RS @{thm eq_reflection}
      val nth_successor = @{thm nth_Cons_Suc} RS @{thm eq_reflection}
      fun descend remaining current =
        let
          val (function_ct,index_ct) = Thm.dest_comb current
          val (constant_ct,_) = Thm.dest_comb function_ct
          val _ = (case Thm.term_of constant_ct of
            Const (name,_) => if name = @{const_name nth} then ()
              else error "Weighted CRT literal selection changed the nth operator"
          | _ => error "Weighted CRT literal selection lost the nth operator")
          val _ = if Thm.term_of index_ct aconv nat remaining then ()
            else error "Weighted CRT literal selection exceeded its checked spine"
        in
          if remaining = 0 then Conv.rewr_conv nth_zero current
          else
            let
              val index_equation = Thm.symmetric
                (successor_equation (remaining - 1))
              val selected_index = Conv.arg_conv
                (Conv.rewr_conv index_equation) current
              val selected_head = Conv.rewr_conv nth_successor
                (Thm.rhs_of selected_index)
              val tail = descend (remaining - 1) (Thm.rhs_of selected_head)
            in Thm.transitive selected_index
              (Thm.transitive selected_head tail) end
        end
      val conversion = descend index request_ct
      val selected = List.nth (cells,index)
      val _ = if Thm.term_of (Thm.lhs_of conversion) aconv request andalso
          Thm.term_of (Thm.rhs_of conversion) aconv selected then ()
        else error "Weighted CRT literal selection returned another row"
    in conversion end

  fun check_axis axis =
    if 0 <= axis andalso axis < length radices then List.nth (radices,axis)
    else error "Weighted CRT term transport axis is outside 0..3"

  fun axis_weight axis =
    let val _ = check_axis axis
    in List.nth (clock_weights,axis) end

  type clock_env = int option * int option * int option * int option
  val empty_env: clock_env = (NONE,NONE,NONE,NONE)

  fun phase_of_env axis_radix axis_weight (env: clock_env) =
    let
      fun coordinate ((a,_,_,_),0) = a
        | coordinate ((_,b,_,_),1) = b
        | coordinate ((_,_,c,_),2) = c
        | coordinate ((_,_,_,d),3) = d
        | coordinate (_,_) = error "CRT environment axis is outside 0..3"
      fun axis_coordinate axis =
        (case coordinate (env,axis) of
          NONE => 0
        | SOME slot => if 0 <= slot andalso slot < axis_radix axis then slot
            else error "CRT environment character is outside its radix")
      val phase = fold (fn axis => fn sum =>
        sum + axis_weight axis * axis_coordinate axis) (0 upto 3) 0
    in phase mod 924 end

  fun check_term_type label expected term =
    if fastype_of term = expected then ()
    else error (label ^ " has the wrong type")

  type root_definition_resolver = term -> thm option

  fun checked_root_definition ctxt source resolver =
    (case resolver source of
      NONE => error "Weighted CRT named root has no checked definition"
    | SOME theorem =>
        let
          val proposition = Thm.prop_of theorem
          val (left,right) =
            (case try Logic.dest_equals proposition of
              SOME equation => equation
            | NONE => error "Weighted CRT root authority is not a meta equality")
          val _ = if Thm.nprems_of theorem = 0 andalso
              null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
              not (Term.is_open proposition) andalso
              null (Term.add_frees proposition []) andalso
              null (Term.add_vars proposition []) andalso
              left aconv source andalso fastype_of left = fastype_of right andalso
              Context.subthy (Thm.theory_of_thm theorem,
                Proof_Context.theory_of ctxt) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
            else error "Weighted CRT named root definition is open, foreign, or mismatched"
          val _ = (case strip_comb right of
            (Const (name,_),[_]) =>
              if name = @{const_name Comma_Weighted_CRT_Leaf} then ()
              else error "Weighted CRT named root is not a leaf constructor"
          | (Const (name,_),[_,_]) =>
              if name = @{const_name Comma_Weighted_CRT_Branch} then ()
              else error "Weighted CRT named root is not a branch constructor"
          | _ => error "Weighted CRT named root does not expose one constructor")
        in theorem end)

  (* Relate two child roots only by exact syntax or by their issued one-node
     definitions.  This deliberately does not normalize either descendant. *)
  fun checked_root_tree_equation ctxt resolver left_tree right_tree =
    if left_tree aconv right_tree then
      Thm.reflexive (Thm.cterm_of ctxt left_tree)
    else
      let
        fun resolve tree =
          (case resolver tree of
            NONE => NONE
          | SOME _ => SOME (checked_root_definition ctxt tree resolver))
        fun rhs theorem = #2 (Logic.dest_equals (Thm.prop_of theorem))
        val left_definition = resolve left_tree
        val right_definition = resolve right_tree
        fun summary tree = diagnostic_head tree ^ " : " ^
          Syntax.string_of_typ ctxt (fastype_of tree)
        fun fail () = error
          ("Weighted CRT row action changed its exact child; computed=" ^
            summary left_tree ^ "; expected=" ^ summary right_tree)
      in
        (case (left_definition,right_definition) of
          (SOME left,SOME right) =>
            if rhs left aconv right_tree then left
            else if rhs right aconv left_tree then Thm.symmetric right
            else if rhs left aconv rhs right then
              Thm.transitive left (Thm.symmetric right)
            else fail ()
        | (SOME left,NONE) => if rhs left aconv right_tree then left else fail ()
        | (NONE,SOME right) =>
            if rhs right aconv left_tree then Thm.symmetric right else fail ()
        | (NONE,NONE) => fail ())
      end

  type scoped_checker_stats =
    {emissions: int, proof_nodes: int, native_calls: int,
     native_failed_calls: int, native_milliseconds: int, closed_profile: string}
  type scoped_checker =
    {check: string -> term -> thm -> thm,
     audit: string -> thm list -> unit,
     set_context: Proof.context -> unit,
     stats: unit -> scoped_checker_stats}
  type scoped_checker_scope = {checker: scoped_checker, receiving_theory: theory}

  structure Scoped_Checker_Data = Proof_Data
  (
    type T = scoped_checker_scope option
    fun init _ = NONE
  )

  fun install_scoped_checker ctxt checker =
    Scoped_Checker_Data.put
      (SOME {checker=checker,receiving_theory=Proof_Context.theory_of ctxt}) ctxt

  fun checked_closed_default ctxt label proposition theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        not (Term.is_open (Thm.prop_of theorem)) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Term.add_vars (Thm.prop_of theorem) []) andalso
        Thm.prop_of theorem aconv proposition andalso
        null (Thm_Deps.all_oracles [theorem]) andalso
        Context.subthy (Thm.theory_of_thm theorem,
          Proof_Context.theory_of ctxt)
    then theorem
    else error (label ^ " was not a closed native theorem in this context")

  fun checked_closed ctxt label proposition theorem =
    (case Scoped_Checker_Data.get ctxt of
      SOME {checker,receiving_theory} =>
        let
          val theorem_theory = Thm.theory_of_thm theorem
          val current_theory = Proof_Context.theory_of ctxt
          val _ = if Context.subthy (receiving_theory,current_theory) andalso
              Context.subthy (theorem_theory,current_theory) then ()
            else error (label ^ " left its source compiler receiving context")
        in #check checker label proposition theorem end
    | NONE => checked_closed_default ctxt label proposition theorem)

  fun checked_tuple_projections ctxt label bundle tuple paths =
    let
      val _ = if List.all (List.all (fn 0 => true | 1 => true | _ => false)) paths
        then () else error "Tuple projection path contains an unsupported selector"
      fun project [] value = value
        | project (0::rest) value = project rest (HOLogic.mk_fst value)
        | project (_::rest) value = project rest (HOLogic.mk_snd value)
      fun component [] value = value
        | component (0::rest) value = component rest (#1 (HOLogic.dest_prod value))
        | component (_::rest) value = component rest (#2 (HOLogic.dest_prod value))
      val context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms fst_conv snd_conv}
      fun projection path =
        let
          val left = component path tuple
          val tuple_rhs = Thm.term_of (Thm.rhs_of bundle)
          val right = component path tuple_rhs
          val free = Free ("checked_tuple",fastype_of tuple)
          val selector = Term.lambda free (project path free)
          val applied = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt selector)) bundle
          val left_conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt (selector $ tuple))
          val right_conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt (selector $ tuple_rhs))
          val _ = if Thm.term_of (Thm.rhs_of left_conversion) aconv left andalso
              Thm.term_of (Thm.rhs_of right_conversion) aconv right then ()
            else error (label ^ " did not reduce to the selected tuple components")
          val theorem = Thm.transitive (Thm.symmetric left_conversion)
            (Thm.transitive applied right_conversion)
        in checked_closed ctxt label (Logic.mk_equals (left,right)) theorem end
    in map projection paths end

  fun closed_head_subterms name arity resultT term =
    let
      fun visit subterm =
        let val (head,args) = Term.strip_comb subterm
        in case head of
          Const (found,_) => if found=name then
            if length args=arity andalso fastype_of subterm=resultT andalso
                not (Term.is_open subterm) andalso
                null (Term.add_frees subterm []) andalso
                null (Term.add_vars subterm [])
            then subterm :: maps visit args
            else error "Closed-head scalar call is partial, open, or ill-typed"
          else children subterm
        | _ => children subterm end
      and children (Abs (_,_,body)) = visit body
        | children (f $ x) = visit f @ visit x
        | children _ = []
    in distinct (op aconv) (visit term) end

  fun checked_subterm_rewrite ctxt label name arity resultT term normalize convert =
    let
      val raw_calls = closed_head_subterms name arity resultT term
      fun canonicalize call =
        let
          val theorem = normalize call
          val checked = checked_closed ctxt (label ^ " canonical input")
            (Thm.prop_of theorem) theorem
          val canonical = Thm.term_of (Thm.rhs_of checked)
          val nested_calls = closed_head_subterms name arity resultT canonical
          val _ = if Thm.term_of (Thm.lhs_of checked) aconv call andalso
              fastype_of canonical=resultT andalso not (Term.is_open canonical) andalso
              null (Term.add_frees canonical []) andalso
              null (Term.add_vars canonical []) andalso null nested_calls
            then () else error "Closed-head canonicalization changed its scalar contract"
        in (canonical,checked) end
      val canonicalized = map canonicalize raw_calls
      val canonical_calls = distinct (op aconv) (map #1 canonicalized)
      val converted_rows = fold (fn call => fn entries =>
        let
          val theorem = convert call
          val checked = checked_closed ctxt (label ^ " scalar conversion")
            (Thm.prop_of theorem) theorem
          val _ = if Thm.term_of (Thm.lhs_of checked) aconv call andalso
              fastype_of (Thm.term_of (Thm.rhs_of checked))=resultT then ()
            else error "Closed-head conversion changed its canonical scalar or type"
        in Termtab.update (call,checked) entries end)
        canonical_calls Termtab.empty
      val equations = map (fn (canonical,normalization) =>
        (case Termtab.lookup converted_rows canonical of
          SOME conversion => Thm.transitive normalization conversion
        | NONE => error "Canonical scalar row lost its checked conversion")) canonicalized
      val context = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps equations
      val theorem = Simplifier.rewrite context (Thm.cterm_of ctxt term)
      val checked = checked_closed ctxt label (Thm.prop_of theorem) theorem
      val _ = if Thm.term_of (Thm.lhs_of checked) aconv term then ()
        else error "Closed-head substitution changed its exact source term"
      val output = Thm.term_of (Thm.rhs_of checked)
      val _ = if closed_head_subterms name arity resultT output = [] then ()
        else error "Closed-head scalar calls remain after checked substitution"
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("closed-head substitution label=" ^ label ^ " calls=" ^
          Int.toString (length raw_calls) ^ " canonical=" ^
          Int.toString (length canonical_calls)) else ()
    in {term=output,theorem=checked,calls=length raw_calls,
        canonical_calls=length canonical_calls} end

  fun checked_rewrite_in ctxt base_context label rules term =
    let
      (* Concrete source/action reductions need closed nat div/mod and list
         arithmetic. Keep family recursion and observers opt-in through the
         explicit rule list rather than using the broad fast evaluator. *)
      val context = Simplifier.add_simps rules base_context
      val trace = Comma_Proof_Profile.enabled () andalso member (op =)
        ["Closed source-to-program normalization","Closed source action reduction",
         "Source action canonical phase","Source action operator specialization"] label
      val rewrite_started = Time.now ()
      val _ = if trace then Comma_Proof_Profile.report
        ("checked_rewrite label=" ^ label ^ " stage=rewrite-start") else ()
      val theorem = Simplifier.rewrite context (Thm.cterm_of context term)
      val _ = if trace then Comma_Proof_Profile.report
        ("checked_rewrite label=" ^ label ^ " stage=rewrite-done elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms rewrite_started) else ()
      val audit_started = Time.now ()
      val _ = if trace then Comma_Proof_Profile.report
        ("checked_rewrite label=" ^ label ^ " stage=closed-audit-start") else ()
      val checked = checked_closed ctxt label (Thm.prop_of theorem) theorem
      val _ = if trace then Comma_Proof_Profile.report
        ("checked_rewrite label=" ^ label ^ " stage=closed-audit-done elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms audit_started) else ()
    in {term=Thm.term_of (Thm.rhs_of checked),theorem=checked} end

  fun checked_closed_profile native_certify profile ctxt label proposition theorem =
    with_profile profile "closed_validation" (fn () =>
      if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          not (Term.is_open (Thm.prop_of theorem)) andalso
          null (Term.add_frees (Thm.prop_of theorem) []) andalso
          null (Term.add_vars (Thm.prop_of theorem) []) andalso
          Thm.prop_of theorem aconv proposition andalso
          Context.subthy (Thm.theory_of_thm theorem,
            Proof_Context.theory_of ctxt) then
        (ignore (native_certify theorem); theorem)
      else error (label ^ " was not a closed native theorem in this context"))

  fun first_port_root_admissible native_certify profile ctxt axis tree resolver =
    let
      val proposition = HOLogic.mk_Trueprop
        (Const (@{const_name comma_weighted_crt_first_port_admissible},
          natT --> fastype_of tree --> HOLogic.boolT) $ nat axis $ tree)
      fun prove goal = prove_profiled profile "selector_admissibility" ctxt [] []
        goal (fn {context,...} =>
          simp_tac (arithmetic_context context |> Simplifier.add_simps
            @{thms comma_weighted_crt_first_port_admissible.simps
              comma_crt_axis_radix_def list.size}) 1)
      fun checked theorem = checked_closed_profile native_certify profile ctxt
        "Weighted CRT first-port root admissibility" proposition theorem
    in
      (case strip_comb tree of
        (Const (name,_),[_]) =>
          if name = @{const_name Comma_Weighted_CRT_Leaf} then checked (prove proposition)
          else error "Weighted CRT input root is not a leaf or branch"
      | (Const (name,_),[_,_]) =>
          if name = @{const_name Comma_Weighted_CRT_Branch} then checked (prove proposition)
          else error "Weighted CRT input root is not a leaf or branch"
      | _ =>
          let
            val definition = checked_root_definition ctxt tree resolver
            val conversion = Conv.arg_conv
              (Conv.arg_conv (Conv.rewr_conv definition))
              (Thm.cterm_of ctxt proposition)
            val exposed = Thm.term_of (Thm.rhs_of conversion)
            val body = prove exposed
            val theorem = Thm.equal_elim (Thm.symmetric conversion) body
          in checked theorem end)
    end

  (* One proof-construction scope shares Isabelle proof-node visits while every
     emission still checks its exact proposition and receiving context.  The
     final builtin audit covers the exported bundle once; the Entry certifier
     already rejects every oracle (including skip_proof) at each visited node. *)
  fun make_scoped_checker ctxt owner: scoped_checker =
    let
      val (native_certify,native_stats) =
        Comma_Entry_Arithmetic.make_certifier ctxt
      val receiving_context = Unsynchronized.ref ctxt
      val profile = make_profile owner ["closed_validation"]
      val emitted = Unsynchronized.ref 0
      fun set_context next =
        let
          val previous_theory = Proof_Context.theory_of (!receiving_context)
          val next_theory = Proof_Context.theory_of next
          val _ = if Context.subthy (previous_theory,next_theory) then ()
            else error "Scoped checker context moved backwards or to a foreign theory"
        in receiving_context := next end
      fun check label proposition theorem =
        let
          val receiving_ctxt = !receiving_context
          val checked = checked_closed_profile native_certify profile receiving_ctxt
            label proposition theorem
          val _ = emitted := !emitted + 1
        in checked end
      fun audit label theorems =
        if null (Thm_Deps.all_oracles theorems) andalso
            List.all (fn theorem =>
              Context.subthy (Thm.theory_of_thm theorem,
                Proof_Context.theory_of (!receiving_context)) andalso
              Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem))
              theorems then ()
        else error (label ^ " exported an open or non-native theorem")
      fun stats () =
        let val native = native_stats ()
        in {emissions= !emitted,
          proof_nodes= #nodes native,
          native_calls= #calls native,
          native_failed_calls= #failed_calls native,
          native_milliseconds= #milliseconds native,
          closed_profile=profile_stats profile} end
    in {check=check,audit=audit,set_context=set_context,stats=stats} end

  fun specialize_hol_all ctxt argument theorem =
    let
      val quantified = HOLogic.dest_Trueprop (Thm.prop_of theorem)
      val (_,quantified_ct) = Thm.dest_comb (Thm.cprop_of theorem)
      val _ = if Thm.term_of quantified_ct aconv quantified then ()
        else error "Weighted CRT specialization changed its certified proposition"
      val _ =
        (case strip_comb quantified of
          (Const (name,_),[abstraction as Abs (_,domainT,_)]) =>
            if name = @{const_name All} andalso domainT = natT andalso
                fastype_of abstraction = natT --> HOLogic.boolT then ()
            else error "Weighted CRT specialization expects a natural HOL universal"
        | _ => error "Weighted CRT specialization expects a HOL universal")
      (* The theorem already owns this certified predicate.  Re-certifying its
         complete child trees for every scalar specialization defeats reuse. *)
      val (_,predicate_ct) = Thm.dest_comb quantified_ct
      val rule = Drule.infer_instantiate' ctxt
        [SOME predicate_ct,
         SOME (Thm.cterm_of ctxt argument)] @{thm spec}
    in Thm.implies_elim rule theorem end

  fun pointwise_reflexive native_certify profile ctxt apply_const root_offset phase action =
    let
      val _ = if fastype_of root_offset = natT andalso fastype_of phase = natT
        then () else error "Weighted CRT reflexivity variables are not natural"
      val application = apply_const $ action $ phase
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset", natT, HOLogic.mk_all ("phase", natT,
          HOLogic.mk_eq (application, application))))
      val reflexivity = Thm.reflexive (Thm.cterm_of ctxt application)
      val object_equality = reflexivity RS @{thm meta_eq_to_obj_eq}
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase)
        object_equality COMP @{thm allI}
      val theorem = Thm.forall_intr (Thm.cterm_of ctxt root_offset)
        phase_all COMP @{thm allI}
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT leaf reflexivity theorem" proposition theorem end

  fun compose_pointwise_with check ctxt label apply_const root_offset phase
      source target facts =
    let
      val _ = if fastype_of root_offset = natT andalso fastype_of phase = natT andalso
          fastype_of source = fastype_of target then ()
        else error "Weighted CRT pointwise composition has mismatched endpoint types"
      val (source_reconstruction,canonical) =
        (case facts of
          [reconstruction,normalization] => (reconstruction,normalization)
        | _ => error "Weighted CRT pointwise transport needs two certificates")
      val source_at_offset = specialize_hol_all ctxt root_offset source_reconstruction
      val source_at_phase = specialize_hol_all ctxt phase source_at_offset
      val normalized_at_offset = specialize_hol_all ctxt root_offset canonical
      val normalized_at_phase = specialize_hol_all ctxt phase normalized_at_offset
      fun equation theorem =
        HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of theorem))
      val (source_lhs,source_rhs) = equation source_at_phase
      val (normalized_lhs,normalized_rhs) = equation normalized_at_phase
      val _ = if source_lhs aconv (apply_const $ source $ phase) andalso
          source_rhs aconv normalized_lhs andalso
          normalized_rhs aconv (apply_const $ target $ phase) then ()
        else error (label ^ ": weighted CRT certificates do not compose at exact endpoints")
      val composed_meta = Thm.transitive
        (source_at_phase RS @{thm eq_reflection})
        (normalized_at_phase RS @{thm eq_reflection})
      val composed_object = composed_meta RS @{thm meta_eq_to_obj_eq}
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase)
        composed_object COMP @{thm allI}
      val closed = Thm.forall_intr (Thm.cterm_of ctxt root_offset)
        phase_all COMP @{thm allI}
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (apply_const $ source $ phase,apply_const $ target $ phase))))
    in check label proposition closed end

  fun compose_pointwise ctxt label apply_const root_offset phase source target facts =
    compose_pointwise_with (fn name => fn proposition => fn theorem =>
      checked_closed ctxt name proposition theorem) ctxt label apply_const
      root_offset phase source target facts

  fun compose_pointwise_profile native_certify profile ctxt label apply_const root_offset phase
      source target facts =
    with_profile profile "branch_normalize"
      (fn () => compose_pointwise_with
        (fn name => fn proposition => fn theorem =>
          checked_closed_profile native_certify profile ctxt name proposition theorem)
        ctxt label apply_const root_offset phase source target facts)

  (* The data owner performs traversal, reservation, cache admission, and
     publication.  These proof constructors only consume its checked terms
     and already-certified child facts. *)
  fun certify_wellformed_tree ctxt payloadT tree child_wellformed =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val _ = check_term_type "Weighted CRT wellformed tree" dagT tree
      val wellformed_const = Const
        (@{const_name comma_weighted_crt_wellformed},dagT --> HOLogic.boolT)
      val proposition = HOLogic.mk_Trueprop (wellformed_const $ tree)
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (Simplifier.add_simps ((@{thms comma_weighted_crt_wellformed.simps
              comma_crt_axis_radix_def list_all_iff prod_set_defs} @
              child_wellformed)) (context)) 1)
        |> checked_closed ctxt "Weighted CRT recursive wellformedness" proposition
    in theorem end

  fun certify_raw_cofactor ctxt payloadT axis slot source_tree result_action
      child_equations =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val _ = check_axis axis
      val _ = if slot >= 0 andalso slot < List.nth (radices,axis) then ()
        else error "Weighted CRT raw cofactor proof slot is outside its radix"
      val _ = check_term_type "Weighted CRT raw cofactor source" dagT source_tree
      val _ = check_term_type "Weighted CRT raw cofactor result" actionT result_action
      val raw_cofactor_const = Const
        (@{const_name comma_weighted_crt_cofactor_all_raw},
          natT --> natT --> dagT --> actionT)
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (result_action,raw_cofactor_const $ nat axis $ nat slot $ source_tree))
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (Simplifier.add_simps ((@{thms comma_weighted_crt_cofactor_all_raw.simps
              comma_crt_axis_radix_def Let_def case_prod_unfold} @
              child_equations)) (context)) 1)
        |> checked_closed ctxt "Weighted CRT raw cofactor constructor" proposition
    in theorem end

  fun certify_cofactor_result_wellformed ctxt payloadT result_tree
      source_wellformed cofactor_equation =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val _ = check_term_type "Weighted CRT cofactor wellformed result" dagT result_tree
      val wellformed_const = Const
        (@{const_name comma_weighted_crt_wellformed},dagT --> HOLogic.boolT)
      val proposition = HOLogic.mk_Trueprop (wellformed_const $ result_tree)
      val _ = if Thm.nprems_of source_wellformed = 0 andalso
          Thm.nprems_of cofactor_equation = 0 then ()
        else error "Weighted CRT cofactor wellformedness needs closed source facts"
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (Simplifier.add_simps ([source_wellformed,cofactor_equation,
             @{thm comma_weighted_crt_cofactor_all_raw_wellformed},
             @{thm comma_crt_axis_radix_def}]) (context)) 1)
        |> checked_closed ctxt "Weighted CRT cofactor-result wellformedness"
          proposition
    in theorem end


end
