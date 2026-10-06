(* Data-only sparse powers.  Intermediate cells contain exact labels and
   bounded 924-bit masks; six whole-table equations certify the five squares. *)
structure Comma_Sparse_Power_Constructor =
struct
  datatype terminal = Fork of IntInf.int | Landmine
  datatype label = Invalid | Live of IntInf.int | Stop of IntInf.int * terminal
  type row = {label: label, mask: IntInf.int}
  type word = row list

  val phase_count = 924
  val full_mask = IntInf.pow (2, phase_count) - 1
  val natT = @{typ nat}
  val wordT = @{typ comma_sparse_word}
  val numT = @{typ num}
  val profiling = getenv "COMMA_PROFILE_LOG" <> ""

  fun timed stage operation =
    if not profiling then operation ()
    else
      let
        val started = Time.now ()
        val result = Exn.capture operation ()
        val status = (case result of Exn.Res _ => "complete" | Exn.Exn _ => "failed")
        val _ = Comma_Proof_Profile.report
          ("sparse_power_stage=" ^ stage ^ " status=" ^ status ^
           " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
      in Exn.release result end

  fun compare_terminal (Fork a, Fork b) = IntInf.compare (a, b)
    | compare_terminal (Fork _, Landmine) = LESS
    | compare_terminal (Landmine, Fork _) = GREATER
    | compare_terminal (Landmine, Landmine) = EQUAL

  (* This order is the order of comma_sparse_label_key, not a cache identity. *)
  fun compare_label (Invalid, Invalid) = EQUAL
    | compare_label (Invalid, _) = LESS
    | compare_label (_, Invalid) = GREATER
    | compare_label (Live a, Live b) = IntInf.compare (a, b)
    | compare_label (Live _, Stop _) = LESS
    | compare_label (Stop _, Live _) = GREATER
    | compare_label (Stop (ha, ta), Stop (hb, tb)) =
        (case IntInf.compare (ha, hb) of EQUAL => compare_terminal (ta, tb) | order => order)

  structure Labels = Table
  (type key = label val ord = compare_label)

  fun parse_num term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Num.One} then 1
        else error "Sparse row has an unknown HOL numeral constructor"
    | (Const (name, _), [arg]) =>
        if name = @{const_name Num.Bit0} then 2 * parse_num arg
        else if name = @{const_name Num.Bit1} then 2 * parse_num arg + 1
        else error "Sparse row has an unknown HOL numeral constructor"
    | _ => error "Sparse row contains a non-numeral natural")

  fun natural_value term =
    if fastype_of term <> natT then error "Sparse row value is not a natural"
    else if term aconv @{term "0::nat"} then 0
    else if term aconv @{term "1::nat"} then 1
    else
      (case strip_comb term of
        (Const (name, _), [digits]) =>
          if name = @{const_name numeral} then parse_num digits
          else if name = @{const_name Suc} then natural_value digits + 1
          else error "Sparse row contains an unsupported natural expression"
      | _ => error "Sparse row contains an unsupported natural expression")

  fun num_term value =
    if value <= 0 then error "HOL num constructor requires a positive value"
    else if value = 1 then Const (@{const_name Num.One}, numT)
    else if IntInf.mod (value, 2) = 0 then
      Const (@{const_name Num.Bit0}, numT --> numT) $ num_term (IntInf.div (value, 2))
    else Const (@{const_name Num.Bit1}, numT --> numT) $ num_term (IntInf.div (value, 2))

  fun nat_term value =
    if value < 0 then error "Cannot serialize a negative sparse natural"
    else if value = 0 then @{term "0::nat"}
    else if value = 1 then @{term "1::nat"}
    else Const (@{const_name numeral}, numT --> natT) $ num_term value

  fun parse_terminal term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Comma_Terminal_Landmine} then Landmine
        else error "Sparse stop row has an unknown terminal"
    | (Const (name, _), [argument]) =>
        if name = @{const_name Comma_Terminal_Fork} then Fork (natural_value argument)
        else error "Sparse stop row has an unknown terminal"
    | _ => error "Sparse stop row has a malformed terminal")

  fun parse_label term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Comma_Word_Invalid} then Invalid
        else error "Sparse row has an unknown nullary output"
    | (Const (name, _), [argument]) =>
        if name = @{const_name Comma_Word_Live} then Live (natural_value argument)
        else error "Sparse row has an unknown unary output"
    | (Const (name, _), [height, terminal_term]) =>
        if name = @{const_name Comma_Word_Stop} then
          Stop (natural_value height, parse_terminal terminal_term)
        else error "Sparse row has an unknown binary output"
    | _ => error "Sparse row has a malformed output label")

  fun parse_cell term =
    let
      val (label_term, mask_term) = HOLogic.dest_prod term
      val label = parse_label label_term
      val mask = natural_value mask_term
      val _ = (case label of Live index =>
          if index < 46 then ()
          else error "Sparse live output points outside the admitted fibers"
        | _ => ())
      val _ = if mask <= full_mask then ()
        else error "Sparse row mask exceeds the 924-phase domain"
    in {label=label, mask=mask}: row end

  fun parse_word term =
    if fastype_of term <> wordT then error "Sparse base item is not a sparse word"
    else map parse_cell (HOLogic.dest_list term)

  fun parse_table terms =
    if length terms <> 46 then
      error "Sparse power requires exactly 46 checked base words"
    else map parse_word terms

  fun label_term label =
    (case label of
      Invalid => @{term Comma_Word_Invalid}
    | Live index => @{term Comma_Word_Live} $ nat_term index
    | Stop (height, terminal) =>
        @{term Comma_Word_Stop} $ nat_term height $
          (case terminal of
            Fork port => @{term Comma_Terminal_Fork} $ nat_term port
          | Landmine => @{term Comma_Terminal_Landmine}))

  fun word_term rows =
    HOLogic.mk_list (HOLogic.mk_prodT (@{typ comma_word_result},natT))
      (map (fn ({label,mask}:row) =>
        HOLogic.mk_prod (label_term label, nat_term mask)) rows)

  fun normalize rows =
    let
      fun insert ({label,mask}:row) table =
        if mask = 0 then table
        else
          (case Labels.lookup table label of
            NONE => Labels.update (label, mask) table
          | SOME prior => Labels.update (label, IntInf.orb (prior, mask)) table)
      val table = fold insert rows Labels.empty
    in map (fn (label,mask) => {label=label,mask=mask}:row) (Labels.dest table) end

  fun rotate amount value =
    let
      val shift = amount mod phase_count
      val bounded = IntInf.andb (value, full_mask)
      val divisor = IntInf.pow (2, shift)
      val high = IntInf.div (bounded, divisor)
      val low = IntInf.mod (bounded, divisor)
    in
      IntInf.andb (IntInf.orb (high, low * IntInf.pow (2, phase_count - shift)), full_mask)
    end

  fun shift_label amount (Stop (height, terminal)) = Stop (height + amount, terminal)
    | shift_label _ label = label

  fun compose_raw amount left right =
    let
      fun branch ({label=Live index,mask}:row) =
            let
              val tail_index =
                if index < 0 orelse index >= IntInf.fromInt (Vector.length right) then
                  error "Sparse live output points outside the admitted fibers"
                else IntInf.toInt index
              val tail = Vector.sub (right, tail_index)
            in map (fn ({label,mask=tail_mask}:row) =>
              {label=shift_label (IntInf.fromInt amount) label,
               mask=IntInf.andb (mask, rotate amount tail_mask)}:row) tail end
        | branch ({label,mask}:row) = [{label=label,mask=mask}:row]
    in maps branch left end


  fun list_term rows = HOLogic.mk_list wordT (map word_term rows)

  (* Exactly one equation for the whole table at each level.  No fiber proof
     receives the other 45 fibers as simplifier rules.  Intermediate tables
     are data, not named constants or collections of retained certificates. *)
  fun prove_table_equation ctxt base base_definition level rows previous =
    let
      val target = @{term comma_sparse_table_power} $ base $
        nat_term (IntInf.fromInt level)
      val power_rules = @{thms comma_sparse_table_power.simps}
      val selected = List.nth (power_rules, if level=0 then 0 else 1)
      val variables = [( ("base",0), Thm.cterm_of ctxt base)] @
        (if level=0 then [] else
          [(("k",0),Thm.cterm_of ctxt (nat_term (IntInf.fromInt (level-1))))])
      val instance = Simplifier.full_simplify
        (Comma_Entry_Arithmetic.numeral_context ctxt
          delsimps @{thms comma_sparse_table_power.simps})
        (Drule.infer_instantiate ctxt variables selected)
      val source_rules = if level=0 then [base_definition]
        else (case previous of SOME theorem => [theorem RS @{thm sym}]
          | NONE => error "Sparse table square has no checked predecessor")
      val rules = source_rules @
        [@{lemma "case_nat a f (1::nat) = f 0" by simp}] @
        @{thms comma_sparse_table_square_def comma_sparse_table_lookup_def
          comma_sparse_table_valid_def
          comma_sparse_data_compose_def comma_sparse_normalize_def
          comma_sparse_label_key.simps
          list.size list.map list.inject list.distinct list.case prod.case fst_conv snd_conv
          filter.simps concat.simps append.simps take.simps drop.simps
          nat.case case_nat_numeral pred_numeral_simps Let_def
          comma_word_result.inject comma_word_result.distinct
          comma_decade_terminal.inject comma_decade_terminal.distinct
          Cons_le_Cons le_Nil Nil_le_Cons
          comma_sparse_prune_def comma_sparse_compose_def comma_sparse_branch.simps
          comma_sparse_shift.simps power_numeral_even power_numeral_odd power_0
          power_one_right power_Suc0_right nth_Cons' nth_Cons_0 nth_Cons_Suc}
      val root = instance RS @{thm eq_reflection}
      val _ = if Thm.term_of (Thm.lhs_of root) aconv target then ()
        else error "Sparse square equation lost its selected power head"
      val evaluated = Simplifier.full_rewrite
        (ctxt delsimps @{thms comma_sparse_table_power.simps} addsimps rules)
        (Thm.rhs_of root)
      val _ = if Thm.term_of (Thm.rhs_of evaluated) aconv list_term rows then ()
        else
          let
            val residual = Thm.term_of (Thm.rhs_of evaluated)
            val head = Term.head_of residual
            val first = (case try HOLogic.dest_list residual of
                SOME (item :: _) => Term.head_of item
              | _ => head)
          in error ("Sparse square did not reproduce the computed row data at level " ^
            Int.toString level ^ "; root=" ^ Syntax.string_of_term ctxt head ^
            "; first=" ^ Syntax.string_of_term ctxt first ^
            "; sample=" ^ (case try HOLogic.dest_list residual of
                SOME (item :: _) => Syntax.string_of_term ctxt item
              | _ => "not a list")) end
    in Thm.symmetric (Thm.transitive root evaluated) RS @{thm meta_eq_to_obj_eq} end

  fun publish {base, definition} lthy =
    let
      val source_context = Local_Theory.target_of lthy
      val raw_rhs = Thm.term_of (Thm.rhs_of definition)
      val _ = if Thm.nprems_of definition=0 andalso
          null (Thm.hyps_of definition) andalso
          null (Thm_Deps.all_oracles [definition]) then ()
        else error "Sparse base definition is not closed and oracle-free"
      val _ = if Thm.term_of (Thm.lhs_of definition) aconv base andalso
          fastype_of raw_rhs = HOLogic.listT wordT then ()
        else error "Sparse base definition has the wrong owner or type"
      val base_terms = (case try HOLogic.dest_list raw_rhs of
          SOME terms => terms
        | NONE => error "Sparse base definition is not a literal list")
      val base_rows = timed "host_parse_base" (fn () => parse_table base_terms)
      val guards = Comma_Sector_Guards.make source_context {max_nodes=8192}
      fun rotate_conversion ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [amount, bits]) =>
            if name <> @{const_name comma_rotate_phase} then NONE
            else (case (try natural_value amount, try natural_value bits) of
                (SOME n, SOME _) =>
                  SOME (#theorem (#mask_rotate guards
                    (IntInf.toInt n) bits))
              | _ => NONE)
        | _ => NONE)
      val rotation = Simplifier.make_simproc source_context
        {name="comma_sparse_closed_rotation", kind=Simplifier.Simproc,
         lhss=[Term.map_aterms
           (fn Free (name,typ) => Var ((name,0),typ) | atom => atom)
           @{term "comma_rotate_phase n bits"}],
         proc=fn _ => fn _ => rotate_conversion, identifier=[]}
      val comparison_context = #packed_context guards addsimps
        @{thms comma_sparse_label_key.simps fst_conv snd_conv
          comma_word_result.inject comma_word_result.distinct
          comma_decade_terminal.inject comma_decade_terminal.distinct
          list.inject list.distinct Cons_le_Cons le_Nil Nil_le_Cons}
      fun packed_or ct =
        (case strip_comb (Thm.term_of ct) of
          (head, [left,right]) =>
            if head = Term.head_of @{term "a OR b :: nat"} then
              #theorem (#mask_or guards left right)
            else error "Sparse normalizer received a foreign mask operation"
        | _ => error "Sparse normalizer received a malformed OR")
      val normalize_rows_conv = Comma_Mask_Rows_Conversion.make source_context
        {key_order=Simplifier.rewrite comparison_context,
         label_equal=Simplifier.rewrite comparison_context, mask_or=packed_or}
      (* This cache lives only during this publication in this proof context.
         Its key is the complete typed conversion request, including the row
         labels and masks.  Equal fibers can reuse a checked normalization;
         neither a fiber number nor a temporal level is semantic authority. *)
      val normalization_cache = Unsynchronized.ref (Termtab.empty : thm Termtab.table)
      val normalization_hits = Unsynchronized.ref 0
      val normalization_misses = Unsynchronized.ref 0
      val normalization_capacity = 256
      fun normalized_rows ct =
        let val request = Thm.term_of ct
        in
          (case Termtab.lookup (!normalization_cache) request of
            SOME theorem =>
              (normalization_hits := !normalization_hits + 1; theorem)
          | NONE =>
              let
                val _ = normalization_misses := !normalization_misses + 1
                val theorem = normalize_rows_conv ct
                val _ = if Termtab.size (!normalization_cache) < normalization_capacity
                  then normalization_cache := Termtab.update (request,theorem)
                    (!normalization_cache)
                  else ()
              in theorem end)
        end
      fun normalize_conversion ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name,_), [_,rows]) =>
            if name <> @{const_name comma_mask_rows_normalize} then NONE
            else (case try HOLogic.dest_list rows of
                NONE => NONE
              | SOME _ =>
                  if Term.maxidx_of_term rows < 0 andalso
                      null (Term.add_frees rows []) andalso not (Term.is_open rows)
                  then SOME (normalized_rows ct)
                  else error "Sparse normalizer received open row data")
        | _ => NONE)
      val normalization = Simplifier.make_simproc source_context
        {name="comma_sparse_closed_normalization", kind=Simplifier.Simproc,
         lhss=[Term.map_aterms
           (fn Free (name,typ) => Var ((name,0),typ) | atom => atom)
           @{term "comma_mask_rows_normalize comma_sparse_label_key rows"}],
         proc=fn _ => fn _ => normalize_conversion, identifier=[]}
      val ctxt = #packed_context guards
        |> Simplifier.add_proc rotation
        |> Simplifier.add_proc normalization
      val base_definition = Local_Defs.meta_rewrite_rule ctxt definition
      val _ = if Thm.term_of (Thm.lhs_of base_definition) aconv base andalso
          Thm.term_of (Thm.rhs_of base_definition) aconv raw_rhs
        then () else error "Sparse base definition does not bind the supplied table"
      val initial = timed "power_level=0 host_normalize" (fn () => map normalize base_rows)
      fun certify level rows previous = timed
        ("power_level=" ^ Int.toString level ^ " table_equation")
        (fn () => prove_table_equation ctxt base base_definition level rows previous)
      val initial_equation = certify 0 initial NONE
      fun square (level,rows,equation) =
        if level=5 then (rows,equation)
        else
          let
            val amount = IntInf.toInt (IntInf.pow (2,level))
            val power_level = level+1
            val indexed_rows = Vector.fromList rows
            val next = timed ("power_level=" ^ Int.toString power_level ^ " host_square")
              (fn () => map (normalize o (fn left => compose_raw amount left indexed_rows)) rows)
            val next_equation = certify power_level next (SOME equation)
          in square (power_level,next,next_equation) end
      val (final_rows,final_equation) = square (0,initial,initial_equation)
      val _ = if profiling then Comma_Fast_Kernel.report
        ("sparse_normalization_cache hits=" ^ Int.toString (!normalization_hits) ^
         " misses=" ^ Int.toString (!normalization_misses) ^
         " retained=" ^ Int.toString (Termtab.size (!normalization_cache))) else ()
      val table_name = "comma_checked_sparse_B32_rows_table"
      val ((table,(_,table_def)), next) = Local_Theory.define
        ((Binding.name table_name,NoSyn),
          ((Binding.name (table_name ^ "_def"),[]),list_term final_rows)) lthy
      val equation = Thm.transitive
        (Local_Defs.meta_rewrite_rule next table_def)
        (final_equation RS @{thm eq_reflection}) RS @{thm meta_eq_to_obj_eq}
      val _ = if Thm.prop_of equation aconv HOLogic.mk_Trueprop
          (HOLogic.mk_eq (table, @{term comma_sparse_table_power} $ base $ nat_term 5))
        then () else error "Sparse publication lost its exact table binding"
      val (_,finished) = Local_Theory.note
        ((Binding.name "comma_sparse_power_B32_data_equation",[]),[equation]) next
      val published = Proof_Context.get_thm (Local_Theory.target_of finished)
        "comma_sparse_power_B32_data_equation"
      val _ = if Thm.nprems_of published=0 andalso null (Thm.hyps_of published) andalso
          null (Thm_Deps.all_oracles [published]) then ()
        else error "Sparse table power is not closed and oracle-free"
      val _ = if profiling then Comma_Fast_Kernel.report
        ("sparse_power_complete table_equations=6 intermediate_fiber_equations=0 rows=" ^
         Int.toString (fold (fn rows => fn count => length rows+count) final_rows 0)) else ()
    in finished end
end
