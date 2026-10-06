(* Publish only the 46 source-selected Compact B1 sparse roots.  The evaluator
   follows the checked short-period packet recurrence and retains one root
   equation/refinement per source, never response-node or phase certificates. *)
structure Comma_Compact_Sparse_Base_Constructor =
struct
  type item = {expression: term, value: term, refinement: thm}

  val natT = @{typ nat}
  val wordT = @{typ comma_sparse_word}
  val profiling = getenv "COMMA_PROFILE_LOG" <> ""

  fun nat n = HOLogic.mk_number natT n

  fun closed term =
    null (Term.add_frees term []) andalso null (Term.add_vars term []) andalso
      not (Term.is_open term)

  fun num_spine term =
    (case strip_comb term of
      (Const (name, _), []) => name = @{const_name Num.One}
    | (Const (name, _), [tail]) =>
        (name = @{const_name Num.Bit0} orelse name = @{const_name Num.Bit1}) andalso
          num_spine tail
    | _ => false)

  fun nat_literal term =
    fastype_of term = natT andalso closed term andalso
      (term aconv @{term "0::nat"} orelse term aconv @{term "1::nat"} orelse
        (case strip_comb term of
          (Const (name, _), [digits]) =>
            name = @{const_name numeral} andalso num_spine digits
        | _ => false))

  fun small_nat limit term =
    let
      fun bounded_num number =
        (case strip_comb number of
          (Const (name, _), []) =>
            if name = @{const_name Num.One} then SOME 1 else NONE
        | (Const (name, _), [tail]) =>
            (case bounded_num tail of
              NONE => NONE
            | SOME prior =>
                let
                  val next = 2 * prior + (if name = @{const_name Num.Bit1} then 1 else 0)
                in if name = @{const_name Num.Bit0} orelse
                      name = @{const_name Num.Bit1} then
                     if next <= limit then SOME next else NONE
                   else NONE end)
        | _ => NONE)
    in
      if fastype_of term <> natT orelse not (closed term) then NONE
      else if term aconv @{term "0::nat"} then SOME 0
      else if term aconv @{term "1::nat"} then SOME 1
      else
        (case strip_comb term of
          (Const (name, _), [digits]) =>
            if name = @{const_name numeral} then bounded_num digits else NONE
        | _ => NONE)
    end

  fun mask_width number =
    (case strip_comb number of
      (Const (name, _), []) => if name = @{const_name Num.One} then SOME 1 else NONE
    | (Const (name, _), [tail]) =>
        if name = @{const_name Num.Bit0} orelse name = @{const_name Num.Bit1} then
          Option.map (fn width => width + 1) (mask_width tail)
        else NONE
    | _ => NONE)

  fun sparse_label term =
    (case strip_comb term of
      (Const (name, _), []) => name = @{const_name Comma_Word_Invalid}
    | (Const (name, _), [index]) =>
        name = @{const_name Comma_Word_Live} andalso
          small_nat 45 index <> NONE
    | (Const (name, _), [height, terminal]) =>
        name = @{const_name Comma_Word_Stop} andalso nat_literal height andalso
          (case strip_comb terminal of
            (Const (terminal_name, _), []) =>
              terminal_name = @{const_name Comma_Terminal_Landmine}
          | (Const (terminal_name, _), [port]) =>
              terminal_name = @{const_name Comma_Terminal_Fork} andalso
                (case small_nat 9 port of SOME value => 2 <= value | NONE => false)
          | _ => false)
    | _ => false)

  fun sparse_row row =
    (case try HOLogic.dest_prod row of
      NONE => false
    | SOME (label, bits) => sparse_label label andalso
        nat_literal bits andalso not (bits aconv @{term "0::nat"}) andalso
        (if bits aconv @{term "1::nat"} then true
         else
           (case strip_comb bits of
             (Const (name, _), [digits]) =>
               name = @{const_name numeral} andalso
                 (case mask_width digits of SOME width => width <= 924 | NONE => false)
           | _ => false)))

  fun sparse_word term =
    if fastype_of term <> wordT orelse not (closed term) then false
    else
      (case try HOLogic.dest_list term of
        NONE => false
      | SOME rows => forall sparse_row rows)

  fun sparse_word_failure term =
    (case try HOLogic.dest_list term of
      NONE => NONE
    | SOME rows =>
        get_first (fn row => if sparse_row row then NONE else SOME row) rows)

  fun short_shape depth term =
    let
      fun tag value =
        (case value of
          Const (name, _) => Long_Name.base_name name
        | Free (name, _) => "free:" ^ name
        | Var ((name, _), _) => "var:" ^ name
        | Bound index => "bound:" ^ Int.toString index
        | Abs _ => "Abs")
      fun shape remaining value =
        let
          val (head, args) = strip_comb value
          val label = tag head
        in
          if remaining = 0 orelse null args then label
          else label ^ "(" ^ space_implode ","
            (map (shape (remaining - 1)) (take 2 args)) ^
            (if length args > 2 then ",..." else "") ^ ")"
        end
      val rendered = shape depth term
    in String.substring (rendered, 0, Int.min (500, size rendered)) end

  fun check_sparse_value term =
    if sparse_word term then ()
    else error "Compact sparse value is open, nonliteral, zero-masked, or oversized"

  fun check_root_equation requested theorem =
    if Thm.term_of (Thm.lhs_of theorem) aconv requested andalso
      Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) then ()
    else error "Compact B1 root equation has the wrong owner or open authority"

  fun root_expression i =
    @{term comma_compact_b1_sparse_base} $ HOLogic.mk_number @{typ nat} i

  fun make ctxt =
    let
      val kernel = Comma_Fast_Kernel.make ctxt
      val guards = Comma_Sector_Guards.make ctxt {max_nodes = 8192}
      val scope_requests = Unsynchronized.ref 0
      val scope_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val phase_class_head = Term.head_of @{term "comma_phase_class p s k"}
      val and_head = Term.head_of @{term "a AND b :: nat"}
      fun require_closed_equation request theorem =
        (check_root_equation request theorem; theorem)

      fun phase_class ct =
        (case strip_comb (Thm.term_of ct) of
          (head, [period_term, shift_term, residue_term]) =>
            if head <> phase_class_head then NONE
            else
              (case (small_nat 924 period_term, small_nat 923 shift_term,
                     small_nat 923 residue_term) of
                (SOME period, SOME shift, SOME residue) =>
                  if period <= 0 orelse residue >= period then NONE
                  else
                    let
                      val theorem = #guard guards period shift residue
                      val _ = require_closed_equation (Thm.term_of ct) theorem
                    in SOME theorem end
              | _ => NONE)
        | _ => NONE)

      fun schematic pattern = Term.map_aterms
        (fn Free (name, typ) => Var ((name, 0), typ) | atom => atom) pattern

      val scope_arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms gcd_nat.simps lcm_nat_def dvd_eq_mod_eq_0 comma_phase_scope_admitted_def}
      fun phase_scope term =
        (case strip_comb term of
          (head, [p, zero, a]) =>
            if head = phase_class_head andalso zero aconv nat 0 then
              (case (small_nat 924 p, small_nat 923 a) of
                (SOME period, SOME residue) =>
                  if period > 0 andalso 924 mod period = 0 andalso residue < period
                  then SOME (period, residue) else NONE
              | _ => NONE)
            else NONE
        | _ => NONE)
      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name, value) => ((name, 0), Thm.cterm_of ctxt (nat value))) bindings)
        theorem
      fun close_premise premise =
        Goal.prove ctxt [] [] (Thm.term_of premise)
          (fn _ => simp_tac scope_arithmetic 1)
      fun extended_gcd a b =
        if b = 0 then (a, 1, 0)
        else let val (g, x, y) = extended_gcd b (a mod b)
          in (g, y, x - (a div b) * y) end
      fun meet_scope ct =
        let val request = Thm.term_of ct in
          case strip_comb request of
            (head, [left, right]) =>
              if head <> and_head then NONE else
              (case (phase_scope left, phase_scope right) of
                (SOME (p,a), SOME (q,b)) =>
                  let
                    val _ = scope_requests := !scope_requests + 1
                    val _ = if profiling andalso !scope_requests mod 128 = 0 then
                      Comma_Fast_Kernel.report ("compact_scope_requests=" ^
                        Int.toString (!scope_requests) ^ " unique_meets=" ^
                        Int.toString (Termtab.size (!scope_memo))) else ()
                    val cached = Termtab.lookup (!scope_memo) request
                    fun construct () =
                      let
                        val (g, inverse, _) = extended_gcd p q
                        val bindings = [("p",p),("q",q),("a",a),("b",b)]
                        val rule = if a mod g <> b mod g then
                            instantiate bindings @{thm comma_phase_scope_disjoint}
                          else
                            let
                              val l = (p div g) * q
                              val c = (a + p * ((((b-a) div g) * inverse) mod (q div g))) mod l
                            in instantiate (("l",l)::("c",c)::bindings)
                              @{thm comma_phase_scope_meet} end
                        val theorem = (rule OF (map close_premise (Thm.cprems_of rule)))
                          RS @{thm eq_reflection}
                        val _ = require_closed_equation request theorem
                        val _ = if Termtab.size (!scope_memo) < 8192 then
                          scope_memo := Termtab.update (request,theorem) (!scope_memo)
                          else ()
                      in theorem end
                  in SOME (case cached of SOME theorem => theorem | NONE => construct ()) end
              | _ => NONE)
          | _ => NONE
        end

      val endpoint_kernel = Comma_Decisive_Endpoint_Kernel.make ctxt (#context kernel)
      val scope_proc = Simplifier.make_simproc ctxt
        {name = "comma_compact_phase_scope_meet", kind = Simplifier.Simproc,
         lhss = [schematic @{term "a AND b :: nat"}],
         proc = fn _ => fn _ => meet_scope, identifier = []}

      val full_scope = Thm.symmetric
        (@{thm comma_guard_full_phase} RS @{thm eq_reflection})
      val base = #context kernel
        delsimps @{thms comma_fast_entry_round_jump comma_fast_round_aux_eval}
        addsimps (@{thms comma_compact_b1_sparse_base_def
          comma_compact_b1_source_rows_def comma_compact_b1_rows_scope_eval
          comma_compact_b1_packet_plan_def comma_compact_b1_attach_rows_def
          comma_compact_packet_mask_def comma_sparse_sector_base_def
          comma_sparse_prune_def comma_sector_base_project.simps
          comma_offset_representatives_def comma_decisive_endpoint_packet_def
          comma_decisive_endpoint_round.simps comma_round_admitted.simps
          comma_compact_b1_plan.case
          list.map list.case concat.simps append.simps filter.simps
          prod.case case_prod_beta fst_conv snd_conv upt_rec Let_def
          comma_finite_move.case comma_finite_position.case comma_round_result.case}
          @ @{thms comma_phase_scope_nonzero comma_phase_scope_bounded
            and_zero_eq zero_and_eq dvd_eq_mod_eq_0 gcd_nat.simps comma_phase_scope_admitted_def} @ [full_scope])
        |> Simplifier.add_proc scope_proc
        |> Simplifier.add_proc (#simproc endpoint_kernel)
        |> Simplifier.add_cong @{thm comma_compact_b1_plan.case_cong_weak}

      val requests = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      fun expected_refinement i value =
        let
          val observer = Abs ("r", natT,
            @{term comma_orbit_word} $ nat 0 $ Bound 0 $ nat i)
        in HOLogic.mk_Trueprop
          (@{term comma_sparse_refines} $ observer $ value) end

      fun one i =
        let
          val _ = if 0 <= i andalso i < 46 then ()
            else error "Compact sparse base root index is outside 0..45"
          val expression = root_expression i
          val started_root = Time.now ()
          val _ = requests := !requests + 1
          val computed = Exn.capture (fn () =>
            let
              val equation = Simplifier.full_rewrite base
                (Thm.cterm_of ctxt expression)
              (* Scope decisions stay symbolic. Only the returned sparse word
                 demands numeral masks, using the shared checked guard owner. *)
              val _ = if profiling then Comma_Fast_Kernel.report
                ("compact_scope_root=" ^ Int.toString i ^ " symbolic_ms=" ^
                  LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started_root))))
                else ()
              val emitted = Conv.bottom_conv (fn _ => fn ct =>
                case phase_class ct of SOME theorem => theorem | NONE => Conv.all_conv ct)
                ctxt (Thm.rhs_of equation)
              val equation = require_closed_equation expression
                (Thm.transitive equation emitted)
              val value = Thm.term_of (Thm.rhs_of equation)
              val _ = if sparse_word value then () else
                let
                  val bad = (case sparse_word_failure value of
                    NONE => "nonliteral-root"
                  | SOME row => short_shape 5 row)
                in error ("Compact sparse root is not a bounded literal word: root=" ^
                  short_shape 4 expression ^ " value=" ^ short_shape 5 value ^
                  " bad=" ^ bad) end
              val index = Goal.prove ctxt [] []
                (HOLogic.mk_Trueprop
                  (@{term "(<) :: nat => nat => bool"} $ nat i $ nat 46))
                (fn {context, ...} => simp_tac context 1)
              val generic = Drule.infer_instantiate ctxt
                [(("i", 0), Thm.cterm_of ctxt (nat i))]
                @{thm comma_compact_b1_sparse_base_refines}
              val root_refinement = Thm.implies_elim generic index
              val refinement = Conv.fconv_rule
                (Conv.top_sweep_rewrs_conv [equation] ctxt) root_refinement
              val expected = expected_refinement i value
              val _ = if Thm.prop_of refinement aconv expected then ()
                else error "Compact sparse refinement lost its root binding"
              (* The published aggregate is audited once below. Rewalking every
                 root's shared dependency graph duplicates that complete audit. *)
              val _ = if Thm.nprems_of refinement = 0 andalso
                  null (Thm.hyps_of refinement) then ()
                else error "Compact sparse root refinement is not closed"
            in {expression = expression, value = value,
                refinement = refinement}: item end) ()
          val duration = Time.- (Time.now (), started_root)
          val _ = elapsed := Time.+ (!elapsed, duration)
          val _ = if Exn.is_exn computed then failures := !failures + 1 else ()
          val _ = if profiling then Comma_Fast_Kernel.report
            ("compact_sparse_b1_root=" ^ Int.toString i ^
             " status=" ^ (if Exn.is_exn computed then "failed" else "complete") ^
             " elapsed_ms=" ^ LargeInt.toString (Time.toMilliseconds duration))
            else ()
        in Exn.release computed end

      fun stats () = "compact_sparse_b1_requests=" ^ Int.toString (!requests) ^
        " compact_scope_requests=" ^ Int.toString (!scope_requests) ^
        " " ^ #stats endpoint_kernel () ^
        " compact_sparse_b1_failures=" ^ Int.toString (!failures) ^
        " compact_sparse_b1_elapsed_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed)) ^
          " " ^ #stats kernel () ^ " " ^ #report guards ()
    in {one = one, stats = stats, scope_meet = meet_scope} end
end
