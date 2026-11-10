(* Packed guards are assembled from a one-period certificate by binary joins.
   Host arithmetic chooses a proof tree; it supplies no bit-pattern premise. *)
structure Comma_Sector_Guards =
struct
  datatype numeric_operator = And_Num | Or_Num
  structure Pattern_Table = Table
  (
    type key = int * int * int
    fun ord ((a, b, c), (d, e, f)) =
      prod_ord int_ord (prod_ord int_ord int_ord) ((a, (b, c)), (d, (e, f)))
  )
  type pattern = {width: int, bits: term, theorem: thm}
  type packed_stats =
    {lookups:int, hits:int, misses:int, failures:int, num_nodes:int,
     num_conversions:int, num_failures:int, num_retained:int, num_evicted:int,
     num_limit:int, total_retained:int,
     total_limit:int, retained:int, evicted:int, full_hits:int,
     full_missing_bounds:int, publication_reuses:int}
  fun make ctxt {max_nodes} =
    let
      val _ = if 1 <= max_nodes andalso max_nodes <= 8192 then ()
        else error "Guard node capacity must lie in 1..8192"
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simps
        @{thms power_numeral_even power_numeral_odd power_0 power_one_right power_Suc0_right
          dvd_eq_mod_eq_0 upt_rec list_all_Nil_iff list_all_Cons_iff}
      val packed = arithmetic |> Simplifier.add_simps
        @{thms numeral_or_num or_num.simps or.left_neutral or.right_neutral
          numeral_and_num and_num.simps and_numerals
          mask_Suc_0 mask_0
          push_bit_numeral push_bit_Suc_numeral push_bit_0_id push_bit_of_0 push_bit_of_1
          drop_bit_numeral_bit0 drop_bit_numeral_bit1 drop_bit_Suc_bit0 drop_bit_Suc_bit1
          drop_bit_0 drop_bit_of_0 drop_bit_of_1
          take_bit_numeral_numeral take_bit_num_simps take_bit_0 take_bit_of_0
          take_bit_numeral_1 take_bit_Suc_1 pred_numeral_simps option.case option.map id_apply
          comma_guard_push_one_numeral
          comma_guard_drop_one_numeral
          comma_guard_take_one_numeral
          comma_guard_take_num_one comma_guard_take_one_one of_bool_eq
          or_numerals(1,2,5,8)}
      val packed_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      (* FIFO, one eviction per publication. Existing checked results stay valid
         after eviction; no cache operation grants source authority. *)
      val packed_front = Unsynchronized.ref ([]: term list)
      val packed_back = Unsynchronized.ref ([]: term list)
      val packed_lookups = Unsynchronized.ref 0
      val packed_hits = Unsynchronized.ref 0
      val packed_misses = Unsynchronized.ref 0
      val packed_identities = Unsynchronized.ref 0
      val packed_failures = Unsynchronized.ref 0
      val packed_evicted = Unsynchronized.ref 0
      val packed_elapsed = Unsynchronized.ref Time.zeroTime
      val packed_publication_reuses = Unsynchronized.ref 0
      val packed_num_nodes = Unsynchronized.ref 0
      val packed_num_conversions = Unsynchronized.ref 0
      val packed_num_failures = Unsynchronized.ref 0
      (* Keep the previous numeric-cache reservation while benchmarking the
         root-only owner; unused recipe capacity is not silently reassigned. *)
      val packed_num_capacity = Int.min (512, max_nodes div 4)
      val packed_root_capacity = max_nodes - packed_num_capacity
      val trim_seeds = Unsynchronized.ref 0
      val full_hits = Unsynchronized.ref 0
      val full_missing_bounds = Unsynchronized.ref 0
      val full_word = Unsynchronized.ref (NONE: thm option)
      fun trim_key bits = @{term "take_bit 924 :: nat => nat"} $ bits
      fun closed_natural t = (case try HOLogic.dest_number t of
        SOME (typ,n) => typ = @{typ nat} andalso n >= 0 | NONE => false)
      fun plain_term term = XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt term))
      fun validate_equation key theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv key andalso
            closed_natural (Thm.term_of (Thm.rhs_of theorem)) andalso
            null (Thm.hyps_of theorem) andalso Thm.nprems_of theorem = 0 andalso
            null (Thm.tpairs_of theorem)
        then theorem
        else error ("Packed arithmetic requires an exact closed numeral equation: requested=" ^
          plain_term key ^ " lhs=" ^
          plain_term (Thm.term_of (Thm.lhs_of theorem)) ^ " rhs=" ^
          String.substring (plain_term (Thm.term_of (Thm.rhs_of theorem)), 0,
            Int.min (240, size (plain_term (Thm.term_of (Thm.rhs_of theorem))))))
      fun checked_equation key theorem = certify (validate_equation key theorem)
      fun packed_publish key theorem =
        (case Termtab.lookup (!packed_memo) key of
          SOME prior =>
            if Thm.prop_of prior aconv Thm.prop_of theorem then
              (packed_publication_reuses := !packed_publication_reuses + 1; prior)
            else error "Conflicting packed equation publication"
        | NONE =>
          let
            val _ = if Termtab.size (!packed_memo) < packed_root_capacity then () else
              let
                val _ = if null (!packed_front) then
                  (packed_front := rev (!packed_back); packed_back := []) else ()
                val oldest = hd (!packed_front)
                val _ = packed_front := tl (!packed_front)
                val _ = packed_memo := Termtab.delete oldest (!packed_memo)
              in packed_evicted := !packed_evicted + 1 end
            val _ = packed_memo := Termtab.update (key,theorem) (!packed_memo)
            val _ = packed_back := key :: !packed_back
          in theorem end)
      fun mask_trim bits = Termtab.lookup (!packed_memo) (trim_key bits)
      fun publish_trim bits theorem =
        let
          val key = trim_key bits
        in
          case Termtab.lookup (!packed_memo) key of
            SOME existing => validate_equation key existing
          | NONE =>
              let
                val checked = checked_equation key theorem
                val published = packed_publish key checked
                val _ = trim_seeds := !trim_seeds + 1
              in published end
        end
      fun numeral_width numeral =
        let
          fun num_width (Const (name, _)) =
                if name = @{const_name Num.num.One} then SOME 1 else NONE
            | num_width (Const (name, _) $ tail) =
                if name = @{const_name Num.num.Bit0} orelse
                    name = @{const_name Num.num.Bit1}
                then Option.map (fn width => width + 1) (num_width tail)
                else NONE
            | num_width _ = NONE
          fun nat_width (Const (name, _)) =
                if name = @{const_name Groups.zero_class.zero} then SOME 0
                else if name = @{const_name Groups.one_class.one} then SOME 1
                else NONE
            | nat_width (Const (name, _) $ digits) =
                if name = "Num.numeral_class.numeral" then num_width digits else NONE
            | nat_width _ = NONE
        in nat_width numeral end
      val num_steps = map (fn theorem => theorem RS @{thm eq_reflection})
        @{thms and_num.simps or_num.simps}
      val option_steps = map (fn theorem => theorem RS @{thm eq_reflection})
        @{thms option.map option.case}
      fun num_head (Const (name, _)) = name = @{const_name Num.num.One}
        | num_head (Const (name, _) $ _) =
            name = @{const_name Num.num.Bit0} orelse name = @{const_name Num.num.Bit1}
        | num_head _ = false
      fun operator_name And_Num = @{const_name and_num}
        | operator_name Or_Num = @{const_name or_num}
      fun operator_type And_Num = @{typ "num option"}
        | operator_type Or_Num = @{typ num}
      fun validate_num_result operator theorem =
        let
          val result = Thm.term_of (Thm.rhs_of theorem)
          val result_shape = if operator = And_Num then
              (result aconv @{term "None :: num option"} orelse
                (case result of Const (name, _) $ n =>
                  name = @{const_name Some} andalso num_head n | _ => false))
            else num_head result
          val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso result_shape then ()
            else error "Packed numeric result failed its exact typed constructor check"
        in theorem end
      fun sub_conversion operator ct =
        let
          val key_term = Thm.term_of ct
          val (head, operands) = strip_comb key_term
          val head_name = (case head of Const (name, _) => name
            | _ => error "Packed numeric request has a nonconstant operator")
          val _ = if head_name = operator_name operator andalso length operands = 2 then ()
            else error "Packed numeric operator metadata does not match the exact request"
          val _ = if Thm.typ_of_cterm ct = operator_type operator then ()
            else error "Packed numeric operator metadata has the wrong result type"
          val _ = packed_num_nodes := !packed_num_nodes + 1
          fun exact_attempt () =
            let
              val step = Conv.rewrs_conv num_steps ct
              val _ = packed_num_conversions := !packed_num_conversions + 1
              fun child nested =
                (case strip_comb (Thm.term_of nested) of
                  (Const (name, _), [left, right]) =>
                    if name = @{const_name and_num} orelse name = @{const_name or_num} then
                      if name = operator_name operator andalso
                          num_head left andalso num_head right then
                        sub_conversion operator nested
                      else if name <> operator_name operator then
                        error "Packed num equation recursed under a different operator"
                      else Conv.all_conv nested
                    else Conv.all_conv nested
                | _ => Conv.all_conv nested)
              val rhs = Thm.rhs_of step
              val tail = (case strip_comb (Thm.term_of rhs) of
                  (Const (name, _), [_]) =>
                    if name = @{const_name Num.num.Bit0} orelse
                        name = @{const_name Num.num.Bit1}
                    then Conv.arg_conv child rhs else Conv.all_conv rhs
                | (Const (name, _), _) =>
                    if name = @{const_name map_option} orelse
                        name = @{const_name case_option}
                    then (Conv.arg_conv child then_conv Conv.rewrs_conv option_steps
                      then_conv Conv.try_conv (Thm.beta_conversion false)) rhs
                    else Conv.all_conv rhs
                | _ => Conv.all_conv rhs)
              val theorem = Thm.transitive step tail
              val theorem = validate_num_result operator theorem
            in theorem end
          val attempt = Exn.capture exact_attempt ()
          val _ = if Exn.is_exn attempt then
              packed_num_failures := !packed_num_failures + 1
            else ()
        in Exn.release attempt end
      val sub_proc = Simplifier.make_simproc ctxt
        {name="comma_closed_num_subexpression",kind=Simplifier.Simproc,
         lhss=map (Term.map_aterms
           (fn Free(name,typ)=>Var((name,0),typ) | atom=>atom))
           [@{term "and_num m n"},@{term "or_num m n"}],
         proc=fn _=>fn _=>fn ct=>
           (case strip_comb (Thm.term_of ct) of
             (Const (name, _), [left, right]) =>
               let
                 val operator = if name = @{const_name and_num} then SOME And_Num
                   else if name = @{const_name or_num} then SOME Or_Num else NONE
               in
                 case operator of
                   SOME selected => if num_head left andalso num_head right
                     then SOME (sub_conversion selected ct) else NONE
                 | NONE => NONE
               end
           | _ => NONE), identifier=[]}
      val packed_raw = (packed |> Simplifier.del_simps @{thms and_num.simps or_num.simps})
        |> Simplifier.add_proc sub_proc
      fun packed_lookup evaluation key =
        (packed_lookups := !packed_lookups + 1;
         case Termtab.lookup (!packed_memo) key of
           SOME theorem => (packed_hits := !packed_hits + 1; theorem)
         | NONE =>
             (packed_misses := !packed_misses + 1;
              packed_publish key (checked_equation key
                (Simplifier.rewrite evaluation (Thm.cterm_of ctxt key)))))
      fun packed_lookup_by key compute =
        (packed_lookups := !packed_lookups + 1;
         case Termtab.lookup (!packed_memo) key of
           SOME theorem => (packed_hits := !packed_hits + 1; theorem)
         | NONE =>
             (packed_misses := !packed_misses + 1;
              packed_publish key (checked_equation key (compute ()))))
      fun packed_request operation =
        let val begun = Time.now ()
            val result = Exn.capture operation ()
            val _ = packed_elapsed := Time.+ (!packed_elapsed, Time.-(Time.now (),begun))
            val _ = if Exn.is_exn result then packed_failures := !packed_failures + 1 else ()
            val theorem = Exn.release result
        in {value = Thm.term_of (Thm.rhs_of theorem), theorem = theorem} end
      fun packed_instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name,value) => ((name,0),Thm.cterm_of ctxt value)) bindings) theorem
      val and_head = Term.head_of @{term "a AND b :: nat"}
      val or_head = Term.head_of @{term "a OR b :: nat"}
      fun mask_binary conjunction left right = packed_request (fn () =>
        let
          val _ = if closed_natural left andalso closed_natural right then ()
            else error "Mask operation requires closed natural numeral operands"
          val head = if conjunction then and_head else or_head
          val requested = head $ left $ right
          val zero_left = snd (HOLogic.dest_number left) = 0
          val zero_right = snd (HOLogic.dest_number right) = 0
          fun swap a b = packed_instantiate [("a",a),("b",b)]
            (if conjunction then @{thm comma_mask_and_swap} else @{thm comma_mask_or_swap})
              RS @{thm eq_reflection}
          fun identity theorem arg =
            (packed_identities := !packed_identities + 1;
             packed_instantiate [("a",arg)] theorem RS @{thm eq_reflection})
          fun with_full a b = (case !full_word of
              NONE => NONE
            | SOME full_equation =>
              if not (b aconv Thm.term_of (Thm.rhs_of full_equation)) then NONE
              else (case Termtab.lookup (!packed_memo) (trim_key a) of
                NONE => (full_missing_bounds := !full_missing_bounds + 1; NONE)
              | SOME bound =>
                let
                  val lemma = packed_instantiate [("a",a),("full",b)]
                    (if conjunction then @{thm comma_mask_and_full} else @{thm comma_mask_or_full})
                  val theorem = (lemma OF [bound RS @{thm meta_eq_to_obj_eq},
                    full_equation RS @{thm meta_eq_to_obj_eq}]) RS @{thm eq_reflection}
                  val _ = full_hits := !full_hits + 1
                in SOME theorem end))
          fun general () = (case with_full left right of
              SOME theorem => (false,theorem)
            | NONE => (case with_full right left of
                SOME theorem => (false,Thm.transitive (swap left right) theorem)
              | NONE => if snd (HOLogic.dest_number left) <= snd (HOLogic.dest_number right) then
                  (true,packed_lookup packed_raw requested)
                else (false,Thm.transitive (swap left right)
                  (packed_lookup packed_raw (head $ right $ left)))))
          (* Only direct results from the private checked cache bypass another
             oracle walk. Newly instantiated identities/swaps remain certified. *)
          val (already_checked,result) = if left aconv right then (false,identity
                (if conjunction then @{thm comma_mask_and_self} else @{thm comma_mask_or_self}) left)
            else if zero_right then (false,identity
                (if conjunction then @{thm comma_mask_and_zero} else @{thm comma_mask_or_zero}) left)
            else if zero_left then (false,Thm.transitive (swap left right) (identity
                (if conjunction then @{thm comma_mask_and_zero} else @{thm comma_mask_or_zero}) right))
            else general ()
          val equation = if already_checked then validate_equation requested result
            else checked_equation requested result
          val _ = if not conjunction then () else
            let
              val result_value = Thm.term_of (Thm.rhs_of equation)
              val result_key = trim_key result_value
            in
              case Termtab.lookup (!packed_memo) result_key of
                SOME existing => ignore (validate_equation result_key existing)
              | NONE =>
                  (case (mask_trim left, mask_trim right) of
                    (SOME left_bound, SOME right_bound) =>
                      let
                        val bound_rule = Drule.infer_instantiate ctxt
                          [( ("a",0), Thm.cterm_of ctxt left),
                           ( ("b",0), Thm.cterm_of ctxt right)]
                          @{thm comma_mask_and_preserves_bounded}
                        val bounded = bound_rule OF
                          [left_bound RS @{thm meta_eq_to_obj_eq},
                           right_bound RS @{thm meta_eq_to_obj_eq}]
                        val bounded = bounded RS @{thm eq_reflection}
                        val bounded = Conv.fconv_rule
                          (Conv.top_sweep_rewrs_conv [equation] ctxt) bounded
                        val _ = publish_trim result_value bounded
                      in () end
                  | _ => ())
            end
        in equation end)
      fun mask_and left right = mask_binary true left right
      fun mask_or left right = mask_binary false left right
      fun mask_rotate shift bits = packed_request (fn () =>
        let
          val _ = if shift >= 0 andalso closed_natural bits then ()
            else error "Mask rotation requires a nonnegative shift and closed natural word"
          val expression = @{term comma_rotate_phase} $ HOLogic.mk_number @{typ nat} shift $ bits
          fun exact_rotation () =
            packed_lookup (packed_raw |> Simplifier.add_simps @{thms comma_rotate_phase_def}) expression
          fun checked_trim () =
            (case mask_trim bits of
              SOME theorem => SOME (validate_equation (trim_key bits) theorem)
            | NONE =>
                (case numeral_width bits of
                  SOME width =>
                    if width > 924 then NONE
                    else
                      let
                        val bound_prop = HOLogic.mk_binrel @{const_name less}
                          (bits, HOLogic.mk_binop @{const_name power}
                            (HOLogic.mk_number @{typ nat} 2,
                             HOLogic.mk_number @{typ nat} 924))
                        val normalized = Simplifier.rewrite arithmetic
                          (Thm.cterm_of ctxt (HOLogic.mk_Trueprop bound_prop))
                        val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True}
                          then () else error "Packed rotation width bound is not true"
                        val bound = certify
                          (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI})
                        val trim_rule = packed_instantiate
                          [("m", bits), ("n", HOLogic.mk_number @{typ nat} 924)]
                          @{thm take_bit_nat_eq_self}
                        val trim = (trim_rule OF [bound]) RS @{thm eq_reflection}
                      in SOME (publish_trim bits trim) end
                | NONE => NONE))
          fun rotate_one () = packed_lookup_by expression (fn () =>
            (case checked_trim () of
              NONE =>
                Simplifier.rewrite
                  (packed_raw |> Simplifier.add_simps @{thms comma_rotate_phase_def})
                  (Thm.cterm_of ctxt expression)
            | SOME trim =>
                let
                  val rotation_rule = packed_instantiate [("bits", bits)]
                    @{thm comma_rotate_phase_one_bounded}
                  val rotation_rule = (rotation_rule OF
                    [trim RS @{thm meta_eq_to_obj_eq}]) RS @{thm eq_reflection}
                  val rhs = Thm.term_of (Thm.rhs_of rotation_rule)
                  val computed = packed_lookup packed_raw rhs
                in Thm.transitive rotation_rule computed end))
        in if shift = 1 then rotate_one () else exact_rotation () end)
      fun packed_convert ct =
        (case strip_comb (Thm.term_of ct) of
          (head,[left,right]) =>
            if not (closed_natural left andalso closed_natural right) then NONE
            else if head = and_head then SOME (#theorem (mask_and left right))
            else if head = or_head then SOME (#theorem (mask_or left right)) else NONE
        | _ => NONE)
      val packed_proc = Simplifier.make_simproc ctxt
        {name = "comma_closed_packed_root", kind = Simplifier.Simproc,
         lhss = map (Term.map_aterms
           (fn Free (name,typ) => Var ((name,0),typ) | atom => atom))
           [@{term "a AND b :: nat"}, @{term "a OR b :: nat"}],
         proc = fn _ => fn _ => packed_convert, identifier = []}
      val packed = (packed_raw |> Simplifier.del_simps
        @{thms numeral_and_num numeral_or_num and_numerals or_numerals})
        |> Simplifier.add_proc packed_proc
      val memo = Unsynchronized.ref (Pattern_Table.empty: pattern Pattern_Table.table)
      val classes = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val class_publications = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val attempts = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val joins = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val join_elapsed = Unsynchronized.ref Time.zeroTime
      val rotate_elapsed = Unsynchronized.ref Time.zeroTime
      val normalizations = Unsynchronized.ref 0
      fun timed elapsed operation =
        let val started = Time.now ()
            val result = Exn.capture operation ()
            val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), started))
        in Exn.release result end
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name, value) => ((name, 0), Thm.cterm_of ctxt value)) bindings) theorem
      fun boolean expression =
        let
          val normalized = Simplifier.rewrite arithmetic
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop expression))
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True} then ()
            else error "Guard arithmetic admission is false"
        in certify (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI}) end
      fun room () = if !retained < max_nodes then ()
        else error "Guard node budget exhausted before arithmetic"
      fun normalize theorem =
        (normalizations := !normalizations + 1;
         certify (Simplifier.full_simplify packed theorem))
      fun join period residue (a: pattern) (b: pattern) = timed join_elapsed (fn () =>
        let
          val _ = joins := !joins + 1
          val width = #width a
          val height = #width b
          val aligned = boolean (@{term "(dvd) :: nat => nat => bool"} $ nat period $ nat width)
          val raw = instantiate [("period", nat period), ("residue", nat residue),
            ("width", nat width), ("height", nat height), ("a", #bits a), ("b", #bits b)]
              @{thm comma_guard_join} OF [#theorem a, #theorem b, aligned]
          val theorem = normalize raw
          val conclusion = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val args = snd (strip_comb conclusion)
          val bits = List.nth (args, 3)
          val (typ, value) = HOLogic.dest_number bits
          val _ = if typ = @{typ nat} andalso value >= 0 then ()
            else error "Guard join left unresolved bit arithmetic"
        in {width = width + height, bits = bits, theorem = theorem}: pattern end)
      fun repeat period residue count =
        let val index = (period, residue, count) in
          case Pattern_Table.lookup (!memo) index of
            SOME answer => (hits := !hits + 1; answer)
          | NONE =>
            let
              val _ = room ()
              val _ = attempts := !attempts + 1
              val answer = if count = 1 then
                  let
                    val admitted = boolean (HOLogic.mk_binrel @{const_name less}
                      (nat residue, nat period))
                    val raw = instantiate [("period", nat period), ("residue", nat residue)]
                      @{thm comma_guard_single_period} OF [admitted]
                    val theorem = normalize raw
                    val bits = List.nth (snd (strip_comb
                      (HOLogic.dest_Trueprop (Thm.prop_of theorem))), 3)
                    val _ = HOLogic.dest_number bits
                  in {width = period, bits = bits, theorem = theorem}: pattern end
                else
                  let
                    val half = repeat period residue (count div 2)
                    val _ = room ()
                    val twice = join period residue half half
                  in if count mod 2 = 0 then twice
                    else
                      let val first = repeat period residue 1
                          val _ = room ()
                      in join period residue first twice end
                  end
              val _ = room ()
              val _ = memo := Pattern_Table.update (index, answer) (!memo)
              val _ = retained := !retained + 1
            in answer end
        end
      fun guard period shift residue =
        let
          val start = Time.now ()
          val result = Exn.capture (fn () =>
            let
              val _ = if 0 < period andalso period <= 924 andalso 924 mod period = 0
                  andalso 0 <= residue andalso residue < period andalso shift >= 0 then ()
                else error "Guard requires a divisor of 924 and admitted residue/shift"
              val expression = @{term comma_phase_class} $ nat period $ nat shift $ nat residue
            in case Termtab.lookup (!classes) expression of
              SOME theorem => (hits := !hits + 1; theorem)
            | NONE =>
              let
                val _ = room ()
                val target = (residue + period - shift mod period) mod period
                val word = repeat period target (924 div period)
                val _ = if #width word = 924 then () else error "Guard width is not 924"
                val _ = room ()
                val positive = boolean (@{term "(less) :: nat => nat => bool"} $ nat 0 $ nat period)
                val phase_template = instantiate [("period", nat period), ("target", nat target),
                  ("bits", #bits word), ("shift", nat shift), ("residue", nat residue)]
                    @{thm comma_guard_shifted_pattern}
                val phase_prop = Thm.term_of (List.nth (Thm.cprems_of phase_template, 2))
                val phase = timed rotate_elapsed (fn () =>
                  (normalizations := !normalizations + 1;
                   boolean (HOLogic.dest_Trueprop phase_prop)))
                val theorem = certify ((phase_template OF [#theorem word, positive, phase])
                  RS @{thm eq_reflection})
                val _ = if Thm.term_of (Thm.lhs_of theorem) aconv expression then ()
                  else error "Guard publication lost period/residue/shift identity"
                val bits = Thm.term_of (Thm.rhs_of theorem)
                val trim_equation_key = trim_key bits
                val _ = (case mask_trim bits of
                  SOME existing => ignore (validate_equation trim_equation_key existing)
                | NONE =>
                    let
                      val trim = (@{thm comma_mask_phase_class_bounded} OF
                        [theorem RS @{thm meta_eq_to_obj_eq}]) RS @{thm eq_reflection}
                    in ignore (publish_trim bits trim) end)
                val _ = if period = 1 andalso shift = 0 andalso residue = 0 then
                  full_word := SOME (certify (Thm.transitive
                    (Thm.symmetric (@{thm comma_guard_full_phase} RS @{thm eq_reflection})) theorem))
                  else ()
                val _ = classes := Termtab.update (expression, theorem) (!classes)
                val _ = class_publications := !class_publications + 1
                val _ = retained := !retained + 1
              in theorem end
            end) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
          val _ = if Exn.is_exn result then failures := !failures + 1 else ()
        in Exn.release result end
      fun stats () = {attempts = !attempts, hits = !hits, joins = !joins, normalizations = !normalizations,
        failures = !failures, retained = !retained, class_publications = !class_publications}
      fun report () = "packed_trim_seeds=" ^ Int.toString (!trim_seeds) ^
        " packed_num_nodes=" ^ Int.toString (!packed_num_nodes) ^
        " packed_num_conversions=" ^ Int.toString (!packed_num_conversions) ^
        " packed_num_failures=" ^ Int.toString (!packed_num_failures) ^
        " packed_num_retained=0 packed_num_evicted=0" ^
        " packed_num_limit=" ^ Int.toString packed_num_capacity ^
        " packed_root_limit=" ^ Int.toString packed_root_capacity ^
        " packed_total_retained=" ^ Int.toString (Termtab.size (!packed_memo)) ^
        " packed_total_limit=" ^ Int.toString max_nodes ^
        " packed_full_hits=" ^ Int.toString (!full_hits) ^
        " packed_full_missing_bounds=" ^ Int.toString (!full_missing_bounds) ^
        " packed_publication_reuses=" ^ Int.toString (!packed_publication_reuses) ^
        " packed_lookups=" ^ Int.toString (!packed_lookups) ^
        " packed_hits=" ^ Int.toString (!packed_hits) ^
        " packed_misses=" ^ Int.toString (!packed_misses) ^
        " packed_identities=" ^ Int.toString (!packed_identities) ^
        " packed_failures=" ^ Int.toString (!packed_failures) ^
        " packed_retained=" ^ Int.toString (Termtab.size (!packed_memo)) ^
        " packed_limit=" ^ Int.toString max_nodes ^
        " packed_evicted=" ^ Int.toString (!packed_evicted) ^
        " packed_ms=" ^ LargeInt.toString (Time.toMilliseconds (!packed_elapsed)) ^
        " guard_nodes=" ^ Int.toString (!retained) ^
        " guard_class_publications=" ^ Int.toString (!class_publications) ^
        " guard_attempts=" ^ Int.toString (!attempts) ^
        " guard_hits=" ^ Int.toString (!hits) ^
        " guard_joins=" ^ Int.toString (!joins) ^
        " guard_normalizations=" ^ Int.toString (!normalizations) ^
        " guard_join_ms=" ^ LargeInt.toString (Time.toMilliseconds (!join_elapsed)) ^
        " guard_rotate_ms=" ^ LargeInt.toString (Time.toMilliseconds (!rotate_elapsed)) ^
        " guard_failures=" ^ Int.toString (!failures) ^
        " guard_inclusive_ms=" ^ LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {guard = guard, mask_and = mask_and, mask_or = mask_or, mask_rotate = mask_rotate,
      mask_trim = mask_trim,
      stats = stats, report = report, certification = certification,
      packed_stats = fn () => ({lookups = !packed_lookups, hits = !packed_hits,
        misses = !packed_misses, failures = !packed_failures,
        num_nodes = !packed_num_nodes, num_conversions = !packed_num_conversions,
        num_failures = !packed_num_failures,
        num_retained = 0, num_evicted = 0, num_limit = packed_num_capacity,
        total_retained = Termtab.size (!packed_memo),
        total_limit = max_nodes,
        retained = Termtab.size (!packed_memo), evicted = !packed_evicted,
        full_hits = !full_hits, full_missing_bounds = !full_missing_bounds,
        publication_reuses = !packed_publication_reuses}: packed_stats),
      packed_context = packed} end
end
