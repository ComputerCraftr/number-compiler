structure Comma_Sector_Response_Check =
struct
  type branch = {move: term, equation: thm}
  type period_result = {value: int, equation: thm}

  fun natural term =
    (case try HOLogic.dest_number term of
      SOME (typ, n) => typ = @{typ nat} andalso n >= 0
    | NONE => can HOLogic.dest_nat term)
  fun position term =
    (case strip_comb term of
      (Const (name, _), [f, d, x]) =>
        member (op =) [@{const_name Comma_Entry}, @{const_name Comma_Near}] name
          andalso forall natural [f, d, x]
    | _ => false)
  fun move term =
    (case strip_comb term of
      (Const (name, _), []) => name = @{const_name Comma_Invalid}
    | (Const (name, _), [target]) =>
        (name = @{const_name Comma_Next} andalso position target) orelse
        (name = @{const_name Comma_Landmine} andalso natural target)
    | (Const (name, _), [a, d]) =>
        name = @{const_name Comma_Fork} andalso natural a andalso natural d
    | _ => false)
  (* Shape and complete typed source identity are checked before certification
     and publication. This check has no cache authority of its own. *)
  fun validate_branch_equation expression equation =
    let
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv expression then ()
        else error "Sector branch theorem does not bind its full source key"
      val _ = if Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) then ()
        else error "Sector branch theorem has unproved premises or hypotheses"
      val result = Thm.term_of (Thm.rhs_of equation)
      val _ = if move result then ()
        else error "Sector branch did not normalize to a closed move"
    in {move = result, equation = equation}: branch end

  fun make ctxt {max_clauses} =
    let
      val _ = if 1 <= max_clauses andalso max_clauses <= 8192 then ()
        else error "Sector clause capacity must lie in 1..8192"
      val kernel = Comma_Fast_Kernel.make ctxt
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val memo = Unsynchronized.ref (Termtab.empty: branch Termtab.table)
      val canonical_near = Unsynchronized.ref (Termtab.empty: branch Termtab.table)
      val canonical_near_lookups = Unsynchronized.ref 0
      val canonical_near_hits = Unsynchronized.ref 0
      val canonical_near_misses = Unsynchronized.ref 0
      val canonical_near_attempts = Unsynchronized.ref 0
      val canonical_near_failures = Unsynchronized.ref 0
      val period_memo = Unsynchronized.ref (Termtab.empty: period_result Termtab.table)
      val canonical_periods = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val canonical_period_hits = Unsynchronized.ref 0
      val canonical_period_attempts = Unsynchronized.ref 0
      val period_attempts = Unsynchronized.ref 0
      val period_hits = Unsynchronized.ref 0
      val period_failures = Unsynchronized.ref 0
      val period_retained = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val attempts = Unsynchronized.ref 0
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun evaluate expression =
        certify (Simplifier.rewrite (#context kernel) (Thm.cterm_of ctxt expression))
      (* Period proofs have their own explicit max_clauses cap. *)
      fun period f x =
        let
          val outcome = Exn.capture (fn () =>
            let
              val _ = if 1 <= f andalso f <= 9 andalso 0 <= x andalso x <= 98 then ()
                else error "Sector period requires f=1..9 and x=0..98"
              val expression = @{term comma_short_period} $
                (@{term comma_finite_period_fast} $ nat f $
                  (@{term "\<lambda>x::nat. x mod 10"} $ nat x))
            in case Termtab.lookup (!period_memo) expression of
              SOME answer => (period_hits := !period_hits + 1; answer)
            | NONE =>
              let
                val _ = if !period_retained < max_clauses then ()
                  else error "Sector period retention budget exhausted"
                val _ = period_attempts := !period_attempts + 1
                val digit_term = @{term "\<lambda>x::nat. x mod 10"} $ nat x
                val digit_equation = certify (Simplifier.rewrite
                  (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.cterm_of ctxt digit_term))
                val prefix = @{term comma_finite_period_fast} $ nat f
                val binding = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt @{term comma_short_period}))
                  (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt prefix)) digit_equation)
                val canonical = Thm.term_of (Thm.rhs_of binding)
                val canonical_equation = (case Termtab.lookup (!canonical_periods) canonical of
                    SOME theorem => (canonical_period_hits := !canonical_period_hits + 1; theorem)
                  | NONE =>
                    let
                      val _ = if Termtab.size (!canonical_periods) < max_clauses then ()
                        else error "Canonical period retention budget exhausted"
                      val _ = canonical_period_attempts := !canonical_period_attempts + 1
                      val theorem = evaluate canonical
                      val (_, checked) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem))
                      val _ = if member (op =) [1,2,3,6,22,28] checked andalso
                          Thm.term_of (Thm.lhs_of theorem) aconv canonical then ()
                        else error "Canonical period did not produce a checked short period"
                      val _ = canonical_periods := Termtab.update (canonical,theorem) (!canonical_periods)
                    in theorem end)
                val equation = certify (Thm.transitive binding canonical_equation)
                val _ = if Thm.term_of (Thm.lhs_of equation) aconv expression then ()
                  else error "Canonical period lost its original source binding"
                val (_, value) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation))
                val _ = if member (op =) [1,2,3,6,22,28] value then ()
                  else error "Sector period did not return the admitted short alphabet"
                val answer = {value = value, equation = equation}
                val _ = period_memo := Termtab.update (expression, answer) (!period_memo)
                val _ = period_retained := !period_retained + 1
              in answer end
            end) ()
          val _ = if Exn.is_exn outcome then period_failures := !period_failures + 1 else ()
        in Exn.release outcome end
      fun branch f x k =
        let
          val begin = Time.now ()
          val outcome = Exn.capture (fn () =>
            let
              val _ = if 1 <= f andalso f <= 9 andalso 0 <= x andalso x <= 98
                  andalso 0 <= k andalso k < 28 then ()
                else error "Sector branch requires f=1..9, x=0..98, k=0..27"
              val endpoint = @{term comma_entry_alphabet_endpoint} $ nat f $ nat x $ nat k
              val target = @{term Comma_Near} $ nat f $ nat 0 $ endpoint
              val expression = @{term comma_fast_step} $ nat 0 $ target
              val _ = lookups := !lookups + 1
            in
              case Termtab.lookup (!memo) expression of
                SOME result => (hits := !hits + 1; result)
              | NONE =>
                  let
                    val _ = if !retained < max_clauses then ()
                      else error "Sector clause retention budget exhausted"
                    val _ = attempts := !attempts + 1
                    val admitted_period = period f x
                    val _ = if k < #value admitted_period then ()
                      else error "Sector branch phase is outside its proved short period"
                    (* Normalize the Entry endpoint while it still carries its
                       complete source equation. Only then share the Near step. *)
                    val endpoint_equation = evaluate endpoint
                    val _ = if Thm.term_of (Thm.lhs_of endpoint_equation) aconv endpoint
                        andalso natural (Thm.term_of (Thm.rhs_of endpoint_equation)) then ()
                      else error "Entry endpoint did not produce a checked closed natural"
                    val prefix = @{term Comma_Near} $ nat f $ nat 0
                    val binding = certify (Thm.combination
                      (Thm.reflexive (Thm.cterm_of ctxt (@{term comma_fast_step} $ nat 0)))
                      (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt prefix))
                        endpoint_equation))
                    val canonical = Thm.term_of (Thm.rhs_of binding)
                    val _ = canonical_near_lookups := !canonical_near_lookups + 1
                    val cached = Termtab.lookup (!canonical_near) canonical
                    val checked = (case cached of
                        SOME answer => (canonical_near_hits := !canonical_near_hits + 1; answer)
                      | NONE =>
                        let
                          val _ = canonical_near_misses := !canonical_near_misses + 1
                          val _ = if Termtab.size (!canonical_near) < max_clauses then ()
                            else error "Canonical Near retention budget exhausted"
                          val _ = canonical_near_attempts := !canonical_near_attempts + 1
                          val proof = Exn.capture (fn () =>
                            validate_branch_equation canonical (evaluate canonical)) ()
                          val _ = if Exn.is_exn proof then
                            canonical_near_failures := !canonical_near_failures + 1 else ()
                        in Exn.release proof end)
                    val equation = certify (Thm.transitive binding (#equation checked))
                    val entry = validate_branch_equation expression equation
                    (* Delay both publications until the rebound source proof
                       passes every check. Failed work publishes no Near result. *)
                    val _ = (case cached of SOME _ => () | NONE =>
                      canonical_near := Termtab.update (canonical, checked) (!canonical_near))
                    val _ = memo := Termtab.update (expression, entry) (!memo)
                    val _ = retained := !retained + 1
                  in entry end
            end) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), begin))
          val _ = if Exn.is_exn outcome then failures := !failures + 1 else ()
        in Exn.release outcome end
      fun stats () = {lookups = !lookups, hits = !hits, attempts = !attempts,
        failures = !failures, retained = !retained,
        canonical_near_lookups = !canonical_near_lookups,
        canonical_near_hits = !canonical_near_hits,
        canonical_near_misses = !canonical_near_misses,
        canonical_near_attempts = !canonical_near_attempts,
        canonical_near_failures = !canonical_near_failures,
        canonical_near_retained = Termtab.size (!canonical_near), period_attempts = !period_attempts,
        canonical_period_attempts = !canonical_period_attempts,
        canonical_period_hits = !canonical_period_hits,
        period_hits = !period_hits, period_failures = !period_failures, period_retained = !period_retained}
      fun report () = "sector_clause_lookups=" ^ Int.toString (!lookups) ^
        " sector_clause_hits=" ^ Int.toString (!hits) ^
        " sector_clause_attempts=" ^ Int.toString (!attempts) ^
        " sector_clause_failures=" ^ Int.toString (!failures) ^
        " sector_clause_retained=" ^ Int.toString (!retained) ^
        " canonical_near_lookups=" ^ Int.toString (!canonical_near_lookups) ^
        " canonical_near_hits=" ^ Int.toString (!canonical_near_hits) ^
        " canonical_near_misses=" ^ Int.toString (!canonical_near_misses) ^
        " canonical_near_attempts=" ^ Int.toString (!canonical_near_attempts) ^
        " canonical_near_failures=" ^ Int.toString (!canonical_near_failures) ^
        " canonical_near_retained=" ^ Int.toString (Termtab.size (!canonical_near)) ^
        " canonical_period_attempts=" ^ Int.toString (!canonical_period_attempts) ^
        " canonical_period_hits=" ^ Int.toString (!canonical_period_hits) ^
        " canonical_period_retained=" ^ Int.toString (Termtab.size (!canonical_periods)) ^
        " sector_period_attempts=" ^ Int.toString (!period_attempts) ^
        " sector_period_hits=" ^ Int.toString (!period_hits) ^
        " sector_period_failures=" ^ Int.toString (!period_failures) ^
        " sector_period_retained=" ^ Int.toString (!period_retained) ^
        " sector_clause_inclusive_ms=" ^ LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {branch = branch, period = period, stats = stats, report = report,
      arithmetic_stats = #stats kernel, certification = certification} end
end

(* Packed guards are assembled from a one-period certificate by binary joins.
   Host arithmetic chooses a proof tree; it supplies no bit-pattern premise. *)
structure Comma_Sector_Guards =
struct
  structure Pattern_Table = Table
  (
    type key = int * int * int
    fun ord ((a, b, c), (d, e, f)) =
      prod_ord int_ord (prod_ord int_ord int_ord) ((a, (b, c)), (d, (e, f)))
  )
  type pattern = {width: int, bits: term, theorem: thm}
  fun make ctxt {max_nodes} =
    let
      val _ = if 1 <= max_nodes andalso max_nodes <= 8192 then ()
        else error "Guard node capacity must lie in 1..8192"
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms power_numeral_even power_numeral_odd power_0 power_one_right power_Suc0_right
          dvd_eq_mod_eq_0 upt_rec list_all_Nil_iff list_all_Cons_iff}
      val packed = arithmetic addsimps
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
          comma_guard_take_num_one
          or_numerals(1,2,5,8)}
      (* One bounded arithmetic cache owns closed root equations, never source
         rows or intermediate numeral suffixes. Full typed terms are its keys. *)
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
            null (Thm.hyps_of theorem) andalso Thm.nprems_of theorem = 0
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
            val _ = if Termtab.size (!packed_memo) < max_nodes then () else
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
      val num_steps = map (fn theorem => theorem RS @{thm eq_reflection})
        @{thms and_num.simps or_num.simps}
      (* Constructor validation avoids decoding every descending suffix into
         another growing host integer. Open numeral variables are rejected. *)
      fun closed_num t =
        let fun spine (Const(name,_)) = name = @{const_name Num.num.One}
              | spine (Const(name,_) $ tail) =
                  (name = @{const_name Num.num.Bit0} orelse name = @{const_name Num.num.Bit1}) andalso spine tail
              | spine _ = false
        in fastype_of t = @{typ num} andalso spine t end
      val option_steps = map (fn theorem => theorem RS @{thm eq_reflection})
        @{thms option.map option.case}
      fun num_head (Const(name,_)) = name = @{const_name Num.num.One}
        | num_head (Const(name,_) $ _) =
            name = @{const_name Num.num.Bit0} orelse name = @{const_name Num.num.Bit1}
        | num_head _ = false
      fun sub_conversion ct =
        let
          val key = Thm.term_of ct
          val _ = packed_num_nodes := !packed_num_nodes+1
          val attempt = Exn.capture (fn () =>
                let
                  val step = Conv.rewrs_conv num_steps ct
                  fun child nested =
                    (case strip_comb(Thm.term_of nested) of
                      (Const(name,_),[_,_]) =>
                        if name = @{const_name and_num} orelse name = @{const_name or_num}
                          then sub_conversion nested else Conv.all_conv nested
                    | _ => Conv.all_conv nested)
                  val rhs = Thm.rhs_of step
                  val tail = (case strip_comb(Thm.term_of rhs) of
                      (Const(name,_),[_]) =>
                        if name = @{const_name Num.num.Bit0} orelse name = @{const_name Num.num.Bit1}
                          then Conv.arg_conv child rhs else Conv.all_conv rhs
                    | (Const(name,_),_) =>
                        if name = @{const_name map_option} orelse name = @{const_name case_option}
                          then (Conv.arg_conv child then_conv Conv.rewrs_conv option_steps
                            then_conv Conv.try_conv (Thm.beta_conversion false)) rhs
                        else Conv.all_conv rhs
                    | _ => Conv.all_conv rhs)
                  val theorem = Thm.transitive step tail
                  val result = Thm.term_of(Thm.rhs_of theorem)
                  (* Root inputs are checked constructor spines once. Recursive
                     inputs and results are constructor children of the checked
                     defining equations, so this local shape check is constant. *)
                  val valid = if fastype_of key = @{typ num} then num_head result
                    else fastype_of key = @{typ "num option"} andalso
                      (result aconv @{term "None :: num option"} orelse
                        (case result of Const(name,_) $ n =>
                          name = @{const_name Some} andalso num_head n | _=>false))
                  val _ = if valid then ()
                    else error "Packed directed conversion retained a nonconstructor result"
                in theorem end) ()
          val _ = if Exn.is_exn attempt then packed_num_failures := !packed_num_failures+1
            else packed_num_conversions := !packed_num_conversions+1
        in Exn.release attempt end
      val sub_proc = Simplifier.make_simproc ctxt
        {name="comma_closed_num_subexpression",kind=Simplifier.Simproc,
         lhss=map (Term.map_aterms
           (fn Free(name,typ)=>Var((name,0),typ) | atom=>atom))
           [@{term "and_num m n"},@{term "or_num m n"}],
         proc=fn _=>fn _=>fn ct=>
           (case strip_comb(Thm.term_of ct) of
             (_, [left,right]) => if closed_num left andalso closed_num right
               then SOME(sub_conversion ct) else NONE
           | _=>NONE),identifier=[]}
      val packed_raw = (packed delsimps @{thms and_num.simps or_num.simps})
        |> Simplifier.add_proc sub_proc
      fun packed_lookup evaluation key =
        (packed_lookups := !packed_lookups + 1;
         case Termtab.lookup (!packed_memo) key of
           SOME theorem => (packed_hits := !packed_hits + 1; theorem)
         | NONE =>
             (packed_misses := !packed_misses + 1;
              packed_publish key (checked_equation key
                (Simplifier.rewrite evaluation (Thm.cterm_of ctxt key)))))
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
        in if already_checked then validate_equation requested result
          else checked_equation requested result end)
      fun mask_and left right = mask_binary true left right
      fun mask_or left right = mask_binary false left right
      fun mask_rotate shift bits = packed_request (fn () =>
        let
          val _ = if shift >= 0 andalso closed_natural bits then ()
            else error "Mask rotation requires a nonnegative shift and closed natural word"
          val expression = @{term comma_rotate_phase} $ HOLogic.mk_number @{typ nat} shift $ bits
        in packed_lookup (packed_raw addsimps @{thms comma_rotate_phase_def}) expression end)
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
      val packed = (packed_raw delsimps
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
              val _ = if member (op =) [1, 2, 3, 6, 22, 28] period
                  andalso 0 <= residue andalso residue < period andalso shift >= 0 then ()
                else error "Guard requires a supported short period and admitted residue/shift"
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
                val trim = (@{thm comma_mask_phase_class_bounded} OF
                  [theorem RS @{thm meta_eq_to_obj_eq}]) RS @{thm eq_reflection}
                val _ = trim_seeds := !trim_seeds + 1
                val _ = packed_publish (trim_key bits) (checked_equation (trim_key bits) trim)
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
      stats = stats, report = report, certification = certification,
      packed_stats = fn () => {lookups = !packed_lookups, hits = !packed_hits,
        misses = !packed_misses, failures = !packed_failures,
        num_nodes = !packed_num_nodes, num_conversions = !packed_num_conversions,
        num_failures = !packed_num_failures,
        retained = Termtab.size (!packed_memo), evicted = !packed_evicted,
        full_hits = !full_hits, full_missing_bounds = !full_missing_bounds,
        publication_reuses = !packed_publication_reuses},
      packed_context = packed} end
end
