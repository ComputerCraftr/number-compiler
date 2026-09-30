(* Proof-producing reachable-sector discovery and bottom-up publication.
   Host integers select syntax and proof trees only; all masks and outcome
   claims are kernel theorems. *)
structure Comma_Sector_Mask_Constructor =
struct
  structure Key = Table(type key = int * int val ord = prod_ord int_ord int_ord)
  type part = {outcome: term, bits: term, value: IntInf.int, width: int, theorem: thm}
  type row = {source: int * int, rows: term, count: int, parts: part list, theorem: thm}
  datatype destination = Stop | Cross of thm | Child of int * int * thm
  type clause = {k: int, move: term, equation: thm, destination: destination}
  type plan = {period: int, period_equation: thm, clauses: clause list}
  fun make ctxt {max_rows, max_clauses, max_guard_nodes, max_operations} =
    let
      val _ = if 1 <= max_rows andalso max_rows <= 900 andalso
          1 <= max_operations then () else error "Invalid sector constructor budgets"
      val clauses = Comma_Sector_Response_Check.make ctxt {max_clauses=max_clauses}
      val guards = Comma_Sector_Guards.make ctxt {max_nodes=max_guard_nodes}
      (* Crossing ignores endpoint headroom and target offset. Never import
         endpoint/sector evaluation rules here: clauses already own that work. *)
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_round_crossing_def prod.case comma_finite_position.case}
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      (* The full word is another checked binary guard construction; expanding
         mask 924 by unary bit recursion is deliberately excluded. *)
      val full_equation = certify (Thm.transitive
        (Thm.symmetric (@{thm comma_guard_full_phase} RS @{thm eq_reflection}))
        (#guard guards 1 0 0))
      val memo = Unsynchronized.ref (Key.empty: row Key.table)
      val plans = Unsynchronized.ref (Key.empty: plan Key.table)
      val discoveries = Unsynchronized.ref 0
      val discovery_failures = Unsynchronized.ref 0
      val attempts = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val operations = Unsynchronized.ref 0
      val intersections = Unsynchronized.ref 0
      val joins = Unsynchronized.ref 0
      val branch_attempts = Unsynchronized.ref 0
      val max_period = Unsynchronized.ref 0
      val singleton_constructions = Unsynchronized.ref 0
      val singleton_retained = Unsynchronized.ref 0
      val zero_singletons = Unsynchronized.ref 0
      val transports = Unsynchronized.ref 0
      val forwarding_aliases = Unsynchronized.ref 0
      val intersection_tests = Unsynchronized.ref 0
      val intersection_operand_bits = Unsynchronized.ref 0
      val scheduled_omissions = Unsynchronized.ref 0
      val omission_budget = Unsynchronized.ref 0
      val injected_omissions = Unsynchronized.ref 0
      val template_memo = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val template_attempts = Unsynchronized.ref 0
      val template_hits = Unsynchronized.ref 0
      val template_failures = Unsynchronized.ref 0
      val merges = Unsynchronized.ref 0
      val assembly_input_rows = Unsynchronized.ref 0
      val assembly_max_input_rows = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val admissions = Unsynchronized.ref 0
      val admission_elapsed = Unsynchronized.ref Time.zeroTime
      val merge_elapsed = Unsynchronized.ref Time.zeroTime
      val transport_elapsed = Unsynchronized.ref Time.zeroTime
      val progress_enabled = getenv "COMMA_PROFILE_LOG" <> ""
      val progress_started = Time.now ()
      fun progress stage (f,x) = if progress_enabled then
        Comma_Fast_Kernel.report ("sector_stage=" ^ stage ^
          " source=" ^ Int.toString f ^ "," ^ Int.toString x ^
          " plans=" ^ Int.toString(Key.size(!plans)) ^
          " rows=" ^ Int.toString(Key.size(!memo)) ^
          " operations=" ^ Int.toString(!operations) ^
          " branches=" ^ Int.toString(!branch_attempts) ^
          " transports=" ^ Int.toString(!transports) ^
          " merges=" ^ Int.toString(!merges) ^
          " elapsed_ms=" ^ LargeInt.toString
            (Time.toMilliseconds(Time.-(Time.now(),progress_started)))) else ()
      fun timed clock operation =
        let val started = Time.now ()
            val result = Exn.capture operation ()
            val _ = clock := Time.+ (!clock,Time.- (Time.now (),started))
        in Exn.release result end
      fun milliseconds clock = LargeInt.toString (Time.toMilliseconds (!clock))
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun step () = (operations := !operations + 1;
        if !operations <= max_operations then () else error "Sector operation budget exhausted")
      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name,value) => ((name,0),Thm.cterm_of ctxt value)) bindings) theorem
      (* At most four checked rule templates per leading sector. Normalize
         Suc/numeral syntax before inserting any 924-bit guard or source offset. *)
      fun rule_template f tag theorem =
        let val key=4*(f-1)+tag in
          case Inttab.lookup (!template_memo) key of
            SOME template => (template_hits := !template_hits+1; template)
          | NONE =>
              let
                val _ = template_attempts := !template_attempts+1
                val _ = step ()
                val result = Exn.capture (fn () => Simplifier.full_simplify
                  (Comma_Entry_Arithmetic.numeral_context ctxt)
                  (instantiate [("f",nat f)] theorem)) ()
                val _ = if Exn.is_exn result then template_failures := !template_failures+1 else ()
                val template = Exn.release result
                val _ = template_memo := Inttab.update (key,template) (!template_memo)
              in template end
        end
      fun evaluate expression = (step (); certify
        (Simplifier.rewrite arithmetic (Thm.cterm_of ctxt expression)))
      (* This closed probe deliberately leaves endpoint arguments and the
         target offset undefined. A crossing proof must discard those fields,
         not evaluate the endpoint function. No endpoint rule is in arithmetic. *)
      val opaque_crossing = @{term "comma_round_crossing
        (Comma_Near 9 0 (comma_entry_alphabet_endpoint undefined undefined undefined))
        (Comma_Entry 1 1 undefined)"}
      fun crossing_probe () =
        let
          val theorem = evaluate (HOLogic.mk_Trueprop opaque_crossing)
          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv HOLogic.mk_Trueprop opaque_crossing
              andalso Thm.term_of (Thm.rhs_of theorem) aconv @{prop True}
            then () else error "Restricted crossing context evaluated or retained opaque endpoint fields"
        in theorem end
      fun truth expression =
        let val equation = evaluate (HOLogic.mk_Trueprop expression)
        in if Thm.term_of (Thm.rhs_of equation) aconv @{prop True} then
          certify (Thm.equal_elim (Thm.symmetric equation) @{thm TrueI})
        else error "Sector admission arithmetic did not prove True" end
      (* Higher-order rule composition can retain the guard identity
         (member bits r ==> member bits r) as a premise. Discharge it by
         assumption, never by admitting an open certificate. *)
      fun close_identities theorem =
        if Thm.nprems_of theorem = 0 then theorem
        else Goal.prove ctxt [] [] (Thm.concl_of theorem)
          (fn {context,...} => resolve_tac context [theorem] 1 THEN
            ALLGOALS (assume_tac context))
      val append_nil = @{thm append_Nil} RS @{thm eq_reflection}
      val append_cons = @{thm append_Cons} RS @{thm eq_reflection}
      fun append_conv ct =
        (case Thm.term_of ct of
          Const (name,_) $ left $ _ =>
            if name = @{const_name append} then
              (case left of
                Const (nil_name,_) => if nil_name = @{const_name Nil}
                  then Conv.rewr_conv append_nil ct else error "Malformed append left list"
              | Const (cons,_) $ _ $ _ => if cons = @{const_name Cons}
                  then (Conv.rewr_conv append_cons then_conv Conv.arg_conv append_conv) ct
                  else error "Malformed append left spine"
              | _ => error "Nonexplicit append left list")
            else error "Unexpected append conversion root"
        | _ => error "Malformed append conversion term")
      fun flatten_conv ct =
        (case Thm.term_of ct of
          Const (name,_) $ _ $ _ =>
            if name = @{const_name append} then
              (Conv.combination_conv (Conv.arg_conv flatten_conv) flatten_conv
                then_conv append_conv) ct
            else Conv.all_conv ct
        | _ => Conv.all_conv ct)
      fun admit theorem = timed admission_elapsed (fn () =>
        (admissions := !admissions + 1; step (); certify (close_identities theorem)))
      fun object equation = equation RS @{thm meta_eq_to_obj_eq}
      fun shape theorem =
        (case strip_comb (HOLogic.dest_Trueprop (Thm.prop_of theorem)) of
          (Const (name,_),[source,scope,rows]) =>
            if name = @{const_name comma_sector_rows_refine} then (source,scope,rows)
            else error "Unexpected sector certificate predicate"
        | _ => error "Malformed sector certificate")
      fun singleton theorem =
        let
          val _ = singleton_constructions := !singleton_constructions + 1
          val (_,scope,rows) = shape theorem
          val (outcome,bits) = HOLogic.dest_prod (the_single (HOLogic.dest_list rows))
          val (typ,value) = HOLogic.dest_number bits
          val _ = if typ = @{typ nat} andalso value >= 0 andalso scope aconv bits
            then () else error "Singleton certificate scope is not its checked numeral mask"
          val integer = IntInf.fromInt value
          val width = if value=0 then 0 else size (IntInf.fmt StringCvt.BIN integer)
        in {outcome=outcome,bits=bits,value=integer,width=width,theorem=theorem}: part end
      (* Exact result terms index the work queue, never a projected live fiber.
         Duplicate merging touches exactly two singleton rows, not a growing
         list. Zero omission uses a normalized closed singleton certificate. *)
      fun add_part (part: part) table =
        if snd (HOLogic.dest_number (#bits part)) = 0 then
          (zero_singletons := !zero_singletons + 1; table)
        else
          (case Termtab.lookup table (#outcome part) of
            NONE => Termtab.update (#outcome part,part) table
          | SOME previous => timed merge_elapsed (fn () =>
              let
                val _ = merges := !merges + 1
                val _ = joins := !joins + 1
                val {value=_,theorem=mask} = #mask_or guards (#bits previous) (#bits part)
                val merged = singleton (admit (@{thm comma_sector_rows_merge_singletons} OF
                  [#theorem previous,#theorem part,object mask]))
              in Termtab.update (#outcome part,merged) table end))
      fun full_number () =
        let val _ = step ()
            val bits = Thm.term_of (Thm.rhs_of full_equation)
            val _ = HOLogic.dest_number bits
        in bits end
      val full = full_number ()
      fun crossing_fact f x k target =
        let
          val near = @{term Comma_Near} $ nat f $ nat 0 $
            (@{term comma_entry_alphabet_endpoint} $ nat f $ nat x $ nat k)
          val crossing = @{term comma_round_crossing} $ near $ target
          val decision = evaluate (HOLogic.mk_Trueprop crossing)
        in
          if Thm.term_of (Thm.rhs_of decision) aconv @{prop True} then
            (true,certify (Thm.equal_elim (Thm.symmetric decision) @{thm TrueI}))
          else if Thm.term_of (Thm.rhs_of decision) aconv @{prop False} then
            let
              val source = Thm.lhs_of decision
              val contradiction = Thm.equal_elim decision (Thm.assume source)
              val implication = Thm.implies_intr source contradiction
              val negative = Goal.prove ctxt [] []
                (HOLogic.mk_Trueprop (HOLogic.mk_not crossing))
                (fn {context,...} => resolve_tac context [@{thm notI}] 1 THEN
                  resolve_tac context [implication] 1 THEN assume_tac context 1)
            in (false,certify negative) end
          else error "Sector crossing decision did not normalize to Boolean"
        end
      fun discover_row (f,x) =
        let
          val _ = progress "discover_start" (f,x)
          val _ = discoveries := !discoveries + 1
          val _ = step ()
          val _ = if Key.size (!plans) < max_rows then () else error "Sector discovery budget exhausted"
          val {value=period,equation=period_equation} = #period clauses f x
          val _ = max_period := Int.max (!max_period,period)
          fun branch k =
            let
              val _ = branch_attempts := !branch_attempts + 1
              val _ = step ()
              val {move,equation} = #branch clauses f x k
              val (head,args) = strip_comb move
              val name = (case head of Const(n,_) => n | _ => error "Open sector move")
              val destination =
                if member (op =) [@{const_name Comma_Fork},@{const_name Comma_Landmine}] name
                then Stop
                else if name = @{const_name Comma_Next} then
                  let
                    val target = the_single args
                    val (crossing,fact) = crossing_fact f x k target
                  in if crossing then Cross fact else
                    let
                      val (target_head,target_args) = strip_comb target
                      val _ = if target_head = @{term Comma_Entry} then ()
                        else error "Noncrossing target is not Entry"
                      val [tf,td,tx] = map (snd o HOLogic.dest_number) target_args
                      val _ = if tf=f+1 andalso tf<=9 andalso td=0 andalso tx<=98
                        then () else error "Nonchronological or inadmissible sector edge"
                    in Child (tf,tx,fact) end end
                else error "Invalid sector branch cannot be published"
            in {k=k,move=move,equation=equation,destination=destination}: clause end
          val result = {period=period,period_equation=period_equation,
            clauses=map branch (0 upto (period-1))}: plan
          val _ = plans := Key.update ((f,x),result) (!plans)
          val _ = progress "discover_done" (f,x)
        in result end
      fun publish_regular (key as (f,x)) (plan: plan) =
        let
          val _ = progress "publish_start" key
          val _ = attempts := !attempts + 1
          val _ = step ()
          val sector = map truth
            [HOLogic.mk_binrel @{const_name less_eq} (nat 1,nat f),
             HOLogic.mk_binrel @{const_name less_eq} (nat f,nat 9),
             HOLogic.mk_binrel @{const_name less_eq} (nat x,nat 98)]
          val period = #period plan
          val period_fact = object (Thm.symmetric (#period_equation plan))
          fun branch (clause: clause) =
            let
              val k = #k clause
              val _ = step ()
              val guard_eq = #guard guards period 919 k
              val bits = Thm.term_of (Thm.rhs_of guard_eq)
              val guard_value = IntInf.fromInt (snd (HOLogic.dest_number bits))
              val guard_width = size (IntInf.fmt StringCvt.BIN guard_value)
              val phase = instantiate
                [("f",nat f),("x",nat x),("period",nat period),("k",nat k),("bits",bits)]
                @{thm comma_sector_guard_phase_checked} OF [period_fact,object guard_eq]
              fun rule tag th = instantiate [("x",nat x),("k",nat k),("bits",bits)]
                (rule_template f tag th)
              val premises = sector @ [phase,object (#equation clause)]
            in case #destination clause of
              Stop =>
                let val (Const(name,_),_) = strip_comb (#move clause)
                    val (tag,th) = if name = @{const_name Comma_Fork}
                      then (0,@{thm comma_sector_mask_fork}) else (1,@{thm comma_sector_mask_landmine})
                in [singleton (admit (rule tag th OF premises))] end
            | Cross fact => [singleton (admit (rule 2 @{thm comma_sector_mask_cross} OF (premises@[fact])))]
            | Child (tf,tx,fact) =>
                let
                  val child = (case Key.lookup (!memo) (tf,tx) of SOME row => row
                    | NONE => error "Bottom-up publication lacks a checked child row")
                  val transport_rule = rule 3 @{thm comma_sector_mask_successor_singleton}
                  fun selected (component: part) =
                    let
                      val _ = intersection_tests := !intersection_tests + 1
                      val _ = intersection_operand_bits := !intersection_operand_bits +
                        guard_width + #width component
                      val _ = step ()
                      (* Scheduling supplies no proof premise. Incorrect omissions
                         fail the checked full-scope publication test below. *)
                      val positive = IntInf.andb (guard_value,#value component) <> 0
                      val injected = positive andalso !omission_budget <> 0
                      val _ = if injected then
                        (injected_omissions := !injected_omissions+1;
                         if !omission_budget > 0 then omission_budget := !omission_budget-1 else ())
                        else ()
                      val keep = positive andalso not injected
                      val _ = if keep then () else scheduled_omissions := !scheduled_omissions + 1
                    in keep end
                  fun transport (component: part) = timed transport_elapsed (fn () =>
                    let
                      val _ = transports := !transports + 1
                      val _ = intersections := !intersections + 1
                      val {value=_,theorem=mask} = #mask_and guards bits (#bits component)
                    in singleton (admit (transport_rule OF
                      (premises @ [fact,#theorem component,object mask]))) end)
                in map transport (filter selected (#parts child)) end
            end
          val parts_table = fold
            (fn clause => fn table => fold add_part (branch clause) table)
            (#clauses plan) (Termtab.empty: part Termtab.table)
          val parts = map snd (Termtab.dest parts_table)
          val pieces = map (fn (part: part) => (#theorem part,1,#bits part)) parts
          fun join (left,left_count,a) (right,right_count,b) =
            let
              val input_count = left_count+right_count
              val _ = joins := !joins + 1
              val _ = assembly_input_rows := !assembly_input_rows + input_count
              val _ = assembly_max_input_rows := Int.max (!assembly_max_input_rows,input_count)
              val {value,theorem=mask} = #mask_or guards a b
            in (admit (@{thm comma_sector_rows_join_checked} OF [left,right,object mask]),input_count,value) end
          fun pairs (left::right::rest) = join left right :: pairs rest | pairs rest = rest
          fun assemble [piece] = piece
            | assemble [] = error "Empty sector phase partition"
            | assemble pieces = assemble (pairs pieces)
          val (raw,count,_) = assemble pieces
          (* One structural conversion per published row. Existing pair terms,
             masks and source function are untouched. *)
          val theorem = certify (Conv.fconv_rule
            (Conv.arg_conv (Conv.arg_conv flatten_conv)) raw)
          val (source,scope,rows) = shape theorem
          val expected = @{term comma_sector_mask_value} $ nat f $ nat x
          val _ = if source aconv expected andalso scope aconv full then ()
            else error "Sector theorem source or full coverage does not match its key"
          val _ = forall (fn pair => let val (_,bits)=HOLogic.dest_prod pair
            in snd(HOLogic.dest_number bits)>0 end) (HOLogic.dest_list rows)
            orelse error "Sector assembly retained an empty or unresolved mask"
          val _ = if !singleton_retained + count <= max_operations then ()
            else error "Retained singleton theorem budget exhausted"
          val answer = {source=key,rows=rows,count=count,parts=parts,theorem=theorem}: row
          val _ = memo := Key.update (key,answer) (!memo)
          val _ = singleton_retained := !singleton_retained + count
          val _ = progress "publish_done" key
          val _ = if Key.size (!memo) <= 4 orelse Key.size (!memo) mod 16=0 then
            writeln ("sector_progress rows=" ^ Int.toString(Key.size(!memo)) ^
              " source=" ^ Int.toString f ^ "," ^ Int.toString x ^
              " operations=" ^ Int.toString(!operations) ^
              " singleton_retained=" ^ Int.toString(!singleton_retained) ^
              " transports=" ^ Int.toString(!transports) ^ " merges=" ^ Int.toString(!merges) ^
              " admission_ms=" ^ milliseconds admission_elapsed ^
              " transport_inclusive_ms=" ^ milliseconds transport_elapsed ^
              " merge_inclusive_ms=" ^ milliseconds merge_elapsed) else ()
        in () end
      fun publish key (plan: plan) =
        (case (#period plan,#clauses plan) of
          (1,[clause]) => (case #destination clause of
            Child(tf,tx,crossing) =>
              if !omission_budget <> 0 then publish_regular key plan else
              let
                val (f,x)=key
                val _ = progress "forward_start" key
                val _ = attempts := !attempts+1
                val _ = step ()
                val child = (case Key.lookup (!memo) (tf,tx) of SOME row => row
                  | NONE => error "Forwarding publication lacks a checked child")
                val sector = map truth
                  [HOLogic.mk_binrel @{const_name less_eq} (nat 1,nat f),
                   HOLogic.mk_binrel @{const_name less_eq} (nat f,nat 9),
                   HOLogic.mk_binrel @{const_name less_eq} (nat x,nat 98)]
                val rule = Simplifier.full_simplify
                  (Comma_Entry_Arithmetic.numeral_context ctxt)
                  (instantiate [("f",nat f),("x",nat x),("y",nat tx)]
                    @{thm comma_sector_mask_period_one_forward})
                val equal = admit (rule OF
                  (sector@[object (#period_equation plan),object (#equation clause),crossing]))
                fun rebind theorem = admit (@{thm comma_sector_rows_rebind} OF [equal,theorem])
                val theorem = rebind (#theorem child)
                val (source,scope,rows)=shape theorem
                val expected = @{term comma_sector_mask_value} $ nat f $ nat x
                val _ = if source aconv expected andalso scope aconv full
                    andalso rows aconv #rows child then ()
                  else error "Forwarding lost source authority or full coverage"
                fun bind_part (part: part) =
                  {outcome= #outcome part,bits= #bits part,value= #value part,
                   width= #width part,theorem=rebind (#theorem part)}: part
                val count= #count child
                val _ = if !singleton_retained+count <= max_operations then ()
                  else error "Forwarded singleton theorem budget exhausted"
                val parts = map bind_part (#parts child)
                val answer = {source=key,rows=rows,count=count,parts=parts,theorem=theorem}: row
                val _ = memo := Key.update (key,answer) (!memo)
                val _ = singleton_retained := !singleton_retained+count
                val _ = forwarding_aliases := !forwarding_aliases+1
                val _ = progress "forward_done" key
              in () end
          | _ => publish_regular key plan)
        | _ => publish_regular key plan)
      fun ensure roots = timed elapsed (fn () =>
        let
          val seen = Unsynchronized.ref (Key.empty: unit Key.table)
          fun visit (key as (f,x)) =
            let
              val _ = lookups := !lookups + 1
              val _ = if 1<=f andalso f<=9 andalso 0<=x andalso x<=98
                then () else error "Sector key outside f=1..9, x=0..98"
            in if Key.defined (!seen) key orelse Key.defined (!memo) key then hits := !hits+1
              else
                let
                  val _ = seen := Key.update (key,()) (!seen)
                  val result = Exn.capture (fn () =>
                    case Key.lookup (!plans) key of SOME plan => plan | NONE => discover_row key) ()
                  val _ = if Exn.is_exn result then discovery_failures := !discovery_failures+1 else ()
                  val plan = Exn.release result
                  fun child (clause: clause) = (case #destination clause of
                    Child(tf,tx,_) => visit(tf,tx) | _ => ())
                in List.app child (#clauses plan) end
            end
          val _ = List.app visit roots
          (* Key order is lexicographic (f,x); reversed order guarantees every
             f+1 child is already published. Only discovered roots/edges appear. *)
          fun publish_key (key,()) =
            let val result = Exn.capture (fn () => publish key (the(Key.lookup(!plans)key))) ()
                val _ = if Exn.is_exn result then failures := !failures+1 else ()
            in Exn.release result end
        in List.app publish_key (rev(Key.dest(!seen))) end)
      fun lookup key = (case Key.lookup (!memo) key of SOME row => row
        | NONE => error "Requested sector row was not published")
      fun word f x = (ensure [(f,x)]; lookup(f,x))
      (* Host selection of representatives is not an orbit proof. Each returned
         row still certifies its exact raw offset. Quotient admission is separate. *)
      fun representatives () =
        let fun orbit x = let val d=x mod 10 in ((x-(5*d*d-4*d)) mod 460) div 10 end
        in map (fn i => the (find_first (fn x => orbit x=i) (0 upto 90))) (0 upto 45) end
      fun base_words () =
        let val roots=map (fn x => (1,x)) (representatives ())
        in ensure roots; map lookup roots end
      fun stats () = {lookups= !lookups,hits= !hits,attempts= !attempts,
        failures= !failures,retained=Key.size (!memo),operations= !operations,
        discoveries= !discoveries,discovery_failures= !discovery_failures,plans=Key.size(!plans),
        intersections= !intersections,joins= !joins,
        branch_attempts= !branch_attempts,max_period= !max_period,
        singleton_constructions= !singleton_constructions,
        singleton_retained= !singleton_retained,zero_singletons= !zero_singletons,
        transports= !transports,merges= !merges,forwarding_aliases= !forwarding_aliases,
        intersection_tests= !intersection_tests,intersection_operand_bits= !intersection_operand_bits,
        scheduled_omissions= !scheduled_omissions,injected_omissions= !injected_omissions,
        template_attempts= !template_attempts,template_hits= !template_hits,
        template_failures= !template_failures,template_retained=Inttab.size(!template_memo),
        assembly_input_rows= !assembly_input_rows,assembly_max_input_rows= !assembly_max_input_rows,
        admissions= !admissions,
        admission_milliseconds=Time.toMilliseconds (!admission_elapsed),
        transport_inclusive_milliseconds=Time.toMilliseconds (!transport_elapsed),
        merge_inclusive_milliseconds=Time.toMilliseconds (!merge_elapsed)}
      fun report () = "sector_rows=" ^ Int.toString(Key.size (!memo)) ^
        " sector_discoveries=" ^ Int.toString(!discoveries) ^
        " sector_discovery_failures=" ^ Int.toString(!discovery_failures) ^
        " sector_attempts=" ^ Int.toString(!attempts) ^ " sector_failures=" ^ Int.toString(!failures) ^
        " sector_operations=" ^ Int.toString(!operations) ^
        " sector_intersections=" ^ Int.toString(!intersections) ^
        " sector_joins=" ^ Int.toString(!joins) ^
        " sector_branch_attempts=" ^ Int.toString(!branch_attempts) ^
        " sector_max_period=" ^ Int.toString(!max_period) ^
        " sector_singleton_constructions=" ^ Int.toString(!singleton_constructions) ^
        " sector_singleton_retained=" ^ Int.toString(!singleton_retained) ^
        " sector_zero_singletons=" ^ Int.toString(!zero_singletons) ^
        " sector_forwarding_aliases=" ^ Int.toString(!forwarding_aliases) ^
        " sector_transports=" ^ Int.toString(!transports) ^
        " sector_intersection_tests=" ^ Int.toString(!intersection_tests) ^
        " sector_intersection_operand_bits=" ^ Int.toString(!intersection_operand_bits) ^
        " sector_scheduled_omissions=" ^ Int.toString(!scheduled_omissions) ^
        " sector_injected_omissions=" ^ Int.toString(!injected_omissions) ^
        " sector_template_attempts=" ^ Int.toString(!template_attempts) ^
        " sector_template_hits=" ^ Int.toString(!template_hits) ^
        " sector_template_failures=" ^ Int.toString(!template_failures) ^
        " sector_template_retained=" ^ Int.toString(Inttab.size(!template_memo)) ^
        " sector_merges=" ^ Int.toString(!merges) ^
        " sector_assembly_input_rows=" ^ Int.toString(!assembly_input_rows) ^
        " sector_assembly_max_input_rows=" ^ Int.toString(!assembly_max_input_rows) ^
        " sector_admissions=" ^ Int.toString(!admissions) ^
        " sector_admission_ms=" ^ milliseconds admission_elapsed ^
        " sector_transport_inclusive_ms=" ^ milliseconds transport_elapsed ^
        " sector_merge_inclusive_ms=" ^ milliseconds merge_elapsed ^
        " sector_request_ms=" ^ LargeInt.toString(Time.toMilliseconds(!elapsed)) ^
        " " ^ #report clauses () ^ " " ^ #report guards ()
    in {word=word,base_words=base_words,representatives=representatives,
      stats=stats,report=report,certification=certification,crossing_probe=crossing_probe,
      full_mask=full_equation,
      set_omission_budget=fn budget =>
        if budget >= ~1 then omission_budget := budget else error "Omission budget must be -1 or nonnegative"} end
end
