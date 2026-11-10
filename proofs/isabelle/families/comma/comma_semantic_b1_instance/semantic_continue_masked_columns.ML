structure Comma_Semantic_Continue_Masked_Columns =
struct
  open Comma_Semantic_Continue_Observer_Contract

  val coreT = @{typ comma_phase_core_id}
  val jobT = @{typ comma_phase_continue_job}
  val observerT = @{typ comma_continue_observer}
  val operationT = @{typ comma_crt_boolean_operation}

  type callbacks =
    {ctxt: Proof.context,
     validate_native: string -> thm -> thm,
     validate_equation: string -> term -> term -> thm -> thm,
     scalar: string -> term -> thm,
     evaluate: string -> term -> thm}

  type normalized_column =
    {actual: term,
     column: term,
     actual_admitted: thm,
     admitted: thm,
     equivalent: thm,
     conversion: thm}

  type value = Comma_Semantic_Continue_Observer_Contract.value

  type core_guard =
    {value:int, certificate:certified_column, conversion:thm}

  type core_preselection =
    {allowed:int list, guards:core_guard list, coverage:thm}

  type pullback =
    {actual: term,
     column: term,
     actual_admitted: thm,
     admitted: thm,
     equivalent: thm}

  fun number n = HOLogic.mk_number natT n

  fun apply_and left right =
    Const (@{const_name comma_crt_apply},
      operationT --> columnT --> columnT --> columnT) $
      Const (@{const_name Comma_CRT_And}, operationT) $ left $ right

  fun apply_or left right =
    Const (@{const_name comma_crt_apply},
      operationT --> columnT --> columnT --> columnT) $
      Const (@{const_name Comma_CRT_Or}, operationT) $ left $ right

  fun shift amount column =
    Const (@{const_name comma_crt_shift}, natT --> columnT --> columnT) $
      number amount $ column

  fun admitted_prop column =
    HOLogic.mk_Trueprop (@{term comma_crt_admitted} $ number 0 $ column)

  fun core_guard_term core value =
    @{term comma_core_value_guard} $ core $ number value

  fun union_term_at core amount values =
    @{term comma_continue_core_guard_union} $ core $ amount $
      HOLogic.mk_list natT (map number values)

  fun union_term core amount values = union_term_at core (number amount) values

  fun filter_core_values_term allowed values =
    let
      val setT = HOLogic.mk_setT natT
      val allowed_set = Const (@{const_name set}, HOLogic.listT natT --> setT) $
        HOLogic.mk_list natT (map number allowed)
      val predicate = Abs ("core_value",natT,
        HOLogic.mk_mem (Bound 0, allowed_set))
      val filter_const = Const (@{const_name filter},
        (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.listT natT)
    in filter_const $ predicate $ HOLogic.mk_list natT (map number values) end

  fun lift_argument_equation ctxt function argument_equation =
    Thm.combination (Thm.reflexive (Thm.cterm_of ctxt function)) argument_equation

  fun equiv_prop left right =
    HOLogic.mk_Trueprop (@{term comma_crt_equiv_check} $ left $ right)

  fun require_proposition validate label expected theorem =
    if Thm.prop_of theorem aconv expected then validate label theorem
    else error (label ^ " proves a different proposition")

  fun require_column label column =
    if fastype_of column = columnT then ()
    else error (label ^ " is not a CRT column")

  (* Propose whether two admitted literal columns have a common CRT residue.
     This walks only matching node cofactors in the four independent axes; it
     does not build an Apply proof or enumerate external clock phases. The
     separate checked coverage theorem remains the authority for pruning. *)
  fun literal_support_intersection left right =
    let
      fun dest_natural term =
        Comma_Semantic_Continue_Column_Proofs.natural_value term
      fun dest_bit term =
        (case Term.strip_comb term of
          (Const (name,_),[bit]) =>
            if name = @{const_name Comma_CRT_Bool} then
              (case bit of
                Const (bit_name,_) =>
                  if bit_name = @{const_name True} then SOME true
                  else if bit_name = @{const_name False} then SOME false
                  else NONE
              | _ => NONE)
            else NONE
        | _ => NONE)
      fun node term =
        (case Term.strip_comb term of
          (Const (name,_),[level,children]) =>
            if name = @{const_name Comma_CRT_Node} then
              (case (dest_natural level,try HOLogic.dest_list children) of
                (SOME level,SOME children) => SOME (level,children)
              | _ => error "Malformed literal CRT node during support proposal")
            else NONE
        | _ => NONE)
      fun branch label level digit column =
        (case node column of
          NONE => column
        | SOME (node_level,children) =>
            if node_level < level then
              error (label ^ " has a non-increasing CRT node level")
            else if node_level > level then column
            else if node_level >= 4 orelse digit >= length children then
              error (label ^ " has an invalid CRT node branch")
            else List.nth (children,digit))
      fun matching_width level option =
        (case option of
          SOME (node_level,children) =>
            if node_level = level then
              let val width = length children
              in
                if width > 0 then SOME width
                else error "Empty literal CRT node in support proposal"
              end
            else NONE
        | NONE => NONE)
      fun branch_width level left_node right_node =
        (case (matching_width level left_node, matching_width level right_node) of
          (SOME left_width,SOME right_width) =>
            if left_width = right_width then left_width
            else error "Same-level CRT nodes have different widths"
        | (SOME width,NONE) => width
        | (NONE,SOME width) => width
        | (NONE,NONE) => error "Selected CRT level has no matching node")
      fun visit left right =
        (case (dest_bit left,dest_bit right) of
          (SOME false,_) => false
        | (_,SOME false) => false
        | (SOME true,SOME true) => true
        | _ =>
            let
              val left_node=node left
              val right_node=node right
              val level=(case (left_node,right_node) of
                (SOME (left_level,_),SOME (right_level,_)) =>
                  Int.min (left_level,right_level)
              | (SOME (left_level,_),NONE) => left_level
              | (NONE,SOME (right_level,_)) => right_level
              | (NONE,NONE) =>
                  error "Malformed Boolean CRT leaf in support proposal")
              val _=if level<4 then ()
                else error "CRT support proposal exceeded its four axes"
              val width = branch_width level left_node right_node
            in
              List.exists (fn digit =>
                visit (branch "Left support column" level digit left)
                  (branch "Right support column" level digit right))
                (0 upto (width - 1))
            end)
    in visit left right end

  fun apply_admitted_raw (callbacks: callbacks) label operation left right
      left_admitted right_admitted =
    let
      val theorem = Goal.prove (#ctxt callbacks) [] []
        (HOLogic.mk_Trueprop
          (@{term comma_crt_admitted} $ number 0 $
            (@{term comma_crt_apply} $ operation $ left $ right)))
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_apply_admitted}] 1
          THEN resolve_tac context [left_admitted] 1
          THEN resolve_tac context [right_admitted] 1)
    in #validate_native callbacks label theorem end

  fun check_certified (callbacks: callbacks) label
      (certified: certified_column) =
    let
      val _ = require_column (label ^ " column") (#column certified)
      val admitted = require_proposition (#validate_native callbacks)
        (label ^ " admission") (admitted_prop (#column certified))
        (#admitted certified)
    in {column= #column certified, admitted=admitted}:certified_column end

  fun check_job_value validate_closed validate_native observer job amount
      (mask:mask) (result:value) =
    let
      val actual=guarded_column (#column mask)
        (job_observe_call (observer_term observer) job amount 0)
      val expected=HOLogic.mk_Trueprop
        (@{term comma_crt_equiv_check} $ actual $ #column result)
      val admitted=admitted_prop (#column result)
      val actual_admitted=admitted_prop actual
      val _=if Thm.prop_of (#equivalent result) aconv expected then ()
        else error "Continue job certificate lost its exact request"
      val _=if Thm.prop_of (#admitted result) aconv admitted then ()
        else error "Continue job certificate has a foreign column admission"
      val _=if Thm.prop_of (#actual_admitted result) aconv actual_admitted then ()
        else error "Continue job certificate has a foreign output admission"
      val _=validate_closed "Fused Continue job result" (#column result)
      val _=Comma_Semantic_Continue_Column_Proofs.require_literal_column
        "Continue result boundary" (#column result)
    in
      {column= #column result,
       admitted=validate_native "Continue job column admission" (#admitted result),
       actual_admitted=validate_native "Continue job output admission"
         (#actual_admitted result),
       equivalent=validate_native "Continue job semantic authority"
         (#equivalent result)}:value
    end

  fun mask_admitted_raw (callbacks: callbacks) label
      (mask: certified_column) column column_admitted =
    let val mask = check_certified callbacks (label ^ " mask") mask
    in apply_admitted_raw callbacks label @{term Comma_CRT_And}
      (#column mask) column (#admitted mask) column_admitted end

  fun reflexive_equiv (callbacks: callbacks) label column admitted =
    let
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " admission") (admitted_prop column) admitted
      val theorem = @{thm comma_crt_equiv_check_refl} OF [admitted]
    in require_proposition (#validate_native callbacks) label
      (equiv_prop column column) theorem end

  fun mask_equiv (callbacks: callbacks) label (mask: certified_column)
      left right equivalent =
    let
      val mask = check_certified callbacks (label ^ " mask") mask
      val mask_refl = reflexive_equiv callbacks
        (label ^ " mask reflexivity") (#column mask) (#admitted mask)
    in
      Comma_Semantic_Continue_Column_Proofs.apply_equiv
        (#ctxt callbacks) (#validate_native callbacks) label
        @{term Comma_CRT_And} (#column mask) left (#column mask) right
        mask_refl equivalent
    end

  fun propose_core_values (callbacks:callbacks) label
      (incoming:certified_column) core amount (guards:core_guard list) =
    let
      val incoming=check_certified callbacks (label ^ " incoming mask") incoming
      val _=Comma_Semantic_Continue_Column_Proofs.require_literal_column
        (label ^ " incoming mask") (#column incoming)
      fun checked_guard (guard:core_guard) =
        let
          val certificate=check_certified callbacks
            (label ^ " shifted core guard") (#certificate guard)
          val _=Comma_Semantic_Continue_Column_Proofs.require_literal_column
            (label ^ " shifted core guard") (#column certificate)
          val expected=Logic.mk_equals
            (shift amount (core_guard_term core (#value guard)),#column certificate)
          val conversion=require_proposition (#validate_native callbacks)
            (label ^ " shifted core guard conversion") expected (#conversion guard)
        in {value= #value guard,certificate=certificate,
            conversion=conversion}:core_guard end
      val guards=map checked_guard guards
    in
      map (fn (guard:core_guard) => #value guard)
        (filter (fn (guard:core_guard) =>
          literal_support_intersection (#column incoming)
            (#column (#certificate guard))) guards)
    end

  fun apply_admitted (callbacks: callbacks) label
      (left: certified_column) (right: certified_column) =
    let
      val left = check_certified callbacks (label ^ " left") left
      val right = check_certified callbacks (label ^ " right") right
      val theorem = @{thm comma_crt_guarded_and_admitted} OF
        [#admitted left, #admitted right]
    in
      require_proposition (#validate_native callbacks) label
        (admitted_prop (apply_and (#column left) (#column right))) theorem
    end

  fun shift_admitted (callbacks: callbacks) label amount
      (certified: certified_column) =
    let
      val certified = check_certified callbacks label certified
      val shifted = shift amount (#column certified)
      val goal = admitted_prop shifted
      val theorem = Goal.prove (#ctxt callbacks) [] [] goal
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_shift_admitted}] 1
          THEN resolve_tac context [#admitted certified] 1)
    in
      require_proposition (#validate_native callbacks) label
        goal theorem
    end

  fun shift_admitted_raw (callbacks: callbacks) label amount column admitted =
    let
      val _ = require_column (label ^ " input") column
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " input admission") (admitted_prop column) admitted
      val shifted = shift amount column
      val goal = admitted_prop shifted
      val theorem = Goal.prove (#ctxt callbacks) [] [] goal
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_shift_admitted}] 1
          THEN resolve_tac context [admitted] 1)
    in require_proposition (#validate_native callbacks) label goal theorem end

  fun true_mask (callbacks: callbacks) label =
    let
      val column = @{term "Comma_CRT_Bool True"}
      val admitted = #validate_native callbacks (label ^ " admission")
        @{lemma "comma_crt_admitted 0 (Comma_CRT_Bool True)" by simp}
    in {column=column, admitted=admitted}:certified_column end

  fun true_mask_equiv (callbacks: callbacks) label
      (certified: certified_column) =
    let
      val certified = check_certified callbacks label certified
      val true_column = @{term "Comma_CRT_Bool True"}
      val theorem = @{thm comma_crt_guarded_true_equiv} OF [#admitted certified]
    in
      require_proposition (#validate_native callbacks) (label ^ " True mask identity")
        (equiv_prop (apply_and true_column (#column certified)) (#column certified))
        theorem
    end

  fun symmetric_equiv (callbacks: callbacks) label left right theorem =
    let
      val theorem = require_proposition (#validate_native callbacks)
        (label ^ " input equivalence") (equiv_prop left right) theorem
      val symmetric = @{thm comma_crt_equiv_check_sym} OF [theorem]
    in
      require_proposition (#validate_native callbacks) (label ^ " symmetric equivalence")
        (equiv_prop right left) symmetric
    end

  fun normalize (callbacks: callbacks) label actual actual_admitted =
    let
      val _ = require_column (label ^ " input") actual
      val actual_admitted = require_proposition (#validate_native callbacks)
        (label ^ " input admission") (admitted_prop actual) actual_admitted
      val (column, admitted, equivalent, conversion) =
        Comma_Semantic_Continue_Column_Proofs.canonicalize_column
          (#ctxt callbacks) (#validate_native callbacks) (#scalar callbacks)
          label actual actual_admitted
      val _ = require_column (label ^ " canonical output") column
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " canonical admission") (admitted_prop column) admitted
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " canonical equivalence") (equiv_prop actual column) equivalent
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " canonical conversion") (Logic.mk_equals (actual, column)) conversion
    in
      {actual=actual, column=column, actual_admitted=actual_admitted,
       admitted=admitted, equivalent=equivalent, conversion=conversion}:
        normalized_column
    end

  (* Construct and normalize one guarded intersection.  The exact incoming
     mask remains an explicit argument and is never folded into a semantic key. *)
  fun intersect (callbacks: callbacks) label
      (mask: certified_column) (column: certified_column) =
    let
      val mask = check_certified callbacks (label ^ " mask") mask
      val column = check_certified callbacks (label ^ " operand") column
      val raw = apply_and (#column mask) (#column column)
      val raw_admitted = apply_admitted callbacks
        (label ^ " raw intersection admission") mask column
    in normalize callbacks label raw raw_admitted end

  (* Apply an incoming mask to an already-certified child result.  The result's
     equivalence is for the exact masked child observer, while `conversion`
     records the raw canonical-column rewrite for parent equation transport. *)
  fun mask_value (callbacks: callbacks) label
      (mask: certified_column) child_actual
      (child: value) =
    let
      val mask = check_certified callbacks (label ^ " mask") mask
      val _ = require_column (label ^ " child actual") child_actual
      val _ = require_column (label ^ " child canonical") (#column child)
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " child result admission")
        (admitted_prop (#column child)) (#admitted child)
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " child actual admission")
        (admitted_prop child_actual) (#actual_admitted child)
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " child equivalence")
        (equiv_prop child_actual (#column child)) (#equivalent child)
      val raw_actual = apply_and (#column mask) child_actual
      val raw_actual_admitted = apply_admitted callbacks
        (label ^ " exact masked observer admission") mask
        {column=child_actual, admitted= #actual_admitted child}
      val raw_canonical = apply_and (#column mask) (#column child)
      val raw_canonical_admitted = apply_admitted callbacks
        (label ^ " masked canonical column admission") mask
        {column= #column child, admitted= #admitted child}
      val mask_refl = require_proposition (#validate_native callbacks)
        (label ^ " mask reflexivity")
        (equiv_prop (#column mask) (#column mask))
        (@{thm comma_crt_equiv_check_refl} OF [#admitted mask])
      val child_congruence =
        Comma_Semantic_Continue_Column_Proofs.apply_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " masked child congruence")
          @{term Comma_CRT_And} (#column mask) child_actual
          (#column mask) (#column child) mask_refl (#equivalent child)
      val (column, admitted, canonical_equiv, conversion) =
        Comma_Semantic_Continue_Column_Proofs.canonicalize_column
          (#ctxt callbacks) (#validate_native callbacks) (#scalar callbacks)
          (label ^ " canonical intersection") raw_canonical
          raw_canonical_admitted
      val total_equiv =
        Comma_Semantic_Continue_Column_Proofs.trans_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " exact masked result") raw_actual raw_canonical column
          child_congruence canonical_equiv
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " exact masked result admission")
        (admitted_prop raw_actual) raw_actual_admitted
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " final masked result equivalence")
        (equiv_prop raw_actual column) total_equiv
    in
      ({column=column, admitted=admitted,
        actual_admitted=raw_actual_admitted, equivalent=total_equiv}:value,
       conversion)
    end

  (* A false support result short-circuits before child discovery.  The suffix
     stays a term supplied by the observer contract; it is never evaluated by
     this helper. *)
  fun unsupported_intersection (callbacks: callbacks) label
      (mask: certified_column) suffix suffix_admitted unsupported =
    let
      val mask = check_certified callbacks (label ^ " mask") mask
      val _ = require_column (label ^ " suffix observer") suffix
      val unsupported_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_not (@{term comma_crt_supported} $ #column mask))
      val unsupported = require_proposition (#validate_native callbacks)
        (label ^ " unsupported mask") unsupported_prop unsupported
      val suffix_admitted = require_proposition (#validate_native callbacks)
        (label ^ " suffix observer admission") (admitted_prop suffix)
        suffix_admitted
      val actual = apply_and (#column mask) suffix
      val actual_admitted = apply_admitted callbacks
        (label ^ " pruned result admission") mask
        {column=suffix, admitted=suffix_admitted}
      val false_admitted = #validate_native callbacks
        (label ^ " False column admission")
        @{lemma "comma_crt_admitted 0 (Comma_CRT_Bool False)" by simp}
      val equivalent = @{thm comma_crt_guarded_and_empty_equiv_false} OF
        [#admitted mask, suffix_admitted, unsupported]
      val equivalent = require_proposition (#validate_native callbacks)
        (label ^ " unsupported intersection pruning")
        (equiv_prop actual @{term "Comma_CRT_Bool False"}) equivalent
      val _ = require_proposition (#validate_native callbacks)
        (label ^ " pruned result admission") (admitted_prop actual)
        actual_admitted
    in
      {column= @{term "Comma_CRT_Bool False"}, admitted=false_admitted,
       actual_admitted=actual_admitted, equivalent=equivalent}:value
    end

  fun support (callbacks: callbacks) label (certified: certified_column) =
    let
      val certified = check_certified callbacks label certified
      val proposition = @{term comma_crt_supported} $ #column certified
      val theorem = #evaluate callbacks label proposition
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv proposition then ()
        else error (label ^ " changed the support query")
      val theorem = (#validate_equation callbacks) label proposition
        (Thm.term_of (Thm.rhs_of theorem)) theorem
      val rhs = Thm.term_of (Thm.rhs_of theorem)
      val supported =
        if rhs aconv @{term True} then true
        else if rhs aconv @{term False} then false
        else error (label ^ " did not reduce to a Boolean")
    in (supported, theorem) end

  fun core_values_equiv (callbacks: callbacks) label
      (mask: certified_column) (guard: certified_column)
      (action: certified_column) (rest: certified_column) =
    let
      val (mask, guard, action, rest) =
        (check_certified callbacks (label ^ " mask") mask,
         check_certified callbacks (label ^ " guard") guard,
         check_certified callbacks (label ^ " action") action,
         check_certified callbacks (label ^ " rest") rest)
      val columns = [mask, guard, action, rest]
      val theorem = @{thm comma_crt_guarded_core_step_equiv} OF
        (map #admitted columns)
      val left = apply_and (#column mask)
        (apply_or (apply_and (#column guard) (#column action)) (#column rest))
      val right = apply_or
        (apply_and (apply_and (#column mask) (#column guard)) (#column action))
        (apply_and (#column mask) (#column rest))
    in
      require_proposition (#validate_native callbacks)
        (label ^ " guarded CoreValues distribution")
        (equiv_prop left right) theorem
    end

  fun pullback_one_tick (callbacks: callbacks) label
      (mask: certified_column) (suffix: certified_column) =
    let
      val mask = check_certified callbacks (label ^ " mask") mask
      val suffix = check_certified callbacks (label ^ " suffix") suffix
      val theorem = @{thm comma_crt_mask_pullback_one_tick_equiv} OF
        [#admitted mask, #admitted suffix]
      val actual = shift 1
        (apply_and (shift 923 (#column mask)) (#column suffix))
      val column = apply_and (#column mask) (shift 1 (#column suffix))
      val back_mask_admitted = shift_admitted callbacks
        (label ^ " shifted incoming-mask admission") 923 mask
      val intersection_admitted = apply_admitted callbacks
        (label ^ " pulled-back intersection admission")
        {column=shift 923 (#column mask), admitted=back_mask_admitted} suffix
      val actual_admitted = shift_admitted callbacks
        (label ^ " shifted pulled-back admission") 1
        {column=apply_and (shift 923 (#column mask)) (#column suffix),
         admitted=intersection_admitted}
      val shifted_suffix_admitted = shift_admitted callbacks
        (label ^ " shifted suffix admission") 1 suffix
      val column_admitted = apply_admitted callbacks
        (label ^ " pulled-back result admission") mask
        {column=shift 1 (#column suffix), admitted=shifted_suffix_admitted}
      val equivalent = require_proposition (#validate_native callbacks)
        (label ^ " one-tick mask pullback") (equiv_prop actual column) theorem
    in
      {actual=actual, column=column, actual_admitted=actual_admitted,
       admitted=column_admitted, equivalent=equivalent}:pullback
    end

  fun core_modulus (callbacks: callbacks) label core =
    let
      val _ = if fastype_of core = coreT then ()
        else error (label ^ " is not a core identity")
      val term = @{term comma_phase_core_modulus} $ core
      val theorem = #scalar callbacks (label ^ " core modulus") term
      val rhs = Thm.term_of (Thm.rhs_of theorem)
      val _ = #validate_equation callbacks (label ^ " core modulus")
        term rhs theorem
      val modulus =
        (case try HOLogic.dest_number rhs of
          SOME (typ,value) =>
            if typ = natT andalso value > 0 then value
            else error (label ^ " has a non-positive core modulus")
        | NONE => error (label ^ " core modulus did not reduce to a numeral"))
    in modulus end

  fun full_core_values callbacks label core values =
    let
      val modulus = core_modulus callbacks label core
      val expected = 0 upto (modulus - 1)
    in
      if values = expected then expected
      else error (label ^ " must be the complete core value range")
    end

  fun is_full_core_values callbacks label core values =
    values = (0 upto (core_modulus callbacks label core - 1))

  fun core_value_guard_certificates (callbacks: callbacks) label core amount values =
    Comma_Semantic_Continue_Column_Proofs.profile_stage
      (label ^ " core guard construction")
      (fn () => map (fn value =>
        let
          val guard = core_guard_term core value
          val guard_admission_goal = admitted_prop guard
          val guard_admission = Goal.prove (#ctxt callbacks) [] []
            guard_admission_goal
            (fn {context,...} =>
              resolve_tac context [@{thm comma_core_value_guard_admitted}] 1)
          val guard_admission = require_proposition (#validate_native callbacks)
            (label ^ " core guard admission") guard_admission_goal guard_admission
          val shifted = shift amount guard
          val shifted_admission = shift_admitted_raw callbacks
            (label ^ " shifted core guard admission") amount guard guard_admission
          val normalized = normalize callbacks (label ^ " shifted core guard")
            shifted shifted_admission
        in
          {value=value,
           certificate={column= #column normalized,admitted= #admitted normalized},
           conversion= #conversion normalized}:core_guard
        end) values)

  fun find_core_guard label value (guards:core_guard list) =
    (case guards of
      [] => error (label ^ " is missing a core guard")
    | (guard:core_guard)::remaining =>
        if #value guard = value then guard
        else find_core_guard label value remaining)

  fun apply_binary_conversion ctxt operation left right left_conversion
      right_conversion =
    let
      val head = @{term comma_crt_apply} $ operation
      val first = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt head)) left_conversion
    in Thm.combination first right_conversion end

  fun canonical_union columns =
    (case columns of
      [] => @{term "Comma_CRT_Bool False"}
    | column::remaining => apply_or column (canonical_union remaining))

  fun union_conversion (callbacks:callbacks) label core amount values guards =
    let
      val ctxt = #ctxt callbacks
      fun build [] =
            Conv.rewr_conv (mk_meta_eq
              @{thm comma_continue_core_guard_union.simps(1)})
              (Thm.cterm_of ctxt (union_term core amount []))
        | build (value::remaining) =
            let
              val raw = union_term core amount (value::remaining)
              val unfold = Conv.rewr_conv (mk_meta_eq
                @{thm comma_continue_core_guard_union.simps(2)})
                (Thm.cterm_of ctxt raw)
              val guard = find_core_guard label value guards
              val tail = build remaining
              val raw_guard = shift amount (core_guard_term core value)
              val raw_tail = union_term core amount remaining
              val body = apply_binary_conversion ctxt @{term Comma_CRT_Or}
                raw_guard raw_tail (#conversion guard) tail
            in Thm.transitive unfold body end
      val conversion = build values
      val expected_raw = union_term core amount values
      val expected_column = canonical_union
        (map (fn value => #column (#certificate
          (find_core_guard label value guards))) values)
      val _ = if Thm.term_of (Thm.lhs_of conversion) aconv expected_raw then ()
        else error (label ^ " union conversion changed its exact input")
      val _ = if Thm.term_of (Thm.rhs_of conversion) aconv expected_column then ()
        else error (label ^ " union conversion changed its selected guards")
      val conversion = #validate_equation callbacks (label ^ " guard union conversion")
        expected_raw expected_column conversion
    in conversion end

  fun union_certificate (callbacks:callbacks) label core amount values guards =
    let
      val raw = union_term core amount values
      val raw_admission_goal = admitted_prop raw
      val raw_admission = Goal.prove (#ctxt callbacks) [] [] raw_admission_goal
        (fn {context,...} =>
          resolve_tac context [@{thm comma_continue_core_guard_union_admitted}] 1)
      val raw_admission = require_proposition (#validate_native callbacks)
        (label ^ " raw union admission") raw_admission_goal raw_admission
      val raw_conversion = union_conversion callbacks label core amount values guards
      val intermediate = Thm.term_of (Thm.rhs_of raw_conversion)
      val intermediate_admission =
        Comma_Semantic_Continue_Column_Proofs.transport_admission
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " composed union admission") raw_conversion raw intermediate
          raw_admission
      val normalized = normalize callbacks label intermediate intermediate_admission
      val conversion = Thm.transitive raw_conversion (#conversion normalized)
      val _ = #validate_equation callbacks (label ^ " final union conversion")
        raw (#column normalized) conversion
      val equivalent =
        Comma_Semantic_Continue_Column_Proofs.equation_to_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " exact union equivalence") conversion raw (#column normalized)
          raw_admission (#admitted normalized)
    in
      {actual=raw,column= #column normalized,actual_admitted=raw_admission,
       admitted= #admitted normalized,equivalent=equivalent,
       conversion=conversion}:normalized_column
    end

  fun canonical_coverage (callbacks:callbacks) label incoming union =
    let
      val intersection = intersect callbacks (label ^ " canonical mask coverage")
        incoming union
      val canonical_and = apply_and (#column incoming) (#column union)
    in
      if #column intersection aconv #column incoming then
          let
            val incoming_refl = reflexive_equiv callbacks
              (label ^ " incoming mask reflexivity")
              (#column incoming) (#admitted incoming)
          in
            SOME (Comma_Semantic_Continue_Column_Proofs.trans_equiv
              (#ctxt callbacks) (#validate_native callbacks)
              (label ^ " canonical mask coverage by normalized equality")
              canonical_and (#column intersection) (#column incoming)
              (#equivalent intersection) incoming_refl)
          end
      else NONE
    end

  fun coverage_theorem (callbacks:callbacks) label incoming
      (union:normalized_column) =
    let
      val canonical_union:certified_column =
        {column= #column union,admitted= #admitted union}
      val canonical_coverage = canonical_coverage callbacks label incoming
        canonical_union
    in
      case canonical_coverage of
        NONE => NONE
      | SOME canonical_coverage =>
       let
          val incoming_refl = reflexive_equiv callbacks
            (label ^ " incoming coverage mask reflexivity")
            (#column incoming) (#admitted incoming)
          val raw_intersection =
            Comma_Semantic_Continue_Column_Proofs.apply_equiv
              (#ctxt callbacks) (#validate_native callbacks)
              (label ^ " coverage transport across union conversion")
              @{term Comma_CRT_And} (#column incoming) (#actual union)
              (#column incoming) (#column union)
              incoming_refl (#equivalent union)
          val exact_coverage =
            Comma_Semantic_Continue_Column_Proofs.trans_equiv
              (#ctxt callbacks) (#validate_native callbacks)
              (label ^ " exact incoming mask coverage")
              (apply_and (#column incoming) (#actual union))
              (apply_and (#column incoming) (#column union))
              (#column incoming) raw_intersection canonical_coverage
          val expected = equiv_prop
            (apply_and (#column incoming) (#actual union)) (#column incoming)
          val exact_coverage = require_proposition (#validate_native callbacks)
            (label ^ " checked full-mask coverage") expected exact_coverage
        in SOME exact_coverage end
    end

  fun valid_candidate_values label full proposed =
    let
      fun all_members [] = true
        | all_members (value::rest) = member (op =) full value andalso
            all_members rest
      fun distinct [] = true
        | distinct (value::rest) = not (member (op =) rest value) andalso
            distinct rest
    in
      if all_members proposed andalso distinct proposed then proposed
      else error (label ^ " contains an invalid or repeated core value")
    end

  fun refine_core_filter (callbacks:callbacks) label observer observer_admitted
      f residue core amount values (incoming:certified_column)
      (selection:core_preselection) filtered_values (filtered_value:value)
      full_actual full_actual_admitted =
    let
      val incoming=check_certified callbacks (label ^ " incoming mask") incoming
      val _=if fastype_of observer=observerT then ()
        else error (label ^ " is not a Continue observer")
      val observer_admitted=require_proposition (#validate_native callbacks)
        (label ^ " observer admission")
        (HOLogic.mk_Trueprop (@{term comma_continue_observer_admitted} $ observer))
        observer_admitted
      val full=full_core_values callbacks label core values
      val allowed=valid_candidate_values label full (#allowed selection)
      val expected_coverage=equiv_prop
        (apply_and (#column incoming) (union_term core amount allowed))
        (#column incoming)
      val coverage=require_proposition (#validate_native callbacks)
        (label ^ " exact selected guard coverage") expected_coverage
        (#coverage selection)
      val expected_filtered=filter (fn value => member (op =) allowed value) values
      val _=if filtered_values=expected_filtered then ()
        else error (label ^ " changed filtered core-value order")
      val filtered_expression=filter_core_values_term allowed values
      val raw_filter_equation = Comma_Semantic_Continue_Column_Proofs.profile_stage
        (label ^ " exact finite selected core-value filter")
        (fn () => Simplifier.rewrite
          (Comma_Entry_Arithmetic.natural_context (#ctxt callbacks)
            |> Simplifier.add_simps @{thms filter.simps list.set insert_iff empty_iff})
          (Thm.cterm_of (#ctxt callbacks) filtered_expression))
      val filtered_literal=HOLogic.mk_list natT (map number filtered_values)
      val raw_filter_rhs=Thm.term_of (Thm.rhs_of raw_filter_equation)
      fun bounded_term term = let val rendered = Pretty.pure_string_of
        (Syntax.pretty_term (#ctxt callbacks) term)
      in String.substring (rendered,0,Int.min (size rendered,1200)) end
      val _ = if raw_filter_rhs aconv filtered_literal then ()
        else error (label ^ " filter computation disagrees with selected values; RHS=" ^
          bounded_term raw_filter_rhs ^ "; expected=" ^ bounded_term filtered_literal)
      val filter_equation = #validate_equation callbacks
        (label ^ " exact selected core-value filter")
        filtered_expression filtered_literal raw_filter_equation
      val general_filtered_list=filter_core_values_term allowed values
      val filtered_general_job=
        mk_core_values_job_list f residue core general_filtered_list
      val filtered_literal_job=mk_core_values_job f residue core filtered_values
      val full_job=mk_core_values_job f residue core values
      val full_actual_expected=job_observe_call observer full_job amount 0
      val _=if full_actual aconv full_actual_expected then ()
        else error (label ^ " full result belongs to another Continue request")
      val _=require_proposition (#validate_native callbacks)
        (label ^ " full observer admission") (admitted_prop full_actual)
        full_actual_admitted
      val filtered_actual=job_observe_call observer filtered_literal_job amount 0
      val filtered_masked_actual=apply_and (#column incoming) filtered_actual
      val _=require_proposition (#validate_native callbacks)
        (label ^ " filtered observer admission")
        (admitted_prop filtered_masked_actual) (#actual_admitted filtered_value)
      val _=require_proposition (#validate_native callbacks)
        (label ^ " filtered observer equivalence")
        (equiv_prop filtered_masked_actual (#column filtered_value))
        (#equivalent filtered_value)
      val _=require_proposition (#validate_native callbacks)
        (label ^ " filtered canonical admission")
        (admitted_prop (#column filtered_value)) (#admitted filtered_value)
      val general_filtered_actual=job_observe_call observer filtered_general_job amount 0
      val general_masked_actual=apply_and (#column incoming) general_filtered_actual
      val full_masked_actual=apply_and (#column incoming) full_actual
      val constructor_prefix=
        Const (@{const_name Comma_Continue_Core_Values_Job},
          natT --> natT --> coreT --> HOLogic.listT natT --> jobT) $
          number f $ number residue $ core
      val job_equation=lift_argument_equation (#ctxt callbacks)
        constructor_prefix filter_equation
      val observer_prefix=
        Const (@{const_name comma_continue_job_observe},
          observerT --> jobT --> natT --> natT --> columnT) $ observer
      val observer_job_equation=lift_argument_equation (#ctxt callbacks)
        observer_prefix job_equation
      val observer_amount_equation=Thm.combination observer_job_equation
        (Thm.reflexive (Thm.cterm_of (#ctxt callbacks) (number amount)))
      val observer_call_equation=Thm.combination observer_amount_equation
        (Thm.reflexive (Thm.cterm_of (#ctxt callbacks) (number 0)))
      val mask_prefix = @{term comma_crt_apply} $ @{term Comma_CRT_And} $
        #column incoming
      val masked_filter_equation=Thm.combination
        (Thm.reflexive (Thm.cterm_of (#ctxt callbacks) mask_prefix))
        observer_call_equation
      val _ = #validate_equation callbacks (label ^ " masked filter equation")
        general_masked_actual filtered_masked_actual masked_filter_equation
      val general_filtered_admitted=
        Comma_Semantic_Continue_Column_Proofs.transport_admission
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " generic filtered observer admission")
          (Thm.symmetric masked_filter_equation) filtered_masked_actual
          general_masked_actual (#actual_admitted filtered_value)
      val zero_plus=Const (@{const_name Groups.plus_class.plus},
        natT --> natT --> natT) $ number 0 $ number amount
      val zero_coverage_goal=equiv_prop
        (apply_and (#column incoming) (union_term_at core zero_plus allowed))
        (#column incoming)
      val zero_coverage=Goal.prove (#ctxt callbacks) [] [] zero_coverage_goal
        (fn {context,...} =>
          simp_tac (put_simpset HOL_basic_ss context
            |> Simplifier.add_simps @{thms add_0_left}) 1
          THEN resolve_tac context [coverage] 1)
      val zero_coverage=require_proposition (#validate_native callbacks)
        (label ^ " zero-clock coverage specialization") zero_coverage_goal
        zero_coverage
      val filter_goal=equiv_prop full_masked_actual general_masked_actual
      val filter_rule=Drule.infer_instantiate (#ctxt callbacks)
        [(("observer",0),Thm.cterm_of (#ctxt callbacks) observer),
         (("incoming",0),Thm.cterm_of (#ctxt callbacks) (#column incoming)),
         (("core",0),Thm.cterm_of (#ctxt callbacks) core),
         (("clock",0),Thm.cterm_of (#ctxt callbacks) (number 0)),
         (("shift",0),Thm.cterm_of (#ctxt callbacks) (number amount)),
         (("allowed",0),Thm.cterm_of (#ctxt callbacks)
           (HOLogic.mk_list natT (map number allowed))),
         (("f",0),Thm.cterm_of (#ctxt callbacks) (number f)),
         (("residue",0),Thm.cterm_of (#ctxt callbacks) (number residue)),
         (("values",0),Thm.cterm_of (#ctxt callbacks)
           (HOLogic.mk_list natT (map number values)))]
        @{thm comma_continue_job_observe_masked_core_values_filter}
      val filter_refinement=filter_rule OF
        [observer_admitted,#admitted incoming,zero_coverage]
      val filter_refinement=require_proposition (#validate_native callbacks)
        (label ^ " generic masked CoreValues filter") filter_goal filter_refinement
      val list_transport=
        Comma_Semantic_Continue_Column_Proofs.equation_to_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " literal filtered-list transport") masked_filter_equation
          general_masked_actual filtered_masked_actual general_filtered_admitted
          (#actual_admitted filtered_value)
      val filtered_actual_equiv=
        Comma_Semantic_Continue_Column_Proofs.trans_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " filtered CoreValues result")
          full_masked_actual general_masked_actual filtered_masked_actual
          filter_refinement list_transport
      val equivalent=
        Comma_Semantic_Continue_Column_Proofs.trans_equiv
          (#ctxt callbacks) (#validate_native callbacks)
          (label ^ " filtered canonical result") full_masked_actual
          filtered_masked_actual (#column filtered_value)
          filtered_actual_equiv (#equivalent filtered_value)
      val full_masked_admitted=mask_admitted_raw callbacks
        (label ^ " full masked result admission") incoming full_actual
        full_actual_admitted
    in
      {column= #column filtered_value,admitted= #admitted filtered_value,
       actual_admitted=full_masked_admitted,equivalent=equivalent}:value
    end

  fun check_core_guard_certificates (callbacks:callbacks) label incoming core
      amount full (guards:core_guard list) =
    let
      val incoming = check_certified callbacks (label ^ " incoming mask") incoming
      val _ = Comma_Semantic_Continue_Column_Proofs.require_literal_column
        (label ^ " incoming mask") (#column incoming)
      fun checked_guard (guard:core_guard) =
        let
          val certificate=check_certified callbacks
            (label ^ " shifted core guard") (#certificate guard)
          val _=Comma_Semantic_Continue_Column_Proofs.require_literal_column
            (label ^ " shifted core guard") (#column certificate)
          val expected=Logic.mk_equals
            (shift amount (core_guard_term core (#value guard)),#column certificate)
          val conversion=require_proposition (#validate_native callbacks)
            (label ^ " shifted core guard conversion") expected (#conversion guard)
        in {value= #value guard,certificate=certificate,
            conversion=conversion}:core_guard end
      val guards=map checked_guard guards
      val guard_values=map (fn (guard:core_guard) => #value guard) guards
    in
      if guard_values = full then guards
      else error (label ^ " guard certificates are not a complete ordered range")
    end

  fun certify_with_guards (callbacks:callbacks) label incoming core amount full
      proposed guards =
    let
      val proposed = valid_candidate_values label full proposed
      val guards = check_core_guard_certificates callbacks label incoming core
        amount full guards
      val selected_union_guards=map (fn value => find_core_guard label value guards)
        proposed
      val union = Comma_Semantic_Continue_Column_Proofs.profile_stage
        (label ^ " core guard union")
        (fn () => union_certificate callbacks (label ^ " selected core guard union")
          core amount proposed selected_union_guards)
    in
      case Comma_Semantic_Continue_Column_Proofs.profile_stage
          (label ^ " core guard coverage")
          (fn () => coverage_theorem callbacks label incoming union) of
        NONE => NONE
      | SOME coverage => SOME
          {allowed=proposed,
           guards=guards,
           coverage=coverage}:core_preselection option
    end

  fun certify_core_preselection (callbacks:callbacks) label incoming core amount
      values proposed =
    let
      val full=full_core_values callbacks label core values
      val proposed=valid_candidate_values label full proposed
      val guards=core_value_guard_certificates callbacks label core amount full
    in certify_with_guards callbacks label incoming core amount full proposed guards end

  fun preselect_core_values (callbacks:callbacks) label incoming core amount values =
    let
      val full=full_core_values callbacks label core values
      val guards=core_value_guard_certificates callbacks label core amount full
      val proposed=Comma_Semantic_Continue_Column_Proofs.profile_stage
        (label ^ " core guard proposal")
        (fn () => propose_core_values callbacks label incoming core amount guards)
    in certify_with_guards callbacks label incoming core amount full proposed guards end

  fun preselected_core_value (callbacks:callbacks) label observer observer_admitted
      f residue core amount values incoming full_actual (full_actual_admitted:unit -> thm)
      (build_filtered:int list -> core_guard list -> term -> value)
      (build_fallback:unit -> value) =
    if not (is_full_core_values callbacks label core values) then build_fallback ()
    else
      (case preselect_core_values callbacks label incoming core amount values of
        NONE => build_fallback ()
      | SOME selection =>
          let
            val allowed= #allowed selection
            val filtered_values=filter
              (fn value => member (op =) allowed value) values
          in
            if filtered_values=values then build_fallback ()
            else
              let
                val selected_guards=map (fn value =>
                  find_core_guard label value (#guards selection)) filtered_values
                val filtered_job=mk_core_values_job f residue core filtered_values
                val filtered_value=build_filtered filtered_values selected_guards filtered_job
              in
                refine_core_filter callbacks label observer observer_admitted
                  f residue core amount values incoming selection filtered_values
                  filtered_value full_actual (full_actual_admitted ())
              end
          end)
end
