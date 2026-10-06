(* Checked, spine-directed execution of the shared masked-row normalizer.
   List heads are carried opaquely; only label comparisons and mask ORs are
   delegated to proof-producing conversions supplied by the caller. *)
structure Comma_Mask_Rows_Conversion =
struct
  datatype spine = Nil | Cons of term * term | Open

  (* Fuse mask restriction and zero filtering so completed child rows are
     consumed once, in list order, without an intermediate mapped table. *)
  fun make_restrict_filter ctxt mask_and =
    let
      val (certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      val natural_context = Comma_Entry_Arithmetic.natural_context ctxt
      val and_head = Term.head_of @{term "a AND b :: nat"}
      val filter_head = Term.head_of @{term "comma_sector_rows_filter_nonzero xs"}
      val restrict_head = Term.head_of @{term "comma_sector_rows_restrict g xs"}
      val filter_zero = @{thm comma_sector_rows_filter_restrict_zero} RS @{thm eq_reflection}
      val filter_empty = @{thm comma_sector_rows_filter_restrict_empty} RS @{thm eq_reflection}
      val filter_cons = @{thm comma_sector_rows_filter_restrict_cons} RS @{thm eq_reflection}
      val if_true = @{thm if_True} RS @{thm eq_reflection}
      val if_false = @{thm if_False} RS @{thm eq_reflection}
      val if_name = @{const_name If}
      val eq_name = @{const_name HOL.eq}

      fun closed t = Term.maxidx_of_term t < 0 andalso
        null (Term.add_frees t []) andalso not (Term.is_open t)
      fun nat t = (case try HOLogic.dest_number t of
        SOME (typ, n) => typ = @{typ nat} andalso n >= 0
      | NONE => false)
      fun spine_of term =
        (case term of
          Const (name, _) =>
            if name = @{const_name Nil} then Nil else Open
        | Const (name, _) $ head $ tail =>
            if name = @{const_name Cons} then Cons (head, tail) else Open
        | _ => Open)
      fun checked_callback label request theorem =
        let
          val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
            then () else error ("Restricted-row " ^ label ^ " theorem is conditional")
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val _ = if lhs aconv request then ()
            else error ("Restricted-row " ^ label ^ " theorem changed its request")
        in certify theorem end

      fun checked_rule label request rule ct =
        let
          val theorem = Conv.rewr_conv rule ct
        in checked_callback label request theorem end

      fun checked_mask_and masked =
        let
          val theorem = checked_callback "mask AND" (Thm.term_of masked)
            (mask_and masked)
          val value = Thm.term_of (Thm.rhs_of theorem)
          val _ = if nat value then ()
            else error "Restricted-row mask AND did not return a natural numeral"
        in theorem end

      (* The source list is a public input, so its closedness is checked once
         at the boundary.  Rechecking the entire tail at every recursive
         conversion step turns a linear spine walk into quadratic work. *)
      fun root_parts ct =
        let
          val term = Thm.term_of ct
          val (head, args) = strip_comb term
          val _ = if head = filter_head andalso length args = 1 then ()
            else error "Restricted-row conversion received a foreign filter"
          val restricted = List.nth (args, 0)
          val (rh, rargs) = strip_comb restricted
          val _ = if rh = restrict_head andalso length rargs = 2 then ()
            else error "Restricted-row conversion received a foreign restriction"
        in (List.nth (rargs, 0), List.nth (rargs, 1)) end

      fun convert_raw ct =
        let
          val term = Thm.term_of ct
          val (guard, rows) = root_parts ct
          val _ = if nat guard then ()
            else error "Restricted-row conversion has a nonnumeric guard"
        in
          if snd (HOLogic.dest_number guard) = 0 then
            checked_rule "zero" term filter_zero ct
          else case spine_of rows of
            Nil => checked_rule "empty" term filter_empty ct
          | Cons (row, tail) =>
              let
                val (out, bits) = HOLogic.dest_prod row
                val _ = if closed out andalso nat bits then ()
                  else error "Restricted-row input head is malformed"
                val root = checked_rule "cons" term filter_cons ct
                val conditional = Thm.term_of (Thm.rhs_of root)
                val (if_head, if_args) = strip_comb conditional
                val _ = if (case if_head of
                      Const (name, _) => name = if_name | _ => false) andalso
                    length if_args = 3 then ()
                  else error "Restricted-row cons theorem did not expose a decision"
                val test = List.nth (if_args, 0)
                val (eq_head, eq_args) = strip_comb test
                val _ = if (case eq_head of
                      Const (name, _) => name = eq_name | _ => false) andalso
                    length eq_args = 2 andalso
                    nat (List.nth (eq_args, 1)) andalso
                    snd (HOLogic.dest_number (List.nth (eq_args, 1))) = 0 then ()
                  else error "Restricted-row decision is not a zero test"
                val masked = List.nth (eq_args, 0)
                val (mh, margs) = strip_comb masked
                val _ = if mh = and_head andalso length margs = 2 andalso
                    List.nth (margs, 0) aconv guard andalso
                    List.nth (margs, 1) aconv bits then ()
                  else error "Restricted-row decision has a foreign mask"
                val mask_eq = checked_mask_and (Thm.cterm_of ctxt masked)
                val test_mask = Conv.fun_conv (Conv.arg_conv
                  (Conv.rewr_conv mask_eq)) (Thm.cterm_of ctxt test)
                val test_value = Simplifier.rewrite natural_context (Thm.rhs_of test_mask)
                val test_eq = Thm.transitive test_mask test_value
                val decision = Conv.fun_conv (Conv.fun_conv (Conv.arg_conv
                  (Conv.rewr_conv test_eq))) (Thm.rhs_of root)
                val bool_term = Thm.term_of (Thm.rhs_of test_eq)
                val is_zero = if bool_term aconv @{term True} then true
                  else if bool_term aconv @{term False} then false
                  else error "Restricted-row zero test did not normalize"
                val selected = Conv.rewr_conv (if is_zero then if_true else if_false)
                  (Thm.rhs_of decision)
                val continuation =
                  if is_zero then convert_raw (Thm.rhs_of selected)
                  else
                    let
                      val row_mask = Conv.arg_conv (Conv.rewr_conv mask_eq)
                      val head_masked = Conv.fun_conv (Conv.arg_conv row_mask)
                        (Thm.rhs_of selected)
                      val tail_eq = Conv.arg_conv convert_raw (Thm.rhs_of head_masked)
                    in Thm.transitive head_masked tail_eq end
              in Thm.transitive root (Thm.transitive decision
                (Thm.transitive selected continuation)) end
          | Open => error "Restricted-row conversion requires a literal row spine"
        end
      fun convert ct =
        let
          val (guard, rows) = root_parts ct
          val _ = if nat guard andalso closed rows then ()
            else error "Restricted-row conversion has an open guard or source"
          val result = convert_raw ct
          val _ = certify result
        in result end
    in convert end

  fun make ctxt {key_order, label_equal, mask_or} =
    let
      val (certify_callback, callback_stats) =
        Comma_Entry_Arithmetic.make_certifier ctxt
      val mask_or_head = Term.head_of @{term "a OR b :: nat"}
      fun spine term =
        (case term of
          Const (name, _) => if name = @{const_name Nil} then Nil else Open
        | Const (name, _) $ head $ tail =>
            if name = @{const_name Cons} then Cons (head, tail) else Open
        | _ => Open)

      fun list_length term =
        let
          fun count current total =
            (case spine current of
              Nil => total
            | Cons (_, tail) => count tail (total + 1)
            | Open => error "Masked-row operation requires a literal list spine")
        in count term 0 end

      fun is_natural_numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, number) => typ = @{typ nat} andalso number >= 0
        | NONE => false)

      fun is_closed term =
        Term.maxidx_of_term term < 0 andalso
        null (Term.add_frees term []) andalso not (Term.is_open term)

      fun validate_rows rows =
        let
          fun loop current =
            (case spine current of
              Nil => ()
            | Cons (row, tail) =>
                let
                  val (label, bits) = HOLogic.dest_prod row
                  val _ = if is_closed label andalso is_closed bits then ()
                    else error "Masked-row normalizer received an open label or mask"
                  val _ = if is_natural_numeral bits then ()
                    else error "Masked-row normalizer received a nonnumeric mask"
                in loop tail end
            | Open => error "Masked-row normalizer requires a literal input row list")
        in loop rows end

      fun call name arity ct =
        let val (head, args) = strip_comb (Thm.term_of ct)
        in
          (case head of
            Const (constant, _) =>
              if constant = name andalso length args = arity then args
              else error "Masked-row conversion received a foreign or partial head"
          | _ => error "Masked-row conversion expected a constant head")
        end

      fun checked_callback label requested theorem =
        let
          val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
            then () else error ("Masked-row " ^ label ^ " callback is conditional")
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val _ = if lhs aconv requested then ()
            else error ("Masked-row " ^ label ^ " callback changed its request")
        in certify_callback theorem end

      fun checked_mask_or ct =
        let
          val requested = Thm.term_of ct
          val (head, args) = strip_comb requested
          val _ = if head = mask_or_head andalso length args = 2 then ()
            else error "Masked-row OR callback received a foreign operation"
          val theorem = checked_callback "mask OR" requested (mask_or ct)
          val result = Thm.term_of (Thm.rhs_of theorem)
          val _ = if is_natural_numeral result then ()
            else error "Masked-row OR callback did not return a natural numeral"
        in theorem end

      fun bool_value label theorem =
        let val value = Thm.term_of (Thm.rhs_of theorem)
        in
          if value aconv @{term True} then true
          else if value aconv @{term False} then false
          else error ("Masked-row " ^ label ^ " callback did not return a Boolean literal")
        end

      val if_true = @{thm if_True} RS @{thm eq_reflection}
      val if_false = @{thm if_False} RS @{thm eq_reflection}

      fun decide_if conversion ct =
        let
          val (head, args) = strip_comb (Thm.term_of ct)
          val _ = (case head of
              Const (name, _) => if name = @{const_name If} andalso length args = 3
                then () else error "Masked-row decision is not a saturated if"
            | _ => error "Masked-row decision has a nonconstant head")
          val condition = List.nth (args, 0)
          val equation = checked_callback "Boolean" condition
            (conversion (Thm.cterm_of ctxt condition))
          val selected = bool_value "Boolean" equation
          val condition_rewrite = Conv.fun_conv (Conv.fun_conv
            (Conv.arg_conv (Conv.rewr_conv equation))) ct
          val branch = Conv.rewr_conv (if selected then if_true else if_false)
            (Thm.rhs_of condition_rewrite)
        in (condition_rewrite, branch, selected) end

      val sort_empty = @{thm comma_mask_rows_sort.simps(1)} RS @{thm eq_reflection}
      val sort_single = @{thm comma_mask_rows_sort.simps(2)} RS @{thm eq_reflection}
      val sort_many = @{thm comma_mask_rows_sort.simps(3)} RS @{thm eq_reflection}
      val merge_left_empty = @{thm comma_mask_rows_merge.simps(1)} RS @{thm eq_reflection}
      val merge_right_empty = @{thm comma_mask_rows_merge.simps(2)} RS @{thm eq_reflection}
      val merge_cons = @{thm comma_mask_rows_merge.simps(3)} RS @{thm eq_reflection}
      val merge_sorted_empty = @{thm comma_mask_rows_merge_sorted.simps(1)} RS @{thm eq_reflection}
      val merge_sorted_single = @{thm comma_mask_rows_merge_sorted.simps(2)} RS @{thm eq_reflection}
      val merge_sorted_many = @{thm comma_mask_rows_merge_sorted.simps(3)} RS @{thm eq_reflection}
      val normalize_definition = @{thm comma_mask_rows_normalize_def} RS @{thm eq_reflection}
      val prune_definition = @{thm comma_mask_rows_prune_def} RS @{thm eq_reflection}
      val filter_empty = @{thm filter.simps(1)} RS @{thm eq_reflection}
      val filter_cons = @{thm filter.simps(2)} RS @{thm eq_reflection}
      val take_cons = @{thm take_Cons'} RS @{thm eq_reflection}
      val take_nil = @{thm take_Nil} RS @{thm eq_reflection}
      val drop_cons = @{thm drop_Cons'} RS @{thm eq_reflection}
      val drop_nil = @{thm drop_Nil} RS @{thm eq_reflection}
      val arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms list.size take.simps drop.simps nat.case case_nat_numeral
          pred_numeral_simps Let_def}
      val prune_condition_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms snd_conv}
      val length_cons = @{thm length_Cons} RS @{thm eq_reflection}
      val snd_projection = @{thm snd_conv} RS @{thm eq_reflection}
      val natural_division_head = Term.head_of @{term "(x::nat) div y"}
      val sort_calls = Unsynchronized.ref 0
      val merge_calls = Unsynchronized.ref 0
      val adjacent_calls = Unsynchronized.ref 0
      val or_calls = Unsynchronized.ref 0
      val prune_rows_visited = Unsynchronized.ref 0
      val normalize_calls = Unsynchronized.ref 0
      val normalize_input_rows = Unsynchronized.ref 0

      fun short_shape depth term =
        let
          fun name t =
            (case Term.head_of t of
              Const (constant, _) => Long_Name.base_name constant
            | Free (free, _) => "free:" ^ free
            | Var ((variable, _), _) => "var:" ^ variable
            | Bound index => "bound:" ^ Int.toString index
            | Abs _ => "lambda")
        in
          if depth <= 0 then name term
          else
            let val (head, args) = strip_comb term
                val shown = take (Int.min (2, length args)) args
            in name head ^ "[" ^ space_implode "," (map (short_shape (depth - 1)) shown) ^
              (if length args > 2 then ",…" else "") ^ "]" end
        end

      fun natural_value term =
        (case try HOLogic.dest_number term of
          SOME (typ, number) =>
            if typ = @{typ nat} andalso number >= 0 then IntInf.toInt number
            else error ("Masked-row split index is not a natural numeral: " ^
              short_shape 2 term)
        | NONE =>
            (case strip_comb term of
              (Const (name, _), [predecessor]) =>
                if name = @{const_name Suc} then natural_value predecessor + 1
                else error ("Masked-row split index is not a natural numeral: " ^
                  short_shape 2 term)
            | _ => error ("Masked-row split index is not a natural numeral: " ^
                short_shape 2 term)))

      fun length_spine ct =
        let val [rows] = call @{const_name size} 1 ct
        in (case spine rows of
          Nil => Simplifier.rewrite arithmetic_context ct
        | Cons _ =>
            let val root = Conv.rewr_conv length_cons ct
            in Thm.transitive root
              (Conv.arg_conv length_spine (Thm.rhs_of root)) end
        | Open => error "Masked-row length requires a literal row spine") end

      fun normalize_index index =
        let
          val requested = Thm.cterm_of ctxt index
          val (head, args) = strip_comb index
          val length_conversion = (case (head, args) of
            (head, [dividend, _]) =>
              if head = natural_division_head then
                (case strip_comb dividend of
                  (Const (length_name, _), [_]) =>
                    if length_name = @{const_name size} then
                      Conv.fun_conv (Conv.arg_conv length_spine) requested
                    else Conv.all_conv requested
                | _ => Conv.all_conv requested)
              else Conv.all_conv requested
          | _ => Conv.all_conv requested)
          val arithmetic = Simplifier.rewrite arithmetic_context
            (Thm.rhs_of length_conversion)
          val equation = Thm.transitive length_conversion arithmetic
          val equation = checked_callback "split-index" index equation
          val value = Thm.term_of (Thm.rhs_of equation)
          val _ = ignore (natural_value value)
        in equation end

      fun prune_nonzero_mask requested =
        let
          val beta = Conv.try_conv (Thm.beta_conversion false) requested
          val ct = Thm.rhs_of beta
          val (head, args) = strip_comb (Thm.term_of ct)
          val comparison = (case (head, args) of
            (Const (name, _), [value]) =>
              if name = @{const_name Not} then value
              else error "Masked-row zero test is not a negated equality"
          | _ => error "Masked-row zero test has an unexpected shape")
          val (eq_head, eq_args) = strip_comb comparison
          val mask = (case (eq_head, eq_args) of
            (Const (name, _), [value, _]) =>
              if name = @{const_name HOL.eq} then value
              else error "Masked-row zero test compares with a foreign relation"
          | _ => error "Masked-row zero test equality is not binary")
          val (projection, projection_args) = strip_comb mask
          val _ = (case (projection, projection_args) of
            (Const (name, _), [_]) => if name = @{const_name snd} then ()
              else error "Masked-row zero test does not select the mask"
          | _ => error "Masked-row zero test has a partial mask projection")
          val comparison_eq = Conv.fun_conv
            (Conv.arg_conv (Conv.rewr_conv snd_projection))
            (Thm.cterm_of ctxt comparison)
          val projected = Conv.arg_conv
            (Conv.rewr_conv comparison_eq) ct
          val normalized = Thm.transitive projected
            (Simplifier.rewrite prune_condition_context (Thm.rhs_of projected))
        in Thm.transitive beta normalized end

      fun take_or_drop_spine operation ct =
        let
          val original_args = call operation 2 ct
          val original_index = List.nth (original_args, 0)
          val index_eq = normalize_index original_index
          val indexed = Conv.fun_conv
            (Conv.arg_conv (Conv.rewr_conv index_eq)) ct
          val args = call operation 2 (Thm.rhs_of indexed)
          val index = List.nth (args, 0)
          val rows = List.nth (args, 1)
          val value = natural_value index
          val is_take = operation = @{const_name take}
          val nil_eq = if is_take then take_nil else drop_nil
          val cons_eq = if is_take then take_cons else drop_cons
        in
          (case spine rows of
            Nil => Thm.transitive indexed (Conv.rewr_conv nil_eq
              (Thm.rhs_of indexed))
          | Cons _ =>
              let
                val root = Conv.rewr_conv cons_eq (Thm.rhs_of indexed)
                val (condition, selected, at_zero) = decide_if
                  (Simplifier.rewrite arithmetic_context) (Thm.rhs_of root)
                val expected_zero = value = 0
                val _ = if at_zero = expected_zero then ()
                  else error "Masked-row split index decision disagrees with its numeral"
                val remainder =
                  if at_zero then Conv.all_conv (Thm.rhs_of selected)
                  else if is_take then
                    Conv.arg_conv (take_or_drop_spine operation) (Thm.rhs_of selected)
                  else take_or_drop_spine operation (Thm.rhs_of selected)
                val recursion = Thm.transitive root
                  (Thm.transitive condition (Thm.transitive selected remainder))
              in Thm.transitive indexed recursion end
          | Open => error "Masked-row split encountered an open source list")
        end

      fun sort_argument ct =
        let
          val args = call @{const_name comma_mask_rows_sort} 2 ct
          val source = List.nth (args, 1)
          val (source_head, source_args) = strip_comb source
          val operation =
            (case source_head of
              Const (name, _) =>
                if length source_args = 2 andalso
                    (name = @{const_name take} orelse name = @{const_name drop}) then name
                else error "Masked-row sort split has an unexpected source"
            | _ => error "Masked-row sort split is not a list operation")
          val reduced = take_or_drop_spine operation (Thm.cterm_of ctxt source)
          val value = Thm.term_of (Thm.rhs_of reduced)
          val _ = if spine value = Open then
              error "Masked-row sort split did not produce a literal list" else ()
        in Conv.arg_conv (Conv.rewr_conv reduced) ct end

      fun rows_normalizer ct =
        let
          val args = call @{const_name comma_mask_rows_normalize} 2 ct
          val key = List.nth (args, 0)
          val rows = List.nth (args, 1)
          val _ = if is_closed key then ()
            else error "Masked-row normalizer received an open ordering key"
          val _ = validate_rows rows
          val before_count = list_length rows
          val sorts_before = !sort_calls
          val merges_before = !merge_calls
          val adjacent_before = !adjacent_calls
          val ors_before = !or_calls
          val pruned_before = !prune_rows_visited
          val callback_calls_before = #calls (callback_stats ())
          val callback_nodes_before = #nodes (callback_stats ())
          val callback_ms_before = #milliseconds (callback_stats ())
          val _ = normalize_calls := !normalize_calls + 1
          val _ = normalize_input_rows := !normalize_input_rows + before_count
          val trace_call = getenv "COMMA_PROFILE_LOG" <> "" andalso
            (!normalize_calls = 1 orelse !normalize_calls mod 10 = 0)
          fun report_stage stage start = if trace_call then Comma_Fast_Kernel.report
            ("masked_row_normalize_stage call=" ^ Int.toString (!normalize_calls) ^
             " stage=" ^ stage ^ " elapsed_ms=" ^
             LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), start)))) else ()
          val _ = if not trace_call then ()
            else Comma_Fast_Kernel.report
              ("masked_row_normalize_started call=" ^ Int.toString (!normalize_calls) ^
               " cumulative_input_rows=" ^ Int.toString (!normalize_input_rows) ^
               " current_input_rows=" ^ Int.toString before_count)
          val started = Time.now ()
          val root_started = Time.now ()
          val root = Conv.rewr_conv normalize_definition ct
          val _ = report_stage "definition" root_started
          val sort_started = Time.now ()
          val sorted = Conv.arg_conv (Conv.arg_conv sort_rows) (Thm.rhs_of root)
          val _ = report_stage "sort" sort_started
          val adjacent_started = Time.now ()
          val adjacent = Conv.arg_conv merge_adjacent (Thm.rhs_of sorted)
          val _ = report_stage "merge_equal_labels" adjacent_started
          val prune_started = Time.now ()
          val pruned = prune_rows (Thm.rhs_of adjacent)
          val _ = report_stage "prune_zero_masks" prune_started
          val result = Thm.transitive root
            (Thm.transitive sorted (Thm.transitive adjacent pruned))
          val certificate_started = Time.now ()
          val _ = certify_callback result
          val _ = report_stage "cached_certificate" certificate_started
          val after_rows = Thm.term_of (Thm.rhs_of result)
          val after_count = list_length after_rows
          val _ = if getenv "COMMA_PROFILE_LOG" = "" then ()
            else Comma_Fast_Kernel.report
              ("masked_row_normalize input_rows=" ^ Int.toString before_count ^
               " output_rows=" ^ Int.toString after_count ^
               " sort_calls=" ^ Int.toString (!sort_calls - sorts_before) ^
               " merge_calls=" ^ Int.toString (!merge_calls - merges_before) ^
               " adjacent_calls=" ^ Int.toString (!adjacent_calls - adjacent_before) ^
               " packed_or_calls=" ^ Int.toString (!or_calls - ors_before) ^
               " prune_rows_visited=" ^
                 Int.toString (!prune_rows_visited - pruned_before) ^
               " callback_certificate_calls=" ^ Int.toString
                 (#calls (callback_stats ()) - callback_calls_before) ^
               " callback_certificate_nodes=" ^ Int.toString
                 (#nodes (callback_stats ()) - callback_nodes_before) ^
               " callback_certificate_ms=" ^ LargeInt.toString
                 (#milliseconds (callback_stats ()) - callback_ms_before) ^
               " elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (Time.- (Time.now (), started))))
        in result end

      and sort_rows ct =
        let
          val _ = sort_calls := !sort_calls + 1
          val args = call @{const_name comma_mask_rows_sort} 2 ct
          val rows = List.nth (args, 1)
        in
          (case spine rows of
            Nil => Conv.rewr_conv sort_empty ct
          | Cons (_, tail) =>
              (case spine tail of
                Nil => Conv.rewr_conv sort_single ct
              | Cons _ =>
                  let
                    val root = Conv.rewr_conv sort_many ct
                    val take = Conv.fun_conv (Conv.arg_conv sort_argument)
                      (Thm.rhs_of root)
                    val drop = Conv.arg_conv sort_argument (Thm.rhs_of take)
                    val left = Conv.fun_conv (Conv.arg_conv sort_rows) (Thm.rhs_of drop)
                    val right = Conv.arg_conv sort_rows (Thm.rhs_of left)
                    val merged = merge_rows (Thm.rhs_of right)
                  in Thm.transitive root
                    (Thm.transitive take (Thm.transitive drop
                      (Thm.transitive left (Thm.transitive right merged)))) end
              | Open => error "Masked-row sort encountered an open tail")
          | Open => error "Masked-row sort input is not a literal list")
        end

      and merge_rows ct =
        let
          val _ = merge_calls := !merge_calls + 1
          val args = call @{const_name comma_mask_rows_merge} 3 ct
          val left_rows = List.nth (args, 1)
          val right_rows = List.nth (args, 2)
        in
          (case (spine left_rows, spine right_rows) of
            (Nil, _) => Conv.rewr_conv merge_left_empty ct
          | (_, Nil) => Conv.rewr_conv merge_right_empty ct
          | (Cons _, Cons _) =>
              let
                val root = Conv.rewr_conv merge_cons ct
                val (decision, selected, _) = decide_if key_order (Thm.rhs_of root)
                val tail = Conv.arg_conv merge_rows (Thm.rhs_of selected)
              in Thm.transitive root (Thm.transitive decision
                (Thm.transitive selected tail)) end
          | _ => error "Masked-row merge received a nonliteral list")
        end

      and merge_adjacent ct =
        let
          val _ = adjacent_calls := !adjacent_calls + 1
          val args = call @{const_name comma_mask_rows_merge_sorted} 1 ct
          val rows = List.nth (args, 0)
        in
          (case spine rows of
            Nil => Conv.rewr_conv merge_sorted_empty ct
          | Cons (_, tail) =>
              (case spine tail of
                Nil => Conv.rewr_conv merge_sorted_single ct
              | Cons _ =>
                  let
                    val root = Conv.rewr_conv merge_sorted_many ct
                    val (decision, selected, equal_labels) = decide_if label_equal
                      (Thm.rhs_of root)
                    val continued =
                      if equal_labels then
                        let
                          val combined = Conv.arg_conv
                            (Conv.fun_conv (Conv.arg_conv
                              (Conv.arg_conv checked_mask_or))) (Thm.rhs_of selected)
                          val _ = or_calls := !or_calls + 1
                          val rest = merge_adjacent (Thm.rhs_of combined)
                        in Thm.transitive combined rest end
                      else Conv.arg_conv merge_adjacent (Thm.rhs_of selected)
                  in Thm.transitive root
                    (Thm.transitive decision (Thm.transitive selected continued)) end
              | Open => error "Masked-row adjacent merge encountered an open tail")
          | Open => error "Masked-row adjacent merge requires a literal list")
        end

      and prune_rows ct =
        let
          val args = call @{const_name comma_mask_rows_prune} 1 ct
          val _ = prune_rows_visited := !prune_rows_visited +
            list_length (List.nth (args, 0))
          val root = Conv.rewr_conv prune_definition ct
          val filtered = filter_rows (Thm.rhs_of root)
        in Thm.transitive root filtered end

      and filter_rows ct =
        let
          val (head, args) = strip_comb (Thm.term_of ct)
          val _ = (case head of
              Const (name, _) => if name = @{const_name filter} andalso length args = 2
                then () else error "Masked-row prune has a foreign filter"
            | _ => error "Masked-row prune expected a filter")
          val rows = List.nth (args, 1)
        in
          (case spine rows of
            Nil => Conv.rewr_conv filter_empty ct
          | Cons _ =>
              let
                val root = Conv.rewr_conv filter_cons ct
                val (decision, selected, keep) = decide_if
                  prune_nonzero_mask (Thm.rhs_of root)
                val tail = if keep then
                    Conv.arg_conv filter_rows (Thm.rhs_of selected)
                  else filter_rows (Thm.rhs_of selected)
              in Thm.transitive root (Thm.transitive decision
                (Thm.transitive selected tail)) end
          | Open => error "Masked-row prune input is not a literal list")
        end
    in rows_normalizer end
end
