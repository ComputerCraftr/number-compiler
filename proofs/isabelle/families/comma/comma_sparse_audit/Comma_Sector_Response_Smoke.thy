theory Comma_Sector_Response_Smoke
  imports Comma_Sparse_Core.Comma_Sector_Response_Check
begin

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Response_Check.make lthy {max_clauses = 1}
      val first = #branch engine 1 0 0
      val prior = #stats engine ()
      val repeated = #branch engine 1 0 0
      val checked_period = #period engine 1 0
      val after = #stats engine ()
      val _ = if #attempts prior = #attempts after andalso
          #hits after = #hits prior + 1 andalso
          #period_attempts after = #period_attempts prior andalso
          #period_hits after = #period_hits prior + 1 andalso #value checked_period > 0 andalso
          #canonical_near_attempts after = #canonical_near_attempts prior andalso
          #canonical_near_retained after = 1 andalso
          Thm.prop_of (#equation first) aconv Thm.prop_of (#equation repeated)
        then () else error "Local clause cache did not reuse its exact checked equation"
      val invalid = Exn.capture (fn () => #branch engine 1 0 28) ()
      val _ = if Exn.is_exn invalid then () else error "Out-of-range phase was admitted"
      val capped = Exn.capture (fn () => #branch engine 1 1 0) ()
      val _ = if Exn.is_exn capped then () else error "Clause budget was ignored"
      val final = #stats engine ()
      val _ = if #attempts final = #attempts prior andalso #retained final = 1
          andalso #failures final = 2 andalso
          #canonical_near_attempts final = #canonical_near_attempts prior andalso
          #canonical_near_retained final = 1 then ()
        else error "Rejected local clauses did work or corrupted retention accounting"
      val _ = Comma_Fast_Kernel.report (#report engine ())
      val period_engine = Comma_Sector_Response_Check.make lthy {max_clauses = 2}
      val _ = #period period_engine 1 5
      val second_period = #period period_engine 1 15
      val period_stats = #stats period_engine ()
      val expected_period = @{term comma_short_period} $
        (@{term comma_finite_period_fast} $ HOLogic.mk_number @{typ nat} 1 $
          (@{term "\<lambda>x::nat. x mod 10"} $ HOLogic.mk_number @{typ nat} 15))
      val _ = if #canonical_period_attempts period_stats = 1 andalso
          #canonical_period_hits period_stats = 1 andalso
          Thm.term_of (Thm.lhs_of (#equation second_period)) aconv expected_period
        then () else error ("Period sharing failed: " ^ #report period_engine () ^
          " lhs=" ^ Syntax.string_of_term lthy (Thm.term_of (Thm.lhs_of (#equation second_period))))
      val diagonal_engine = Comma_Sector_Response_Check.make lthy {max_clauses = 4}
      val diagonal_first = #branch diagonal_engine 1 0 6
      val diagonal_second = #branch diagonal_engine 1 20 0
      val diagonal_stats = #stats diagonal_engine ()
      fun source f x k = @{term comma_fast_step} $ HOLogic.mk_number @{typ nat} 0 $
        (@{term Comma_Near} $ HOLogic.mk_number @{typ nat} f $ HOLogic.mk_number @{typ nat} 0 $
          (@{term comma_entry_alphabet_endpoint} $ HOLogic.mk_number @{typ nat} f $
            HOLogic.mk_number @{typ nat} x $ HOLogic.mk_number @{typ nat} k))
      val _ = if #attempts diagonal_stats = 2 andalso #retained diagonal_stats = 2 andalso
          #canonical_near_lookups diagonal_stats = 2 andalso
          #canonical_near_attempts diagonal_stats = 1 andalso
          #canonical_near_hits diagonal_stats = 1 andalso
          #canonical_near_retained diagonal_stats = 1 andalso
          Thm.term_of (Thm.lhs_of (#equation diagonal_first)) aconv source 1 0 6 andalso
          Thm.term_of (Thm.lhs_of (#equation diagonal_second)) aconv source 1 20 0 then ()
        else error "Distinct Entry endpoints did not share one checked canonical Near equation"
      val _ = if #move diagonal_first aconv #move diagonal_second andalso
          not (Thm.term_of (Thm.lhs_of (#equation diagonal_first)) aconv
            Thm.term_of (Thm.lhs_of (#equation diagonal_second)))
        then () else error "Diagonal reuse lost its exact occurrence bindings"
      (* Validation is pure: a foreign source theorem or unfinished reflexive
         proof cannot grant publication authority to either memo. *)
      val foreign = Exn.capture (fn () =>
        Comma_Sector_Response_Check.validate_branch_equation (source 1 20 0)
          (#equation diagonal_first)) ()
      val unfinished = Exn.capture (fn () =>
        Comma_Sector_Response_Check.validate_branch_equation (source 1 20 0)
          (Thm.reflexive (Thm.cterm_of lthy (source 1 20 0)))) ()
      val validation_stats = #stats diagonal_engine ()
      val _ = if Exn.is_exn foreign andalso Exn.is_exn unfinished andalso
          #retained validation_stats = #retained diagonal_stats andalso
          #canonical_near_retained validation_stats = #canonical_near_retained diagonal_stats
        then () else error "Foreign or unfinished clause proof gained memo authority"
      val rejected_engine = Comma_Sector_Response_Check.make lthy {max_clauses = 2}
      val phase_bound = #period rejected_engine 1 0
      val out_of_period = Exn.capture (fn () =>
        #branch rejected_engine 1 0 (#value phase_bound)) ()
      val rejected_stats = #stats rejected_engine ()
      val _ = if #value phase_bound < 28 andalso Exn.is_exn out_of_period andalso
          #attempts rejected_stats = 1 andalso #failures rejected_stats = 1 andalso
          #retained rejected_stats = 0 andalso #canonical_near_lookups rejected_stats = 0 andalso
          #canonical_near_attempts rejected_stats = 0 andalso
          #canonical_near_retained rejected_stats = 0 then ()
        else error "Unproved branch phase reached or published a canonical Near proof"
      val recovered = #branch rejected_engine 1 0 0
      val recovered_stats = #stats rejected_engine ()
      val _ = if #retained recovered_stats = 1 andalso
          #canonical_near_retained recovered_stats = 1 andalso
          Thm.term_of (Thm.lhs_of (#equation recovered)) aconv source 1 0 0 then ()
        else error "Rejected phase corrupted subsequent checked publication"
      val changed_phase = #branch diagonal_engine 1 20 1
      val _ = if not (Thm.term_of (Thm.lhs_of (#equation changed_phase)) aconv
          Thm.term_of (Thm.lhs_of (#equation diagonal_second))) then ()
        else error "Changed phase lost its original source binding"
      val exact_multiple = #branch diagonal_engine 2 38 0
      val _ = if #move exact_multiple aconv @{term "Comma_Next (Comma_Entry 3 0 81)"}
        then () else error "Signed exact-multiple diagonal was not normalized"
      val _ = Comma_Fast_Kernel.report ("entry_diagonal " ^ #report diagonal_engine ())
      val (_, lthy') = Local_Theory.note
        ((Binding.name "comma_local_clause_smoke", []),
          [#equation first, #equation second_period,
            #equation diagonal_first, #equation diagonal_second,
            #equation exact_multiple]) lthy
    in lthy' end
\<close>
ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_local_clause_smoke}) then ()
    else error "Local sector clause smoke depends on an oracle";
\<close>

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Guards.make lthy {max_nodes = 1024}
      val first = #guard engine 2 919 1
      val prior = #stats engine ()
      val repeated = #guard engine 2 919 1
      val repeated_stats = #stats engine ()
      val _ = if #attempts prior = #attempts repeated_stats andalso
          #joins prior = #joins repeated_stats andalso
          #hits repeated_stats = #hits prior + 1 andalso
          Thm.prop_of first aconv Thm.prop_of repeated then ()
        else error "Guard cache did not preserve its checked complete key"
      val changed_period = #guard engine 3 919 1
      val changed_shift = #guard engine 3 920 1
      val zero_residue = #guard engine 1 919 0
      val opposite = #guard engine 2 919 0
      fun bits theorem = Thm.term_of (Thm.rhs_of theorem)
      fun intersect left right = Simplifier.rewrite (#packed_context engine)
        (Thm.cterm_of lthy (@{term "\<lambda>a b::nat. a AND b"} $ bits left $ bits right))
      val disjoint = intersect first opposite
      val restricted = intersect first zero_residue
      val packed_prior = #packed_stats engine ()
      val restricted_again = intersect first zero_residue
      val packed_after = #packed_stats engine ()
      val _ = if #misses packed_prior = #misses packed_after andalso
          #hits packed_after = #hits packed_prior + 1 andalso
          Thm.prop_of restricted aconv Thm.prop_of restricted_again then ()
        else error "Packed arithmetic memo did not reuse its exact root equation"
      val _ = if snd (HOLogic.dest_number (bits disjoint)) = 0 andalso
          bits restricted aconv bits first then ()
        else error "Packed AND did not preserve disjoint/full-mask intersections"
      val _ = if not (Thm.term_of (Thm.lhs_of first) aconv
          Thm.term_of (Thm.lhs_of changed_period)) andalso
          not (Thm.term_of (Thm.rhs_of changed_period) aconv
            Thm.term_of (Thm.rhs_of changed_shift)) then ()
        else error "Guard cache confused a changed period or positive phase shift"
      val invalid = Exn.capture (fn () => #guard engine 3 919 3) ()
      val _ = if Exn.is_exn invalid then () else error "Out-of-period guard residue was admitted"
      val _ = Comma_Fast_Kernel.report (#report engine ())
      val basis = maps (fn period => map (fn residue => #guard engine period 919 residue)
        (0 upto (period - 1))) [1, 2, 3, 6, 22, 28]
      val _ = if length basis = 62 andalso #class_publications (#stats engine ()) = 63 then ()
        else error "Short-period guard basis is incomplete"
      val _ = Comma_Fast_Kernel.report ("guard_basis_62 " ^ #report engine ())
      val explicit_full = #guard engine 1 0 0
      val full_prior = #packed_stats engine ()
      val full_and = #mask_and engine (bits first) (bits explicit_full)
      val full_or = #mask_or engine (bits first) (bits explicit_full)
      val full_after = #packed_stats engine ()
      val _ = if #value full_and aconv bits first andalso
          #value full_or aconv bits explicit_full andalso
          #full_hits full_after = #full_hits full_prior + 2 andalso
          #misses full_after = #misses full_prior then ()
        else error "Seeded trim certificates did not justify the full-mask identities"
      val overwide = HOLogic.mk_number @{typ nat}
        (snd (HOLogic.dest_number (bits explicit_full)) + 1)
      val wide_and = #mask_and engine overwide (bits explicit_full)
      val wide_after = #packed_stats engine ()
      val _ = if snd (HOLogic.dest_number (#value wide_and)) = 0 andalso
          #full_hits wide_after = #full_hits full_after andalso
          #full_missing_bounds wide_after > #full_missing_bounds full_after then ()
        else error "An overwide mask incorrectly used the bounded full-mask identity"
      val _ = Comma_Fast_Kernel.report ("seeded_full_masks " ^ #report engine ())
      val cold_bits = Comma_Sector_Guards.make lthy {max_nodes = 8192}
      val cold_intersection = #mask_and cold_bits (bits first) (bits changed_period)
      val expected_intersection = #guard engine 6 919 1
      val _ = if #value cold_intersection aconv bits expected_intersection then ()
        else error "Cold 924-bit constructor differs from the independently proved period-six guard"
      val _ = Comma_Fast_Kernel.report ("cold_924_and " ^ #report cold_bits ())
      (* A refused parent may retain complete child proofs, never a class result. *)
      val tiny = Comma_Sector_Guards.make lthy {max_nodes = 1}
      val failed = Exn.capture (fn () => #guard tiny 2 919 1) ()
      val partial = #stats tiny ()
      val retried = Exn.capture (fn () => #guard tiny 2 919 1) ()
      val final = #stats tiny ()
      val _ = if Exn.is_exn failed andalso Exn.is_exn retried andalso
          #retained partial = 1 andalso #retained final = 1 andalso
          #class_publications final = 0 andalso #failures final = 2 andalso
          #attempts partial > 0 andalso #attempts final = #attempts partial andalso
          #normalizations partial > 0 andalso
          #normalizations final = #normalizations partial then ()
        else error "Guard budget failure published a parent or hid attempted work"
      val _ = Comma_Fast_Kernel.report ("guard_budget " ^ #report tiny ())
      val arithmetic_engine = Comma_Sector_Guards.make lthy {max_nodes = 2}
      fun numeral n = HOLogic.mk_number @{typ nat} n
      val and_num_head = Term.head_of @{term "and_num m n"}
      val or_num_head = Term.head_of @{term "or_num m n"}
      val and_nat_head = Term.head_of @{term "a AND b :: nat"}
      val or_nat_head = Term.head_of @{term "a OR b :: nat"}
      val some_num_head = Term.head_of @{term "Some (m::num)"}
      fun digits value =
        if value = 1 then Const (@{const_name Num.num.One}, @{typ num})
        else
          (case numeral value of
            Const (name, _) $ ds => if name = "Num.numeral_class.numeral" then ds
              else error "Expected num digits below a natural numeral"
          | _ => error "Expected a natural numeral application")
      fun check_exact theorem request rhs =
        if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            null (Term.add_frees (Thm.prop_of theorem) []) andalso
            null (Term.add_vars (Thm.prop_of theorem) []) andalso
            null (Thm_Deps.all_oracles [theorem])
        then theorem else error "Native numeric conversion lost its exact closed equation"
      fun numeric_result operator left right expected =
        let
          val head = if operator = Comma_Sector_Guards.And_Num then and_num_head else or_num_head
          val request = head $ digits left $ digits right
          val expected_rhs = if operator = Comma_Sector_Guards.And_Num
            then some_num_head $ digits expected else digits expected
          val theorem = Simplifier.rewrite (#packed_context arithmetic_engine)
            (Thm.cterm_of lthy request)
        in check_exact theorem request expected_rhs end
      fun numeric_none_result left right =
        let
          val request = and_num_head $ digits left $ digits right
          val theorem = Simplifier.rewrite (#packed_context arithmetic_engine)
            (Thm.cterm_of lthy request)
        in check_exact theorem request @{term "None :: num option"} end
      val exact_and_one = numeric_result Comma_Sector_Guards.And_Num 17 19 17
      val exact_and_two = numeric_result Comma_Sector_Guards.And_Num 33 35 33
      val exact_and_none = numeric_none_result 16 32
      val exact_and_branch = numeric_result Comma_Sector_Guards.And_Num 17 33 1
      val exact_or_one = numeric_result Comma_Sector_Guards.Or_Num 17 19 19
      val exact_or_two = numeric_result Comma_Sector_Guards.Or_Num 33 35 35
      val native_stats = #packed_stats arithmetic_engine ()
      val _ = if #num_nodes native_stats > 0 andalso
          #num_nodes native_stats = #num_conversions native_stats andalso
          #num_failures native_stats = 0 andalso
          #num_retained native_stats = 0 andalso #num_evicted native_stats = 0 andalso
          #num_limit native_stats = 0 andalso
          #total_retained native_stats <= #total_limit native_stats then ()
        else error "Exact numeric arithmetic accounting or root budget was inconsistent"
      val _ = Comma_Fast_Kernel.report
        ("packed_native_numeric " ^ #report arithmetic_engine ())
      fun power_two exponent =
        let fun loop 0 value = value
              | loop count value = loop (count - 1) (2 * value)
        in loop exponent 1 end
      val wide_base = power_two 923
      val wide_left = wide_base + 17
      val wide_right = wide_base + 19
      val wide_and_engine = Comma_Sector_Guards.make lthy {max_nodes = 8192}
      val wide_and_result = #mask_and wide_and_engine (numeral wide_left) (numeral wide_right)
      val wide_and_theorem = #theorem wide_and_result
      val wide_and_stats = #packed_stats wide_and_engine ()
      val wide_and_request = and_nat_head $ numeral wide_left $ numeral wide_right
      val _ = if #value wide_and_result aconv numeral (wide_base + 17) andalso
          Thm.term_of (Thm.lhs_of wide_and_theorem) aconv wide_and_request andalso
          Thm.nprems_of wide_and_theorem = 0 andalso null (Thm.hyps_of wide_and_theorem) andalso
          null (Thm.tpairs_of wide_and_theorem) andalso
          null (Term.add_frees (Thm.prop_of wide_and_theorem) []) andalso
          null (Term.add_vars (Thm.prop_of wide_and_theorem) []) andalso
          null (Thm_Deps.all_oracles [wide_and_theorem]) andalso
          #num_nodes wide_and_stats > 0 andalso
          #num_nodes wide_and_stats = #num_conversions wide_and_stats andalso
          #num_failures wide_and_stats = 0 andalso
          #total_retained wide_and_stats <= #total_limit wide_and_stats then ()
        else error "924-bit AND failed its exact closed-root gate"
      val _ = Comma_Fast_Kernel.report ("wide_924_and " ^ #report wide_and_engine ())
      val wide_or_engine = Comma_Sector_Guards.make lthy {max_nodes = 8192}
      val wide_or_result = #mask_or wide_or_engine (numeral wide_left) (numeral wide_right)
      val wide_or_theorem = #theorem wide_or_result
      val wide_or_stats = #packed_stats wide_or_engine ()
      val wide_or_request = or_nat_head $ numeral wide_left $ numeral wide_right
      val _ = if #value wide_or_result aconv numeral wide_right andalso
          Thm.term_of (Thm.lhs_of wide_or_theorem) aconv wide_or_request andalso
          Thm.nprems_of wide_or_theorem = 0 andalso null (Thm.hyps_of wide_or_theorem) andalso
          null (Thm.tpairs_of wide_or_theorem) andalso
          null (Term.add_frees (Thm.prop_of wide_or_theorem) []) andalso
          null (Term.add_vars (Thm.prop_of wide_or_theorem) []) andalso
          null (Thm_Deps.all_oracles [wide_or_theorem]) andalso
          #num_nodes wide_or_stats > 0 andalso
          #num_nodes wide_or_stats = #num_conversions wide_or_stats andalso
          #num_failures wide_or_stats = 0 andalso
          #total_retained wide_or_stats <= #total_limit wide_or_stats then ()
        else error "924-bit OR failed its exact closed-root gate"
      val _ = Comma_Fast_Kernel.report ("wide_924_or " ^ #report wide_or_engine ())
      val first_and = #mask_and arithmetic_engine (numeral 6) (numeral 3)
      val swapped_and = #mask_and arithmetic_engine (numeral 3) (numeral 6)
      val arithmetic_stats = #packed_stats arithmetic_engine ()
      val _ = if #misses arithmetic_stats = 1 andalso
          #hits arithmetic_stats = 1 andalso #num_limit arithmetic_stats = 0 andalso
          #num_retained arithmetic_stats = 0 andalso
          #total_retained arithmetic_stats <= #total_limit arithmetic_stats andalso
          #value first_and aconv #value swapped_and andalso
          not (Thm.term_of (Thm.lhs_of (#theorem first_and)) aconv
            Thm.term_of (Thm.lhs_of (#theorem swapped_and))) then ()
        else error "Commutative mask reuse lost its requested operand order"
      (* A separate engine makes the FIFO assertion independent of prior calls. *)
      val fifo_engine = Comma_Sector_Guards.make lthy {max_nodes = 2}
      val _ = #mask_rotate fifo_engine 0 (numeral 3)
      val _ = #mask_rotate fifo_engine 0 (numeral 5)
      val _ = #mask_rotate fifo_engine 0 (numeral 6)
      val evicted_stats = #packed_stats fifo_engine ()
      val _ = #mask_rotate fifo_engine 0 (numeral 5)
      val survivor_stats = #packed_stats fifo_engine ()
      val _ = if #retained evicted_stats = 2 andalso #evicted evicted_stats = 1 andalso
          #hits survivor_stats = #hits evicted_stats + 1 then ()
        else error "Packed FIFO discarded more than its oldest entry"
      val _ = #mask_rotate fifo_engine 0 (numeral 3)
      val reinserted_stats = #packed_stats fifo_engine ()
      val _ = #mask_rotate fifo_engine 0 (numeral 6)
      val _ = if #retained reinserted_stats = 2 andalso #evicted reinserted_stats = 2 andalso
          #hits (#packed_stats fifo_engine ()) = #hits reinserted_stats + 1 then ()
        else error "FIFO reinsertion duplicated an entry or evicted the wrong survivor"
      val identity_and = #mask_and arithmetic_engine (numeral 0) (numeral 7)
      val rotation = #mask_rotate arithmetic_engine 1 (numeral 2)
      val wrapped_rotation = #mask_rotate arithmetic_engine 925 (numeral 2)
      val first_or = #mask_or arithmetic_engine (numeral 6) (numeral 3)
      val or_prior = #packed_stats arithmetic_engine ()
      val swapped_or = #mask_or arithmetic_engine (numeral 3) (numeral 6)
      val _ = if #value first_or aconv #value swapped_or andalso
          #hits (#packed_stats arithmetic_engine ()) = #hits or_prior + 1 andalso
          #value wrapped_rotation aconv #value rotation then ()
        else error "OR commutative reuse or rotation wrap failed"
      val _ = if #value rotation aconv numeral 1 andalso #value identity_and aconv numeral 0 then ()
        else error "Explicit rotation or zero-mask identity failed"
      val invalid_mask = Exn.capture (fn () => #mask_or arithmetic_engine
        (Free ("unbound_mask", @{typ nat})) (numeral 1)) ()
      val _ = if Exn.is_exn invalid_mask andalso
          #failures (#packed_stats arithmetic_engine ()) = 1 then ()
        else error "Packed API accepted an open operand or hid failed work"
      val _ = Comma_Fast_Kernel.report ("explicit_mask_fifo " ^ #report arithmetic_engine ())
      val (_, lthy') = Local_Theory.note
        ((Binding.name "comma_periodic_guard_smoke", []),
          ([first, changed_period, changed_shift, zero_residue, disjoint, restricted,
            #theorem first_and, #theorem swapped_and, #theorem identity_and,
            #theorem rotation, #theorem wrapped_rotation, #theorem first_or,
            #theorem swapped_or, #theorem cold_intersection, #theorem full_and,
            #theorem full_or, #theorem wide_and] @ basis)) lthy
    in lthy' end
\<close>

local_setup \<open>
  fn lthy =>
    let
      fun numeral n = HOLogic.mk_number @{typ nat} n
      val preparation = Comma_Sector_Guards.make lthy {max_nodes=16}
      fun power_of_two exponent =
        let
          val request = @{term "push_bit :: nat => nat => nat"} $
            numeral exponent $ numeral 1
          val theorem = Simplifier.rewrite (#packed_context preparation)
            (Thm.cterm_of lthy request)
          val value = Thm.term_of (Thm.rhs_of theorem)
          val (typ, _) = HOLogic.dest_number value
          val _ = if typ = @{typ nat} andalso
              Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Term.add_frees (Thm.prop_of theorem) []) andalso
              null (Term.add_vars (Thm.prop_of theorem) []) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
            else error "Rotation fixture power is not a closed checked numeral"
        in value end
      val zero = numeral 0
      val bit_zero = numeral 1
      val bit_922 = power_of_two 922
      val bit_923 = power_of_two 923
      val bit_924 = power_of_two 924
      val engine = Comma_Sector_Guards.make lthy {max_nodes=32}
      fun rotate bits = #mask_rotate engine 1 bits
      val zero_rotation = rotate zero
      val wrap_rotation = rotate bit_zero
      val high_rotation = rotate bit_923
      val cold_stats = #packed_stats engine ()
      val repeated_high_rotation = rotate bit_923
      val warm_stats = #packed_stats engine ()
      val wide_rotation = rotate bit_924
      fun exact_rotation bits expected (result: {value: term, theorem: thm}) =
        let
          val requested = @{term comma_rotate_phase} $ numeral 1 $ bits
          val theorem = #theorem result
          val _ = if #value result aconv expected andalso
              Thm.term_of (Thm.lhs_of theorem) aconv requested andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Term.add_frees (Thm.prop_of theorem) []) andalso
              null (Term.add_vars (Thm.prop_of theorem) []) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
            else error "Rotation fast/fallback result did not match its exact closed equation"
        in () end
      val _ = exact_rotation zero zero zero_rotation
      val _ = exact_rotation bit_zero bit_923 wrap_rotation
      val _ = exact_rotation bit_923 bit_922 high_rotation
      val _ = exact_rotation bit_923 bit_922 repeated_high_rotation
      val _ = exact_rotation bit_924 zero wide_rotation
      val _ = if #misses warm_stats = #misses cold_stats andalso
          #hits warm_stats = #hits cold_stats + 1 andalso
          Thm.prop_of (#theorem high_rotation) aconv
            Thm.prop_of (#theorem repeated_high_rotation) then ()
        else error "Repeated bounded rotation did not reuse its exact root equation"
      val _ = Comma_Fast_Kernel.report
        ("rotation_one_fixtures " ^ #report engine ())
    in lthy end
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_periodic_guard_smoke}) then ()
    else error "Periodic guard smoke depends on an oracle";
\<close>
end
