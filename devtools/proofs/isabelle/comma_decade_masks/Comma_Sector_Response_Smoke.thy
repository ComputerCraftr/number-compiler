theory Comma_Sector_Response_Smoke
  imports Comma_Sector_Response_Check
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
      val trim_prior = #packed_stats engine ()
      val explicit_full = #guard engine 1 0 0
      val full_prior = #packed_stats engine ()
      val full_and = #mask_and engine (bits first) (bits explicit_full)
      val full_or = #mask_or engine (bits first) (bits explicit_full)
      val full_after = #packed_stats engine ()
      val _ = if #value full_and aconv bits first andalso
          #value full_or aconv bits explicit_full andalso
          #full_hits full_after = #full_hits full_prior + 2 andalso
          #misses full_after = #misses full_prior andalso
          #publication_reuses full_prior = #publication_reuses trim_prior + 1 then ()
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
      (* AND returns num option while OR returns num. Directed constructor
         conversion preserves both result types without storing suffix proofs. *)
      val sub_engine = Comma_Sector_Guards.make lthy {max_nodes = 128}
      val sub_and = #mask_and sub_engine (numeral 12) (numeral 6)
      val shared_and = #mask_and sub_engine (numeral 25) (numeral 13)
      val sub_or = #mask_or sub_engine (numeral 12) (numeral 6)
      val shared_or = #mask_or sub_engine (numeral 25) (numeral 13)
      val or_sub_after = #packed_stats sub_engine ()
      val _ = if #value sub_and aconv numeral 4 andalso
          #value shared_and aconv numeral 9 andalso
          #value sub_or aconv numeral 14 andalso #value shared_or aconv numeral 29 andalso
          #num_nodes or_sub_after > 0 andalso
          #num_nodes or_sub_after = #num_conversions or_sub_after andalso
          #retained or_sub_after = 4 andalso #num_failures or_sub_after=0 andalso
          null(Thm_Deps.all_oracles (map #theorem [sub_and,shared_and,sub_or,shared_or]))
        then () else error "Typed directed packed conversion lost exact authority or retained suffixes"
      val _ = Comma_Fast_Kernel.report ("packed_direct_num " ^ #report sub_engine ())
      val first_and = #mask_and arithmetic_engine (numeral 6) (numeral 3)
      val swapped_and = #mask_and arithmetic_engine (numeral 3) (numeral 6)
      val _ = if #misses (#packed_stats arithmetic_engine ()) = 1 andalso
          #hits (#packed_stats arithmetic_engine ()) = 1 andalso
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

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_periodic_guard_smoke}) then ()
    else error "Periodic guard smoke depends on an oracle";
\<close>
end
