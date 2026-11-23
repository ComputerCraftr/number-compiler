theory Five_Reverse_Prefix_Bridge
  imports Five_Reverse
begin

text \<open>
The concrete source window is checked by a chain of kernel conversion facts.
Each step rewrites one orbit successor, transports the preceding numeral fact,
and evaluates only one decimal reversal.  This avoids normalizing a single
184-step recursive expression.  The resulting facts remain equalities about
the declared integer recurrence; they are not a separately supplied input
word or an extrapolation beyond the finite window.
\<close>

ML \<open>
structure Five_Reverse_Profile =
struct
  fun elapsed_ms started =
    LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started)))

  fun report_elapsed stage started =
    let
      val destination = getenv "ISABELLE_PROOF_PROFILE_LOG"
      val line = "Five reverse stage=" ^ stage ^
        " elapsed_ms=" ^ elapsed_ms started ^ " family=5rev10"
    in
      if destination = "" then ()
      else
        (Output.physical_stderr (line ^ "\n");
          if destination = "1" then ()
          else File.append (Path.explode destination) (line ^ "\n"))
    end
end
\<close>

local_setup \<open>fn lthy =>
  let
    val natT = @{typ nat}
    fun numeral n = HOLogic.mk_number natT n
    val orbit = @{term five_reverse_orbit}
    val step = @{term five_reverse_step}
    (* Use the shared closed-arithmetic simpset: it retains binary numeral and
       div/mod evaluation while excluding unrelated family transition rules. *)
    val setup_started = Time.now ()
    val _ = Five_Reverse_Profile.report_elapsed "simpset-setup-start" setup_started
    val arithmetic_ctxt = Shared_Closed_Arithmetic.natural_context lthy
      |> Simplifier.del_simps
        (@{thms decimal_reverse.simps decimal_digit_count.simps
          decimal_reverse_acc_chunk3.simps decimal_reverse_acc.simps})
    val _ = Five_Reverse_Profile.report_elapsed
      "legacy-reversal-rules-removed" setup_started
    val evaluation_ctxt = Simplifier.add_simps
      (@{thms five_reverse_step_def five_reverse_orbit.simps
        decimal_reverse_accumulator_chunk3})
      arithmetic_ctxt
    val _ = Five_Reverse_Profile.report_elapsed
      "accumulator-rules-added" setup_started
    val started = Time.now ()
    fun orbit_at generation = list_comb (orbit, [numeral generation, numeral 196])
    fun orbit_at_successor generation = list_comb
      (orbit, [HOLogic.mk_Suc (numeral generation), numeral 196])
    fun cterm ctxt term = Thm.cterm_of ctxt term
    fun binop name (left, right) = HOLogic.mk_binop name (left, right)
    fun comparison name (left, right) =
      Const (name, natT --> natT --> HOLogic.boolT) $ left $ right
    fun equation_prop left right =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (left, right))
    fun arithmetic_proof ctxt proposition =
      Goal.prove ctxt [] [] proposition
        (fn {context, ...} => asm_full_simp_tac context 1)
    fun less_prop left right =
      HOLogic.mk_Trueprop (comparison @{const_name less} (left, right))
    fun not_less_prop left right =
      HOLogic.mk_Trueprop (HOLogic.mk_not
        (comparison @{const_name less} (left, right)))
    fun chunk_term n accumulator = list_comb
      (@{term decimal_reverse_acc_chunk3}, [numeral n, numeral accumulator])
    fun decomposition_fact ctxt n q r =
      arithmetic_proof ctxt
        (equation_prop (numeral n)
          (binop @{const_name plus}
            (binop @{const_name times} (numeral 1000, numeral q), numeral r)))
    fun remainder_fact ctxt r =
      arithmetic_proof ctxt (less_prop (numeral r) (numeral 1000))
    fun indexed_decomposition_fact ctxt theorem n q r decomposition remainder =
      let
        val instance = Drule.infer_instantiate ctxt
          [(("n", 0), cterm ctxt (numeral n)),
           (("k", 0), cterm ctxt (numeral 1000)),
           (("q", 0), cterm ctxt (numeral q)),
           (("r", 0), cterm ctxt (numeral r))]
          theorem
      in
        Thm.implies_elim (Thm.implies_elim instance decomposition) remainder
      end
    fun chunk_step ctxt n accumulator =
      let
        val q = IntInf.div (n, 1000)
        val r = IntInf.mod (n, 1000)
        val next_accumulator =
          1000 * accumulator + IntInf.mod (r, 10) * 100 +
            IntInf.mod (IntInf.div (r, 10), 10) * 10 + IntInf.div (r, 100)
        val n_term = numeral n
        val lower = arithmetic_proof ctxt
          (HOLogic.mk_Trueprop
            (comparison @{const_name less_eq} (numeral 1000, n_term)))
        val above_lower = arithmetic_proof ctxt
          (not_less_prop n_term (numeral 1000))
        val decomposition = decomposition_fact ctxt n q r
        val remainder = remainder_fact ctxt r
        val quotient = indexed_decomposition_fact ctxt
          @{thm decimal_nat_div_from_decomposition} n q r decomposition remainder
        val residue = indexed_decomposition_fact ctxt
          @{thm decimal_nat_mod_from_decomposition} n q r decomposition remainder
        val one_step_context = Simplifier.add_simps
          (@{thms decimal_reverse_block3_def} @
            [lower, above_lower, quotient, residue])
          (Simplifier.del_simps @{thms decimal_reverse_acc_chunk3.simps}
            arithmetic_ctxt)
        val input = cterm ctxt (chunk_term n accumulator)
        val unfolded = Conv.rewr_conv
          (mk_meta_eq @{thm decimal_reverse_acc_chunk3.simps}) input
        val reduced = Simplifier.rewrite one_step_context (Thm.rhs_of unfolded)
        val canonical = Conv.bottom_conv
          (K (Conv.try_conv (Conv.rewr_conv
            (Thm.symmetric (mk_meta_eq @{thm One_nat_def}))))) ctxt
          (Thm.rhs_of reduced)
        val result = Thm.transitive unfolded (Thm.transitive reduced canonical)
        val expected = chunk_term q next_accumulator
        val actual = Thm.term_of (Thm.rhs_of result)
        val _ = if Term.aconv_untyped (actual, expected) then ()
          else error ("Five-reverse chunk step did not reduce to its checked state: " ^
            Syntax.string_of_term ctxt actual ^ " expected " ^
            Syntax.string_of_term ctxt expected)
      in (result, q, next_accumulator) end
    fun evaluate_chunk ctxt n initial_accumulator =
      let
        val initial = Thm.reflexive
          (cterm ctxt (chunk_term n initial_accumulator))
        fun loop current accumulator accumulated =
          if current < 1000 then
            let
              val input = Thm.rhs_of accumulated
              val unfolded = Conv.rewr_conv
                (mk_meta_eq @{thm decimal_reverse_acc_chunk3.simps}) input
              val below_upper = arithmetic_proof ctxt
                (less_prop (numeral current) (numeral 1000))
              val terminal_context = Simplifier.add_simps
                (@{thms decimal_reverse_acc.simps} @ [below_upper])
                (Simplifier.del_simps
                  @{thms decimal_reverse_acc_chunk3.simps} arithmetic_ctxt)
              val terminal = Simplifier.rewrite terminal_context
                (Thm.rhs_of unfolded)
              val result = Thm.transitive accumulated
                (Thm.transitive unfolded terminal)
              val _ = HOLogic.dest_number (Thm.term_of (Thm.rhs_of result))
            in result end
          else
            let
              val (transition, quotient, next_accumulator) =
                chunk_step ctxt current accumulator
              val accumulated' = Thm.transitive accumulated transition
            in loop quotient next_accumulator accumulated' end
      in loop n initial_accumulator initial end
    fun evaluate_step ctxt step_application =
      let
        val source = Thm.term_of (snd (Thm.dest_comb step_application))
        val (_, source_value) = HOLogic.dest_number source
        val expansion = Simplifier.rewrite evaluation_ctxt step_application
        val chunk = evaluate_chunk ctxt source_value 0
        val expanded_chunk = Thm.term_of
          (snd (Thm.dest_comb (Thm.rhs_of expansion)))
        val chunk_lhs = Thm.term_of (Thm.lhs_of chunk)
        val _ = if Term.aconv_untyped (expanded_chunk, chunk_lhs) then ()
          else error "Five-reverse expansion changed its chunk source"
        val lifted = Thm.combination
          (Thm.reflexive (fst (Thm.dest_comb (Thm.rhs_of expansion)))) chunk
        val combined = Thm.transitive expansion lifted
        val final = Simplifier.rewrite arithmetic_ctxt (Thm.rhs_of combined)
        val result = Thm.transitive combined final
        val _ = HOLogic.dest_number (Thm.term_of (Thm.rhs_of result))
      in result end
    fun publish generation theorem thy =
      if generation < 180 orelse generation > 184 then thy
      else
        let
          val name = "five_reverse_seed196_orbit_" ^ Int.toString generation
          val (_, thy') = Local_Theory.note
            ((Binding.name name, []), [theorem]) thy
        in thy' end
    fun advance generation previous thy =
      let
        val ctxt = thy
        val next = generation + 1
        (* Function equations are HOL equalities; conversions consume Pure
           equalities.  Turn the checked equation into a meta rewrite before
           applying it to the successor application. *)
        val unfolding = Conv.rewr_conv
          (mk_meta_eq @{thm five_reverse_orbit.simps(2)})
          (cterm ctxt (orbit_at_successor generation))
        val transported = Thm.combination
          (Thm.reflexive (cterm ctxt step)) previous
        val computation_started = Time.now ()
        val computation = evaluate_step ctxt (Thm.rhs_of transported)
        val _ = if next = 1 orelse next = 2 orelse next = 4 then
          Five_Reverse_Profile.report_elapsed
            ("step-normalization-" ^ Int.toString next) computation_started
          else ()
        val stepped = Thm.transitive unfolding
          (Thm.transitive transported computation)
        val index_started = Time.now ()
        val index_equality = Goal.prove ctxt [] []
          (Logic.mk_equals (HOLogic.mk_Suc (numeral generation), numeral next))
          (fn {context, ...} => Arith_Data.arith_tac context 1)
        val _ = if next = 1 orelse next = 2 orelse next = 4 then
          Five_Reverse_Profile.report_elapsed
            ("numeral-index-" ^ Int.toString next) index_started
          else ()
        val orbit_reindex = Thm.combination
          (Thm.combination (Thm.reflexive (cterm ctxt orbit)) index_equality)
          (Thm.reflexive (cterm ctxt (numeral 196)))
        val result = Thm.transitive (Thm.symmetric orbit_reindex) stepped
        val checkpoint =
          if next = 1 orelse next = 2 orelse next = 4 orelse
              next mod 32 = 0 orelse next = 184 then
            (Five_Reverse_Profile.report_elapsed
              ("orbit-prefix-through-" ^ Int.toString next) started;
             thy)
          else thy
      in (result, checkpoint) end
    val ctxt = lthy
    val initial_started = Time.now ()
    val _ = Five_Reverse_Profile.report_elapsed
      "initial-normalization-start" initial_started
    val initial_conversion = Conv.rewr_conv
      (mk_meta_eq @{thm five_reverse_orbit.simps(1)})
      (cterm ctxt (orbit_at 0))
    val _ = HOLogic.dest_number
      (Thm.term_of (Thm.rhs_of initial_conversion))
    val _ = Five_Reverse_Profile.report_elapsed
      "initial-normalization-complete" initial_started
    val initial = initial_conversion
    fun loop generation previous pending =
      if generation = 184 then
        fold (fn (index, theorem) => publish index theorem) (rev pending) lthy
      else
        let
          val (next, _) = advance generation previous lthy
          val next_index = generation + 1
          val pending' = if next_index >= 180 then (next_index, next) :: pending
            else pending
        in loop next_index next pending' end
  in loop 0 initial [] end\<close>

theorem five_reverse_seed196_window_ports_are_orbit_ports:
  "five_reverse_window_ports_from_states
      five_reverse_seed196_window_states =
    map (five_reverse_window_port 196) [180..<184]"
  unfolding five_reverse_seed196_window_states_def
  by (simp add: five_reverse_window_ports_from_states.simps
      five_reverse_window_port_def)

theorem five_reverse_seed196_window_orbit_anchor:
  "map (five_reverse_window_port 196) [180..<184] =
    [(3,(348,960),(348,215)),
     (4,(348,215),(256,215)),
     (2,(256,215),(256,260)),
     (1,(256,260),(311,260))]"
  using five_reverse_seed196_orbit_180 five_reverse_seed196_orbit_181
    five_reverse_seed196_orbit_182 five_reverse_seed196_orbit_183
    five_reverse_seed196_orbit_184
  by (tactic \<open>asm_full_simp_tac
      (Shared_Closed_Arithmetic.natural_context \<^context>
        |> Simplifier.add_simps @{thms five_reverse_window_port_def
          five_reverse_inlet_def five_reverse_border_def
          five_reverse_seed196_orbit_180 five_reverse_seed196_orbit_181
          five_reverse_seed196_orbit_182 five_reverse_seed196_orbit_183
          five_reverse_seed196_orbit_184 upt_rec_numeral list.map
          decimal_digit_count.simps power_numeral_even power_numeral_odd
          power_0 power_one_right}) 1\<close>)

theorem five_reverse_seed196_window_anchor:
  "five_reverse_window_ports_from_states
      five_reverse_seed196_window_states =
    [(3,(348,960),(348,215)),
     (4,(348,215),(256,215)),
     (2,(256,215),(256,260)),
     (1,(256,260),(311,260))]"
  using five_reverse_seed196_window_ports_are_orbit_ports
    five_reverse_seed196_window_orbit_anchor
  by simp

ML \<open>
  val audit_started = Time.now ();
  val _ = Five_Reverse_Profile.report_elapsed
    "final-theorem-audit-start" audit_started;
  val checked = @{thms five_reverse_seed196_orbit_180
    five_reverse_seed196_orbit_181 five_reverse_seed196_orbit_182
    five_reverse_seed196_orbit_183 five_reverse_seed196_orbit_184
    five_reverse_seed196_window_orbit_anchor five_reverse_seed196_window_anchor};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse source-window theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse source-window proof" else ();
  val _ = Five_Reverse_Profile.report_elapsed "final-theorem-audit" audit_started;
\<close>

end
