(* Closed, oracle-free compilation of the existing arithmetic definitions. *)
structure Comma_Entry_Arithmetic =
struct
  fun numeral n = HOLogic.mk_number @{typ nat} n
  fun numeral_context ctxt = put_simpset HOL_basic_ss ctxt addsimps
    @{thms One_nat_def[symmetric] Suc_1 Suc_numeral add_num_simps}
  (* Closed natural arithmetic: no family transition or recursive observer rules. *)
  fun natural_context ctxt = (put_simpset HOL_ss ctxt
    |> Simplifier.add_cong @{thm if_weak_cong}) addsimps
    @{thms arith_simps arith_special rel_simps Let_def
      One_nat_def[symmetric] Suc_1 Suc_numeral
      diff_nat_numeral nat_numeral_diff_1 nat_numeral nat_0 nat_1 diff_zero
      diff_self_eq_0 diff_0_eq_0
      div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
      one_div_numeral one_mod_numeral numeral_div_numeral numeral_mod_numeral
      divmod_trivial divmod_cancel divmod_steps divmod_step_def
      fst_conv snd_conv numeral_One case_prod_beta
      euclidean_size_nat_less_eq_iff mult_1_left mult_1_right}
  (* Dependency nodes are immutable and identified by Isabelle's proof serial.
     Each root is inspected on every call. A node certificate is committed only
     after the entire traversal succeeds; final exports use the builtin audit. *)
  fun make_certifier ctxt =
    let
      val certified = Unsynchronized.ref Intset.empty
      val calls = Unsynchronized.ref 0
      val failed_calls = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      fun collect (PBody {oracles, thms, ...}) seen =
        if not (null oracles) then error "Oracle in local arithmetic proof"
        else fold (fn (id, node) => fn known =>
          if Intset.member known id then known
          else collect (Future.join (Proofterm.thm_node_body node))
            (Intset.insert id known)) thms seen
      fun certify th =
        let
          val start = Time.now ()
          val result = Exn.capture (fn () =>
            let
              val _ = if Thm.nprems_of th = 0 andalso null (Thm.hyps_of th)
                then () else error ("Open cached theorem: " ^ Thm.string_of_thm ctxt th)
            in collect (Thm.proof_body_of th) (!certified) end) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
        in case result of
          Exn.Res next => (certified := next; calls := !calls + 1; th)
        | Exn.Exn failure => (failed_calls := !failed_calls + 1; Exn.reraise failure)
        end
      fun stats () = {calls = !calls, failed_calls = !failed_calls,
        nodes = Intset.size (!certified), milliseconds = Time.toMilliseconds (!elapsed)}
    in (certify, stats) end

  fun build ctxt =
    let
      val canonical = numeral_context ctxt
      val (certify, _) = make_certifier ctxt
      fun finish th = certify (Thm.transitive th
        (Simplifier.rewrite canonical (Thm.rhs_of th)))
      val gcd_ctxt = ctxt addsimps @{thms gcd_nat.simps}
      val gcds = map (fn f => finish (Simplifier.rewrite gcd_ctxt
        (Thm.cterm_of ctxt (@{term "gcd :: nat => nat => nat"} $
          numeral f $ numeral 10)))) (1 upto 9)
      val arithmetic = ctxt addsimps gcds
      (* The same nine closed gcd certificates discharge cycle lengths once.
         Consumers select one exact unary equation; no recursive gcd rule is
         exported or required by their hot arithmetic context. *)
      val cycle_unfold = put_simpset HOL_basic_ss ctxt addsimps
        @{thms comma_cycle_length_def}
      fun cycle_length f =
        let
          val unfolded = Simplifier.rewrite cycle_unfold (Thm.cterm_of ctxt
            (@{term comma_cycle_length} $ numeral f))
        in finish (Thm.transitive unfolded
          (Simplifier.rewrite arithmetic (Thm.rhs_of unfolded))) end
      val cycle_lengths = map cycle_length (1 upto 9)
      val period_unfold = put_simpset HOL_basic_ss ctxt addsimps
        @{thms comma_finite_period_def Let_def}
      fun period f d =
        let
          val unfolded = Simplifier.rewrite period_unfold (Thm.cterm_of ctxt
            (@{term comma_finite_period} $ numeral f $ numeral d))
        in finish (Thm.transitive unfolded
          (Simplifier.rewrite arithmetic (Thm.rhs_of unfolded))) end
      val periods = maps (fn f => map (period f) (0 upto 9)) (1 upto 9)
      fun value th = snd (HOLogic.dest_number (Thm.term_of (Thm.rhs_of th)))
      val catalog = sort_distinct int_ord (map value periods)
      fun short p = finish (Simplifier.rewrite
        (arithmetic addsimps @{thms comma_short_period_def})
        (Thm.cterm_of ctxt (@{term comma_short_period} $ numeral p)))
      val short_periods = map short catalog
      fun power p k = finish (Simplifier.rewrite arithmetic
        (Thm.cterm_of ctxt (@{term "mod_exp :: nat => nat => nat => nat"} $
          numeral 10 $ numeral (5 + k) $ numeral p)))
      val powers = maps (fn (p, th) => map (power p) (0 upto (value th - 1)))
        (catalog ~~ short_periods)
      val _ = if length cycle_lengths = 9 andalso
        map value cycle_lengths = [10, 5, 10, 5, 2, 5, 10, 5, 10] andalso
        length periods = 90 andalso length catalog = 17 andalso
        length powers = 116 then ()
        else error "Unexpected canonical Entry arithmetic catalog size"
    in {cycle_lengths = cycle_lengths, periods = periods,
      short_periods = short_periods, powers = powers} end

  fun conversion ctxt certify {periods, short_periods, powers} =
    let
      val canonical = numeral_context ctxt
      val arithmetic = ctxt
        |> fold Simplifier.del_simp @{thms eval_mod_exp eval_mod_exp_aux}
      fun rules facts = put_simpset HOL_basic_ss ctxt addsimps facts
      val period_rules = rules periods
      val short_rules = rules short_periods
      val power_rules = rules powers
      val power_calls = Unsynchronized.ref 0
      fun trans th conversion = Thm.transitive th (conversion (Thm.rhs_of th))
      fun normalize ct = Simplifier.rewrite arithmetic ct
        |> (fn th => trans th (Simplifier.rewrite canonical))
      fun closed_number th =
        (HOLogic.dest_number (Thm.term_of (Thm.rhs_of th)); certify th)
      fun table rules ct = normalize ct
        |> (fn th => trans th (Simplifier.rewrite rules)) |> closed_number
      fun short_conv _ ct =
        (case Thm.term_of ct of
          Const (name, _) $ _ => if name = @{const_name comma_short_period}
            then table short_rules ct else Conv.all_conv ct
        | _ => Conv.all_conv ct)
      fun power ct =
        let
          val _ = power_calls := !power_calls + 1
          val normalized = normalize ct
          val expanded = trans normalized (Conv.rewr_conv
            (@{thm comma_power_residue_rotated} RS @{thm eq_reflection}))
          val period = trans expanded (Conv.bottom_conv short_conv ctxt)
          val exponent = trans period normalize
        in trans exponent (Simplifier.rewrite power_rules) |> closed_number end
      fun local_conv _ ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [_, _]) =>
            if name = @{const_name comma_finite_period} then table period_rules ct
            else if name = @{const_name comma_power_residue} then power ct
            else Conv.all_conv ct
        | (Const (name, _), [_]) =>
            if name = @{const_name comma_short_period} then table short_rules ct
            else Conv.all_conv ct
        | _ => Conv.all_conv ct)
    in (Conv.bottom_conv local_conv ctxt, fn () => !power_calls) end

end
