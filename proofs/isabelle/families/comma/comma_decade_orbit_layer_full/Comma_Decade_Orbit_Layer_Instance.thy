theory Comma_Decade_Orbit_Layer_Instance
  imports Comma_Decade_Orbit_Layer.Comma_Decade_Orbit_Layer
begin

declare comma_decade_block_power.simps [simp del]

definition comma_B5_orbit_phase_complete :: "nat \<Rightarrow> bool" where
  "comma_B5_orbit_phase_complete r = (\<forall>x<91. \<exists>h terminal.
    comma_decade_block_power 5 (Comma_Decade r x)=Comma_Block_Stop h terminal \<and> h\<le>26)"

lemma comma_B5_orbit_phase_from_layer:
  assumes "comma_decade_orbit_layer_correct 5 r layer"
    "comma_decade_orbit_layer_complete 26 layer"
  shows "comma_B5_orbit_phase_complete r"
  unfolding comma_B5_orbit_phase_complete_def
  using comma_decade_orbit_layer_complete_sound[OF assms] by blast

lemma comma_B5_orbit_interval_singleton:
  assumes "comma_B5_orbit_phase_complete r"
  shows "\<forall>i. r\<le>i \<and> i<Suc r \<longrightarrow> comma_B5_orbit_phase_complete i"
  using assms by (auto simp: less_Suc_eq_le intro: antisym)

lemma comma_B5_orbit_interval_join:
  assumes "\<forall>i. lo\<le>i \<and> i<mid \<longrightarrow> comma_B5_orbit_phase_complete i"
    "\<forall>i. mid\<le>i \<and> i<hi \<longrightarrow> comma_B5_orbit_phase_complete i"
  shows "\<forall>i. lo\<le>i \<and> i<hi \<longrightarrow> comma_B5_orbit_phase_complete i"
  using assms by (metis leI)

text \<open>This is the same rank-free B5 acceptance obligation as the
ninety-one-cell checker, but every finite layer is represented by the exact
forty-six-class offset orbit quotient.  A timeout still leaves the theorem
unproved.\<close>

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Decade_Orbit_Layer_Check.make lthy {max_layers = 8192}
    val numeral = Comma_Entry_Arithmetic.numeral_context lthy
    fun join ((lo, mid, left), (mid', hi, right)) =
      if mid <> mid' then error "Nonadjacent quotient B5 phase coverage" else
        (lo, hi, @{thm comma_B5_orbit_interval_join} OF [left, right])
    fun push item [] = [item]
      | push (item as (lo, hi, _)) (prior as ((a, b, _) :: rest)) =
          if hi-lo = b-a then push (join (hd prior, item)) rest else item :: prior
    fun add phase stack =
      let
        val checked = #complete engine 5 phase 26
        val phase_fact = @{thm comma_B5_orbit_phase_from_layer} OF
          [#correct (#layer checked), #complete checked]
        val interval = Simplifier.simplify numeral
          (@{thm comma_B5_orbit_interval_singleton} OF [phase_fact])
        val _ = if getenv "COMMA_PROFILE_LOG" = "" then () else
          Comma_Fast_Kernel.report
            ("B5 orbit checked phase=" ^ Int.toString phase ^ " " ^ #report engine ())
      in push (phase, phase+1, interval) stack end
    val stack = fold add (0 upto 923) []
    val (lo, hi, rectangle) = case stack of
        [] => error "Empty quotient B5 coverage"
      | latest :: earlier => fold (fn older => fn acc => join (older, acc)) earlier latest
    val _ = if lo = 0 andalso hi = 924 then ()
      else error "Quotient B5 phase coverage is not exactly [0,924)"
    val _ = if Thm.nprems_of rectangle = 0 andalso null (Thm.hyps_of rectangle)
        andalso null (Thm_Deps.all_oracles [rectangle]) then ()
      else error "Quotient B5 coverage has open assumptions or an oracle"
  in #2 (Local_Theory.note
    ((Binding.name "comma_B5_orbit_phase_coverage", []), [rectangle]) lthy) end\<close>

theorem comma_B5_orbit_all_states_complete:
  assumes "comma_decade_admitted s"
  shows "\<exists>h terminal. comma_decade_block_power 5 s=Comma_Block_Stop h terminal \<and> h\<le>26"
proof -
  obtain r x where shape: "s=Comma_Decade r x" by (cases s) auto
  have phase: "r<924" and offset: "x\<le>90" using assms by (simp_all add: shape)
  have width: "x<91" using offset by arith
  have complete: "comma_B5_orbit_phase_complete r"
    using comma_B5_orbit_phase_coverage phase by simp
  show ?thesis using complete width
    by (simp add: shape comma_B5_orbit_phase_complete_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_B5_orbit_all_states_complete}) then ()
    else error "Quotient B5 complete instance depends on an oracle";
\<close>

end
