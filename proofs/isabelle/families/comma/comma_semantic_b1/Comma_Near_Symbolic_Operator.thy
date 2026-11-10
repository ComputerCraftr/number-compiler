theory Comma_Near_Symbolic_Operator
  imports Comma_Closed_Near.Comma_Closed_Near
    Comma_Terminal_Event.Comma_Terminal_Event
    Comma_Semantic_B1_Guarded_Port_Action
    Comma_C1_Occurrence.Comma_C1_Near_Chart_Refinement
begin

text \<open>
The operator is a sector-indexed function of a later-bound headroom H.
Its output is the existing closed Euclidean Near clock; the occurrence
binding supplies p and delta only when the typed terminal action is requested.
The production-facing Near port operator returns the exact source port and
the physical step count separately; its source theorem retains the exact H.
This does not identify physical Near states at distinct H.
\<close>

definition comma_near_parameterized_operator ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_near_parameterized_operator f H = comma_near_closed_germ f H"

record comma_near_event_clock_result =
  near_clock_steps :: nat
  near_clock_residual :: nat
  near_clock_terminal :: comma_terminal_payload

definition comma_near_event_clock_bind ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_near_event_clock_result" where
  "comma_near_event_clock_bind p f delta H =
    (let clock = comma_near_parameterized_operator f H
     in \<lparr>near_clock_steps=fst clock, near_clock_residual=snd clock,
          near_clock_terminal=comma_terminal_event_germ (p mod 924) f delta
            (snd clock)\<rparr>)"

definition comma_near_event_clock_weight ::
    "comma_near_event_clock_result \<Rightarrow> nat" where
  "comma_near_event_clock_weight clock =
    near_clock_steps clock + terminal_units (near_clock_terminal clock)"

definition comma_near_symbolic_port_operator ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action \<times> nat" where
  "comma_near_symbolic_port_operator f H slot =
    (comma_semantic_b1_near_control_port_action f 0
       (near_clock_residual (comma_near_event_clock_bind slot f 0 H)),
     near_clock_steps (comma_near_event_clock_bind slot f 0 H))"

declare comma_near_symbolic_port_operator_def [code drop]

lemma comma_near_symbolic_port_operator_eval [code]:
  "comma_near_symbolic_port_operator f H slot =
    (case comma_near_closed_germ f H of (n,t) \<Rightarrow>
      (comma_semantic_b1_near_control_port_action f 0 t,n))"
  by (cases "comma_near_closed_germ f H")
    (simp add: comma_near_symbolic_port_operator_def
      comma_near_event_clock_bind_def comma_near_parameterized_operator_def Let_def)

lemma comma_near_symbolic_port_operator_source:
  fixes f H slot :: nat
  shows "comma_near_symbolic_port_operator f H slot =
    (comma_semantic_b1_source_port_action (Comma_Near f 0 H) slot,
     fst (comma_near_closed_germ f H))"
  by (simp add: comma_near_symbolic_port_operator_def
      comma_near_event_clock_bind_def comma_near_parameterized_operator_def
      comma_semantic_b1_source_port_action_def
      comma_source_continuation_base.simps
      comma_decisive_sector_target.simps Let_def)

definition comma_near_residual_binding ::
    "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<times> (nat \<times> nat)" where
  "comma_near_residual_binding f H =
    (let g = (if f<9 then 1 else 0)+1;
         d = (10-H mod 10) mod 10;
         P = comma_finite_period_fast f d;
         B = H-g
     in ((d,B mod P),
         ((B div P)*comma_cycle_length_fast f,g+B mod P)))"

lemma comma_near_symbolic_port_operator_residual:
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "1\<le>H" "H\<le>540"
    and interior: "(if f<9 then 1 else 0)<H"
  shows "let binding = comma_near_residual_binding f H;
             elapsed = fst (snd binding); reduced = snd (snd binding)
         in comma_near_symbolic_port_operator f H slot =
           (fst (comma_near_symbolic_port_operator f reduced slot),
            elapsed + snd (comma_near_symbolic_port_operator f reduced slot))"
proof -
  let ?binding = "comma_near_residual_binding f H"
  let ?reduced = "snd (snd ?binding)"
  let ?elapsed = "fst (snd ?binding)"
  have factor:
    "comma_near_closed_germ f H =
      (?elapsed + fst (comma_near_closed_germ f ?reduced),
       snd (comma_near_closed_germ f ?reduced))"
    using comma_near_closed_germ_residual_factorization[OF sector admitted interior]
    by (simp add: comma_near_residual_binding_def Let_def)
  obtain n t where reduced: "comma_near_closed_germ f ?reduced=(n,t)"
    by (cases "comma_near_closed_germ f ?reduced") auto
  have original: "comma_near_closed_germ f H=(?elapsed+n,t)"
    using factor reduced by simp
  show ?thesis
    by (simp add: Let_def comma_near_symbolic_port_operator_eval original reduced)
qed

lemma comma_near_symbolic_port_source_id:
  assumes admitted: "comma_round_admitted (Comma_Near f 0 H)"
  shows "comma_source_continuation_id (Comma_Near f 0 H) =
    (1,[fst (comma_near_symbolic_port_operator f H 0)])"
proof -
  have port:
    "comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0 =
      fst (comma_near_symbolic_port_operator f H 0)"
    using comma_near_symbolic_port_operator_source[of f H 0] by simp
  show ?thesis
    using comma_semantic_b1_source_id_ports[OF admitted]
    by (simp add: comma_source_continuation_base.simps
      comma_decisive_sector_period_def comma_semantic_b1_source_port_actions_def port)
qed

lemma comma_near_prefix_terminal_positive:
  fixes n f H t :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> H" "H \<le> 540"
    and prefix: "comma_near_prefix n f H t"
  shows "1 \<le> t"
proof (cases n)
  case 0
  then show ?thesis using prefix initial by simp
next
  case (Suc m)
  have "(if f < 9 then 2 else 1) \<le> t"
    by (rule comma_near_prefix_endpoint_reserve[OF sector initial])
      (use Suc prefix in auto)
  then show ?thesis by (cases "f < 9") simp_all
qed

theorem comma_near_event_clock_bind_refines:
  fixes p f delta H :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> H" "H \<le> 540"
  shows prefix:
      "comma_near_prefix
        (near_clock_steps (comma_near_event_clock_bind p f delta H)) f H
        (near_clock_residual (comma_near_event_clock_bind p f delta H))"
    and decisive:
      "comma_near_decisive f
        (near_clock_residual (comma_near_event_clock_bind p f delta H))"
    and residual_positive:
      "1 \<le> near_clock_residual (comma_near_event_clock_bind p f delta H)"
    and residual_upper:
      "near_clock_residual (comma_near_event_clock_bind p f delta H) \<le> 540"
    and displacement:
      "H = near_clock_residual (comma_near_event_clock_bind p f delta H) +
        comma_period_displacement f ((10-H mod 10) mod 10)
          (near_clock_steps (comma_near_event_clock_bind p f delta H))"
    and terminal_step:
      "terminal_move (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        comma_finite_step (p mod 924) (Comma_Near f delta
          (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
    and terminal_guards:
      "list_all (\<lambda>g. comma_guard_holds g
        (X,int (near_clock_residual (comma_near_event_clock_bind p f delta H))))
        (terminal_guards (near_clock_terminal (comma_near_event_clock_bind p f delta H)))"
    and terminal_units:
      "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        comma_finite_next_weight p (Comma_Near f delta
          (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
    and weighted_prefix:
      "comma_round_weighted_prefix p p
        (near_clock_steps (comma_near_event_clock_bind p f delta H))
        (Comma_Near f delta H)
        (Comma_Near f delta (near_clock_residual
          (comma_near_event_clock_bind p f delta H)))
        (near_clock_steps (comma_near_event_clock_bind p f delta H))"
    and consumed_units:
      "comma_near_event_clock_weight (comma_near_event_clock_bind p f delta H) =
        near_clock_steps (comma_near_event_clock_bind p f delta H) +
        comma_finite_next_weight p (Comma_Near f delta
          (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
proof -
  let ?clock = "comma_near_event_clock_bind p f delta H"
  let ?n = "near_clock_steps ?clock"
  let ?t = "near_clock_residual ?clock"
  have closed: "comma_near_closed_germ f H=(?n,?t)"
    by (simp add: comma_near_parameterized_operator_def
      comma_near_event_clock_bind_def Let_def)
  have prefix: "comma_near_prefix ?n f H ?t"
    by (rule comma_near_closed_refines(1)[OF sector initial closed])
  have decisive: "comma_near_decisive f ?t"
    by (rule comma_near_closed_refines(2)[OF sector initial closed])
  have t_positive: "1 \<le> ?t"
    by (rule comma_near_prefix_terminal_positive[OF sector initial prefix])
  have displacement:
      "H=?t+comma_period_displacement f ((10-H mod 10) mod 10) ?n"
    by (rule comma_near_prefix_displacement_refines
      [OF sector initial refl prefix])
  have t_upper: "?t \<le> 540"
    using displacement initial(2) by arith
  have event_guards:
      "list_all (\<lambda>g. comma_guard_holds g (X,int ?t))
        (terminal_guards (comma_terminal_event_germ (p mod 924) f delta ?t))"
    by (rule comma_terminal_guards_admitted[OF sector t_positive t_upper])
  have event_units:
      "terminal_units (comma_terminal_event_germ (p mod 924) f delta ?t) =
        comma_finite_next_weight p (Comma_Near f delta ?t)"
    by (rule comma_terminal_event_weight)
  show "comma_near_prefix
      (near_clock_steps (comma_near_event_clock_bind p f delta H)) f H
      (near_clock_residual (comma_near_event_clock_bind p f delta H))"
    using prefix by simp
  show "comma_near_decisive f
      (near_clock_residual (comma_near_event_clock_bind p f delta H))"
    using decisive by simp
  show "1 \<le> near_clock_residual (comma_near_event_clock_bind p f delta H)"
    using t_positive by simp
  show "near_clock_residual (comma_near_event_clock_bind p f delta H) \<le> 540"
    using t_upper by simp
  show "H = near_clock_residual (comma_near_event_clock_bind p f delta H) +
      comma_period_displacement f ((10-H mod 10) mod 10)
        (near_clock_steps (comma_near_event_clock_bind p f delta H))"
    using displacement by simp
  show "terminal_move
      (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
      comma_finite_step (p mod 924)
        (Comma_Near f delta
          (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
    by (simp add: comma_near_event_clock_bind_def Let_def
      comma_terminal_event_germ_def)
  show "list_all (\<lambda>g. comma_guard_holds g
      (X,int (near_clock_residual (comma_near_event_clock_bind p f delta H))))
      (terminal_guards
        (near_clock_terminal (comma_near_event_clock_bind p f delta H)))"
    using event_guards
    by (simp add: comma_near_event_clock_bind_def Let_def)
  show "terminal_units
      (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
      comma_finite_next_weight p (Comma_Near f delta
        (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
    using event_units
    by (simp add: comma_near_event_clock_bind_def Let_def)
  show "comma_round_weighted_prefix p p
      (near_clock_steps (comma_near_event_clock_bind p f delta H))
      (Comma_Near f delta H)
      (Comma_Near f delta
        (near_clock_residual (comma_near_event_clock_bind p f delta H)))
      (near_clock_steps (comma_near_event_clock_bind p f delta H))"
    by (rule comma_near_prefix_weighted[OF prefix])
  show "comma_near_event_clock_weight
      (comma_near_event_clock_bind p f delta H) =
      near_clock_steps (comma_near_event_clock_bind p f delta H) +
      comma_finite_next_weight p (Comma_Near f delta
        (near_clock_residual (comma_near_event_clock_bind p f delta H)))"
    using event_units by (simp add: comma_near_event_clock_weight_def
      comma_near_event_clock_bind_def Let_def)
qed

theorem comma_near_symbolic_port_operator_exact:
  fixes f H slot :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> H" "H \<le> 540"
  shows source_port:
      "comma_semantic_b1_source_port_action (Comma_Near f 0 H) slot =
        fst (comma_near_symbolic_port_operator f H slot)"
    and clock_packet:
      "fst (comma_near_symbolic_port_operator f H slot) =
        comma_source_continuation_action_of_packet
          (Comma_Near f 0
             (near_clock_residual (comma_near_event_clock_bind slot f 0 H)),
           terminal_move
             (near_clock_terminal (comma_near_event_clock_bind slot f 0 H)))"
    and steps:
      "snd (comma_near_symbolic_port_operator f H slot) =
        near_clock_steps (comma_near_event_clock_bind slot f 0 H)"
    and operator_steps:
      "snd (comma_near_symbolic_port_operator f H slot) =
        fst (comma_near_parameterized_operator f H)"
    and weighted_units:
      "comma_near_event_clock_weight (comma_near_event_clock_bind slot f 0 H) =
        snd (comma_near_symbolic_port_operator f H slot) +
        terminal_units
          (near_clock_terminal (comma_near_event_clock_bind slot f 0 H))"
proof -
  let ?clock = "comma_near_event_clock_bind slot f 0 H"
  let ?t = "near_clock_residual ?clock"
  have residual_positive: "1 \<le> ?t"
    using comma_near_event_clock_bind_refines(3)[OF sector initial] by simp
  have residual_upper: "?t \<le> 540"
    using comma_near_event_clock_bind_refines(4)[OF sector initial] by simp
  have control_packet:
      "comma_semantic_b1_near_control_port_action f 0 ?t =
        comma_source_continuation_action_of_packet
          (Comma_Near f 0 ?t,
           comma_fast_step (slot mod 924) (Comma_Near f 0 ?t))"
    by (rule comma_semantic_b1_near_control_port_action_packet
      [OF sector residual_positive residual_upper])
  have event_move:
      "terminal_move (near_clock_terminal ?clock) =
        comma_fast_step (slot mod 924) (Comma_Near f 0 ?t)"
    by (simp add: comma_near_event_clock_bind_def
        comma_near_parameterized_operator_def Let_def
        comma_terminal_event_germ_def comma_fast_step_correct)
  have clock_action:
      "comma_semantic_b1_near_control_port_action f 0 ?t =
        comma_source_continuation_action_of_packet
          (Comma_Near f 0 ?t, terminal_move (near_clock_terminal ?clock))"
    using control_packet event_move by simp
  show "comma_semantic_b1_source_port_action (Comma_Near f 0 H) slot =
      fst (comma_near_symbolic_port_operator f H slot)"
    using comma_near_symbolic_port_operator_source[of f H slot]
    by simp
  show "fst (comma_near_symbolic_port_operator f H slot) =
      comma_source_continuation_action_of_packet
        (Comma_Near f 0
           (near_clock_residual (comma_near_event_clock_bind slot f 0 H)),
         terminal_move
           (near_clock_terminal (comma_near_event_clock_bind slot f 0 H)))"
    using clock_action by (simp add: comma_near_symbolic_port_operator_def)
  show "snd (comma_near_symbolic_port_operator f H slot) =
      near_clock_steps (comma_near_event_clock_bind slot f 0 H)"
    by (simp add: comma_near_symbolic_port_operator_def)
  show "snd (comma_near_symbolic_port_operator f H slot) =
      fst (comma_near_parameterized_operator f H)"
    by (simp add: comma_near_symbolic_port_operator_def
        comma_near_event_clock_bind_def Let_def)
  show "comma_near_event_clock_weight
      (comma_near_event_clock_bind slot f 0 H) =
      snd (comma_near_symbolic_port_operator f H slot) +
      terminal_units (near_clock_terminal (comma_near_event_clock_bind slot f 0 H))"
    by (simp add: comma_near_event_clock_weight_def
        comma_near_symbolic_port_operator_def)
qed

theorem comma_near_event_clock_round_close_cocycle:
  fixes p f delta H k :: nat and u :: comma_finite_position
    and event :: comma_round_result
  assumes sector: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> H" "H \<le> 540"
    and tail:
      "comma_round_close p
        (Comma_Near f delta
          (near_clock_residual (comma_near_event_clock_bind p f delta H))) =
        (k,u,event)"
  shows "comma_round_close p (Comma_Near f delta H) =
      (near_clock_steps (comma_near_event_clock_bind p f delta H)+k,u,event)"
proof -
  let ?clock = "comma_near_event_clock_bind p f delta H"
  let ?n = "near_clock_steps ?clock"
  let ?t = "near_clock_residual ?clock"
  have closed: "comma_near_closed_germ f H=(?n,?t)"
    by (simp add: comma_near_parameterized_operator_def
      comma_near_event_clock_bind_def Let_def)
  have germ: "comma_near_germ f H=(?n,?t)"
    using comma_near_closed_germ_correct[OF sector initial] closed
    by metis
  show ?thesis by (rule comma_near_germ_round_close[OF germ tail])
qed

lemma comma_near_event_clock_fork_order:
  fixes p f delta H t a :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and initial: "1 \<le> H" "H \<le> 540"
    and fork:
      "terminal_move (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        Comma_Fork a delta"
  defines "t \<equiv> near_clock_residual (comma_near_event_clock_bind p f delta H)"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) =
      [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
    and "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=0"
proof -
  have t_positive: "1 \<le> t"
    using comma_near_event_clock_bind_refines(3)[OF sector initial]
    by (simp add: t_def)
  have t_upper: "t \<le> 540"
    using comma_near_event_clock_bind_refines(4)[OF sector initial]
    by (simp add: t_def)
  have valid: "1 \<le> f" "f \<le> 9" "5 \<le> p" "1 \<le> t" "t \<le> 540"
  proof -
    show "1 \<le> f" by (rule sector(1))
    show "f \<le> 9" by (rule sector(2))
    show "5 \<le> p" by (rule exponent)
    show "1 \<le> t" by (rule t_positive)
    show "t \<le> 540" by (rule t_upper)
  qed
  have move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta t) =
        Comma_Fork a delta"
    using fork by (simp add: t_def comma_near_event_clock_bind_def Let_def)
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) =
      [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
    by (rule comma_terminal_fork_children(1)[OF valid move])
  show "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=0"
    using comma_terminal_fork_children(2)[OF valid move]
    by (simp add: t_def comma_near_event_clock_bind_def Let_def)
qed

lemma comma_near_event_clock_next_action:
  fixes p f delta H t :: nat and target :: comma_finite_position
  assumes next_move:
      "terminal_move (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        Comma_Next target"
  defines "t \<equiv> near_clock_residual (comma_near_event_clock_bind p f delta H)"
  shows "comma_chart_apply
      (terminal_action (near_clock_terminal (comma_near_event_clock_bind p f delta H)))
      (comma_chart_coordinates p (Comma_Near f delta t)) =
      comma_chart_coordinates p target"
    and "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=1"
proof -
  have event_move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta t) =
        Comma_Next target"
    using next_move by (simp add: t_def comma_near_event_clock_bind_def Let_def)
  show "comma_chart_apply
      (terminal_action (near_clock_terminal (comma_near_event_clock_bind p f delta H)))
      (comma_chart_coordinates p (Comma_Near f delta t)) =
      comma_chart_coordinates p target"
    using comma_terminal_event_refines_step(1)[OF event_move]
    by (simp add: t_def comma_near_event_clock_bind_def Let_def)
  show "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=1"
    using comma_terminal_event_refines_step(2)[OF event_move]
    by (simp add: t_def comma_near_event_clock_bind_def Let_def)
qed

lemma comma_near_event_clock_next_child:
  fixes p f delta H t :: nat and target :: comma_finite_position
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and initial: "1 \<le> H" "H \<le> 540"
    and next_move:
      "terminal_move (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        Comma_Next target"
  defines "t \<equiv> near_clock_residual (comma_near_event_clock_bind p f delta H)"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) = [comma_chart_value p target]"
    and "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=1"
proof -
  have t_positive: "1 \<le> t"
    using comma_near_event_clock_bind_refines(3)[OF sector initial]
    by (simp add: t_def)
  have t_upper: "t \<le> 540"
    using comma_near_event_clock_bind_refines(4)[OF sector initial]
    by (simp add: t_def)
  have valid: "1 \<le> f" "f \<le> 9" "5 \<le> p" "1 \<le> t" "t \<le> 540"
  proof -
    show "1 \<le> f" by (rule sector(1))
    show "f \<le> 9" by (rule sector(2))
    show "5 \<le> p" by (rule exponent)
    show "1 \<le> t" by (rule t_positive)
    show "t \<le> 540" by (rule t_upper)
  qed
  have move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta t) =
        Comma_Next target"
    using next_move by (simp add: t_def comma_near_event_clock_bind_def Let_def)
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) = [comma_chart_value p target]"
    by (rule comma_terminal_next_children[OF valid move])
  show "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=1"
    using comma_terminal_event_refines_step(2)[OF move]
    by (simp add: t_def comma_near_event_clock_bind_def Let_def)
qed

lemma comma_near_event_clock_landmine_empty:
  fixes p f delta H t :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and initial: "1 \<le> H" "H \<le> 540"
    and landmine:
      "terminal_move (near_clock_terminal (comma_near_event_clock_bind p f delta H)) =
        Comma_Landmine delta"
  defines "t \<equiv> near_clock_residual (comma_near_event_clock_bind p f delta H)"
  shows "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) = []"
    and "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=0"
proof -
  have t_positive: "1 \<le> t"
    using comma_near_event_clock_bind_refines(3)[OF sector initial]
    by (simp add: t_def)
  have t_upper: "t \<le> 540"
    using comma_near_event_clock_bind_refines(4)[OF sector initial]
    by (simp add: t_def)
  have valid: "1 \<le> f" "f \<le> 9" "5 \<le> p" "1 \<le> t" "t \<le> 540"
  proof -
    show "1 \<le> f" by (rule sector(1))
    show "f \<le> 9" by (rule sector(2))
    show "5 \<le> p" by (rule exponent)
    show "1 \<le> t" by (rule t_positive)
    show "t \<le> 540" by (rule t_upper)
  qed
  have move:
      "terminal_move (comma_terminal_event_germ (p mod 924) f delta t) =
        Comma_Landmine delta"
    using landmine by (simp add: t_def comma_near_event_clock_bind_def Let_def)
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) = []"
    by (rule comma_terminal_landmine_children(1)[OF valid move])
  show "terminal_units (near_clock_terminal (comma_near_event_clock_bind p f delta H))=0"
    using comma_terminal_landmine_children(2)[OF valid move]
    by (simp add: t_def comma_near_event_clock_bind_def Let_def)
qed

lemma comma_near_closed_germ_82_92:
  "comma_near_closed_germ 1 82=(0,82)"
  "comma_near_closed_germ 1 92=(1,11)"
  by (simp_all add: comma_near_closed_germ_def
    comma_near_residual_count.simps(2)[where k=8 and f=1 and d=8 and b=80, simplified]
    comma_near_residual_count.simps(2)[where k=8 and f=1 and d=8 and b=90, simplified]
    comma_near_residual_count.simps(2)[where k=7 and f=1 and d=9 and b=9, simplified]
    comma_cycle_length_fast_def comma_finite_period_fast_def Let_def nth_Cons')

lemma comma_near_event_clock_82_92_separate:
  fixes p delta :: nat
  shows "comma_near_parameterized_operator 1 82=(0,82)"
    and "comma_near_parameterized_operator 1 92=(1,11)"
    and "comma_finite_step (p mod 924) (Comma_Near 1 delta 82)=
      Comma_Fork 2 delta"
    and "comma_finite_step (p mod 924) (Comma_Near 1 delta 92)=
      Comma_Next (Comma_Near 1 delta 11)"
    and "near_clock_steps (comma_near_event_clock_bind p 1 delta 82)=0"
    and "near_clock_steps (comma_near_event_clock_bind p 1 delta 92)=1"
    and "near_clock_residual (comma_near_event_clock_bind p 1 delta 92)=11"
    and "terminal_move (near_clock_terminal
          (comma_near_event_clock_bind p 1 delta 82))=Comma_Fork 2 delta"
    and "terminal_move (near_clock_terminal
          (comma_near_event_clock_bind p 1 delta 92))=
          Comma_Next (Comma_Entry 2 delta 81)"
  by (simp_all add: comma_near_parameterized_operator_def
    comma_near_event_clock_bind_def comma_near_closed_germ_82_92
    comma_near_closed_germ_82_92[simplified]
    comma_terminal_event_germ_def comma_finite_step_def Let_def)

ML \<open>
  val checked = @{thms comma_near_prefix_terminal_positive
    comma_near_symbolic_port_operator_eval
    comma_near_symbolic_port_operator_source
    comma_near_symbolic_port_operator_residual comma_near_symbolic_port_source_id
    comma_near_event_clock_bind_refines comma_near_event_clock_round_close_cocycle
    comma_near_symbolic_port_operator_exact
    comma_near_event_clock_fork_order comma_near_event_clock_next_action
    comma_near_event_clock_next_child comma_near_event_clock_landmine_empty
    comma_near_event_clock_82_92_separate};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Near symbolic operator refinement depends on an oracle";
\<close>
end
