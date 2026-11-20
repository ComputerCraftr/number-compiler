theory Comma_Future_M204_Source_Bridge
  imports Comma_Semantic_Future.Comma_Semantic_Initial_Prefix
    Comma_Semantic_B1.Comma_Frontier_M204_Generic
    Comma_Semantic_B1.Comma_Parametric_Typed_Soundness
begin

text \<open>
The physical source still supplies its actual first round.  The M204 value
is used only after a checked crossing into a decade source; it determines
the exact summary and the existing semantic provider's result.  This theory
does not authenticate a candidate 16-root source table or a global future
class map.
\<close>

lemma comma_future_m204_source_closure_physical_round:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and index: "i < length (cf24_closures bundle)"
    and program: "cf24_programs bundle !
      cf24_closure_program_ref (cf24_closures bundle ! i) = program"
    and shift: "cf24_closure_full_shift (cf24_closures bundle ! i) = 0"
    and canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source = comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source = Some program"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_output_root (cf24_closures bundle ! i)) =
    Some (comma_parametric_typed_mask_code
      (comma_phase_program_full_action_output phase
        (comma_decisive_endpoint_round phase source)))"
proof -
  have physical: "comma_semantic_phase_program_round phase program 0 =
      comma_decisive_endpoint_round phase source"
    using comma_semantic_phase_program_round_exact
      [where phase=phase and shift=0, OF canonical admitted normalized binding]
    by (cases source) simp_all
  show ?thesis
    using comma_frontier24_closures_typed_exact[OF certified index, where phase=phase]
      program shift physical comma_phase_program_full_action_fold_fusion
    by simp
qed

lemma comma_future_m204_summary_lookup:
  assumes cert: "comma_frontier_m204_bellman D"
    and admitted: "comma_decade_admitted (Comma_Decade phase off)"
  obtains h tau where
    "h \<le> 26"
    "comma_decade_exact_summary (Comma_Decade phase off) h tau"
    "D phase (comma_offset_orbit off) = comma_terminal_weight_encode h tau"
    "comma_semantic_decade_summary (Comma_Decade phase off) = Some (h,tau)"
proof -
  have phase: "phase < 924" using admitted by simp
  have root: "comma_offset_orbit off < 46" by (rule comma_offset_orbit_bound)
  obtain h tau where bound: "h \<le> 26"
    and summary: "comma_decade_exact_summary (Comma_Decade phase off) h tau"
    using comma_frontier_m204_B32_from_checked_bellman[OF cert admitted] by blast
  have encoded: "D phase (comma_offset_orbit off) = comma_terminal_weight_encode h tau"
    using comma_frontier_m204_summary_value[OF cert summary admitted] by simp
  have terminal: "comma_terminal_weight_admitted tau"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have decoded: "comma_terminal_weight_decode (D phase (comma_offset_orbit off)) = (h,tau)"
    using encoded comma_terminal_weight_decode_encode[OF terminal] by simp
  have stop: "comma_semantic_b1_action_power 5 phase (comma_offset_orbit off) =
      Comma_Semantic_B1_Stop (D phase (comma_offset_orbit off))"
    by (rule comma_frontier_m204_exact_weight_from_checked_bellman[OF cert phase root])
  have selected: "comma_semantic_decade_summary (Comma_Decade phase off) = Some (h,tau)"
    using admitted stop decoded by (simp add: comma_semantic_decade_summary_def)
  show thesis by (rule that[OF bound summary encoded selected])
qed

lemma comma_future_m204_provider_exact:
  assumes cert: "comma_frontier_m204_bellman D"
  shows "comma_semantic_decade_provider_exact comma_semantic_decade_summary"
proof (unfold comma_semantic_decade_provider_exact_def, intro allI impI)
  fix source
  assume admitted: "comma_decade_admitted source"
  obtain phase off where source: "source = Comma_Decade phase off"
    by (cases source) auto
  obtain h tau where bound: "h \<le> 26"
    and summary: "comma_decade_exact_summary source h tau"
    and selected: "comma_semantic_decade_summary source = Some (h,tau)"
    using comma_future_m204_summary_lookup[OF cert, of phase off] admitted source by blast
  show "case comma_semantic_decade_summary source of None \<Rightarrow> False
      | Some (h,terminal) \<Rightarrow> h \<le> 26 \<and> comma_decade_exact_summary source h terminal"
    using selected bound summary by simp
qed

lemma comma_future_m204_direct_fork_source:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,final,Comma_Round_Fork a delta)"
  shows "delta=0 \<and> 2\<le>a \<and> a\<le>9 \<and>
    comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (Comma_Future_Fork a) \<and>
    comma_semantic_boundary_children comma_semantic_decade_summary q (Comma_Future_Fork a) =
      [(Comma_N,a,snd (snd q)),(Comma_Z,a,snd (snd q))]"
proof -
  obtain kind source_a phase where q: "q=(kind,source_a,phase)" by (cases q) auto
  have source: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases q) (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    using valid by (cases q) (simp add: comma_finite_initial_def comma_boundary_valid_def)
  have terminal_delta: "comma_round_delta final=0"
    using comma_round_close_delta[OF close source] source_delta by simp
  have step: "comma_finite_step (snd (snd q) mod 924) final = Comma_Fork a delta"
    using comma_round_close_refines_trace[OF close] by simp
  have digit: "2\<le>a \<and> a\<le>9" by (rule comma_finite_fork_digit_bounds[OF step])
  have zero: "delta=0" using step terminal_delta
    by (cases final) (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  have phase: "snd (snd q) < 924" using valid q by (simp add: comma_boundary_valid_def)
  show ?thesis using valid close digit zero phase q
    by (simp add: comma_semantic_boundary_control_step_def comma_semantic_boundary_step_def
      comma_semantic_boundary_children_def comma_native_boundary_children_def)
qed

lemma comma_future_m204_direct_landmine_source:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,final,Comma_Round_Landmine delta)"
  shows "delta=0 \<and>
    comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some Comma_Future_Landmine \<and>
    comma_semantic_boundary_children comma_semantic_decade_summary q Comma_Future_Landmine = []"
proof -
  obtain kind source_a phase where q: "q=(kind,source_a,phase)" by (cases q) auto
  have source: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases q) (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    using valid by (cases q) (simp add: comma_finite_initial_def comma_boundary_valid_def)
  have terminal_delta: "comma_round_delta final=0"
    using comma_round_close_delta[OF close source] source_delta by simp
  have step: "comma_finite_step (snd (snd q) mod 924) final = Comma_Landmine delta"
    using comma_round_close_refines_trace[OF close] by simp
  have zero: "delta=0" using step terminal_delta
    by (cases final) (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)
  show ?thesis using valid close zero q
    by (simp add: comma_semantic_boundary_control_step_def comma_semantic_boundary_step_def
      comma_semantic_boundary_children_def comma_native_boundary_children_def)
qed

theorem comma_future_m204_crossing_source_exact:
  fixes q :: comma_boundary_state
  assumes cert: "comma_frontier_m204_bellman D"
    and valid: "comma_boundary_valid q"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,final,Comma_Round_Cross (Comma_Entry 1 1 x))"
  obtains h tau where
    "x \<le> 90" "h \<le> 26"
    "comma_decade_exact_summary (Comma_Decade ((snd (snd q)+1) mod 924) x) h tau"
    "D ((snd (snd q)+1) mod 924) (comma_offset_orbit x) =
      comma_terminal_weight_encode h tau"
    "h = D ((snd (snd q)+1) mod 924) (comma_offset_orbit x) div 9"
    "comma_terminal_weight_digit tau =
      D ((snd (snd q)+1) mod 924) (comma_offset_orbit x) mod 9"
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau))"
    "comma_semantic_boundary_children comma_semantic_decade_summary q
      (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau)) =
      (case tau of Comma_Terminal_Fork a \<Rightarrow>
        [(Comma_N,a,(snd (snd q)+1+h) mod 924),
         (Comma_Z,a,(snd (snd q)+1+h) mod 924)]
       | Comma_Terminal_Landmine \<Rightarrow> [])"
proof -
  obtain kind a phase where q: "q=(kind,a,phase)" by (cases q) auto
  have off: "x \<le> 90"
    using comma_round_close_crossing_shape[OF close] by auto
  let ?phase = "(snd (snd q)+1) mod 924"
  have admitted: "comma_decade_admitted (Comma_Decade ?phase x)"
    using off by simp
  obtain h tau where bound: "h \<le> 26"
    and summary: "comma_decade_exact_summary (Comma_Decade ?phase x) h tau"
    and encoded: "D ?phase (comma_offset_orbit x) = comma_terminal_weight_encode h tau"
    and selected: "comma_semantic_decade_summary (Comma_Decade ?phase x) = Some (h,tau)"
    by (rule comma_future_m204_summary_lookup[OF cert admitted])
  have terminal: "comma_terminal_weight_admitted tau"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have decoded: "comma_terminal_weight_decode
      (D ?phase (comma_offset_orbit x)) = (h,tau)"
    using encoded comma_terminal_weight_decode_encode[OF terminal] by simp
  have height: "h = D ?phase (comma_offset_orbit x) div 9"
    using decoded by (simp add: comma_terminal_weight_decode_def)
  have digit: "comma_terminal_weight_digit tau = D ?phase (comma_offset_orbit x) mod 9"
    using decoded comma_terminal_weight_terminal_digit[of "D ?phase (comma_offset_orbit x) mod 9"]
    by (simp add: comma_terminal_weight_decode_def)
  have boundary: "comma_semantic_boundary_step comma_semantic_decade_summary q =
      Some (comma_summary_outcome (h+1) tau)"
    using valid close selected off q
    by (simp add: comma_semantic_boundary_step_def)
  have control: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau))"
    using boundary by (simp add: comma_semantic_boundary_control_step_def)
  have children: "comma_semantic_boundary_children comma_semantic_decade_summary q
      (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau)) =
      (case tau of Comma_Terminal_Fork a \<Rightarrow>
        [(Comma_N,a,(snd (snd q)+1+h) mod 924),
         (Comma_Z,a,(snd (snd q)+1+h) mod 924)]
       | Comma_Terminal_Landmine \<Rightarrow> [])"
    using boundary q by (cases tau)
      (simp_all add: comma_semantic_boundary_children_def comma_native_boundary_children_def
        comma_summary_outcome.simps add.assoc add.commute add.left_commute)
  show thesis by (rule that[OF off bound summary encoded height digit control children])
qed

fun comma_future_m204_control :: "nat \<Rightarrow> comma_future_control" where
  "comma_future_m204_control J =
    (if J=8 then Comma_Future_Landmine else Comma_Future_Fork (J+2))"

definition comma_future_m204_source_output ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> comma_boundary_state \<Rightarrow> (nat \<times> nat) option" where
  "comma_future_m204_source_output D q =
    (let phase=snd (snd q) in
      case comma_semantic_b1_round_output phase (comma_finite_initial q) of
        Comma_Semantic_B1_Stop J \<Rightarrow> Some (J,0)
      | Comma_Semantic_B1_Live root \<Rightarrow>
          (let code=D ((phase+1) mod 924) root in Some (code mod 9,1+code div 9))
      | Comma_Semantic_B1_Invalid \<Rightarrow> None)"

theorem comma_future_m204_source_output_exact:
  fixes q :: comma_boundary_state
  assumes cert: "comma_frontier_m204_bellman D"
    and valid: "comma_boundary_valid q"
  obtains J delta where
    "comma_future_m204_source_output D q = Some (J,delta)"
    "J<9"
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_future_m204_control J)"
    "comma_semantic_boundary_children comma_semantic_decade_summary q
      (comma_future_m204_control J) =
      (if J=8 then [] else
        [(Comma_N,J+2,(snd (snd q)+delta) mod 924),
         (Comma_Z,J+2,(snd (snd q)+delta) mod 924)])"
proof -
  let ?phase = "snd (snd q)"
  let ?source = "comma_finite_initial q"
  have source: "comma_round_admitted ?source"
    using valid by (cases q) (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  have source_delta: "comma_round_delta ?source=0"
    using valid by (cases q) (simp add: comma_finite_initial_def comma_boundary_valid_def)
  obtain steps final event where close:
      "comma_round_close ?phase ?source=(steps,final,event)"
    by (cases "comma_round_close ?phase ?source") auto
  have terminal_delta: "comma_round_delta final=0"
    using comma_round_close_delta[OF close source] source_delta by simp
  have not_invalid: "event \<noteq> Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close source])
  have round: "comma_decisive_endpoint_round ?phase ?source = event"
    using comma_decisive_endpoint_round_refines_close[OF source] close by simp
  have output_fact:
    "comma_semantic_b1_round_output ?phase ?source =
      (case event of
         Comma_Round_Fork a d \<Rightarrow>
           if d=0 then Comma_Semantic_B1_Stop (a-2) else Comma_Semantic_B1_Invalid
       | Comma_Round_Landmine d \<Rightarrow>
           if d=0 then Comma_Semantic_B1_Stop 8 else Comma_Semantic_B1_Invalid
       | Comma_Round_Cross (Comma_Entry f d x) \<Rightarrow>
           if f=1 \<and> d=1 \<and> x\<le>90
           then Comma_Semantic_B1_Live (comma_offset_orbit x)
           else Comma_Semantic_B1_Invalid
       | _ \<Rightarrow> Comma_Semantic_B1_Invalid)"
    using round by (cases event)
      (auto simp: comma_semantic_b1_round_output_def comma_sector_base_project.simps
        comma_semantic_b1_of_word.simps comma_terminal_weight_encode_def
        split: comma_finite_position.splits)
  show thesis
  proof (cases event)
    case (Comma_Round_Fork a d)
    have source_facts:
      "d=0 \<and> 2\<le>a \<and> a\<le>9 \<and>
       comma_semantic_boundary_control_step comma_semantic_decade_summary q =
         Some (Comma_Future_Fork a) \<and>
       comma_semantic_boundary_children comma_semantic_decade_summary q (Comma_Future_Fork a) =
         [(Comma_N,a,?phase),(Comma_Z,a,?phase)]"
      by (rule comma_future_m204_direct_fork_source[OF valid]) (use close Comma_Round_Fork in simp)
    have phase: "?phase<924" using valid by (cases q) (auto simp: comma_boundary_valid_def)
    have j: "a-2<8" using source_facts by arith
    have digit: "a-2+2=a" using source_facts by arith
    have source_output: "comma_future_m204_source_output D q = Some (a-2,0)"
      using output_fact source_facts Comma_Round_Fork by (simp add: comma_future_m204_source_output_def)
    have control: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some (comma_future_m204_control (a-2))"
      using source_facts j digit by simp
    have children: "comma_semantic_boundary_children comma_semantic_decade_summary q
        (comma_future_m204_control (a-2)) =
        (if a-2=8 then [] else [(Comma_N,a-2+2,(?phase+0) mod 924),
          (Comma_Z,a-2+2,(?phase+0) mod 924)])"
      using source_facts j digit phase by simp
    show thesis by (rule that[OF source_output _ control children]) (use j in arith)
  next
    case (Comma_Round_Landmine d)
    have source_facts:
      "d=0 \<and> comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some Comma_Future_Landmine \<and>
       comma_semantic_boundary_children comma_semantic_decade_summary q Comma_Future_Landmine = []"
      by (rule comma_future_m204_direct_landmine_source[OF valid]) (use close Comma_Round_Landmine in simp)
    have source_output: "comma_future_m204_source_output D q = Some (8,0)"
      using output_fact source_facts Comma_Round_Landmine by (simp add: comma_future_m204_source_output_def)
    show thesis by (rule that[OF source_output]) (use source_facts in simp_all)
  next
    case (Comma_Round_Cross target)
    obtain d h x where final: "final=Comma_Near 9 d h"
      and target: "target=Comma_Entry 1 (Suc d) x" and off: "x\<le>90"
      using comma_round_close_crossing_shape[OF close[unfolded Comma_Round_Cross]] by blast
    have d: "d=0" using terminal_delta final by simp
    have crossing: "comma_round_close ?phase ?source =
        (steps,final,Comma_Round_Cross (Comma_Entry 1 1 x))"
      using close Comma_Round_Cross target d by simp
    obtain h tau where bound: "h\<le>26"
      and summary: "comma_decade_exact_summary (Comma_Decade ((?phase+1) mod 924) x) h tau"
      and height: "h = D ((?phase+1) mod 924) (comma_offset_orbit x) div 9"
      and digit: "comma_terminal_weight_digit tau =
        D ((?phase+1) mod 924) (comma_offset_orbit x) mod 9"
      and actual_control:
        "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
          Some (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau))"
      and actual_children:
        "comma_semantic_boundary_children comma_semantic_decade_summary q
          (comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau)) =
          (case tau of Comma_Terminal_Fork a \<Rightarrow>
            [(Comma_N,a,(?phase+1+h) mod 924),(Comma_Z,a,(?phase+1+h) mod 924)]
           | Comma_Terminal_Landmine \<Rightarrow> [])"
      using comma_future_m204_crossing_source_exact[OF cert valid crossing] by blast
    have terminal: "comma_terminal_weight_admitted tau"
      by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
    have digit_bound: "comma_terminal_weight_digit tau<9"
      by (rule comma_terminal_weight_digit_bound[OF terminal])
    have control_of_tau: "comma_future_m204_control (comma_terminal_weight_digit tau) =
        comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau)"
    proof (cases tau)
      case Comma_Terminal_Landmine
      then show ?thesis by simp
    next
      case (Comma_Terminal_Fork a)
      then show ?thesis using terminal
        by (auto simp: comma_terminal_weight_admitted_def; arith)
    qed
    have source_output: "comma_future_m204_source_output D q =
        Some (comma_terminal_weight_digit tau,1+h)"
      using output_fact Comma_Round_Cross target d off digit height
      by (simp add: comma_future_m204_source_output_def Let_def)
    have control: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some (comma_future_m204_control (comma_terminal_weight_digit tau))"
      using actual_control control_of_tau by simp
    have children: "comma_semantic_boundary_children comma_semantic_decade_summary q
        (comma_future_m204_control (comma_terminal_weight_digit tau)) =
        (if comma_terminal_weight_digit tau=8 then [] else
          [(Comma_N,comma_terminal_weight_digit tau+2,(?phase+(1+h)) mod 924),
           (Comma_Z,comma_terminal_weight_digit tau+2,(?phase+(1+h)) mod 924)])"
    proof (cases tau)
      case Comma_Terminal_Landmine
      then show ?thesis using actual_children control_of_tau by simp
    next
      case (Comma_Terminal_Fork a)
      then show ?thesis using actual_children control_of_tau terminal
        by (auto simp: comma_terminal_weight_admitted_def add.assoc; arith)
    qed
    show thesis by (rule that[OF source_output digit_bound control children])
  next
    case Comma_Round_Invalid
    show thesis using not_invalid Comma_Round_Invalid by simp
  qed
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "M204 physical crossing and ordered boundary children"
    @{thms comma_future_m204_source_closure_physical_round
      comma_future_m204_summary_lookup comma_future_m204_provider_exact
      comma_future_m204_direct_fork_source comma_future_m204_direct_landmine_source
      comma_future_m204_crossing_source_exact comma_future_m204_source_output_exact};
\<close>

end
