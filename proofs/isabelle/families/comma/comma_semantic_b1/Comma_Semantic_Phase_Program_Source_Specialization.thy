theory Comma_Semantic_Phase_Program_Source_Specialization
  imports Comma_Semantic_Phase_Action_Program
begin

text \<open>
A checked source binding specializes one source-independent program operator.
The source occurrence remains in the binding and phase transport; it is not a
program identity or a table of phase applications. Near headroom remains an
explicit guarded application argument, and Entry applications are rebased to
the full external phase after using their smaller core period.
\<close>

fun comma_phase_program_application_of_source ::
    "comma_finite_position \<Rightarrow> comma_phase_program_application"
where
  "comma_phase_program_application_of_source (Comma_Entry f delta x) =
    Comma_Entry_Program_Application"
| "comma_phase_program_application_of_source (Comma_Near f delta H) =
    Comma_Near_Program_Application H"

fun comma_phase_program_selector_phase ::
    "comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat"
where
  "comma_phase_program_selector_phase
      (Comma_Entry_Core_Program f d residue core) phase =
    phase mod comma_core_period (comma_phase_core_modulus core)"
| "comma_phase_program_selector_phase
      (Comma_Near_Residual_Program f d residual) phase = 0"
| "comma_phase_program_selector_phase
      (Comma_Near_Boundary_Program f) phase = 0"

lemma comma_phase_program_operator_nf_selector_phase:
  assumes admitted:
    "comma_phase_program_application_admitted program application"
  shows "comma_phase_program_operator_nf program phase =
    comma_phase_program_operator_nf program (comma_phase_program_selector_phase program phase)"
proof (cases program)
  case (Comma_Entry_Core_Program f d residue core)
  show ?thesis
  proof (cases application)
    case Comma_Entry_Program_Application
    have sector: "1\<le>f" "f\<le>9"
      using admitted Comma_Entry_Core_Program Comma_Entry_Program_Application
      by (auto simp: comma_phase_program_application_admitted.simps)
    have core_match:
      "comma_phase_core_modulus core =
        comma_core_modulus (comma_finite_period_fast f (residue mod 10))"
      using admitted Comma_Entry_Core_Program Comma_Entry_Program_Application
      by (auto simp: comma_phase_program_application_admitted.simps)
    let ?T = "comma_core_period (comma_phase_core_modulus core)"
    have period:
      "?T=comma_core_period
        (comma_core_modulus (comma_finite_period_fast f (residue mod 10)))"
      using core_match by simp
    have same: "phase mod ?T=(phase mod ?T) mod ?T"
      by simp
    have action:
      "comma_c1_b1_entry_core_port_action f residue phase =
        comma_c1_b1_entry_core_port_action f residue (phase mod ?T)"
      by (rule comma_c1_b1_entry_core_port_action_period[OF sector period same])
    show ?thesis
      using action Comma_Entry_Core_Program Comma_Entry_Program_Application
      by (simp add: comma_phase_program_operator_nf.simps
          comma_phase_program_selector_phase.simps)
  next
    case (Comma_Near_Program_Application H)
    then show ?thesis
      using admitted Comma_Entry_Core_Program
      by (simp add: comma_phase_program_application_admitted.simps)
  qed
next
  case (Comma_Near_Residual_Program f d residual)
  have independent:
    "fst (comma_near_symbolic_port_operator f
        (((if f<9 then 1 else 0)+1)+residual) phase) =
      fst (comma_near_symbolic_port_operator f
        (((if f<9 then 1 else 0)+1)+residual) 0)"
    by (rule comma_near_symbolic_port_action_phase_independent)
  show ?thesis
    using independent Comma_Near_Residual_Program
    by (simp add: comma_phase_program_operator_nf.simps
      comma_phase_program_selector_phase.simps)
next
  case (Comma_Near_Boundary_Program f)
  have independent:
    "fst (comma_near_symbolic_port_operator f 1 phase) =
      fst (comma_near_symbolic_port_operator f 1 0)"
    by (rule comma_near_symbolic_port_action_phase_independent)
  show ?thesis
    using independent Comma_Near_Boundary_Program
    by (simp add: comma_phase_program_operator_nf.simps
      comma_phase_program_selector_phase.simps)
qed

lemma comma_phase_program_source_application_admitted:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_application_admitted program
    (comma_phase_program_application_of_source source)"
proof (cases source)
  case (Comma_Entry f delta x)
  have delta_zero: "delta=0"
    using normalized Comma_Entry by simp
  have sector: "1\<le>f" "f\<le>9"
    using admitted Comma_Entry by simp_all
  have entry_bound: "comma_sector_entry_bound f x"
    using canonical Comma_Entry delta_zero by simp
  let ?P = "comma_finite_period_fast f (x mod 10)"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have period_positive: "0<?P"
    by (rule comma_entry_period_decimal(1)[OF catalog])
  have period_decimal: "10 dvd ?P"
    by (rule comma_entry_period_decimal(2)[OF catalog])
  have control:
    "comma_entry_control_program f x=Some program"
    using binding canonical Comma_Entry delta_zero
    by (simp add: comma_semantic_port_program_of_source_def
        comma_source_continuation_base.simps)
  obtain core where core_present:
      "comma_phase_core_of_modulus (comma_core_modulus ?P)=Some core"
    and program_shape:
      "comma_entry_control_program f x =
        Some (Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core)"
    using comma_entry_control_program_core[OF sector] by blast
  have shape:
    "program=Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core"
    using control program_shape by auto
  have residue_le_source: "x mod ?P\<le>x"
  proof -
    have equation: "x div ?P * ?P + x mod ?P=x"
      by (rule div_mult_mod_eq)
    show ?thesis using equation by arith
  qed
  have entry_upper: "x\<le>89+f"
    using entry_bound by (simp add: comma_sector_entry_bound_def)
  have residue_upper: "x mod ?P\<le>89+f"
    by (rule order_trans[OF residue_le_source entry_upper])
  have residue_bound: "comma_sector_entry_bound f (x mod ?P)"
    using sector residue_upper by (simp add: comma_sector_entry_bound_def)
  have residue_digit: "(x mod ?P) mod 10=x mod 10"
    by (simp only: mod_mod_cancel[OF period_decimal])
  have residue_lt: "x mod ?P<?P"
    using period_positive by simp
  have core_exact:
    "comma_phase_core_modulus core=comma_core_modulus ?P"
    by (rule comma_phase_core_of_modulus_exact[OF core_present])
  show ?thesis
    using shape sector residue_bound residue_digit residue_lt core_exact Comma_Entry
    by (simp add: comma_phase_program_application_admitted.simps)
next
  case (Comma_Near f delta H)
  have delta_zero: "delta=0"
    using normalized Comma_Near by simp
  have sector: "1\<le>f" "f\<le>9"
    using admitted Comma_Near by simp_all
  have headroom: "1\<le>H" "H\<le>540"
    using admitted Comma_Near by simp_all
  have control:
    "comma_near_control_program f H=program"
    using binding canonical Comma_Near delta_zero
    by (simp add: comma_semantic_port_program_of_source_def
        comma_source_continuation_base.simps)
  let ?g = "(if f<9 then 1 else 0)+1"
  let ?d = "(10-H mod 10) mod 10"
  let ?P = "comma_finite_period_fast f ?d"
  have digit: "?d<10" by simp
  have period_positive: "0<?P"
    by (rule comma_near_fast_period_positive_decimal(1)[OF sector digit])
  show ?thesis
  proof (cases "?g\<le>H")
    case True
    have shape:
      "program=Comma_Near_Residual_Program f ?d ((H-?g) mod ?P)"
      using control True
      by (simp add: comma_near_control_program_def Let_def)
    have residual_lt: "(H-?g) mod ?P<?P"
      using period_positive by simp
    show ?thesis
      using shape sector headroom digit residual_lt True Comma_Near
      by (simp add: comma_phase_program_application_admitted.simps)
  next
    case False
    have boundary: "(if f<9 then 1 else 0)\<ge>H"
      using False by arith
    have shape: "program=Comma_Near_Boundary_Program f"
      using control False
      by (simp add: comma_near_control_program_def Let_def)
    show ?thesis
      using shape sector headroom boundary Comma_Near
      by (simp add: comma_phase_program_application_admitted.simps)
  qed
qed

lemma comma_phase_program_source_local_period:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_decisive_sector_period source =
    (case program of
       Comma_Entry_Core_Program f d residue core \<Rightarrow>
         comma_core_period (comma_phase_core_modulus core)
     | Comma_Near_Residual_Program f d residual \<Rightarrow> 1
     | Comma_Near_Boundary_Program f \<Rightarrow> 1)"
proof (cases source)
  case (Comma_Entry f delta x)
  have delta_zero: "delta=0"
    using normalized Comma_Entry by simp
  have sector: "1\<le>f" "f\<le>9"
    using admitted Comma_Entry by simp_all
  have control:
    "comma_entry_control_program f x=Some program"
    using binding canonical Comma_Entry delta_zero
    by (simp add: comma_semantic_port_program_of_source_def
        comma_source_continuation_base.simps)
  obtain core where core_present:
      "comma_phase_core_of_modulus
        (comma_core_modulus (comma_finite_period_fast f (x mod 10)))=Some core"
    and program_shape:
      "comma_entry_control_program f x =
        Some (Comma_Entry_Core_Program f (x mod 10)
          (x mod comma_finite_period_fast f (x mod 10)) core)"
    using comma_entry_control_program_core[OF sector] by blast
  have program_exact:
      "program=Comma_Entry_Core_Program f (x mod 10)
        (x mod comma_finite_period_fast f (x mod 10)) core"
    using control program_shape by auto
  have core_exact:
      "comma_phase_core_modulus core =
        comma_core_modulus (comma_finite_period_fast f (x mod 10))"
    by (rule comma_phase_core_of_modulus_exact[OF core_present])
  show ?thesis
    using program_exact core_exact Comma_Entry
    by (simp add: comma_decisive_sector_period_def)
next
  case (Comma_Near f delta H)
  have delta_zero: "delta=0"
    using normalized Comma_Near by simp
  have control:
    "comma_near_control_program f H=program"
    using binding canonical Comma_Near delta_zero
    by (simp add: comma_semantic_port_program_of_source_def
        comma_source_continuation_base.simps)
  let ?g = "(if f<9 then 1 else 0)+1"
  let ?d = "(10-H mod 10) mod 10"
  let ?P = "comma_finite_period_fast f ?d"
  have program_shape:
      "program=(if ?g\<le>H then Comma_Near_Residual_Program f ?d ((H-?g) mod ?P)
        else Comma_Near_Boundary_Program f)"
    using control[symmetric]
    by (simp only: comma_near_control_program_def Let_def)
  show ?thesis
    using program_shape Comma_Near
    by (simp add: comma_decisive_sector_period_def)
qed

lemma comma_phase_program_action_at_source_periodic:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and same: "phase mod comma_decisive_sector_period source =
      representative mod comma_decisive_sector_period source"
  shows "comma_phase_program_action_at_source phase source =
    comma_phase_program_action_at_source representative source"
proof -
  have phase_exact:
    "comma_phase_program_action_at_source phase source =
      Some (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
    by (rule comma_phase_program_action_at_source_exact[OF canonical admitted])
  have representative_exact:
    "comma_phase_program_action_at_source representative source =
      Some (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet representative source))"
    by (rule comma_phase_program_action_at_source_exact[OF canonical admitted])
  have packet_same:
    "comma_decisive_endpoint_packet phase source =
      comma_decisive_endpoint_packet representative source"
    by (rule comma_decisive_endpoint_packet_period[OF admitted same])
  show ?thesis using phase_exact representative_exact packet_same by simp
qed

lemma comma_phase_program_action_at_source_selected_round_output:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and selected: "comma_phase_program_action_at_source phase source = Some action"
  shows "comma_semantic_b1_source_slot_output phase action =
    comma_semantic_b1_round_output phase source"
proof -
  obtain chosen where chosen:
      "comma_phase_program_action_at_source phase source = Some chosen"
    and selected_output:
      "comma_semantic_b1_source_slot_output phase chosen =
        comma_semantic_b1_round_output phase source"
    using comma_phase_program_action_at_source_round_output
      [OF canonical admitted normalized] by blast
  have "chosen=action" using chosen selected by simp
  then show ?thesis using selected_output by simp
qed

lemma comma_phase_program_action_at_source_operator_nf:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_action_at_source phase source =
    Some (comma_phase_program_operator_nf program phase)"
proof -
  have application:
    "comma_phase_program_application_admitted program
      (comma_phase_program_application_of_source source)"
    by (rule comma_phase_program_source_application_admitted
      [OF canonical admitted normalized binding])
  have universal:
    "comma_phase_program_operator_eval program
      (comma_phase_program_application_of_source source) phase =
      Some (comma_phase_program_operator_nf program phase)"
    by (rule comma_phase_program_operator_contract[OF application])
  show ?thesis
  proof (cases source)
    case (Comma_Entry f delta x)
    have delta_zero: "delta=0"
      using normalized Comma_Entry by simp
    have sector: "1\<le>f" "f\<le>9"
      using admitted Comma_Entry by simp_all
    have entry_bound: "comma_sector_entry_bound f x"
      using canonical Comma_Entry delta_zero by simp
    let ?P = "comma_finite_period_fast f (x mod 10)"
    have catalog: "?P\<in>comma_cycle_displacements"
      by (rule comma_entry_period_catalog[OF sector])
    have period_positive: "0<?P"
      by (rule comma_entry_period_decimal(1)[OF catalog])
    have period_decimal: "10 dvd ?P"
      by (rule comma_entry_period_decimal(2)[OF catalog])
    have control:
      "comma_entry_control_program f x=Some program"
      using binding canonical Comma_Entry delta_zero
      by (simp add: comma_semantic_port_program_of_source_def
          comma_source_continuation_base.simps)
    obtain core where core_present:
        "comma_phase_core_of_modulus (comma_core_modulus ?P)=Some core"
      and program_shape:
        "comma_entry_control_program f x =
          Some (Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core)"
      using comma_entry_control_program_core[OF sector] by blast
    have shape:
      "program=Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core"
      using control program_shape by auto
    have residue_le_source: "x mod ?P\<le>x"
    proof -
      have equation: "x div ?P * ?P + x mod ?P=x"
        by (rule div_mult_mod_eq)
      show ?thesis using equation by arith
    qed
    have entry_upper: "x\<le>89+f"
      using entry_bound by (simp add: comma_sector_entry_bound_def)
    have residue_upper: "x mod ?P\<le>89+f"
      by (rule order_trans[OF residue_le_source entry_upper])
    have residue_bound: "comma_sector_entry_bound f (x mod ?P)"
      using sector residue_upper by (simp add: comma_sector_entry_bound_def)
    have residue_digit: "(x mod ?P) mod 10=x mod 10"
      by (simp only: mod_mod_cancel[OF period_decimal])
    have residue_lt: "x mod ?P<?P"
      using period_positive by simp
    have core_exact:
      "comma_phase_core_modulus core=comma_core_modulus ?P"
      by (rule comma_phase_core_of_modulus_exact[OF core_present])
    let ?T = "comma_core_period (comma_phase_core_modulus core)"
    have source_period:
      "comma_decisive_sector_period (Comma_Entry f 0 x)=?T"
      using core_exact residue_digit
      by (simp add: comma_decisive_sector_period_def)
    have source_admitted: "comma_round_admitted (Comma_Entry f 0 x)"
      using admitted Comma_Entry delta_zero by simp
    have period_divides: "?T dvd 924"
      using comma_decisive_sector_period_admitted(2)[OF source_admitted]
        source_period by simp
    have phase_rebase:
      "(phase mod 924 mod ?T) mod ?T=phase mod ?T"
      using period_divides by (simp add: mod_mod_cancel[OF period_divides])
    have periodic:
      "comma_phase_program_at_entry
          (Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core)
          ((phase mod 924) mod ?T) =
        comma_phase_program_at_entry
          (Comma_Entry_Core_Program f (x mod 10) (x mod ?P) core) phase"
      by (rule comma_phase_program_at_entry_core_periodic
        [where T="?T" and r="(phase mod 924) mod ?T" and s=phase])
         (use sector residue_bound residue_digit residue_lt core_exact phase_rebase
           in auto)
    have action_eval:
      "comma_phase_program_action_at_source phase source =
        comma_phase_program_operator_eval program
          Comma_Entry_Program_Application phase"
      using control entry_bound shape periodic delta_zero Comma_Entry
      by (simp add: comma_phase_program_action_at_source_def
          comma_phase_program_apply_entry_def
          comma_phase_program_operator_eval.simps option.map_id)
    show ?thesis
      using action_eval universal Comma_Entry by simp
  next
    case (Comma_Near f delta H)
    have delta_zero: "delta=0"
      using normalized Comma_Near by simp
    have control:
      "comma_near_control_program f H=program"
      using binding canonical Comma_Near delta_zero
      by (simp add: comma_semantic_port_program_of_source_def
          comma_source_continuation_base.simps)
    have action_eval:
      "comma_phase_program_action_at_source phase source =
        comma_phase_program_operator_eval program
          (Comma_Near_Program_Application H) phase"
      using control delta_zero Comma_Near
      by (simp add: comma_phase_program_action_at_source_def
          comma_phase_program_operator_eval.simps
          comma_phase_program_at_near_phase_independent option.map_id)
    show ?thesis using action_eval universal Comma_Near by simp
  qed
qed

lemma comma_phase_program_action_at_source_selector_operator_nf:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_action_at_source phase source =
    Some (comma_phase_program_operator_nf program (comma_phase_program_selector_phase program phase))"
proof -
  have exact:
    "comma_phase_program_action_at_source phase source =
      Some (comma_phase_program_operator_nf program phase)"
    by (rule comma_phase_program_action_at_source_operator_nf
      [OF canonical admitted normalized binding])
  have application:
    "comma_phase_program_application_admitted program
      (comma_phase_program_application_of_source source)"
    by (rule comma_phase_program_source_application_admitted
      [OF canonical admitted normalized binding])
  have nf:
    "comma_phase_program_operator_nf program phase =
      comma_phase_program_operator_nf program (comma_phase_program_selector_phase program phase)"
    by (rule comma_phase_program_operator_nf_selector_phase[OF application])
  show ?thesis using exact nf by simp
qed

lemma comma_phase_program_source_operator_function:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "(\<lambda>phase. comma_phase_program_action_at_source phase source) =
    (\<lambda>phase. Some (comma_phase_program_operator_nf program (comma_phase_program_selector_phase program phase)))"
  by (rule ext; rule comma_phase_program_action_at_source_selector_operator_nf
      [OF canonical admitted normalized binding])

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-specialized phase-program normal form"
    @{thms comma_phase_program_operator_nf_selector_phase
      comma_phase_program_source_application_admitted
      comma_phase_program_source_local_period
      comma_phase_program_action_at_source_periodic
      comma_phase_program_action_at_source_selected_round_output
      comma_phase_program_action_at_source_operator_nf
      comma_phase_program_action_at_source_selector_operator_nf
      comma_phase_program_source_operator_function};
\<close>

end
