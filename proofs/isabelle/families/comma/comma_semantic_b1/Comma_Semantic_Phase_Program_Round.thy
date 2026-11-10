theory Comma_Semantic_Phase_Program_Round
  imports Comma_Semantic_Phase_Program_Source_Specialization
begin

text \<open>
The executable local step uses a normalized phase program and an external
clock. A Goto successor is immediately rebound to its child program; a
crossing retains its exact endpoint payload. Structural admission is proved
equivalent to the existence of an admitted application without searching for
physical headroom at execution time. Complete-round refinement is separate.
\<close>

fun comma_phase_program_sector :: "comma_semantic_port_program \<Rightarrow> nat" where
  "comma_phase_program_sector (Comma_Entry_Core_Program f d x core) = f"
| "comma_phase_program_sector (Comma_Near_Residual_Program f d x) = f"
| "comma_phase_program_sector (Comma_Near_Boundary_Program f) = f"

definition comma_phase_program_structurally_admitted ::
    "comma_semantic_port_program \<Rightarrow> bool" where
  "comma_phase_program_structurally_admitted program =
    (case program of
       Comma_Entry_Core_Program f d residue core \<Rightarrow>
         1\<le>f \<and> f\<le>9 \<and> comma_sector_entry_bound f residue \<and>
         d<10 \<and> residue mod 10=d \<and>
         residue<comma_finite_period_fast f d \<and>
         comma_phase_core_modulus core =
           comma_core_modulus (comma_finite_period_fast f d)
     | Comma_Near_Residual_Program f d residual \<Rightarrow>
         (let e=(if f<9 then 1 else 0); g=e+1; H=g+residual;
              P=comma_finite_period_fast f d
          in 1\<le>f \<and> f\<le>9 \<and> d<10 \<and> residual<P \<and>
             H\<le>540 \<and> d=(10-H mod 10) mod 10)
     | Comma_Near_Boundary_Program f \<Rightarrow> 1\<le>f \<and> f<9)"

definition comma_phase_program_source_valid ::
    "comma_semantic_port_program \<Rightarrow> bool" where
  "comma_phase_program_source_valid program \<longleftrightarrow>
    (\<exists>application. comma_phase_program_application_admitted program application)"

lemma comma_phase_program_source_valid_cases:
  "comma_phase_program_source_valid program \<longleftrightarrow>
    comma_phase_program_application_admitted program Comma_Entry_Program_Application \<or>
    (\<exists>H. comma_phase_program_application_admitted program
      (Comma_Near_Program_Application H))"
proof
  assume "comma_phase_program_source_valid program"
  then obtain application where admitted:
    "comma_phase_program_application_admitted program application"
    by (auto simp: comma_phase_program_source_valid_def)
  show "comma_phase_program_application_admitted program Comma_Entry_Program_Application \<or>
      (\<exists>H. comma_phase_program_application_admitted program
        (Comma_Near_Program_Application H))"
    using admitted by (cases application) auto
next
  assume "comma_phase_program_application_admitted program Comma_Entry_Program_Application \<or>
      (\<exists>H. comma_phase_program_application_admitted program
        (Comma_Near_Program_Application H))"
  then show "comma_phase_program_source_valid program"
    unfolding comma_phase_program_source_valid_def by blast
qed

lemma comma_phase_program_source_valid_iff_structural:
  "comma_phase_program_source_valid program =
    comma_phase_program_structurally_admitted program"
proof (cases program)
  case (Comma_Entry_Core_Program f d residue core)
  then show ?thesis
    by (auto simp: comma_phase_program_source_valid_cases
      comma_phase_program_structurally_admitted_def
      comma_phase_program_application_admitted.simps)
next
  case (Comma_Near_Residual_Program f d residual)
  let ?e = "if f<9 then 1 else 0"
  let ?g = "?e+1"
  let ?P = "comma_finite_period_fast f d"
  let ?H = "?g+residual"
  show ?thesis
  proof
    assume valid: "comma_phase_program_source_valid program"
    then obtain H where app:
        "comma_phase_program_application_admitted program
          (Comma_Near_Program_Application H)"
      using Comma_Near_Residual_Program
      by (auto simp: comma_phase_program_source_valid_cases
        comma_phase_program_application_admitted.simps)
    have f_range: "1\<le>f" "f\<le>9" and d_bound: "d<10"
      and residual_lt: "residual<?P" and g_le: "?g\<le>H"
      and phase_digit: "d=(10-H mod 10) mod 10"
      and residual_eq: "residual=(H-?g) mod ?P"
      using app Comma_Near_Residual_Program
      by (auto simp: comma_phase_program_application_admitted.simps Let_def)
    have period_decimal: "?P mod 10=0"
      by (rule comma_near_fast_period_positive_decimal(2)[OF f_range d_bound])
    have ten_dvd: "10 dvd ?P"
      using period_decimal by (simp add: dvd_eq_mod_eq_0)
    have reduced_mod10:
      "(H-?g) mod 10=residual mod 10"
    proof -
      have "((H-?g) mod ?P) mod 10=(H-?g) mod 10"
        by (rule mod_mod_cancel[OF ten_dvd])
      then show ?thesis using residual_eq by simp
    qed
    have H_digit: "H mod 10=?H mod 10"
    proof -
      have H_eq: "H=?g+(H-?g)" using g_le by arith
      have first: "H mod 10=(?g+(H-?g)) mod 10"
        by (rule arg_cong[OF H_eq])
      have reduced: "(?g+(H-?g)) mod 10=(?g+residual) mod 10"
      proof -
        have lifted:
          "(?g+((H-?g) mod 10)) mod 10=(?g+residual mod 10) mod 10"
          by (rule arg_cong[where f="\<lambda>x. (?g+x) mod 10", OF reduced_mod10])
        show ?thesis using lifted by (simp only: mod_add_right_eq)
      qed
      show ?thesis by (rule trans[OF first reduced])
    qed
    have H_bound: "?H\<le>540"
    proof -
      have residual_le: "residual\<le>H-?g"
        using mod_less_eq_dividend[of "H-?g" ?P] residual_eq by simp
      have "?g+residual\<le>?g+(H-?g)" using residual_le by simp
      also have "...=H" using g_le by arith
      also have "...\<le>540" using app Comma_Near_Residual_Program
        by (auto simp: comma_phase_program_application_admitted.simps Let_def)
      finally show ?thesis .
    qed
    show "comma_phase_program_structurally_admitted program"
      using f_range d_bound residual_lt H_bound phase_digit H_digit
        Comma_Near_Residual_Program
      by (simp add: comma_phase_program_structurally_admitted_def Let_def)
  next
    assume structural:
      "comma_phase_program_structurally_admitted program"
    have f_range: "1\<le>f" "f\<le>9" and d_bound: "d<10"
      and residual_lt: "residual<?P" and H_bound: "?H\<le>540"
      and digit: "d=(10-?H mod 10) mod 10"
      using structural Comma_Near_Residual_Program
      by (auto simp: comma_phase_program_structurally_admitted_def Let_def)
    have app:
      "comma_phase_program_application_admitted program
        (Comma_Near_Program_Application ?H)"
      using f_range d_bound residual_lt H_bound digit
        Comma_Near_Residual_Program
      by (simp add: comma_phase_program_application_admitted.simps Let_def)
    show "comma_phase_program_source_valid program"
      using app by (auto simp: comma_phase_program_source_valid_def)
  qed
next
  case (Comma_Near_Boundary_Program f)
  then show ?thesis
    by (auto simp: comma_phase_program_source_valid_cases
      comma_phase_program_structurally_admitted_def
      comma_phase_program_application_admitted.simps
      split: if_splits intro!: exI[of _ 1])
qed

datatype comma_phase_program_step =
    Comma_Program_Goto comma_semantic_port_program nat
  | Comma_Program_Exit comma_finite_position nat
  | Comma_Program_Fork nat nat
  | Comma_Program_Landmine nat
  | Comma_Program_Invalid

fun comma_phase_program_step_of_action ::
    "comma_source_continuation_action \<Rightarrow> comma_phase_program_step" where
  "comma_phase_program_step_of_action (Comma_Continuation_Goto source shift) =
    (case comma_semantic_port_program_of_source source of
       Some child \<Rightarrow> Comma_Program_Goto child shift
     | None \<Rightarrow> Comma_Program_Invalid)"
| "comma_phase_program_step_of_action (Comma_Continuation_Exit source shift) =
    Comma_Program_Exit source shift"
| "comma_phase_program_step_of_action (Comma_Continuation_Fork a shift) =
    Comma_Program_Fork a shift"
| "comma_phase_program_step_of_action (Comma_Continuation_Landmine shift) =
    Comma_Program_Landmine shift"
| "comma_phase_program_step_of_action Comma_Continuation_Invalid =
    Comma_Program_Invalid"

definition comma_phase_program_step_at ::
    "comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_phase_program_step" where
  "comma_phase_program_step_at program phase shift =
    (if comma_phase_program_structurally_admitted program then
       comma_phase_program_step_of_action
         (comma_source_continuation_transport shift
           (comma_phase_program_operator_nf program ((phase+shift) mod 924)))
     else Comma_Program_Invalid)"

lemma comma_phase_program_operator_nf_structural_selector:
  assumes structural: "comma_phase_program_structurally_admitted program"
  shows "comma_phase_program_operator_nf program phase =
    comma_phase_program_operator_nf program
      (comma_phase_program_selector_phase program phase)"
proof -
  obtain application where admitted:
      "comma_phase_program_application_admitted program application"
    using structural comma_phase_program_source_valid_iff_structural
    by (auto simp: comma_phase_program_source_valid_def)
  show ?thesis
    by (rule comma_phase_program_operator_nf_selector_phase[OF admitted])
qed

declare comma_phase_program_step_at_def [code drop]

lemma comma_phase_program_step_at_selected [code]:
  "comma_phase_program_step_at program phase shift =
    (if comma_phase_program_structurally_admitted program then
       comma_phase_program_step_of_action
         (comma_source_continuation_transport shift
           (comma_phase_program_operator_nf program
             (comma_phase_program_selector_phase program
               ((phase+shift) mod 924))))
     else Comma_Program_Invalid)"
proof (cases "comma_phase_program_structurally_admitted program")
  case True
  have selected:
      "comma_phase_program_operator_nf program ((phase+shift) mod 924) =
        comma_phase_program_operator_nf program
          (comma_phase_program_selector_phase program ((phase+shift) mod 924))"
    by (rule comma_phase_program_operator_nf_structural_selector[OF True])
  show ?thesis by (simp only: comma_phase_program_step_at_def True if_True selected)
next
  case False
  show ?thesis by (simp only: comma_phase_program_step_at_def False if_False)
qed


lemma comma_phase_core_of_modulus_self:
  "comma_phase_core_of_modulus (comma_phase_core_modulus core)=Some core"
  by (cases core) (simp_all add: comma_phase_core_of_modulus_def)

lemma comma_phase_program_application_source_facts:
  assumes application:
    "comma_phase_program_application_admitted program application"
  obtains source where
      "comma_canonical_position_admitted source"
    and "comma_round_admitted source"
    and "source=comma_source_continuation_base source"
    and "comma_semantic_port_program_of_source source=Some program"
proof (cases program)
  case (Comma_Entry_Core_Program f d residue core)
  then show thesis
  proof (cases application)
    case Comma_Entry_Program_Application
    have admitted:
      "1\<le>f \<and> f\<le>9 \<and> comma_sector_entry_bound f residue \<and>
       d<10 \<and> residue mod 10=d \<and>
       residue<comma_finite_period_fast f d \<and>
       comma_phase_core_modulus core =
         comma_core_modulus (comma_finite_period_fast f d)"
      using application Comma_Entry_Core_Program
        Comma_Entry_Program_Application
      by (simp add: comma_phase_program_application_admitted.simps)
    have core_modulus:
      "comma_phase_core_modulus core =
        comma_core_modulus (comma_finite_period_fast f d)"
      using admitted by blast
    have core_selector:
      "comma_phase_core_of_modulus
        (comma_core_modulus (comma_finite_period_fast f d))=Some core"
      using comma_phase_core_of_modulus_self[of core] core_modulus by simp
    have control:
      "comma_entry_control_program f residue=Some
        (Comma_Entry_Core_Program f d residue core)"
      using admitted core_selector
      by (simp add: comma_entry_control_program_def)
    have canonical:
      "comma_canonical_position_admitted (Comma_Entry f 0 residue)"
      using admitted by (simp add: comma_canonical_position_admitted_def)
    have round_admitted: "comma_round_admitted (Comma_Entry f 0 residue)"
      by (rule comma_canonical_position_implies_round_admitted[OF canonical])
    have normalized:
      "Comma_Entry f 0 residue=
        comma_source_continuation_base (Comma_Entry f 0 residue)"
      by simp
    have binding:
      "comma_semantic_port_program_of_source (Comma_Entry f 0 residue)=
        Some (Comma_Entry_Core_Program f d residue core)"
      using canonical control
      by (simp add: comma_semantic_port_program_of_source_def)
    show thesis
      by (rule that[of "Comma_Entry f 0 residue"])
        (use canonical round_admitted normalized binding Comma_Entry_Core_Program in simp_all)
  next
    case (Comma_Near_Program_Application H)
    then show thesis using application Comma_Entry_Core_Program
      by (simp add: comma_phase_program_application_admitted.simps)
  qed
next
  case (Comma_Near_Residual_Program f d residual)
  then show thesis
  proof (cases application)
    case Comma_Entry_Program_Application
    then show thesis using application Comma_Near_Residual_Program
      by (simp add: comma_phase_program_application_admitted.simps)
  next
    case (Comma_Near_Program_Application H)
    have admitted:
      "1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
       d<10 \<and> residual<comma_finite_period_fast f d \<and>
       (if f<9 then 1 else 0)+1\<le>H \<and>
       d=(10-H mod 10) mod 10 \<and>
       residual=(H-((if f<9 then 1 else 0)+1)) mod
         comma_finite_period_fast f d"
      by (rule application[unfolded Comma_Near_Residual_Program
        Comma_Near_Program_Application comma_phase_program_application_admitted.simps
        Let_def])
    have canonical:
      "comma_canonical_position_admitted (Comma_Near f 0 H)"
      using admitted by (simp add: comma_canonical_position_admitted_def)
    have round_admitted: "comma_round_admitted (Comma_Near f 0 H)"
      by (rule comma_canonical_position_implies_round_admitted[OF canonical])
    have normalized:
      "Comma_Near f 0 H=comma_source_continuation_base (Comma_Near f 0 H)"
      by simp
    have near_control:
      "comma_near_control_program f H=
        Comma_Near_Residual_Program f d residual"
      using admitted by (simp add: comma_near_control_program_def Let_def)
    have sector: "1\<le>f" "f\<le>9" using admitted by auto
    have H_range: "1\<le>H" "H\<le>540" using admitted by auto
    have near_source:
      "comma_semantic_port_program_of_source (Comma_Near f 0 H)=
        Some (comma_near_control_program f H)"
      by (rule comma_semantic_port_program_of_near
        [OF sector(1) sector(2) H_range(1) H_range(2)])
    have binding:
      "comma_semantic_port_program_of_source (Comma_Near f 0 H)=
        Some (Comma_Near_Residual_Program f d residual)"
      using near_source near_control by simp
    show thesis
      by (rule that[of "Comma_Near f 0 H"])
        (use canonical round_admitted normalized binding Comma_Near_Residual_Program in simp_all)
  qed
next
  case (Comma_Near_Boundary_Program f)
  then show thesis
  proof (cases application)
    case Comma_Entry_Program_Application
    then show thesis using application Comma_Near_Boundary_Program
      by (simp add: comma_phase_program_application_admitted.simps)
  next
    case (Comma_Near_Program_Application H)
    have admitted:
      "1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
       (if f<9 then 1 else 0)\<ge>H"
      using application Comma_Near_Boundary_Program
        Comma_Near_Program_Application
      by (simp add: comma_phase_program_application_admitted.simps)
    have f_low: "1\<le>f" using admitted by blast
    have f_lt: "f<9" using admitted by (cases "f<9") auto
    have f_le9: "f\<le>9" using f_lt by arith
    have canonical:
      "comma_canonical_position_admitted (Comma_Near f 0 1)"
      using f_low f_le9 by (simp add: comma_canonical_position_admitted_def)
    have round_admitted: "comma_round_admitted (Comma_Near f 0 1)"
      by (rule comma_canonical_position_implies_round_admitted[OF canonical])
    have normalized:
      "Comma_Near f 0 1=comma_source_continuation_base (Comma_Near f 0 1)"
      by simp
    have near_control:
      "comma_near_control_program f 1=Comma_Near_Boundary_Program f"
      using f_low f_lt by (simp add: comma_near_control_program_def Let_def)
    have near_source:
      "comma_semantic_port_program_of_source (Comma_Near f 0 1)=
        Some (comma_near_control_program f 1)"
    proof -
      have H_range: "(1::nat)\<le>1" "(1::nat)\<le>540" by simp_all
      show ?thesis
        by (rule comma_semantic_port_program_of_near
          [OF f_low f_le9 H_range(1) H_range(2)])
    qed
    have binding:
      "comma_semantic_port_program_of_source (Comma_Near f 0 1)=
        Some (Comma_Near_Boundary_Program f)"
      using near_source near_control by simp
    show thesis
      by (rule that[of "Comma_Near f 0 1"])
        (use canonical round_admitted normalized binding Comma_Near_Boundary_Program in simp_all)
  qed
qed

lemma comma_semantic_port_program_of_canonical_source_some:
  assumes canonical: "comma_canonical_position_admitted source"
  shows "\<exists>program. comma_semantic_port_program_of_source source=Some program"
proof (cases source)
  case (Comma_Entry f delta x)
  have sector: "1\<le>f" "f\<le>9"
    and entry: "comma_sector_entry_bound f x"
    using canonical Comma_Entry
    by (auto simp: comma_canonical_position_admitted_def
        comma_sector_entry_bound_def)
  obtain core where program:
      "comma_entry_control_program f x =
        Some (Comma_Entry_Core_Program f (x mod 10)
          (x mod comma_finite_period_fast f (x mod 10)) core)"
    using comma_entry_control_program_core[OF sector] by blast
  have binding:
      "comma_semantic_port_program_of_source (Comma_Entry f delta x) =
        Some (Comma_Entry_Core_Program f (x mod 10)
          (x mod comma_finite_period_fast f (x mod 10)) core)"
    using comma_semantic_port_program_of_entry[OF entry] program by simp
  show ?thesis using binding Comma_Entry by blast
next
  case (Comma_Near f delta H)
  have sector: "1\<le>f" "f\<le>9" and headroom: "1\<le>H" "H\<le>540"
    using canonical Comma_Near
    by (auto simp: comma_canonical_position_admitted_def)
  have binding:
      "comma_semantic_port_program_of_source (Comma_Near f delta H) =
        Some (comma_near_control_program f H)"
    by (rule comma_semantic_port_program_of_near
      [OF sector(1) sector(2) headroom(1) headroom(2)])
  show ?thesis using binding Comma_Near by blast
qed

lemma comma_source_continuation_goto_canonical:
  assumes source: "comma_round_admitted source"
    and action:
      "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet r source) =
        Comma_Continuation_Goto next shift"
  shows "comma_canonical_position_admitted next \<and>
    next=comma_source_continuation_base next"
proof -
  obtain target move where raw_packet:
      "comma_decisive_endpoint_packet r source=(target,move)"
    by (cases "comma_decisive_endpoint_packet r source") simp
  have packet_components:
      "fst (comma_decisive_endpoint_packet r source)=target"
      "snd (comma_decisive_endpoint_packet r source)=move"
    using raw_packet by simp_all
  obtain successor where move_eq: "move=Comma_Next successor"
    and internal: "\<not> comma_round_crossing target successor"
    and next_eq: "next=comma_source_continuation_base successor"
    using action by (cases move)
      (auto simp: raw_packet split: if_splits)
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF source, of r]
      packet_components(1) by simp
  have target_eq: "target=comma_decisive_sector_target r source"
    using packet_components(1)
    by (simp only: comma_decisive_endpoint_packet_def Let_def fst_conv)
  obtain f delta h where target_near:
      "comma_decisive_sector_target r source=Comma_Near f delta h"
    by (rule comma_decisive_sector_target_near[OF source])
  have target_canonical: "comma_canonical_position_admitted target"
    using target_admitted target_eq target_near
    by (auto simp: comma_round_admitted.simps
      comma_canonical_position_admitted_def)
  have fast_step:
      "comma_fast_step (r mod 924) target=move"
    using packet_components(2)
    by (simp only: comma_decisive_endpoint_packet_def Let_def snd_conv target_eq)
  have finite_step:
      "comma_finite_step (r mod 924) target=Comma_Next successor"
    using fast_step move_eq by (simp only: comma_fast_step_correct)
  have successor_canonical:
      "comma_canonical_position_admitted successor"
  proof -
    have bounds: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
      using target_canonical target_eq target_near
      by (auto simp: comma_canonical_position_admitted_def)
    show ?thesis
      by (rule comma_near_next_canonical[OF bounds])
        (use finite_step target_eq target_near in simp)
  qed
  have next_canonical: "comma_canonical_position_admitted next"
    using successor_canonical next_eq
    by (cases successor) (simp_all add: comma_canonical_position_admitted_def
      comma_sector_entry_bound_def)
  have normalized: "next=comma_source_continuation_base next"
    using next_eq by (cases successor) simp_all
  show ?thesis using next_canonical normalized by simp
qed

lemma comma_phase_program_nf_packet_exact:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_operator_nf program phase =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet phase source)"
proof -
  have nf:
    "comma_phase_program_action_at_source phase source =
      Some (comma_phase_program_operator_nf program phase)"
    by (rule comma_phase_program_action_at_source_operator_nf
      [OF canonical admitted normalized binding])
  have exact:
    "comma_phase_program_action_at_source phase source =
      Some (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
    by (rule comma_phase_program_action_at_source_exact
      [OF canonical admitted])
  show ?thesis using nf exact by simp
qed

lemma comma_phase_program_step_at_source_packet:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_step_at program phase shift =
    comma_phase_program_step_of_action
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase
          (comma_shift_position shift source)))"
proof -
  have application:
    "comma_phase_program_application_admitted program
      (comma_phase_program_application_of_source source)"
    by (rule comma_phase_program_source_application_admitted
      [OF canonical admitted normalized binding])
  have source_valid: "comma_phase_program_source_valid program"
    using application by (auto simp: comma_phase_program_source_valid_def)
  have structural:
    "comma_phase_program_structurally_admitted program"
    using source_valid
    by (simp only: comma_phase_program_source_valid_iff_structural)
  let ?clock = "(phase+shift) mod 924"
  have nf_action:
    "comma_phase_program_operator_nf program ?clock =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet ?clock source)"
    by (rule comma_phase_program_nf_packet_exact
      [OF canonical admitted normalized binding])
  have zero_shift: "comma_source_continuation_shift source=0"
    using normalized by (cases source) simp_all
  let ?shifted = "comma_shift_position shift source"
  have base_shifted:
    "comma_source_continuation_base ?shifted=source"
    by (simp only: comma_source_continuation_base_shift_position normalized[symmetric])
  have shift_shifted:
    "comma_source_continuation_shift ?shifted=shift"
    using comma_source_continuation_shift_position[of shift source]
      zero_shift by simp
  have packet_transport:
    "comma_decisive_endpoint_packet phase ?shifted =
      (comma_shift_position (comma_source_continuation_shift ?shifted)
         (fst (comma_decisive_endpoint_packet ?clock source)),
       comma_shift_move (comma_source_continuation_shift ?shifted)
         (snd (comma_decisive_endpoint_packet ?clock source)))"
  proof -
    have general:
      "comma_decisive_endpoint_packet phase ?shifted =
        (comma_shift_position
           (comma_source_continuation_shift
             ?shifted)
           (fst (comma_decisive_endpoint_packet
             ((phase + comma_source_continuation_shift
               ?shifted) mod 924)
             (comma_source_continuation_base
               ?shifted))),
         comma_shift_move
           (comma_source_continuation_shift
             ?shifted)
           (snd (comma_decisive_endpoint_packet
             ((phase + comma_source_continuation_shift
               ?shifted) mod 924)
             (comma_source_continuation_base
               ?shifted))))"
      by (rule comma_source_continuation_packet_transport)
    show ?thesis using general base_shifted shift_shifted by simp
  qed
  have action_transport:
    "comma_source_continuation_action_of_packet
       (comma_decisive_endpoint_packet phase
         ?shifted) =
     comma_source_continuation_transport shift
       (comma_source_continuation_action_of_packet
         (comma_decisive_endpoint_packet ?clock source))"
  proof -
    have packet_cong:
      "comma_source_continuation_action_of_packet
         (comma_decisive_endpoint_packet phase
           ?shifted) =
       comma_source_continuation_action_of_packet
         (comma_shift_position shift
            (fst (comma_decisive_endpoint_packet ?clock source)),
          comma_shift_move shift
            (snd (comma_decisive_endpoint_packet ?clock source)))"
      using packet_transport shift_shifted by simp
    have action_shift:
      "comma_source_continuation_action_of_packet
         (comma_shift_position shift
            (fst (comma_decisive_endpoint_packet ?clock source)),
          comma_shift_move shift
            (snd (comma_decisive_endpoint_packet ?clock source))) =
       comma_source_continuation_transport shift
         (comma_source_continuation_action_of_packet
           (comma_decisive_endpoint_packet ?clock source))"
      by (simp only: comma_source_continuation_action_shift prod.collapse)
    show ?thesis
      by (simp only: packet_cong action_shift prod.collapse)
  qed
  show ?thesis
    using structural nf_action action_transport
    by (simp add: comma_phase_program_step_at_def)
qed

lemma comma_semantic_port_program_sector:
  assumes binding:
    "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_sector program=comma_sector_number source"
proof (cases source)
  case (Comma_Entry f delta x)
  then show ?thesis using binding
    by (cases program)
      (auto simp: comma_semantic_port_program_of_source_def
        comma_entry_control_program_def comma_phase_program_sector.simps
        comma_sector_number.simps Let_def split: if_splits option.splits)
next
  case (Comma_Near f delta H)
  then show ?thesis using binding
    by (cases program)
      (auto simp: comma_semantic_port_program_of_source_def
        comma_near_control_program_def comma_phase_program_sector.simps
        comma_sector_number.simps Let_def split: if_splits)
qed

lemma comma_phase_program_step_goto_decreases_from_packet:
  assumes structural:
    "comma_phase_program_structurally_admitted program"
    and step:
    "comma_phase_program_step_at program phase shift =
      Comma_Program_Goto child child_shift"
  shows "9-comma_phase_program_sector child <
    9-comma_phase_program_sector program"
proof -
  have source_valid: "comma_phase_program_source_valid program"
    using structural by (simp only: comma_phase_program_source_valid_iff_structural)
  obtain application where application:
      "comma_phase_program_application_admitted program application"
    using source_valid by (auto simp: comma_phase_program_source_valid_def)
  obtain witness where witness_canonical:
      "comma_canonical_position_admitted witness"
    and witness_admitted: "comma_round_admitted witness"
    and witness_normalized:
      "witness=comma_source_continuation_base witness"
    and witness_binding:
      "comma_semantic_port_program_of_source witness=Some program"
    by (rule comma_phase_program_application_source_facts[OF application])
  have exact_step:
    "comma_phase_program_step_at program phase shift =
      comma_phase_program_step_of_action
        (comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet phase
            (comma_shift_position shift witness)))"
    by (rule comma_phase_program_step_at_source_packet
      [OF witness_canonical witness_admitted witness_normalized witness_binding])
  obtain successor local_shift where packet_action:
      "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase
          (comma_shift_position shift witness)) =
        Comma_Continuation_Goto successor local_shift"
    and child_binding: "comma_semantic_port_program_of_source successor=Some child"
    using exact_step step
    by (cases "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase
          (comma_shift_position shift witness))")
      (auto simp: comma_phase_program_step_of_action.simps
        split: option.splits)
  have shifted_admitted:
      "comma_round_admitted (comma_shift_position shift witness)"
    using witness_admitted by (cases witness) simp_all
  have goto_result:
      "comma_round_admitted successor \<and>
       9-comma_sector_number successor <
         9-comma_sector_number (comma_shift_position shift witness)"
    by (rule comma_source_continuation_goto_decreases
      [OF shifted_admitted packet_action])
  have child_sector:
      "comma_phase_program_sector child=comma_sector_number successor"
    by (rule comma_semantic_port_program_sector[OF child_binding])
  have source_sector:
      "comma_phase_program_sector program=comma_sector_number witness"
    by (rule comma_semantic_port_program_sector[OF witness_binding])
  have shift_sector:
      "comma_sector_number (comma_shift_position shift witness)=
        comma_sector_number witness"
    by (cases witness) simp_all
  have decrease:
      "9-comma_sector_number successor <
        9-comma_sector_number (comma_shift_position shift witness)"
    using goto_result by blast
  show ?thesis using decrease child_sector source_sector shift_sector by simp
qed

lemma comma_phase_program_step_goto_structural:
  assumes step:
    "comma_phase_program_step_at program phase shift =
      Comma_Program_Goto child child_shift"
  shows "comma_phase_program_structurally_admitted program"
  using step by (auto simp: comma_phase_program_step_at_def split: if_splits)

function comma_semantic_phase_program_fold ::
    "(nat \<Rightarrow> comma_round_result \<Rightarrow> 'a) \<Rightarrow>
      nat \<Rightarrow> comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> 'a" where
  "comma_semantic_phase_program_fold observe phase program shift =
    (case comma_phase_program_step_at program phase shift of
       Comma_Program_Goto child child_shift \<Rightarrow>
         comma_semantic_phase_program_fold observe phase child child_shift
     | Comma_Program_Exit target target_shift \<Rightarrow>
         observe phase
           (Comma_Round_Cross (comma_shift_position target_shift target))
     | Comma_Program_Fork a target_shift \<Rightarrow>
         observe phase (Comma_Round_Fork a target_shift)
     | Comma_Program_Landmine target_shift \<Rightarrow>
         observe phase (Comma_Round_Landmine target_shift)
     | Comma_Program_Invalid \<Rightarrow>
         observe phase Comma_Round_Invalid)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(observe,phase,program,shift).
      9-comma_phase_program_sector program)")
    (auto intro: comma_phase_program_step_goto_decreases_from_packet
      comma_phase_program_step_goto_structural)

declare comma_semantic_phase_program_fold.simps [simp del]

definition comma_semantic_phase_program_round ::
    "nat \<Rightarrow> comma_semantic_port_program \<Rightarrow> nat \<Rightarrow>
      comma_round_result" where
  "comma_semantic_phase_program_round phase program shift =
    comma_semantic_phase_program_fold (\<lambda>_ output. output)
      phase program shift"

lemma comma_semantic_phase_program_round_unfold:
  "comma_semantic_phase_program_round phase program shift =
    (case comma_phase_program_step_at program phase shift of
       Comma_Program_Goto child child_shift \<Rightarrow>
         comma_semantic_phase_program_round phase child child_shift
     | Comma_Program_Exit target target_shift \<Rightarrow>
         Comma_Round_Cross (comma_shift_position target_shift target)
     | Comma_Program_Fork a target_shift \<Rightarrow>
         Comma_Round_Fork a target_shift
     | Comma_Program_Landmine target_shift \<Rightarrow>
         Comma_Round_Landmine target_shift
     | Comma_Program_Invalid \<Rightarrow> Comma_Round_Invalid)"
  unfolding comma_semantic_phase_program_round_def
  by (rule comma_semantic_phase_program_fold.simps)

lemma comma_semantic_phase_program_fold_observer_fusion:
  "comma_semantic_phase_program_fold observe phase program shift =
    observe phase
      (comma_semantic_phase_program_round phase program shift)"
proof (induction "9-comma_phase_program_sector program"
    arbitrary: program phase shift rule: less_induct)
  case less
  have fold_equation:
    "comma_semantic_phase_program_fold observe phase program shift =
      (case comma_phase_program_step_at program phase shift of
         Comma_Program_Goto child child_shift \<Rightarrow>
           comma_semantic_phase_program_fold observe phase child child_shift
       | Comma_Program_Exit target target_shift \<Rightarrow>
           observe phase (Comma_Round_Cross
             (comma_shift_position target_shift target))
       | Comma_Program_Fork a target_shift \<Rightarrow>
           observe phase (Comma_Round_Fork a target_shift)
       | Comma_Program_Landmine target_shift \<Rightarrow>
           observe phase (Comma_Round_Landmine target_shift)
       | Comma_Program_Invalid \<Rightarrow>
           observe phase Comma_Round_Invalid)"
    by (rule comma_semantic_phase_program_fold.simps)
  have round_equation:
    "comma_semantic_phase_program_round phase program shift =
      (case comma_phase_program_step_at program phase shift of
         Comma_Program_Goto child child_shift \<Rightarrow>
           comma_semantic_phase_program_round phase child child_shift
       | Comma_Program_Exit target target_shift \<Rightarrow>
           Comma_Round_Cross (comma_shift_position target_shift target)
       | Comma_Program_Fork a target_shift \<Rightarrow>
           Comma_Round_Fork a target_shift
       | Comma_Program_Landmine target_shift \<Rightarrow>
           Comma_Round_Landmine target_shift
       | Comma_Program_Invalid \<Rightarrow> Comma_Round_Invalid)"
    by (rule comma_semantic_phase_program_round_unfold)
  show ?case
  proof (cases "comma_phase_program_step_at program phase shift")
    case (Comma_Program_Goto child child_shift)
    have structural:
      "comma_phase_program_structurally_admitted program"
      by (rule comma_phase_program_step_goto_structural[OF Comma_Program_Goto])
    have decrease:
      "9-comma_phase_program_sector child <
        9-comma_phase_program_sector program"
      by (rule comma_phase_program_step_goto_decreases_from_packet
        [OF structural Comma_Program_Goto])
    have child_fusion:
      "comma_semantic_phase_program_fold observe phase child child_shift =
        observe phase (comma_semantic_phase_program_round phase child child_shift)"
      by (rule less.hyps[OF decrease])
    show ?thesis using fold_equation round_equation
        Comma_Program_Goto child_fusion by simp
  next
    case (Comma_Program_Exit target target_shift)
    then show ?thesis using fold_equation round_equation by simp
  next
    case (Comma_Program_Fork a target_shift)
    then show ?thesis using fold_equation round_equation by simp
  next
    case (Comma_Program_Landmine target_shift)
    then show ?thesis using fold_equation round_equation by simp
  next
    case Comma_Program_Invalid
    then show ?thesis using fold_equation round_equation by simp
  qed
qed

lemma comma_semantic_phase_program_round_exact:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source=Some program"
  shows "comma_semantic_phase_program_round phase program shift =
    comma_decisive_endpoint_round phase (comma_shift_position shift source)"
  using canonical admitted normalized binding
proof (induction "9-comma_sector_number source"
    arbitrary: source program phase shift rule: less_induct)
  case less
  let ?shifted = "comma_shift_position shift source"
  have step_exact:
    "comma_phase_program_step_at program phase shift =
      comma_phase_program_step_of_action
        (comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet phase ?shifted))"
    by (rule comma_phase_program_step_at_source_packet
      [OF less.prems(1) less.prems(2) less.prems(3) less.prems(4)])
  have shifted_admitted: "comma_round_admitted ?shifted"
    using less.prems(2) by (cases source) simp_all
  have packet_round:
    "comma_decisive_endpoint_round phase ?shifted =
      (case comma_decisive_endpoint_packet phase ?shifted of
         (target,Comma_Next next) \<Rightarrow>
           if comma_round_crossing target next then Comma_Round_Cross next
           else comma_decisive_endpoint_round phase next
       | (target,Comma_Fork a delta) \<Rightarrow> Comma_Round_Fork a delta
       | (target,Comma_Landmine delta) \<Rightarrow> Comma_Round_Landmine delta
       | (target,Comma_Invalid) \<Rightarrow> Comma_Round_Invalid)"
    by (rule comma_decisive_endpoint_round_packet[OF shifted_admitted])
  have round_equation:
    "comma_semantic_phase_program_round phase program shift =
      (case comma_phase_program_step_at program phase shift of
         Comma_Program_Goto child child_shift \<Rightarrow>
           comma_semantic_phase_program_round phase child child_shift
       | Comma_Program_Exit target target_shift \<Rightarrow>
           Comma_Round_Cross (comma_shift_position target_shift target)
       | Comma_Program_Fork a target_shift \<Rightarrow>
           Comma_Round_Fork a target_shift
       | Comma_Program_Landmine target_shift \<Rightarrow>
           Comma_Round_Landmine target_shift
       | Comma_Program_Invalid \<Rightarrow> Comma_Round_Invalid)"
    by (rule comma_semantic_phase_program_round_unfold)
  show ?case
  proof (cases "comma_decisive_endpoint_packet phase ?shifted")
    case (Pair target move)
    have packet: "comma_decisive_endpoint_packet phase ?shifted=(target,move)"
      using Pair by simp
    show ?thesis
    proof (cases move)
      case (Comma_Next successor)
      show ?thesis
      proof (cases "comma_round_crossing target successor")
        case True
        have step_exit:
          "comma_phase_program_step_at program phase shift =
            Comma_Program_Exit (comma_source_continuation_base successor)
              (comma_source_continuation_shift successor)"
          using step_exact packet Comma_Next True
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_phase_program_step_of_action.simps)
        have program_result:
          "comma_semantic_phase_program_round phase program shift =
            Comma_Round_Cross successor"
          by (subst round_equation)
            (simp add: step_exit
              comma_source_continuation_reconstruct[symmetric])
        show ?thesis using program_result packet_round packet Comma_Next True
          by simp
      next
        case False
        have action_goto:
          "comma_source_continuation_action_of_packet
              (comma_decisive_endpoint_packet phase ?shifted) =
            Comma_Continuation_Goto
              (comma_source_continuation_base successor)
              (comma_source_continuation_shift successor)"
          using packet Comma_Next False
          by (simp add: comma_source_continuation_action_of_packet.simps)
        have child_facts_pair:
          "comma_canonical_position_admitted
              (comma_source_continuation_base successor) \<and>
           comma_source_continuation_base successor =
              comma_source_continuation_base
                (comma_source_continuation_base successor)"
          by (rule comma_source_continuation_goto_canonical
              [OF shifted_admitted action_goto])
        have child_facts:
          "comma_canonical_position_admitted
              (comma_source_continuation_base successor)"
          using child_facts_pair by simp
        have child_normalized:
          "comma_source_continuation_base successor =
            comma_source_continuation_base
              (comma_source_continuation_base successor)"
          using child_facts_pair by simp
        have child_admitted:
          "comma_round_admitted
              (comma_source_continuation_base successor)"
          by (rule comma_canonical_position_implies_round_admitted
              [OF child_facts])
        obtain child where child_binding:
          "comma_semantic_port_program_of_source
              (comma_source_continuation_base successor) = Some child"
          using comma_semantic_port_program_of_canonical_source_some
              [OF child_facts] by blast
        have step_goto:
          "comma_phase_program_step_at program phase shift =
            Comma_Program_Goto child
              (comma_source_continuation_shift successor)"
          using step_exact action_goto child_binding
          by (simp add: comma_phase_program_step_of_action.simps)
        have child_measure:
          "9-comma_sector_number
              (comma_source_continuation_base successor) <
            9-comma_sector_number source"
          using comma_source_continuation_goto_decreases
              [OF shifted_admitted action_goto]
          by (cases source) simp_all
        have child_exact_raw:
          "comma_semantic_phase_program_round phase child
              (comma_source_continuation_shift successor) =
            comma_decisive_endpoint_round phase
              (comma_shift_position
                (comma_source_continuation_shift successor)
                (comma_source_continuation_base successor))"
          by (rule less.hyps[OF child_measure child_facts child_admitted
              child_normalized child_binding, of phase
              "comma_source_continuation_shift successor"])
        have child_exact:
          "comma_semantic_phase_program_round phase child
              (comma_source_continuation_shift successor) =
            comma_decisive_endpoint_round phase successor"
          using child_exact_raw comma_source_continuation_reconstruct[of successor]
          by simp
        have program_result:
          "comma_semantic_phase_program_round phase program shift =
            comma_decisive_endpoint_round phase successor"
          by (subst round_equation) (simp add: step_goto child_exact)
        show ?thesis using program_result packet_round packet Comma_Next False
          by simp
      qed
    next
      case (Comma_Fork a delta)
      have program_result:
        "comma_semantic_phase_program_round phase program shift =
          Comma_Round_Fork a delta"
        using step_exact packet Comma_Fork
        by (subst round_equation)
          (simp add: comma_source_continuation_action_of_packet.simps
            comma_phase_program_step_of_action.simps)
      show ?thesis using program_result packet_round packet Comma_Fork by simp
    next
      case (Comma_Landmine delta)
      have program_result:
        "comma_semantic_phase_program_round phase program shift =
          Comma_Round_Landmine delta"
        using step_exact packet Comma_Landmine
        by (subst round_equation)
          (simp add: comma_source_continuation_action_of_packet.simps
            comma_phase_program_step_of_action.simps)
      show ?thesis using program_result packet_round packet Comma_Landmine by simp
    next
      case Comma_Invalid
      have program_result:
        "comma_semantic_phase_program_round phase program shift =
          Comma_Round_Invalid"
        using step_exact packet Comma_Invalid
        by (subst round_equation)
          (simp add: comma_source_continuation_action_of_packet.simps
            comma_phase_program_step_of_action.simps)
      show ?thesis using program_result packet_round packet Comma_Invalid by simp
    qed
  qed
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Structural phase program admission"
    @{thms comma_phase_program_source_valid_iff_structural
      comma_semantic_phase_program_round_exact
      comma_semantic_phase_program_fold_observer_fusion};
\<close>

end
