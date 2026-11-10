theory Comma_Native_Summary_Occurrence
  imports Comma_Native_Summary.Comma_Native_Summary
    Comma_Decade_Occurrence_Lift.Comma_Decade_Occurrence_Lift
    Comma_Decade_Totality.Comma_Canonical_Domain
    Comma_Literal_Bridge.Comma_Unique_Path
    Comma_Frobenius_Recurrence.Comma_Carry_Core_Quotient
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

ML \<open>
  structure Comma_Native_Occurrence_Profile =
  struct
    val started = Time.now ()
    fun checkpoint stage = Comma_Proof_Profile.report
      ("Native occurrence stage=" ^ stage ^ " elapsed_ms=" ^
        Comma_Proof_Profile.elapsed_ms started)
  end
\<close>

text \<open>Once the sparse classifier returns an exact decade residual, the
existing occurrence theorem lifts that residual through the literal prefix,
the physical exponent, and the ordered terminal children. This interface
keeps those three obligations tied to the same selected terminal.\<close>

text \<open>A complete native decade summary can also close a boundary
occurrence. The first bounded round is split by its actual event: direct
fork/landmine events finish there, while a crossing is rebased to the next
physical exponent and continued by the same sparse summary. This is the
fuel-free interface needed by global future proofs; it deliberately returns
the literal child set instead of asserting anything about the legacy macro
owner.\<close>

lemma comma_native_decade_entry_round_admitted:
  assumes decade: "comma_decade_admitted (Comma_Decade r x)"
  shows "comma_round_admitted (Comma_Entry 1 0 x)"
proof -
  have root: "comma_decade_root_admitted (Comma_Entry 1 0 x)"
    using decade by simp
  have sector: "comma_sector_entry_admitted (Comma_Entry 1 0 x)"
    by (rule comma_decade_root_admitted_implies_sector_entry[OF root])
  show ?thesis
    by (rule comma_sector_entry_admitted_implies_round_admitted[OF sector])
qed

text \<open>The weighted step is parameterized by its finite headroom producer.
The native producer evaluates the authenticated recursive carry core directly;
the old arithmetic definition remains the proved refinement target for the
literal chart theorem. This keeps the transition rule in one owner while making
the production quotient an actual consumer of that rule.\<close>

definition comma_native_core_headroom ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_native_core_headroom f residue delta entry_offset =
    (let P = comma_finite_period f (entry_offset mod 10);
         e = comma_finite_guard_extra f
     in 1 + e + nat ((int (comma_recursive_core_power_residue P
       ((residue + delta) mod 924)) - int entry_offset - int (1 + e)) mod int P))"

definition comma_native_weighted_step where
  "comma_native_weighted_step residue position =
    comma_weighted_step_with_headroom comma_native_core_headroom residue position"

lemma comma_native_core_headroom_refines:
  assumes sector: "1 \<le> f" "f \<le> 9"
  shows "comma_native_core_headroom f residue delta entry_offset =
    comma_finite_headroom f residue delta entry_offset"
proof -
  have refined:
    "comma_finite_headroom f residue delta entry_offset =
      1 + comma_finite_guard_extra f +
        nat ((int (comma_recursive_core_power_residue
          (comma_finite_period f (entry_offset mod 10)) ((residue + delta) mod 924)) -
          int entry_offset - int (1 + comma_finite_guard_extra f)) mod
            int (comma_finite_period f (entry_offset mod 10)))"
    by (rule comma_finite_headroom_recursive_core[OF sector])
  show ?thesis
    using refined by (simp add: comma_native_core_headroom_def Let_def)
qed

lemma comma_native_weighted_step_refines:
  assumes admitted: "comma_round_admitted position"
  shows "comma_native_weighted_step residue position =
    comma_weighted_step residue position"
proof (cases position)
  case (Comma_Entry f delta entry_offset)
  have sector: "1 \<le> f" "f \<le> 9"
    using admitted by (simp_all add: Comma_Entry)
  have headroom:
    "comma_native_core_headroom f residue delta entry_offset =
      comma_finite_headroom f residue delta entry_offset"
    by (rule comma_native_core_headroom_refines[OF sector])
  show ?thesis
    using headroom by (simp only: Comma_Entry comma_native_weighted_step_def
      comma_weighted_step_def comma_weighted_step_with_headroom_def
      comma_finite_position.case Let_def headroom)
next
  case (Comma_Near f delta headroom)
  show ?thesis
    by (simp only: Comma_Near comma_native_weighted_step_def comma_weighted_step_def
      comma_weighted_step_with_headroom_def comma_finite_position.case Let_def)
qed

lemmas comma_native_round_crossing_unique_prefix =
  comma_round_crossing_unique_literal_prefix
lemmas comma_native_round_close_unique_prefix =
  comma_round_close_unique_prefix

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "generic summary occurrence imported"\<close>

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "comma_decade_summary_unique_occurrence"\<close>

theorem comma_decade_summary_unique_occurrence:
  assumes summary: "comma_decade_exact_summary s h tau"
    and admitted: "comma_decade_admitted s"
    and exponent: "5\<le>p"
    and binding: "s=Comma_Decade (p mod 924) x"
  obtains weight t where
    "comma_unique_literal_path weight (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move tau"
proof -
  have result: "\<exists>weight t. comma_unique_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x)) (comma_chart_value (p+h) t) \<and>
      comma_round_admitted t \<and> comma_round_delta t=0 \<and>
      comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move tau"
    by (rule comma_decade_summary_unique_occurrence_exists
      [OF summary admitted exponent binding])
  show thesis using result that by blast
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "comma_sparse_summary_unique_ordered_occurrence"\<close>

theorem comma_sparse_summary_unique_ordered_occurrence:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and entry_offset: "x\<le>90"
    and exponent: "5\<le>p"
  obtains h terminal weight t where
    "comma_sparse_decade_summary rows (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    "h\<le>26"
    "comma_unique_literal_path weight (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
      = comma_summary_ordered_children terminal (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in>set (comma_summary_ordered_children terminal (p+h))"
proof -
  have admitted: "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using entry_offset by simp
  obtain h terminal where summary:
    "comma_sparse_decade_summary rows (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary (Comma_Decade (p mod 924) x) h terminal"
    using comma_sparse_decade_summary_total_exact[OF powers stops admitted] by blast
  obtain weight t where unique:
    "comma_unique_literal_path weight (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    by (rule comma_decade_summary_unique_occurrence[OF summary(3) admitted exponent refl])
  have pplus: "5\<le>p+h" using exponent by arith
  have children:
    "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
      = comma_summary_ordered_children terminal (p+h)"
    by (rule comma_summary_terminal_children_exact(1)[OF unique(2) unique(3) pplus unique(4)])
  have members:
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in>set (comma_summary_ordered_children terminal (p+h))"
    by (rule comma_summary_terminal_children_exact(2)[OF unique(2) unique(3) pplus unique(4)])
  show thesis
    by (rule that[OF summary(1) summary(2) unique(1) unique(2) unique(3) unique(4)
      children members])
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "comma_sparse_summary_ordered_occurrence"\<close>

theorem comma_sparse_summary_ordered_occurrence:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and entry_offset: "x\<le>90"
    and exponent: "5\<le>p"
  obtains h terminal w t where
    "comma_sparse_decade_summary rows (Comma_Decade (p mod 924) x) = Some (h,terminal)"
    "h\<le>26"
    "comma_literal_path w (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"

      "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"

      "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
        = comma_summary_ordered_children terminal (p+h)"
    "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in> set (comma_summary_ordered_children terminal (p+h))"
proof -
  obtain h terminal weight t where summary:
    "comma_sparse_decade_summary rows (Comma_Decade (p mod 924) x)=Some (h,terminal)"
    and height: "h\<le>26"
    and unique: "comma_unique_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x)) (comma_chart_value (p+h) t)"
    and admitted: "comma_round_admitted t"
    and zero_delta: "comma_round_delta t=0"
    and terminal_move:
      "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    and children:
      "comma_large_children (comma_sector_number t) (p+h) (comma_chart_value (p+h) t)
        = comma_summary_ordered_children terminal (p+h)"
    and members: "\<And>v. comma_child (comma_chart_value (p+h) t) v \<longleftrightarrow>
      v\<in> set (comma_summary_ordered_children terminal (p+h))"
    using comma_sparse_summary_unique_ordered_occurrence[OF powers stops entry_offset exponent] by blast
  have literal: "comma_literal_path weight (comma_chart_value p (Comma_Entry 1 0 x))
      (comma_chart_value (p+h) t)"
    by (rule comma_unique_literal_path_literal[OF unique])
  show thesis by (rule that[OF summary height literal admitted zero_delta terminal_move
      children members])
qed

fun comma_sparse_boundary_event_outcome ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow> nat \<Rightarrow>
    comma_round_result \<Rightarrow> comma_finite_outcome option" where
  "comma_sparse_boundary_event_outcome rows r (Comma_Round_Fork a d) =
    Some (Comma_Fork_At a d)"
| "comma_sparse_boundary_event_outcome rows r (Comma_Round_Landmine d) =
    Some (Comma_Landmine_At d)"
| "comma_sparse_boundary_event_outcome rows r
      (Comma_Round_Cross (Comma_Entry f d x)) =
    (if f=1 then
      (case comma_sparse_decade_weight_summary rows (Comma_Decade ((r+d) mod 924) x) of
        Some D \<Rightarrow>
          (case comma_terminal_weight_decode D of (h,terminal) \<Rightarrow>
            Some (comma_summary_outcome (h+d) terminal))
      | None \<Rightarrow> None)
     else None)"
| "comma_sparse_boundary_event_outcome rows r
      (Comma_Round_Cross (Comma_Near f d h)) = None"
| "comma_sparse_boundary_event_outcome rows r Comma_Round_Invalid = None"

definition comma_native_boundary_step ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_native_boundary_step rows q =
    (case q of (kind,a,r) \<Rightarrow>
      if comma_boundary_valid q then
        (case comma_round_close r (comma_finite_initial q) of
          (n,terminal,event) \<Rightarrow>
            comma_sparse_boundary_event_outcome rows r event)
      else None)"

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "comma_sparse_boundary_ordered_occurrence"\<close>

theorem comma_sparse_boundary_ordered_occurrence_step:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  obtains outcome endpoint w where
    "comma_native_boundary_step rows q=Some outcome"
    "comma_native_boundary_children q outcome =
      (case outcome of Comma_Landmine_At d \<Rightarrow> []
       | Comma_Fork_At a d \<Rightarrow>
          [(Comma_N,a,(snd (snd q)+d) mod 924),
           (Comma_Z,a,(snd (snd q)+d) mod 924)])"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    by (cases kind) (simp_all add: q comma_finite_initial_def)
  have phase_r: "r mod 924=p mod 924"
    using r_bound phase q by simp
  obtain n terminal_position event where close:
    "comma_round_close r (comma_finite_initial q)=(n,terminal_position,event)"
    by (metis surj_pair)
  have close_q: "comma_round_close (snd (snd q)) (comma_finite_initial q)=(n,terminal_position,event)"
    using close q by simp
  have start: "comma_chart_value p (comma_finite_initial q)=comma_boundary_value q p"
    by (rule comma_chart_initial_refines_boundary[OF valid])
  ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-before-event-cases"\<close>
  show thesis
  proof (cases event)
    case (Comma_Round_Fork b d)
    obtain w where path:
      "comma_literal_path w (comma_boundary_value q p)
        (comma_chart_value p terminal_position)"
      and children:
      "\<forall>v. comma_child (comma_chart_value p terminal_position) v \<longleftrightarrow>
        v=comma_near_boundary b (p+d) \<or> v=comma_zero_boundary b (p+d)"
      using comma_boundary_fork_occurrence[OF valid exponent phase close_q[unfolded Comma_Round_Fork]]
      by blast
    obtain unique_weight where unique_prefix:
      "comma_unique_literal_path unique_weight
        (comma_chart_value p (comma_finite_initial q)) (comma_chart_value p terminal_position)"
      by (rule comma_native_round_close_unique_prefix[OF close[unfolded Comma_Round_Fork]
        phase_r exponent source_valid])
    have unique:
      "comma_unique_literal_path unique_weight (comma_boundary_value q p)
        (comma_chart_value p terminal_position)"
      using unique_prefix start by simp
    let ?outcome="Comma_Fork_At b d"
    have close_fork:
      "comma_round_close r (comma_finite_initial q)=
        (n,terminal_position,Comma_Round_Fork b d)"
      using close Comma_Round_Fork by simp
    have event_outcome:
      "comma_sparse_boundary_event_outcome rows r (Comma_Round_Fork b d)=
        Some (Comma_Fork_At b d)"
      by simp
    have step_result: "comma_native_boundary_step rows q=Some ?outcome"
      using valid q close_fork event_outcome
      by (simp only: comma_native_boundary_step_def q valid close_fork if_True
        event_outcome prod.case)
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-fork-step"\<close>
    have child_values:
      "set (map (\<lambda>c. comma_boundary_value c (p+d))
          (comma_native_boundary_children q ?outcome)) =
        {comma_near_boundary b (p+d),comma_zero_boundary b (p+d)}"
      by (rule comma_native_boundary_fork_children_render[OF q])
    have child_values_list:
      "set (map (\<lambda>c. comma_boundary_value c (p+d))
          (comma_native_boundary_children q ?outcome)) =
        set [comma_near_boundary b (p+d),comma_zero_boundary b (p+d)]"
      using child_values by (simp only: child_values list.set)
    have endpoint_children:
      "\<forall>v. comma_child (comma_chart_value p terminal_position) v
        \<longleftrightarrow> v\<in>set [comma_near_boundary b (p+d),comma_zero_boundary b (p+d)]"
      using children by auto
    have child_relation:
      "\<And>v. comma_child (comma_chart_value p terminal_position) v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q ?outcome).
          v=comma_boundary_value child (p+comma_native_outcome_delta ?outcome))"
      using comma_relation_from_rendered_list[OF endpoint_children child_values_list]
      by (simp only: comma_native_outcome_delta_def comma_finite_outcome.case; blast)
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-fork-children"\<close>
    show thesis by (rule that[where outcome="?outcome", OF step_result
      comma_native_boundary_children_cases unique child_relation])
  next
    case (Comma_Round_Landmine d)
    obtain w where path:
      "comma_literal_path w (comma_boundary_value q p)
        (comma_chart_value p terminal_position)"
      and no_child: "\<nexists>v. comma_child (comma_chart_value p terminal_position) v"
      using comma_boundary_landmine_occurrence[OF valid exponent phase close_q[unfolded Comma_Round_Landmine]]
      by blast
    obtain unique_weight where unique_prefix:
      "comma_unique_literal_path unique_weight
        (comma_chart_value p (comma_finite_initial q)) (comma_chart_value p terminal_position)"
      by (rule comma_native_round_close_unique_prefix[OF close[unfolded Comma_Round_Landmine]
        phase_r exponent source_valid])
    have unique:
      "comma_unique_literal_path unique_weight (comma_boundary_value q p)
        (comma_chart_value p terminal_position)"
      using unique_prefix start by simp
    let ?outcome="Comma_Landmine_At d"
    have close_landmine:
      "comma_round_close r (comma_finite_initial q)=
        (n,terminal_position,Comma_Round_Landmine d)"
      using close Comma_Round_Landmine by simp
    have event_outcome:
      "comma_sparse_boundary_event_outcome rows r (Comma_Round_Landmine d)=
        Some (Comma_Landmine_At d)"
      by simp
    have step_result: "comma_native_boundary_step rows q=Some ?outcome"
      using valid q close_landmine event_outcome
      by (simp only: comma_native_boundary_step_def q valid close_landmine if_True
        event_outcome prod.case)
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-landmine-step"\<close>
    have child_relation:
      "\<And>v. comma_child (comma_chart_value p terminal_position) v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q ?outcome).
          v=comma_boundary_value child (p+comma_native_outcome_delta ?outcome))"
      using no_child by (simp add: comma_native_boundary_children_def
        comma_native_outcome_delta_def)
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-landmine-children"\<close>
    show thesis by (rule that[where outcome="?outcome", OF step_result
      comma_native_boundary_children_cases unique child_relation])
  next
    case (Comma_Round_Cross target)
    have close_cross:
      "comma_round_close r (comma_finite_initial q)=(n,terminal_position,Comma_Round_Cross target)"
      using close Comma_Round_Cross by simp
    obtain x where x: "x\<le>90"
      and target: "target=Comma_Entry 1 (Suc (comma_round_delta (comma_finite_initial q))) x"
      using comma_round_close_crossing_phase[OF close_cross source_valid] by blast
    have target_entry: "target=Comma_Entry 1 1 x"
      using target source_delta by simp
    obtain crossing_weight where prefix:
      "comma_unique_literal_path (Suc crossing_weight)
        (comma_chart_value p (comma_finite_initial q)) (comma_chart_value p target)"
      using comma_native_round_crossing_unique_prefix
        [OF close_cross phase_r exponent source_valid]
      by blast
    have rebase:
      "comma_chart_value p target=comma_chart_value (Suc p) (Comma_Entry 1 0 x)"
      using target_entry by (simp add: comma_chart_value_def)
    have next_exponent: "5\<le>Suc p" using exponent by simp
    obtain h terminal w' t where summary:
      "comma_sparse_decade_summary rows (Comma_Decade ((Suc p) mod 924) x)=Some (h,terminal)"
      "h\<le>26"
      "comma_unique_literal_path w' (comma_chart_value (Suc p) (Comma_Entry 1 0 x))
        (comma_chart_value (Suc p+h) t)"
      "comma_round_admitted t"
      "comma_round_delta t=0"
      "comma_finite_step ((Suc p+h) mod 924) t=comma_summary_terminal_move terminal"
      "comma_large_children (comma_sector_number t) (Suc p+h)
        (comma_chart_value (Suc p+h) t)=comma_summary_ordered_children terminal (Suc p+h)"
      "\<And>v. comma_child (comma_chart_value (Suc p+h) t) v \<longleftrightarrow>
        v\<in>set (comma_summary_ordered_children terminal (Suc p+h))"
      using comma_sparse_summary_unique_ordered_occurrence[OF powers stops x next_exponent]
      by blast
    have prefix_rebased:
      "comma_unique_literal_path (Suc crossing_weight) (comma_boundary_value q p)
        (comma_chart_value (Suc p) (Comma_Entry 1 0 x))"
      using prefix start rebase by simp
    have joined:
      "comma_unique_literal_path (Suc crossing_weight+w') (comma_boundary_value q p)
        (comma_chart_value (Suc p+h) t)"
      by (rule comma_unique_literal_path_append[OF prefix_rebased summary(3)])
    let ?outcome="case terminal of
        Comma_Terminal_Landmine \<Rightarrow> Comma_Landmine_At (Suc h)
      | Comma_Terminal_Fork a \<Rightarrow> Comma_Fork_At a (Suc h)"
  have sparse_phase:
      "comma_sparse_decade_summary rows
        (Comma_Decade ((r+1) mod 924) x)=Some (h,terminal)"
    proof -
      have phase_suc:
        "Suc (r mod 924) mod 924=Suc (p mod 924) mod 924"
        using phase_r by (rule arg_cong[where f="\<lambda>v. Suc v mod 924"])
      have phase_next: "(r+1) mod 924=(p+1) mod 924"
      proof -
        have "Suc r mod 924=Suc p mod 924"
          using phase_suc by (simp only: mod_Suc_eq)
        then show ?thesis by simp
      qed
      show ?thesis using summary(1) phase_next by simp
    qed
    have sparse_valid:
      "comma_decade_admitted (Comma_Decade ((r+1) mod 924) x)"
      using x by simp
    obtain D exact_height exact_terminal where weighted_summary:
      "comma_sparse_decade_weight_summary rows
        (Comma_Decade ((r+1) mod 924) x)=Some D"
      and encoded_pair: "comma_terminal_weight_decode D=(exact_height,exact_terminal)"
      and weighted_witness:
        "comma_sparse_decade_summary rows
          (Comma_Decade ((r+1) mod 924) x)=Some (exact_height,exact_terminal)"
      by (rule comma_sparse_decade_weight_summary_complete_exact
        [OF powers stops sparse_valid])
    have exact_pair: "exact_height=h \<and> exact_terminal=terminal"
      using weighted_witness sparse_phase by simp
    have decoded_pair: "comma_terminal_weight_decode D=(h,terminal)"
      using encoded_pair exact_pair by simp
    have close_target:
      "comma_round_close r (comma_finite_initial q)=
        (n,terminal_position,Comma_Round_Cross (Comma_Entry 1 1 x))"
      using close Comma_Round_Cross target_entry by simp
    have event_outcome:
      "comma_sparse_boundary_event_outcome rows r
        (Comma_Round_Cross (Comma_Entry 1 1 x))=Some ?outcome"
    proof -
      have summarized:
        "comma_sparse_boundary_event_outcome rows r
          (Comma_Round_Cross (Comma_Entry 1 1 x)) =
          Some (comma_summary_outcome (h+1) terminal)"
      by (simp only: comma_sparse_boundary_event_outcome.simps if_True refl
        weighted_summary option.case decoded_pair prod.case)
      have outcome_eq:
        "comma_summary_outcome (h+1) terminal=?outcome"
        by (cases terminal) (simp_all add: comma_summary_outcome.simps)
      show ?thesis using summarized outcome_eq by simp
    qed
    have step_result: "comma_native_boundary_step rows q=Some ?outcome"
      using valid q close_target event_outcome
      by (simp only: comma_native_boundary_step_def q valid close_target if_True
        event_outcome prod.case)
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-cross-step"\<close>
    have outcome_summary:
      "?outcome=comma_summary_outcome (Suc h) terminal"
      by (cases terminal) (simp_all add: comma_summary_outcome.simps)
    have outcome_delta: "comma_native_outcome_delta ?outcome=Suc h"
      by (cases terminal) (simp_all add: comma_native_outcome_delta_def)
    have rendered_summary:
      "set (map (\<lambda>child. comma_boundary_value child (p+Suc h))
        (comma_native_boundary_children q (comma_summary_outcome (Suc h) terminal))) =
        set (comma_summary_ordered_children terminal (p+Suc h))"
      by (rule comma_native_boundary_children_render_summary[OF q])
    have rendered_children:
      "set (map (\<lambda>child. comma_boundary_value child
          (p+comma_native_outcome_delta ?outcome))
        (comma_native_boundary_children q ?outcome)) =
        set (comma_summary_ordered_children terminal (Suc p+h))"
      using rendered_summary outcome_summary outcome_delta by simp
    have endpoint_children:
      "\<forall>v. comma_child (comma_chart_value (Suc p+h) t) v
        \<longleftrightarrow> v\<in>set (comma_summary_ordered_children terminal (Suc p+h))"
      using summary(8) by blast
    have child_relation:
      "\<And>v. comma_child (comma_chart_value (Suc p+h) t) v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q ?outcome).
          v=comma_boundary_value child (p+comma_native_outcome_delta ?outcome))"
      using comma_relation_from_rendered_list[OF endpoint_children rendered_children]
      by blast
    ML_prf \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-cross-children"\<close>
    show thesis
      by (rule that[where outcome="?outcome", OF step_result
        comma_native_boundary_children_cases joined child_relation])
  next
    case Comma_Round_Invalid
    have impossible: "event\<noteq>Comma_Round_Invalid"
      by (rule comma_round_close_admitted(2)[OF close source_valid])
    then show thesis using Comma_Round_Invalid by contradiction
  qed
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-ordered-step-complete"\<close>

theorem comma_sparse_boundary_ordered_occurrence:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  obtains outcome endpoint w where
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "comma_native_boundary_children q outcome =
      (case outcome of Comma_Landmine_At d \<Rightarrow> []
       | Comma_Fork_At a d \<Rightarrow>
          [(Comma_N,a,(snd (snd q)+d) mod 924),
           (Comma_Z,a,(snd (snd q)+d) mod 924)])"
    "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
proof -
  show thesis
  proof (rule comma_sparse_boundary_ordered_occurrence_step
      [OF powers stops valid exponent phase])
    fix outcome endpoint w
    assume step: "comma_native_boundary_step rows q=Some outcome"
      and children: "comma_native_boundary_children q outcome =
        (case outcome of Comma_Landmine_At d \<Rightarrow> []
         | Comma_Fork_At a d \<Rightarrow>
            [(Comma_N,a,(snd (snd q)+d) mod 924),
             (Comma_Z,a,(snd (snd q)+d) mod 924)])"
      and occurrence:
        "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
      and child_relation: "\<And>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q outcome).
          v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    show thesis by (rule that[OF occurrence children child_relation])
  qed
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint "native-boundary-ordered-occurrence-complete"\<close>

ML \<open>
  val endpoint = @{thms comma_sparse_summary_ordered_occurrence
      comma_sparse_boundary_ordered_occurrence_step
      comma_sparse_boundary_ordered_occurrence}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native occurrence endpoints" endpoint
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Native occurrence recursive-core authority"
    ["comma_recursive_core_power_residue_refines"] endpoint
\<close>

end
