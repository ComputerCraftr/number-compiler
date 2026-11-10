theory Comma_Continue_Core_Fold
  imports Comma_Program_Continue_Guard_Exact Comma_Symbolic_Class_Step
begin

text \<open>
The source compiler constructs CoreValues binds from right to left.  This
generic fold law gives the same ordered selection without expanding the
observer's recursive list equation at each suffix.  Guard uniqueness is the
only condition needed: repeated labels remain harmless because selection is
idempotent for an equal label.
\<close>

lemma comma_list_ex_guarded_select_foldr:
  fixes xs :: "'a list"
    and guard selected :: "'a \<Rightarrow> bool"
  assumes unique:
    "(\<forall>x\<in>set xs. \<forall>y\<in>set xs.
      guard x \<longrightarrow> guard y \<longrightarrow> x=y)"
  shows "list_ex (\<lambda>x. guard x \<and> selected x) xs =
    foldr (\<lambda>x tail. if guard x then selected x else tail) xs False"
  using unique
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail_unique:
    "(\<forall>u\<in>set xs. \<forall>v\<in>set xs.
      guard u \<longrightarrow> guard v \<longrightarrow> u=v)"
    using Cons.prems by auto
  have tail_fold:
    "list_ex (\<lambda>u. guard u \<and> selected u) xs =
      foldr (\<lambda>u tail. if guard u then selected u else tail) xs False"
    by (rule Cons.IH[OF tail_unique])
  show ?case
  proof (cases "guard x")
    case False
    show ?thesis using tail_fold
      by (simp only: list_ex_Cons_iff foldr.simps comp_apply False if_False simp_thms)
  next
    case True
    have tail_selected:
      "list_ex (\<lambda>u. guard u \<and> selected u) xs \<Longrightarrow> selected x"
    proof -
      assume exists_tail:
        "list_ex (\<lambda>u. guard u \<and> selected u) xs"
      then obtain u where u:
        "u \<in> set xs" "guard u" "selected u"
        by (auto simp: list_ex_iff)
      have x_member: "x \<in> set (x#xs)" by simp
      have u_member: "u \<in> set (x#xs)" using u(1) by simp
      have "x=u"
        by (rule Cons.prems[rule_format, OF x_member u_member True u(2)])
      with u show "selected x" by simp
    qed
    show ?thesis using tail_selected
      by (simp only: list_ex_Cons_iff foldr.simps comp_apply True if_True simp_thms; blast)
  qed
qed

lemma comma_phase_continue_core_values_observer_foldr:
  "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core values) shift target =
    foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_phase_continue_action_observer phase f shift
        (comma_phase_program_entry_core_value_action f residue core wanted) target
      else tail) values False"
proof -
  have unique:
    "(\<forall>wanted\<in>set values. \<forall>other\<in>set values.
      comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) \<longrightarrow>
      comma_crt_eval (phase+shift) (comma_core_value_guard core other) \<longrightarrow>
      wanted=other)"
    using comma_core_value_guard_unique by blast
  show ?thesis
    by (simp only: comma_phase_continue_compile_job_observer.simps(2)
        comma_list_ex_guarded_select_foldr[OF unique])
qed

text \<open>
Unsupported core-value guards cannot select at any phase.  This fold law
allows the proposal compiler to omit those values before it imports their
guard roots or proves their action suffixes; the complete observer remains
unchanged.
\<close>

lemma comma_foldr_if_filter:
  fixes xs :: "'a list"
    and keep active :: "'a \<Rightarrow> bool"
    and selected :: "'a \<Rightarrow> 'b"
    and fallback :: 'b
  assumes inactive:
    "\<forall>x\<in>set xs. \<not> keep x \<longrightarrow> \<not> active x"
  shows "foldr (\<lambda>x tail. if active x then selected x else tail)
      xs fallback =
    foldr (\<lambda>x tail. if active x then selected x else tail)
      (filter keep xs) fallback"
  using inactive
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail_inactive:
    "\<forall>y\<in>set xs. \<not> keep y \<longrightarrow> \<not> active y"
    using Cons.prems by auto
  have head_inactive: "\<not> keep x \<longrightarrow> \<not> active x"
    using Cons.prems by auto
  show ?case
  proof (cases "keep x")
    case True
    then show ?thesis using Cons.IH[OF tail_inactive] by simp
  next
    case False
    have "\<not> active x" using head_inactive False by blast
    then show ?thesis using False Cons.IH[OF tail_inactive] by simp
  qed
qed

definition comma_core_supported_values ::
    "comma_phase_core_id \<Rightarrow> nat list" where
  "comma_core_supported_values core =
    filter (\<lambda>wanted. comma_crt_supported
      (comma_core_value_guard core wanted))
      [0..<comma_phase_core_modulus core]"

lemma comma_phase_core_clock_period_small:
  "comma_core_period (comma_phase_core_modulus core) \<in> {1,2,3,6,22,28}"
  by (cases core) (simp_all add: comma_core_period_def)

lemma comma_core_value_guard_supported_iff_local_period:
  "comma_crt_supported (comma_core_value_guard core wanted) \<longleftrightarrow>
    list_ex (\<lambda>phase.
      comma_cyclotomic_clock_core_value (comma_cyclotomic_clock_of phase)
        (comma_phase_core_modulus core) = wanted)
      [0..<comma_core_period (comma_phase_core_modulus core)]"
proof -
  let ?c = "comma_phase_core_modulus core"
  let ?T = "comma_core_period ?c"
  let ?guard = "comma_core_value_guard core wanted"
  have period: "?T \<in> {1,2,3,6,22,28}"
    by (rule comma_phase_core_clock_period_small)
  have positive: "0 < ?T" and short: "?T < 924"
    using period by auto
  have admitted: "comma_crt_admitted 0 ?guard"
    by (rule comma_core_value_guard_admitted)
  have periodic:
    "comma_cyclotomic_clock_core_value
        (comma_cyclotomic_clock_of r) ?c =
      comma_cyclotomic_clock_core_value
        (comma_cyclotomic_clock_of (r mod ?T)) ?c" for r
    using comma_cyclotomic_clock_projection[OF period, of r 919]
      comma_cyclotomic_clock_projection[OF period, of "r mod ?T" 919]
    by (simp add: comma_cyclotomic_clock_core_value_def mod_add_left_eq)
  have phase_exists:
    "(\<exists>r<924. comma_crt_eval r ?guard) \<longleftrightarrow>
      (\<exists>r<?T. comma_crt_eval r ?guard)"
  proof
    assume "\<exists>r<924. comma_crt_eval r ?guard"
    then obtain r where r: "r<924" "comma_crt_eval r ?guard" by blast
    have bound: "r mod ?T < ?T"
      by (rule mod_less_divisor[OF positive])
    have eval: "comma_crt_eval (r mod ?T) ?guard"
      using r(2) periodic[of r]
      by (simp only: comma_core_value_guard_eval)
    show "\<exists>r<?T. comma_crt_eval r ?guard"
      using bound eval by blast
  next
    assume "\<exists>r<?T. comma_crt_eval r ?guard"
    then obtain r where r: "r<?T" "comma_crt_eval r ?guard" by blast
    have bound: "r<924" by (rule less_trans[OF r(1) short])
    show "\<exists>r<924. comma_crt_eval r ?guard"
      using bound r(2) by blast
  qed
  have supported_iff_eval:
    "comma_crt_supported ?guard \<longleftrightarrow>
      (\<exists>r<924. comma_crt_eval r ?guard)"
    using comma_crt_supported_nonempty[OF admitted]
    by (simp add: comma_crt_set_def)
  have local_eval:
    "(\<exists>r<?T. comma_crt_eval r ?guard) \<longleftrightarrow>
      list_ex (\<lambda>phase.
        comma_cyclotomic_clock_core_value (comma_cyclotomic_clock_of phase) ?c = wanted)
        [0..<?T]"
    by (auto simp: list_ex_iff comma_core_value_guard_eval)
  show ?thesis
    using supported_iff_eval phase_exists local_eval by blast
qed

declare comma_core_supported_values_def[code drop]

lemma comma_core_supported_values_local_period:
  "comma_core_supported_values core =
    filter (\<lambda>wanted. list_ex (\<lambda>phase.
      comma_cyclotomic_clock_core_value (comma_cyclotomic_clock_of phase)
        (comma_phase_core_modulus core) = wanted)
      [0..<comma_core_period (comma_phase_core_modulus core)])
      [0..<comma_phase_core_modulus core]"
  unfolding comma_core_supported_values_def
  by (simp only: comma_core_value_guard_supported_iff_local_period)

lemma comma_core_clock_offset_image_exact:
  assumes period: "T \<in> {1,2,3,6,22,28}"
  shows "(\<exists>phase<T.
      comma_recursive_core_residue c ((phase + 919) mod T) = wanted) \<longleftrightarrow>
    (\<exists>t<T. comma_recursive_core_residue c t = wanted)"
proof
  assume "\<exists>phase<T.
    comma_recursive_core_residue c ((phase + 919) mod T) = wanted"
  then obtain phase where selected:
    "comma_recursive_core_residue c ((phase + 919) mod T) = wanted"
    by blast
  have bound: "(phase + 919) mod T < T"
    using period by auto
  show "\<exists>t<T. comma_recursive_core_residue c t = wanted"
    using bound selected by blast
next
  assume "\<exists>t<T. comma_recursive_core_residue c t = wanted"
  then obtain t where t:
    "t<T" "comma_recursive_core_residue c t = wanted"
    by blast
  have divides: "T dvd 924" using period by auto
  have zero: "924 mod T = 0"
    by (rule dvd_imp_mod_0[OF divides])
  let ?phase = "(t + 5) mod T"
  have phase_bound: "?phase<T"
    using period by auto
  have inverse: "(?phase + 919) mod T = t"
  proof -
    have "((t+5) mod T + 919) mod T = (t+5+919) mod T"
      by (rule mod_add_left_eq)
    also have "... = (t+924) mod T" by (simp add: add.assoc)
    also have "... = (t + (924 mod T)) mod T"
      by (rule mod_add_right_eq[symmetric])
    also have "... = t" using t(1) zero by simp
    finally show ?thesis .
  qed
  have selected:
    "comma_recursive_core_residue c ((?phase + 919) mod T) = wanted"
    by (simp only: inverse t(2))
  show "\<exists>phase<T.
      comma_recursive_core_residue c ((phase + 919) mod T) = wanted"
    using phase_bound selected by blast
qed

lemma comma_core_value_guard_supported_iff_local_residue:
  "comma_crt_supported (comma_core_value_guard core wanted) \<longleftrightarrow>
    (\<exists>t<comma_core_period (comma_phase_core_modulus core).
      comma_recursive_core_residue (comma_phase_core_modulus core) t = wanted)"
proof -
  let ?c = "comma_phase_core_modulus core"
  let ?T = "comma_core_period ?c"
  have period: "?T \<in> {1,2,3,6,22,28}"
    by (rule comma_phase_core_clock_period_small)
  have clock_value:
    "comma_cyclotomic_clock_core_value (comma_cyclotomic_clock_of phase) ?c =
      comma_recursive_core_residue ?c ((phase+919) mod ?T)" for phase
    using comma_cyclotomic_clock_projection[OF period, of phase 919]
    by (simp add: comma_cyclotomic_clock_core_value_def)
  have local_equiv:
    "(\<exists>phase<?T.
      comma_cyclotomic_clock_core_value (comma_cyclotomic_clock_of phase) ?c = wanted)
      \<longleftrightarrow> (\<exists>t<?T. comma_recursive_core_residue ?c t = wanted)"
    using comma_core_clock_offset_image_exact[OF period, of ?c wanted]
    by (simp only: clock_value)
  show ?thesis
    using comma_core_value_guard_supported_iff_local_period[of core wanted] local_equiv
    by (auto simp: list_ex_iff)
qed

text \<open>Evaluate the short generator once and recover its sorted support.
Neither CRT guard trees nor a candidate-by-phase Cartesian product is needed
by the executable selector contract.\<close>

lemma comma_core_supported_values_residue_image [code]:
  "comma_core_supported_values core =
    sort (remdups (map
      (comma_recursive_core_residue (comma_phase_core_modulus core))
      [0..<comma_core_period (comma_phase_core_modulus core)]))"
proof -
  let ?c = "comma_phase_core_modulus core"
  let ?T = "comma_core_period ?c"
  have catalog: "?c \<in> {1,3,7,11,13,21,23,27,29}"
    by (cases core) simp_all
  have positive: "0<?c" using catalog by auto
  have residues_bounded: "comma_recursive_core_residue ?c t < ?c" for t
    by (simp only: comma_recursive_core_residue_refines[OF catalog];
        rule mod_less_divisor[OF positive])
  have support_set:
    "set (comma_core_supported_values core) =
      set (map (comma_recursive_core_residue ?c) [0..<?T])"
    unfolding comma_core_supported_values_def
    using comma_core_value_guard_supported_iff_local_residue[of core]
      residues_bounded
    by auto
  show ?thesis
    by (rule sorted_distinct_set_unique)
      (use support_set in \<open>auto simp: comma_core_supported_values_def
        intro: sorted_wrt_filter\<close>)
qed

lemma comma_phase_continue_core_values_observer_supported_filter:
  "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core values) shift target =
    comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core
        (filter (\<lambda>wanted. comma_crt_supported
          (comma_core_value_guard core wanted)) values)) shift target"
proof -
  have inactive:
    "\<forall>wanted\<in>set values.
      \<not> comma_crt_supported (comma_core_value_guard core wanted) \<longrightarrow>
      \<not> comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)"
    using comma_core_value_guard_unsupported_no_eval by blast
  show ?thesis
    unfolding comma_phase_continue_core_values_observer_foldr
    by (rule comma_foldr_if_filter[OF inactive])
qed

lemma comma_phase_continue_core_supported_values_observer:
  "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core
        [0..<comma_phase_core_modulus core]) shift target =
    comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core
        (comma_core_supported_values core)) shift target"
  unfolding comma_core_supported_values_def
  by (rule comma_phase_continue_core_values_observer_supported_filter)

lemma comma_phase_continue_core_values_observer_cons:
  "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core (wanted#values)) shift target =
    (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
     then comma_phase_continue_action_observer phase f shift
       (comma_phase_program_entry_core_value_action f residue core wanted) target
     else comma_phase_continue_compile_job_observer phase
       (Comma_Continue_Core_Values_Job f residue core values) shift target)"
  by (simp only: comma_phase_continue_core_values_observer_foldr foldr.simps comp_apply)

lemma comma_phase_continue_core_values_guard_tail_disjoint:
  assumes omitted: "wanted \<notin> set values"
  shows "\<not> (comma_crt_eval (phase+shift)
        (comma_core_value_guard core wanted) \<and>
      comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core values) shift target)"
proof
  assume both:
    "comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) \<and>
      comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core values) shift target"
  from both have selected:
    "comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)"
    and tail:
    "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core values) shift target"
    by auto
  from tail obtain other where other:
    "other \<in> set values"
    "comma_crt_eval (phase+shift) (comma_core_value_guard core other)"
    "comma_phase_continue_action_observer phase f shift
       (comma_phase_program_entry_core_value_action f residue core other) target"
    by (auto simp: comma_phase_continue_compile_job_observer.simps(2)
        list_ex_iff)
  have "wanted=other"
    by (rule comma_core_value_guard_unique[OF selected other(2)])
  with omitted other(1) show False by blast
qed

text \<open>
The existing source/program compiler can preserve complete one-step actions
with the same normalized program fold and core guards.  A Continue output is
unlifted to its phase-free label only when the next-phase law is proved;
Fork and Landmine parameters are kept intact.  The MDD producer can intern
these full labels without imposing the 56-label bound on recursive jobs.
\<close>

fun comma_phase_rank_mask_unlift ::
    "nat \<Rightarrow> nat comma_phase_class_action \<Rightarrow>
      comma_phase_rank_mask_action" where
  "comma_phase_rank_mask_unlift phase Comma_Phase_Class_Invalid =
    Comma_Phase_Rank_Mask_Invalid"
| "comma_phase_rank_mask_unlift phase (Comma_Phase_Class_Fork a d) =
    Comma_Phase_Rank_Mask_Fork a d"
| "comma_phase_rank_mask_unlift phase (Comma_Phase_Class_Landmine d) =
    Comma_Phase_Rank_Mask_Landmine d"
| "comma_phase_rank_mask_unlift phase (Comma_Phase_Class_Continue q cid) =
    (if q = (phase+1) mod 924 then Comma_Phase_Rank_Mask_Continue cid
     else Comma_Phase_Rank_Mask_Invalid)"

lemma comma_phase_rank_mask_unlift_lift:
  "comma_phase_rank_mask_unlift phase
      (comma_phase_rank_mask_lift phase action) = action"
  by (cases action) simp_all

lemma comma_phase_rank_mask_lift_unlift:
  assumes continue_clock:
    "\<And>q cid. action = Comma_Phase_Class_Continue q cid
      \<Longrightarrow> q = (phase+1) mod 924"
  shows "comma_phase_rank_mask_lift phase
      (comma_phase_rank_mask_unlift phase action) = action"
  using continue_clock by (cases action) auto

definition comma_phase_program_full_action_output ::
    "nat \<Rightarrow> comma_round_result \<Rightarrow>
      comma_phase_rank_mask_action" where
  "comma_phase_program_full_action_output phase output =
    comma_phase_rank_mask_unlift phase
      (comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_decode phase output))"

lemma comma_phase_program_full_action_terminal:
  "comma_phase_program_full_action_output phase Comma_Round_Invalid =
    Comma_Phase_Rank_Mask_Invalid"
  "comma_phase_program_full_action_output phase (Comma_Round_Fork a delta) =
    Comma_Phase_Rank_Mask_Fork a delta"
  "comma_phase_program_full_action_output phase (Comma_Round_Landmine delta) =
    Comma_Phase_Rank_Mask_Landmine delta"
  by (simp_all only: comma_phase_program_full_action_output_def
      comma_decade_decode.simps comma_phase_classify_decade_control.simps
      comma_phase_rank_mask_unlift.simps)

lemma comma_phase_program_full_action_fold_fusion:
  "comma_semantic_phase_program_fold
      comma_phase_program_full_action_output phase program shift =
    comma_phase_program_full_action_output phase
      (comma_semantic_phase_program_round phase program shift)"
  by (rule comma_semantic_phase_program_fold_observer_fusion)

lemma comma_phase_program_full_action_exit_exact:
  "comma_phase_program_full_action_output phase
      (Comma_Round_Cross (comma_shift_position shift source)) =
    (case comma_shift_position shift source of
       Comma_Entry f delta x \<Rightarrow>
         if comma_decade_root_admitted (Comma_Entry f delta x) \<and>
             (phase+delta) mod 924 = (phase+1) mod 924
         then Comma_Phase_Rank_Mask_Continue (comma_offset_orbit x)
         else Comma_Phase_Rank_Mask_Invalid
     | Comma_Near f delta H \<Rightarrow> Comma_Phase_Rank_Mask_Invalid)"
  by (cases "comma_shift_position shift source")
     (simp_all add: comma_phase_program_full_action_output_def
       comma_phase_rank_mask_unlift.simps comma_decade_decode.simps
       comma_phase_classify_decade_control.simps split: if_splits)

definition comma_phase_program_full_action_step_output ::
    "nat \<Rightarrow> (comma_semantic_port_program \<Rightarrow> nat \<Rightarrow>
      comma_phase_rank_mask_action) \<Rightarrow> comma_phase_program_step \<Rightarrow>
      comma_phase_rank_mask_action" where
  "comma_phase_program_full_action_step_output phase recurse step =
    (case step of
       Comma_Program_Goto child child_shift \<Rightarrow> recurse child child_shift
     | Comma_Program_Exit position delta \<Rightarrow>
         comma_phase_program_full_action_output phase
           (Comma_Round_Cross (comma_shift_position delta position))
     | Comma_Program_Fork a delta \<Rightarrow>
         comma_phase_program_full_action_output phase (Comma_Round_Fork a delta)
     | Comma_Program_Landmine delta \<Rightarrow>
         comma_phase_program_full_action_output phase (Comma_Round_Landmine delta)
     | Comma_Program_Invalid \<Rightarrow>
         comma_phase_program_full_action_output phase Comma_Round_Invalid)"

lemma comma_phase_program_full_action_fold_step:
  "comma_semantic_phase_program_fold
      comma_phase_program_full_action_output phase program shift =
    comma_phase_program_full_action_step_output phase
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase)
      (comma_phase_program_step_at program phase shift)"
  unfolding comma_phase_program_full_action_step_output_def
  by (rule comma_semantic_phase_program_fold.simps)

definition comma_phase_program_full_action_of_source_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_source_continuation_action \<Rightarrow>
      comma_phase_rank_mask_action" where
  "comma_phase_program_full_action_of_source_action phase shift action =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            Some child \<Rightarrow>
              comma_semantic_phase_program_fold
                comma_phase_program_full_action_output phase child (shift+delta)
          | None \<Rightarrow> Comma_Phase_Rank_Mask_Invalid)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         comma_phase_program_full_action_output phase
           (Comma_Round_Cross (comma_shift_position (shift+delta) source))
     | Comma_Continuation_Fork a delta \<Rightarrow>
         comma_phase_program_full_action_output phase
           (Comma_Round_Fork a (shift+delta))
     | Comma_Continuation_Landmine delta \<Rightarrow>
         comma_phase_program_full_action_output phase
           (Comma_Round_Landmine (shift+delta))
     | Comma_Continuation_Invalid \<Rightarrow>
         comma_phase_program_full_action_output phase Comma_Round_Invalid)"

lemma comma_phase_program_full_action_source_step:
  "comma_phase_program_full_action_of_source_action phase shift action =
    comma_phase_program_full_action_step_output phase
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase)
      (comma_phase_program_step_of_action
        (comma_source_continuation_transport shift action))"
  by (cases action)
     (auto simp: comma_phase_program_full_action_of_source_action_def
       comma_phase_program_full_action_step_output_def
       comma_source_continuation_transport.simps
       comma_phase_program_step_of_action.simps
       comma_phase_program_full_action_terminal add.commute
       split: option.splits)

definition comma_phase_program_full_action_core_values_observer ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_phase_core_id \<Rightarrow>
      nat list \<Rightarrow> nat \<Rightarrow> comma_phase_rank_mask_action" where
  "comma_phase_program_full_action_core_values_observer
      phase f residue core xs shift =
    foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_phase_program_full_action_of_source_action phase shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
      else tail) xs Comma_Phase_Rank_Mask_Invalid"

lemma comma_phase_program_full_action_core_values_supported_filter:
  "comma_phase_program_full_action_core_values_observer
      phase f residue core values shift =
    comma_phase_program_full_action_core_values_observer
      phase f residue core
        (filter (\<lambda>wanted. comma_crt_supported
          (comma_core_value_guard core wanted)) values) shift"
proof -
  have inactive:
    "\<forall>wanted\<in>set values.
      \<not> comma_crt_supported (comma_core_value_guard core wanted) \<longrightarrow>
      \<not> comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)"
    using comma_core_value_guard_unsupported_no_eval by blast
  show ?thesis
    unfolding comma_phase_program_full_action_core_values_observer_def
    by (rule comma_foldr_if_filter[OF inactive])
qed

lemma comma_phase_program_full_action_core_values_supported_values:
  "comma_phase_program_full_action_core_values_observer
      phase f residue core [0..<comma_phase_core_modulus core] shift =
    comma_phase_program_full_action_core_values_observer
      phase f residue core (comma_core_supported_values core) shift"
  unfolding comma_core_supported_values_def
  by (rule comma_phase_program_full_action_core_values_supported_filter)

lemma comma_phase_program_full_action_core_values_cons:
  "comma_phase_program_full_action_core_values_observer phase f residue core
      (wanted#xs) shift =
    (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
     then comma_phase_program_full_action_of_source_action phase shift
       (comma_phase_program_entry_core_value_action f residue core wanted)
     else comma_phase_program_full_action_core_values_observer phase f residue
       core xs shift)"
  by (simp add: comma_phase_program_full_action_core_values_observer_def)

lemma comma_list_guarded_value_fold_cons:
  fixes xs :: "'a list" and selected :: "'a \<Rightarrow> 'b"
    and guard :: "'a \<Rightarrow> bool"
  shows "foldr (\<lambda>item tail. if guard item then selected item else tail)
      (head#xs) fallback =
    (if guard head then selected head
     else foldr (\<lambda>item tail. if guard item then selected item else tail)
       xs fallback)"
  by simp

lemma comma_list_guarded_value_fold_selected:
  fixes xs :: "'a list" and selected :: "'a \<Rightarrow> 'b"
    and guard :: "'a \<Rightarrow> bool"
  assumes unique:
      "(\<forall>x\<in>set xs. \<forall>y\<in>set xs. guard x \<longrightarrow> guard y \<longrightarrow> x=y)"
    and member: "chosen \<in> set xs"
    and selected_guard: "guard chosen"
  shows "foldr (\<lambda>item tail. if guard item then selected item else tail)
      xs fallback = selected chosen"
  using unique member selected_guard
proof (induction xs arbitrary: chosen)
  case Nil
  then show ?case by simp
next
  case (Cons item xs)
  have tail_unique:
    "(\<forall>x\<in>set xs. \<forall>y\<in>set xs. guard x \<longrightarrow> guard y \<longrightarrow> x=y)"
    using Cons.prems(1) by auto
  show ?case
  proof (cases "guard item")
    case True
    have item_member: "item \<in> set (item#xs)" by simp
    have chosen_member: "chosen \<in> set (item#xs)"
      using Cons.prems(2) by simp
    have same: "item=chosen"
      using Cons.prems(1) item_member chosen_member True Cons.prems(3)
      by blast
    show ?thesis using True same by simp
  next
    case False
    have chosen_tail: "chosen \<in> set xs"
      using Cons.prems(2) Cons.prems(3) False by auto
    have tail:
      "foldr (\<lambda>item tail. if guard item then selected item else tail)
        xs fallback = selected chosen"
      by (rule Cons.IH[OF tail_unique chosen_tail Cons.prems(3)])
    show ?thesis using False tail by simp
  qed
qed

lemma comma_phase_program_full_action_class_exact:
  assumes phase: "phase < 924"
    and cid: "cid < 46"
    and program:
      "comma_semantic_phase_program_for_class cid = Some program"
  shows "comma_phase_rank_mask_lift phase
      (comma_phase_program_full_action_output phase
        (comma_semantic_phase_program_round phase program 0)) =
      comma_semantic_phase_program_class_step phase cid"
proof -
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have step:
    "comma_semantic_phase_program_class_step phase cid =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_decode phase
          (comma_semantic_phase_program_round phase program 0))"
    using phase cid program
    by (simp add: comma_semantic_phase_program_class_step_def)
  have continue_clock:
    "\<And>q target. comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_decode phase
          (comma_semantic_phase_program_round phase program 0)) =
          Comma_Phase_Class_Continue q target
       \<Longrightarrow> q=(phase+1) mod 924"
  proof -
    fix q target
    assume action:
      "comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_decode phase
          (comma_semantic_phase_program_round phase program 0)) =
        Comma_Phase_Class_Continue q target"
    have "comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue q target"
      using step action by simp
    then show "q=(phase+1) mod 924"
      by (rule comma_semantic_phase_program_class_step_continue_closed(1)[OF valid])
  qed
  show ?thesis
    unfolding comma_phase_program_full_action_output_def
    using comma_phase_rank_mask_lift_unlift[OF continue_clock] step by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Core-value ordered selection fold and guard disjointness"
    @{thms comma_list_ex_guarded_select_foldr
      comma_foldr_if_filter
      comma_core_supported_values_def
      comma_core_value_guard_supported_iff_local_period
      comma_core_supported_values_local_period
      comma_phase_continue_core_values_observer_supported_filter
      comma_phase_continue_core_supported_values_observer
      comma_phase_continue_core_values_observer_foldr
      comma_phase_continue_core_values_observer_cons
      comma_phase_continue_core_values_guard_tail_disjoint
      comma_list_guarded_value_fold_cons
      comma_list_guarded_value_fold_selected
      comma_phase_rank_mask_unlift_lift
      comma_phase_rank_mask_lift_unlift
      comma_phase_program_full_action_terminal
      comma_phase_program_full_action_fold_fusion
      comma_phase_program_full_action_exit_exact
      comma_phase_program_full_action_fold_step
      comma_phase_program_full_action_source_step
      comma_phase_program_full_action_core_values_supported_filter
      comma_phase_program_full_action_core_values_cons
      comma_phase_program_full_action_core_values_supported_values
      comma_phase_program_full_action_class_exact};
\<close>

end
