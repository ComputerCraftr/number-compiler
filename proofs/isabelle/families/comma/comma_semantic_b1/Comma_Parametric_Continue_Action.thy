theory Comma_Parametric_Continue_Action
  imports Comma_Continue_Core_Fold
begin

text \<open>
The Continue projection of an Exit is a symbolic action of the accumulated
source shift.  Resolve that action only after composing the complete shift;
the phase clock is not substituted for this payload.
\<close>

definition comma_parametric_exit_continue_code ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_parametric_exit_continue_code source full_shift =
    (case comma_shift_position full_shift source of
       Comma_Entry f delta x \<Rightarrow>
         if comma_decade_root_admitted (Comma_Entry f delta x) \<and>
              delta mod 924 = 1
         then Suc (comma_offset_orbit x) else 0
     | Comma_Near f delta headroom \<Rightarrow> 0)"

lemma comma_parametric_exit_continue_code_exact:
  "comma_phase_continue_exit_target target source full_shift =
    (comma_parametric_exit_continue_code source full_shift = Suc target)"
  by (cases "comma_shift_position full_shift source")
    (auto simp: comma_phase_continue_exit_target_def
      comma_parametric_exit_continue_code_def)

lemma comma_parametric_exit_continue_code_range:
  "comma_parametric_exit_continue_code source full_shift = 0 \<or>
    (\<exists>target<46. comma_parametric_exit_continue_code source full_shift = Suc target)"
proof (cases "comma_shift_position full_shift source")
  case (Comma_Entry f delta x)
  then show ?thesis
    by (auto simp: comma_parametric_exit_continue_code_def
      comma_decade_root_admitted_def intro: comma_offset_orbit_bound)
next
  case (Comma_Near f delta headroom)
  then show ?thesis
    by (simp add: comma_parametric_exit_continue_code_def)
qed

lemma comma_parametric_exit_continue_code_target_bound:
  assumes emitted:
    "comma_parametric_exit_continue_code source full_shift = Suc target"
  shows "target<46"
proof -
  have exact:
    "comma_phase_continue_exit_target target source full_shift"
    using emitted comma_parametric_exit_continue_code_exact by blast
  then show ?thesis
    by (cases "comma_shift_position full_shift source")
      (auto simp: comma_phase_continue_exit_target_def
        intro: comma_offset_orbit_bound)
qed

text \<open>
The action step is the reusable substitution boundary for the output MDD.
Goto rows delegate to the already compiled child at the complete accumulated
shift.  Exit rows are evaluated locally from that same full shift.  Fork,
Landmine, and Invalid deliberately have no Continue target in this projection;
their full ordered action remains certified by the separate B32 action bridge.
\<close>

definition comma_parametric_continue_action_code ::
    "nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action \<Rightarrow>
      (comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "comma_parametric_continue_action_code parent full_shift action
      child_code =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            None \<Rightarrow> 0
          | Some child \<Rightarrow>
              if parent < comma_phase_program_sector child \<and>
                 comma_phase_program_sector child \<le> 9
              then child_code child (full_shift+delta) else 0)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         comma_parametric_exit_continue_code source (full_shift+delta)
     | _ \<Rightarrow> 0)"

lemma comma_parametric_continue_action_code_exact:
  assumes child_exact:
    "\<And>child child_shift target.
      (child_code child child_shift = Suc target) \<longleftrightarrow>
        comma_semantic_phase_program_continue_guard phase child
              child_shift target"
  shows "comma_parametric_continue_action_code parent full_shift
      action child_code = Suc target \<longleftrightarrow>
    comma_phase_continue_action_observer phase parent full_shift
        action target"
proof (cases action)
  case (Comma_Continuation_Goto source delta)
  then show ?thesis
    by (cases "comma_semantic_port_program_of_source source")
      (auto simp: comma_parametric_continue_action_code_def
        comma_phase_continue_action_observer_def child_exact)
next
  case (Comma_Continuation_Exit source delta)
  then show ?thesis
    using comma_parametric_exit_continue_code_exact[of target source
        "full_shift+delta"]
    by (auto simp: comma_parametric_continue_action_code_def
        comma_phase_continue_action_observer_def)
next
  case (Comma_Continuation_Fork target delta)
  then show ?thesis
    by (simp add: comma_parametric_continue_action_code_def
        comma_phase_continue_action_observer_def)
next
  case (Comma_Continuation_Landmine delta)
  then show ?thesis
    by (simp add: comma_parametric_continue_action_code_def
        comma_phase_continue_action_observer_def)
next
  case Comma_Continuation_Invalid
  then show ?thesis
    by (simp add: comma_parametric_continue_action_code_def
        comma_phase_continue_action_observer_def)
qed

lemma comma_parametric_continue_action_code_range:
  assumes child_range:
    "\<And>child child_shift. child_code child child_shift = 0 \<or>
      (\<exists>target<46. child_code child child_shift = Suc target)"
  shows
  "comma_parametric_continue_action_code parent full_shift action
      child_code = 0 \<or>
    (\<exists>target<46. comma_parametric_continue_action_code parent
      full_shift action child_code = Suc target)"
  using child_range
proof (cases action)
  case (Comma_Continuation_Goto source delta)
  then show ?thesis using child_range
    by (cases "comma_semantic_port_program_of_source source")
      (auto simp: comma_parametric_continue_action_code_def)
next
  case (Comma_Continuation_Exit source delta)
  then show ?thesis
    using comma_parametric_exit_continue_code_range[of source
      "full_shift+delta"]
    by (simp add: comma_parametric_continue_action_code_def)
next
  case (Comma_Continuation_Fork target delta)
  then show ?thesis by (simp add: comma_parametric_continue_action_code_def)
next
  case (Comma_Continuation_Landmine delta)
  then show ?thesis by (simp add: comma_parametric_continue_action_code_def)
next
  case Comma_Continuation_Invalid
  then show ?thesis by (simp add: comma_parametric_continue_action_code_def)
qed

text \<open>
Entry selector rows are an ordered list of guarded action codes.  The next
lemma is the structural fold checker used for that list: with the canonical
cyclotomic guards, at most one row is active, so the list fold is exactly the
Continue observer.  It is proved once for arbitrary rows and can be reused for
all program applications and target columns.
\<close>

lemma comma_parametric_guarded_code_fold_exact:
  fixes rows :: "'a list"
    and active selected :: "'a \<Rightarrow> bool"
    and code :: "'a \<Rightarrow> nat"
  assumes unique:
    "\<And>x y. x \<in> set rows \<Longrightarrow> y \<in> set rows \<Longrightarrow>
      active x \<Longrightarrow> active y \<Longrightarrow> x=y"
    and selected_exact:
      "\<And>x. x \<in> set rows \<Longrightarrow>
        (code x = Suc target) \<longleftrightarrow> selected x"
  shows "(foldr (\<lambda>x tail. if active x then code x else tail)
      rows 0 = Suc target) \<longleftrightarrow>
    list_ex (\<lambda>x. active x \<and> selected x) rows"
  using unique selected_exact
proof (induction rows)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  have tail_unique:
    "\<And>x y. x \<in> set tail \<Longrightarrow> y \<in> set tail \<Longrightarrow>
      active x \<Longrightarrow> active y \<Longrightarrow> x=y"
    using Cons.prems(1) by auto
  have tail_selected:
    "\<And>x. x \<in> set tail \<Longrightarrow>
      (code x = Suc target) \<longleftrightarrow> selected x"
    using Cons.prems(2) by auto
  have tail_exact:
    "(foldr (\<lambda>x tail. if active x then code x else tail)
      tail 0 = Suc target) \<longleftrightarrow>
      list_ex (\<lambda>x. active x \<and> selected x) tail"
    by (rule Cons.IH[OF tail_unique tail_selected])
  have head_selected:
    "(code head = Suc target) \<longleftrightarrow> selected head"
    using Cons.prems(2) by auto
  show ?case
  proof (cases "active head")
    case False
    then show ?thesis using tail_exact
      by (simp add: list_ex_Cons_iff)
  next
    case True
    have tail_active_eq:
      "\<And>x. x \<in> set tail \<Longrightarrow> active x \<Longrightarrow> x=head"
      using Cons.prems(1)[of head] True by auto
    have tail_selected_head:
      "list_ex (\<lambda>x. active x \<and> selected x) tail \<Longrightarrow>
        selected head"
    proof -
      assume exists: "list_ex (\<lambda>x. active x \<and> selected x) tail"
      then obtain x where x: "x \<in> set tail" "active x" "selected x"
        by (auto simp: list_ex_iff)
      have "x=head" by (rule tail_active_eq[OF x(1,2)])
      with x show "selected head" by simp
    qed
    show ?thesis using True head_selected tail_exact tail_selected_head
      by (auto simp: list_ex_Cons_iff)
  qed
qed

lemma comma_parametric_entry_selector_exact:
  assumes child_exact:
    "\<And>child child_shift target.
      (child_code child child_shift = Suc target) \<longleftrightarrow>
        comma_semantic_phase_program_continue_guard phase child
          child_shift target"
  shows "(foldr (\<lambda>wanted tail.
        if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
        then comma_parametric_continue_action_code f shift
          (comma_phase_program_entry_core_value_action f residue core wanted)
          child_code
        else tail)
      (comma_core_supported_values core) 0 = Suc target) \<longleftrightarrow>
    comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core
        (comma_core_supported_values core)) shift target"
proof -
  let ?rows = "comma_core_supported_values core"
  let ?active = "\<lambda>wanted. comma_crt_eval (phase+shift)
    (comma_core_value_guard core wanted)"
  let ?code = "\<lambda>wanted. comma_parametric_continue_action_code f shift
    (comma_phase_program_entry_core_value_action f residue core wanted)
    child_code"
  let ?selected = "\<lambda>wanted. comma_phase_continue_action_observer phase f
    shift (comma_phase_program_entry_core_value_action f residue core wanted)
    target"
  have unique:
    "\<And>x y. x \<in> set ?rows \<Longrightarrow> y \<in> set ?rows \<Longrightarrow>
      ?active x \<Longrightarrow> ?active y \<Longrightarrow> x=y"
    using comma_core_value_guard_unique by blast
  have selected_exact:
    "\<And>wanted. wanted \<in> set ?rows \<Longrightarrow>
      (?code wanted = Suc target) \<longleftrightarrow> ?selected wanted"
    using comma_parametric_continue_action_code_exact[OF child_exact] by simp
  have fold_exact:
    "(foldr (\<lambda>wanted tail. if ?active wanted then ?code wanted else tail)
      ?rows 0 = Suc target) \<longleftrightarrow>
      list_ex (\<lambda>wanted. ?active wanted \<and> ?selected wanted) ?rows"
    by (rule comma_parametric_guarded_code_fold_exact[OF unique selected_exact])
  show ?thesis
    using fold_exact
    by (simp only: comma_phase_continue_compile_job_observer.simps(2))
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Parametric Exit action preserves full accumulated source shift"
    @{thms comma_parametric_exit_continue_code_exact
      comma_parametric_exit_continue_code_range
      comma_parametric_exit_continue_code_target_bound
      comma_parametric_continue_action_code_exact
      comma_parametric_continue_action_code_range
      comma_parametric_guarded_code_fold_exact
      comma_parametric_entry_selector_exact}
\<close>

end
