theory Comma_Targeted_Continue_Guarded_Observer
  imports Comma_Targeted_Continue_Job_Observer
begin

text \<open>
Generic CRT laws for carrying an authenticated incoming phase restriction
through a demanded Continue observer.  The incoming column is an application argument;
it does not become part of the semantic program or job identity.  These laws
preserve the correlation between a source mask and each guarded child.
\<close>

lemma comma_crt_guarded_and_admitted:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and column: "comma_crt_admitted 0 column"
  shows "comma_crt_admitted 0
    (comma_crt_apply Comma_CRT_And incoming column)"
  by (rule comma_crt_apply_admitted[OF incoming column])

lemma comma_crt_guarded_and_eval:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and column: "comma_crt_admitted 0 column"
  shows "comma_crt_eval phase
      (comma_crt_apply Comma_CRT_And incoming column) =
    (comma_crt_eval phase incoming \<and> comma_crt_eval phase column)"
  using comma_crt_apply_refines_boolean[OF incoming column,
      where operation=Comma_CRT_And]
  by (simp add: comma_crt_boolean_value_def)

lemma comma_crt_guarded_and_supported_iff:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and column: "comma_crt_admitted 0 column"
  shows "comma_crt_supported
      (comma_crt_apply Comma_CRT_And incoming column) \<longleftrightarrow>
    (\<exists>phase<924. comma_crt_eval phase incoming \<and>
      comma_crt_eval phase column)"
proof -
  have result:
    "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And incoming column)"
    by (rule comma_crt_guarded_and_admitted[OF incoming column])
  have nonempty:
    "comma_crt_set (comma_crt_apply Comma_CRT_And incoming column) \<noteq> {} \<longleftrightarrow>
      comma_crt_supported
        (comma_crt_apply Comma_CRT_And incoming column)"
    by (rule comma_crt_supported_nonempty[OF result])
  have set_intersection:
    "comma_crt_set (comma_crt_apply Comma_CRT_And incoming column) =
      comma_crt_set incoming \<inter> comma_crt_set column"
    by (rule comma_crt_apply_and_set[OF incoming column])
  show ?thesis
    using nonempty set_intersection
    by (auto simp: comma_crt_set_def)
qed

lemma comma_crt_guarded_and_empty_no_phase:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and column: "comma_crt_admitted 0 column"
    and empty:
      "\<not> comma_crt_supported
        (comma_crt_apply Comma_CRT_And incoming column)"
  shows "\<forall>phase<924.
    \<not> (comma_crt_eval phase incoming \<and> comma_crt_eval phase column)"
  using comma_crt_guarded_and_supported_iff[OF incoming column] empty
  by blast

lemma comma_crt_guarded_and_empty_equiv_false:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and column: "comma_crt_admitted 0 column"
    and empty: "\<not> comma_crt_supported incoming"
  shows "comma_crt_equiv_check
    (comma_crt_apply Comma_CRT_And incoming column)
    (Comma_CRT_Bool False)"
proof (rule comma_crt_equiv_check_complete)
  show "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And incoming column)"
    by (rule comma_crt_guarded_and_admitted[OF incoming column])
  show "comma_crt_admitted 0 (Comma_CRT_Bool False)"
    by simp
  have incoming_empty: "comma_crt_set incoming = {}"
    using comma_crt_supported_nonempty[OF incoming] empty by blast
  have conjunction_empty:
    "comma_crt_set (comma_crt_apply Comma_CRT_And incoming column) = {}"
    using comma_crt_apply_and_set[OF incoming column] incoming_empty by simp
  show "comma_crt_set (comma_crt_apply Comma_CRT_And incoming column) =
      comma_crt_set (Comma_CRT_Bool False)"
    using conjunction_empty by (simp add: comma_crt_set_def)
qed

lemma comma_crt_equiv_check_sym:
  assumes "comma_crt_equiv_check left right"
  shows "comma_crt_equiv_check right left"
  using assms by (auto simp only: comma_crt_equiv_check_iff)

lemma comma_crt_guarded_true_equiv:
  assumes column: "comma_crt_admitted 0 column"
  shows "comma_crt_equiv_check
    (comma_crt_apply Comma_CRT_And (Comma_CRT_Bool True) column)
    column"
proof (rule comma_crt_equiv_check_complete)
  have true_admitted: "comma_crt_admitted 0 (Comma_CRT_Bool True)"
    by simp
  show "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And (Comma_CRT_Bool True) column)"
    by (rule comma_crt_apply_admitted[OF true_admitted column])
  show "comma_crt_admitted 0 column" by (rule column)
  have applied_set:
    "comma_crt_set
      (comma_crt_apply Comma_CRT_And (Comma_CRT_Bool True) column) =
      comma_crt_set (Comma_CRT_Bool True) \<inter> comma_crt_set column"
    by (rule comma_crt_apply_and_set[OF true_admitted column])
  show "comma_crt_set
      (comma_crt_apply Comma_CRT_And (Comma_CRT_Bool True) column) =
      comma_crt_set column"
    unfolding applied_set
    by (auto simp: comma_crt_set_def)
qed

lemma comma_crt_guarded_core_step_equiv:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and guard: "comma_crt_admitted 0 guard"
    and action: "comma_crt_admitted 0 action"
    and rest: "comma_crt_admitted 0 rest"
  shows "comma_crt_equiv_check
    (comma_crt_apply Comma_CRT_And incoming
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And guard action) rest))
    (comma_crt_apply Comma_CRT_Or
      (comma_crt_apply Comma_CRT_And
        (comma_crt_apply Comma_CRT_And incoming guard) action)
      (comma_crt_apply Comma_CRT_And incoming rest))"
proof (rule comma_crt_equiv_check_complete)
  have guarded_action:
    "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And guard action)"
    by (rule comma_crt_apply_admitted[OF guard action])
  have masked_rest:
    "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And incoming rest)"
    by (rule comma_crt_apply_admitted[OF incoming rest])
  have left_union:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And guard action) rest)"
    by (rule comma_crt_apply_admitted[OF guarded_action rest])
  have masked_guard:
    "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And incoming guard)"
    by (rule comma_crt_apply_admitted[OF incoming guard])
  have masked_guarded_action:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And
        (comma_crt_apply Comma_CRT_And incoming guard) action)"
    by (rule comma_crt_apply_admitted[OF masked_guard action])
  have right_union:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And
          (comma_crt_apply Comma_CRT_And incoming guard) action)
        (comma_crt_apply Comma_CRT_And incoming rest))"
    by (rule comma_crt_apply_admitted[OF masked_guarded_action masked_rest])
  show "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And incoming
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And guard action) rest))"
    by (rule comma_crt_apply_admitted[OF incoming left_union])
  show "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And
          (comma_crt_apply Comma_CRT_And incoming guard) action)
        (comma_crt_apply Comma_CRT_And incoming rest))"
    by (rule right_union)
  show "comma_crt_set
      (comma_crt_apply Comma_CRT_And incoming
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And guard action) rest)) =
      comma_crt_set
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And
            (comma_crt_apply Comma_CRT_And incoming guard) action)
          (comma_crt_apply Comma_CRT_And incoming rest))"
  proof -
    have left_set:
      "comma_crt_set
          (comma_crt_apply Comma_CRT_And incoming
            (comma_crt_apply Comma_CRT_Or
              (comma_crt_apply Comma_CRT_And guard action) rest)) =
        comma_crt_set incoming \<inter>
          ((comma_crt_set guard \<inter> comma_crt_set action) \<union>
            comma_crt_set rest)"
      by (simp only:
        comma_crt_apply_and_set[OF incoming left_union]
        comma_crt_apply_or_set[OF guarded_action rest]
        comma_crt_apply_and_set[OF guard action])
    have right_set:
      "comma_crt_set
          (comma_crt_apply Comma_CRT_Or
            (comma_crt_apply Comma_CRT_And
              (comma_crt_apply Comma_CRT_And incoming guard) action)
            (comma_crt_apply Comma_CRT_And incoming rest)) =
        ((comma_crt_set incoming \<inter> comma_crt_set guard) \<inter>
          comma_crt_set action) \<union>
            (comma_crt_set incoming \<inter> comma_crt_set rest)"
      by (simp only:
        comma_crt_apply_or_set[OF masked_guarded_action masked_rest]
        comma_crt_apply_and_set[OF masked_guard action]
        comma_crt_apply_and_set[OF incoming guard]
        comma_crt_apply_and_set[OF incoming rest])
    show ?thesis
      using left_set right_set by (auto simp: Int_assoc)
  qed
qed

lemma comma_crt_mask_pullback_one_tick_eval:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and suffix: "comma_crt_admitted 0 suffix"
  shows "comma_crt_eval phase
      (comma_crt_shift 1
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift 923 incoming) suffix)) =
    (comma_crt_eval phase incoming \<and>
      comma_crt_eval (phase+1) suffix)"
proof -
  have backward_mask:
    "comma_crt_admitted 0 (comma_crt_shift 923 incoming)"
    by (rule comma_crt_shift_admitted[OF incoming])
  have combined:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And
        (comma_crt_shift 923 incoming) suffix)"
    by (rule comma_crt_guarded_and_admitted[OF backward_mask suffix])
  have phase_period:
    "comma_crt_eval (phase+1+923) incoming = comma_crt_eval phase incoming"
  proof -
    have residues: "(phase+924) mod 924=phase mod 924" by simp
    have reduced_phase:
      "comma_crt_eval (phase mod 924) incoming=comma_crt_eval phase incoming"
      by (rule comma_crt_eval_periodic[OF incoming])
    have reduced_next:
      "comma_crt_eval ((phase+924) mod 924) incoming=
        comma_crt_eval (phase+924) incoming"
      by (rule comma_crt_eval_periodic[OF incoming])
    have next_period:
      "comma_crt_eval (phase+924) incoming=comma_crt_eval phase incoming"
    proof -
      have "comma_crt_eval (phase+924) incoming =
          comma_crt_eval ((phase+924) mod 924) incoming"
        by (rule sym[OF reduced_next])
      also have "... = comma_crt_eval (phase mod 924) incoming"
        by (simp only: residues)
      also have "... = comma_crt_eval phase incoming"
        by (rule reduced_phase)
      finally show ?thesis .
    qed
    have offset_period: "phase+1+923=phase+924" by arith
    show ?thesis by (simp only: offset_period next_period)
  qed
  have shifted_outer:
    "comma_crt_eval phase
        (comma_crt_shift 1
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift 923 incoming) suffix)) =
      comma_crt_eval (phase+1)
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift 923 incoming) suffix)"
    by (rule comma_crt_shift_refines[OF combined])
  have inner_shift:
    "comma_crt_eval (phase+1) (comma_crt_shift 923 incoming) =
      comma_crt_eval phase incoming"
    by (rule trans[OF comma_crt_shift_refines[OF incoming] phase_period])
  show ?thesis
    by (simp only: shifted_outer
      comma_crt_guarded_and_eval[OF backward_mask suffix] inner_shift)
qed

lemma comma_crt_mask_pullback_one_tick_equiv:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and suffix: "comma_crt_admitted 0 suffix"
  shows "comma_crt_equiv_check
    (comma_crt_shift 1
      (comma_crt_apply Comma_CRT_And
        (comma_crt_shift 923 incoming) suffix))
    (comma_crt_apply Comma_CRT_And incoming
      (comma_crt_shift 1 suffix))"
proof (rule comma_crt_equiv_check_complete)
  have backward_mask:
    "comma_crt_admitted 0 (comma_crt_shift 923 incoming)"
    by (rule comma_crt_shift_admitted[OF incoming])
  have combined:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And
        (comma_crt_shift 923 incoming) suffix)"
    by (rule comma_crt_guarded_and_admitted[OF backward_mask suffix])
  show "comma_crt_admitted 0
      (comma_crt_shift 1
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift 923 incoming) suffix))"
    by (rule comma_crt_shift_admitted[OF combined])
  have shifted_suffix:
    "comma_crt_admitted 0 (comma_crt_shift 1 suffix)"
    by (rule comma_crt_shift_admitted[OF suffix])
  show "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And incoming
        (comma_crt_shift 1 suffix))"
    by (rule comma_crt_guarded_and_admitted[OF incoming shifted_suffix])
  have left_eval:
    "comma_crt_eval phase
        (comma_crt_shift 1
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift 923 incoming) suffix)) =
      (comma_crt_eval phase incoming \<and>
        comma_crt_eval (phase+1) suffix)" for phase
    by (rule comma_crt_mask_pullback_one_tick_eval[OF incoming suffix])
  have right_eval:
    "comma_crt_eval phase
        (comma_crt_apply Comma_CRT_And incoming
          (comma_crt_shift 1 suffix)) =
      (comma_crt_eval phase incoming \<and>
        comma_crt_eval (phase+1) suffix)" for phase
  proof -
    have shift_eval:
      "comma_crt_eval phase (comma_crt_shift 1 suffix) =
        comma_crt_eval (phase+1) suffix"
      by (rule comma_crt_shift_refines[OF suffix])
    show ?thesis
      by (simp only: comma_crt_guarded_and_eval[OF incoming shifted_suffix]
        shift_eval)
  qed
  show "comma_crt_set
      (comma_crt_shift 1
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift 923 incoming) suffix)) =
      comma_crt_set
        (comma_crt_apply Comma_CRT_And incoming
          (comma_crt_shift 1 suffix))"
  proof (rule set_eqI)
    fix phase
    show "phase \<in> comma_crt_set
        (comma_crt_shift 1
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift 923 incoming) suffix)) \<longleftrightarrow>
      phase \<in> comma_crt_set
        (comma_crt_apply Comma_CRT_And incoming
          (comma_crt_shift 1 suffix))"
      by (simp only: comma_crt_set_def mem_Collect_eq left_eval right_eval)
  qed
qed

fun comma_continue_core_guard_union ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> comma_crt_column"
where
  "comma_continue_core_guard_union core amount [] = Comma_CRT_Bool False"
| "comma_continue_core_guard_union core amount (wanted#remaining) =
    comma_crt_apply Comma_CRT_Or
      (comma_crt_shift amount (comma_core_value_guard core wanted))
      (comma_continue_core_guard_union core amount remaining)"

lemma comma_continue_core_guard_union_admitted:
  "comma_crt_admitted 0
    (comma_continue_core_guard_union core amount values)"
proof (induction "values")
  case Nil
  then show ?case by simp
next
  case (Cons wanted remaining)
  have guard:
    "comma_crt_admitted 0 (comma_core_value_guard core wanted)"
    by (rule comma_core_value_guard_admitted)
  have shifted:
    "comma_crt_admitted 0
      (comma_crt_shift amount (comma_core_value_guard core wanted))"
    by (rule comma_crt_shift_admitted[OF guard])
  have tail:
    "comma_crt_admitted 0
      (comma_continue_core_guard_union core amount remaining)"
    by (rule Cons.IH)
  show ?case
    by (simp only: comma_continue_core_guard_union.simps
        comma_crt_apply_admitted[OF shifted tail])
qed

lemma comma_continue_core_guard_union_eval:
  "comma_crt_eval phase
      (comma_continue_core_guard_union core amount values) =
    (\<exists>wanted\<in>set values.
      comma_crt_eval (phase+amount)
        (comma_core_value_guard core wanted))"
proof (induction "values")
  case Nil
  then show ?case by simp
next
  case (Cons wanted remaining)
  have guard:
    "comma_crt_admitted 0 (comma_core_value_guard core wanted)"
    by (rule comma_core_value_guard_admitted)
  have shifted:
    "comma_crt_admitted 0
      (comma_crt_shift amount (comma_core_value_guard core wanted))"
    by (rule comma_crt_shift_admitted[OF guard])
  have tail:
    "comma_crt_admitted 0
      (comma_continue_core_guard_union core amount remaining)"
    by (rule comma_continue_core_guard_union_admitted)
  have shifted_eval:
    "comma_crt_eval phase
      (comma_crt_shift amount (comma_core_value_guard core wanted)) =
      comma_crt_eval (phase+amount) (comma_core_value_guard core wanted)"
    by (rule comma_crt_shift_refines[OF guard])
  have union_eval:
    "comma_crt_eval phase
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_shift amount (comma_core_value_guard core wanted))
        (comma_continue_core_guard_union core amount remaining)) =
      (comma_crt_eval phase
        (comma_crt_shift amount (comma_core_value_guard core wanted)) \<or>
       comma_crt_eval phase
        (comma_continue_core_guard_union core amount remaining))"
    using comma_crt_apply_refines_boolean[OF shifted tail,
        where operation=Comma_CRT_Or]
    by (simp add: comma_crt_boolean_value_def)
  show ?case
    using Cons.IH shifted_eval union_eval
    by (simp add: comma_continue_core_guard_union.simps)
qed

lemma comma_continue_core_guard_union_covers_mask:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and coverage:
      "comma_crt_equiv_check
        (comma_crt_apply Comma_CRT_And incoming
          (comma_continue_core_guard_union core amount allowed)) incoming"
    and phase_bound: "phase<924"
    and selected: "comma_crt_eval phase incoming"
  shows "\<exists>wanted\<in>set allowed.
    comma_crt_eval (phase+amount)
      (comma_core_value_guard core wanted)"
proof -
  have union:
    "comma_crt_admitted 0
      (comma_continue_core_guard_union core amount allowed)"
    by (rule comma_continue_core_guard_union_admitted)
  have combined:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And incoming
        (comma_continue_core_guard_union core amount allowed))"
    by (rule comma_crt_apply_admitted[OF incoming union])
  have equal_sets:
    "comma_crt_set
      (comma_crt_apply Comma_CRT_And incoming
        (comma_continue_core_guard_union core amount allowed)) =
      comma_crt_set incoming"
    using coverage comma_crt_equiv_check_iff[of
      "comma_crt_apply Comma_CRT_And incoming
        (comma_continue_core_guard_union core amount allowed)" incoming]
      combined incoming
    by blast
  have in_incoming: "phase\<in>comma_crt_set incoming"
    using phase_bound selected by (simp add: comma_crt_set_def)
  have in_combined:
    "phase\<in>comma_crt_set
      (comma_crt_apply Comma_CRT_And incoming
        (comma_continue_core_guard_union core amount allowed))"
    using equal_sets in_incoming by simp
  have selected_intersection:
    "comma_crt_eval phase incoming \<and>
      comma_crt_eval phase
        (comma_continue_core_guard_union core amount allowed)"
    using comma_crt_guarded_and_eval[OF incoming union, of phase]
      in_combined phase_bound
    by (auto simp: comma_crt_set_def)
  then show ?thesis
    using comma_continue_core_guard_union_eval[of phase core amount allowed]
    by blast
qed

lemma comma_continue_core_guard_unselected_no_eval:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and coverage:
      "comma_crt_equiv_check
        (comma_crt_apply Comma_CRT_And incoming
          (comma_continue_core_guard_union core amount allowed)) incoming"
    and phase_bound: "phase<924"
    and selected: "comma_crt_eval phase incoming"
    and omitted: "wanted\<notin>set allowed"
  shows "\<not> comma_crt_eval (phase+amount)
    (comma_core_value_guard core wanted)"
proof
  assume selected_guard:
    "comma_crt_eval (phase+amount)
      (comma_core_value_guard core wanted)"
  obtain allowed_value where
    allowed_value: "allowed_value\<in>set allowed"
      "comma_crt_eval (phase+amount)
        (comma_core_value_guard core allowed_value)"
    using comma_continue_core_guard_union_covers_mask
      [OF incoming coverage phase_bound selected]
    by blast
  have "wanted=allowed_value"
    by (rule comma_core_value_guard_unique[OF selected_guard allowed_value(2)])
  with omitted allowed_value(1) show False by blast
qed

lemma comma_continue_core_values_observer_filter:
  assumes incoming: "comma_crt_admitted 0 incoming"
    and coverage:
      "comma_crt_equiv_check
        (comma_crt_apply Comma_CRT_And incoming
          (comma_continue_core_guard_union core (clock+shift) allowed)) incoming"
    and phase_bound: "phase<924"
    and selected: "comma_crt_eval phase incoming"
  shows "comma_phase_continue_compile_job_observer (phase+clock)
      (Comma_Continue_Core_Values_Job f residue core values) shift target =
    comma_phase_continue_compile_job_observer (phase+clock)
      (Comma_Continue_Core_Values_Job f residue core
        (filter (\<lambda>wanted. wanted\<in>set allowed) values))
      shift target"
proof -
  have no_omitted:
    "wanted\<in>set values \<Longrightarrow> wanted\<notin>set allowed \<Longrightarrow>
      \<not>comma_crt_eval ((phase+clock)+shift)
        (comma_core_value_guard core wanted)" for wanted
    using comma_continue_core_guard_unselected_no_eval
      [OF incoming coverage phase_bound selected]
    by (simp add: add.assoc)
  show ?thesis
    using no_omitted
    by (auto simp: comma_phase_continue_compile_job_observer.simps
        list_ex_iff)
qed

lemma comma_continue_job_observe_masked_core_values_filter:
  assumes observer: "comma_continue_observer_admitted observer"
    and incoming: "comma_crt_admitted 0 incoming"
    and coverage:
      "comma_crt_equiv_check
        (comma_crt_apply Comma_CRT_And incoming
          (comma_continue_core_guard_union core (clock+shift) allowed)) incoming"
  shows "comma_crt_equiv_check
    (comma_crt_apply Comma_CRT_And incoming
      (comma_continue_job_observe observer
        (Comma_Continue_Core_Values_Job f residue core values) shift clock))
    (comma_crt_apply Comma_CRT_And incoming
      (comma_continue_job_observe observer
        (Comma_Continue_Core_Values_Job f residue core
          (filter (\<lambda>wanted. wanted\<in>set allowed) values))
        shift clock))"
proof -
  let ?full = "comma_continue_job_observe observer
    (Comma_Continue_Core_Values_Job f residue core values) shift clock"
  let ?filtered = "comma_continue_job_observe observer
    (Comma_Continue_Core_Values_Job f residue core
      (filter (\<lambda>wanted. wanted\<in>set allowed) values)) shift clock"
  have full: "comma_crt_admitted 0 ?full"
    by (rule comma_continue_job_observe_admitted[OF observer])
  have filtered: "comma_crt_admitted 0 ?filtered"
    by (rule comma_continue_job_observe_admitted[OF observer])
  have selected_equal: "comma_crt_eval phase ?full = comma_crt_eval phase ?filtered"
    if bound: "phase<924" and selected: "comma_crt_eval phase incoming" for phase
  proof -
    have rows:
      "comma_phase_continue_compile_job_observer (phase+clock)
        (Comma_Continue_Core_Values_Job f residue core values) shift target =
       comma_phase_continue_compile_job_observer (phase+clock)
        (Comma_Continue_Core_Values_Job f residue core
          (filter (\<lambda>wanted. wanted\<in>set allowed) values))
        shift target" for target
      by (rule comma_continue_core_values_observer_filter
          [OF incoming coverage bound selected])
    show ?thesis
      by (simp only: comma_continue_job_observe_exact[OF observer] rows)
  qed
  show ?thesis
  proof (rule comma_crt_equiv_check_complete)
    show "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And incoming ?full)"
      by (rule comma_crt_apply_admitted[OF incoming full])
    show "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And incoming ?filtered)"
      by (rule comma_crt_apply_admitted[OF incoming filtered])
    show "comma_crt_set (comma_crt_apply Comma_CRT_And incoming ?full) =
        comma_crt_set (comma_crt_apply Comma_CRT_And incoming ?filtered)"
      using selected_equal comma_crt_guarded_and_eval[OF incoming full]
        comma_crt_guarded_and_eval[OF incoming filtered]
      by (auto simp: comma_crt_set_def)
  qed
qed

ML \<open>
  val published = @{thms comma_crt_guarded_and_admitted
    comma_crt_guarded_and_eval comma_crt_guarded_and_supported_iff
    comma_crt_guarded_and_empty_no_phase comma_crt_guarded_and_empty_equiv_false
    comma_crt_equiv_check_sym comma_crt_guarded_true_equiv
    comma_crt_guarded_core_step_equiv
    comma_crt_mask_pullback_one_tick_eval
    comma_crt_mask_pullback_one_tick_equiv
    comma_continue_core_guard_union_admitted
    comma_continue_core_guard_union_eval
    comma_continue_core_guard_union_covers_mask
    comma_continue_core_guard_unselected_no_eval
    comma_continue_core_values_observer_filter
    comma_continue_job_observe_masked_core_values_filter}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "guarded Continue observer CRT laws" published
\<close>

end
