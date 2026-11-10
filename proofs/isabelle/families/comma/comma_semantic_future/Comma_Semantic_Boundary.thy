theory Comma_Semantic_Boundary
  imports Comma_Semantic_Path Comma_Semantic_B1_Future_Bridge
begin

text \<open>
The boundary action below consumes an exact decade-summary provider.  It
keeps the decade height as occurrence data: a direct event advances by its
round delta, while a crossing uses the exact summary at the rebased decade
and advances by the crossing delta plus that summary height.  The child list
is the existing ordered literal boundary list, so the provider does not
replace or weaken the branching relation.
\<close>

definition comma_semantic_decade_provider_exact ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow> bool"
where
  "comma_semantic_decade_provider_exact provider \<longleftrightarrow>
    (\<forall>s. comma_decade_admitted s \<longrightarrow>
      (case provider s of None \<Rightarrow> False
       | Some (h,terminal) \<Rightarrow>
           h\<le>26 \<and> comma_decade_exact_summary s h terminal))"

fun comma_semantic_boundary_event_outcome ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow>
   nat \<Rightarrow> comma_round_result \<Rightarrow> comma_finite_outcome option"
where
  "comma_semantic_boundary_event_outcome provider r (Comma_Round_Fork a d) =
    Some (Comma_Fork_At a d)"
| "comma_semantic_boundary_event_outcome provider r (Comma_Round_Landmine d) =
    Some (Comma_Landmine_At d)"
| "comma_semantic_boundary_event_outcome provider r
      (Comma_Round_Cross (Comma_Entry f d x)) =
    (if f=1 \<and> x\<le>90 then
      (case provider (Comma_Decade ((r+d) mod 924) x) of
        None \<Rightarrow> None
      | Some (h,terminal) \<Rightarrow>
          Some (comma_summary_outcome (h+d) terminal))
     else None)"
| "comma_semantic_boundary_event_outcome provider r
      (Comma_Round_Cross (Comma_Near f d h)) = None"
| "comma_semantic_boundary_event_outcome provider r Comma_Round_Invalid = None"

definition comma_semantic_boundary_step ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_finite_outcome option"
where
  "comma_semantic_boundary_step provider q =
    (case q of (kind,a,r) \<Rightarrow>
      if comma_boundary_valid q then
        (case comma_round_close r (comma_finite_initial q) of
          (n,terminal,event) \<Rightarrow>
            comma_semantic_boundary_event_outcome provider r event)
      else None)"

fun comma_semantic_boundary_control_of ::
  "comma_finite_outcome \<Rightarrow> comma_future_control"
where
  "comma_semantic_boundary_control_of (Comma_Fork_At a d) =
    Comma_Future_Fork a"
| "comma_semantic_boundary_control_of (Comma_Landmine_At d) =
    Comma_Future_Landmine"

text \<open>The terminal index is a pure projection of the boundary control,
shared by the summary and weighted-action consumers.\<close>

fun comma_semantic_future_action_terminal_position ::
    "comma_future_control \<Rightarrow> nat" where
  "comma_semantic_future_action_terminal_position (Comma_Future_Fork a) = a - 2"
| "comma_semantic_future_action_terminal_position Comma_Future_Landmine = 8"

definition comma_semantic_boundary_control_step ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_future_control option"
where
  "comma_semantic_boundary_control_step provider q =
    map_option comma_semantic_boundary_control_of
      (comma_semantic_boundary_step provider q)"

definition comma_semantic_boundary_exponent_delta ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_future_control \<Rightarrow> nat"
where
  "comma_semantic_boundary_exponent_delta provider q control =
    (case comma_semantic_boundary_step provider q of
      None \<Rightarrow> 0
    | Some outcome \<Rightarrow>
        if control = comma_semantic_boundary_control_of outcome
        then comma_native_outcome_delta outcome else 0)"

definition comma_semantic_boundary_children ::
  "(comma_decade_state \<Rightarrow> comma_decade_residual option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_future_control \<Rightarrow>
   comma_boundary_state list"
where
  "comma_semantic_boundary_children provider q control =
    (case comma_semantic_boundary_step provider q of
      None \<Rightarrow> []
    | Some outcome \<Rightarrow>
        if control = comma_semantic_boundary_control_of outcome
        then comma_native_boundary_children q outcome else [])"

lemma comma_semantic_boundary_step_direct_fork:
  "comma_semantic_boundary_event_outcome provider r (Comma_Round_Fork a d) =
    Some (Comma_Fork_At a d)"
  by simp

lemma comma_semantic_boundary_step_direct_landmine:
  "comma_semantic_boundary_event_outcome provider r (Comma_Round_Landmine d) =
    Some (Comma_Landmine_At d)"
  by simp

lemma comma_semantic_boundary_rejects_noncanonical_crossing:
  "comma_semantic_boundary_event_outcome provider r
      (Comma_Round_Cross (Comma_Entry 1 d 98))=None"
  by simp

lemma comma_semantic_decade_provider_lookup:
  assumes provider: "comma_semantic_decade_provider_exact provider"
    and valid: "comma_decade_admitted s"
  obtains h terminal where
    "provider s=Some (h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary s h terminal"
proof -
  have selected:
    "(case provider s of None \<Rightarrow> False
      | Some (h,terminal) \<Rightarrow>
          h\<le>26 \<and> comma_decade_exact_summary s h terminal)"
    using provider valid
    by (simp only: comma_semantic_decade_provider_exact_def)
  obtain h terminal where
    answer: "provider s=Some (h,terminal)"
    and height: "h\<le>26"
    and exact: "comma_decade_exact_summary s h terminal"
    using selected by (cases "provider s") (auto split: prod.splits)
  show thesis by (rule that[OF answer height exact])
qed

text \<open>A crossing consumes its round delta before the decade summary
starts. The summary therefore begins at exponent @{term "p+d+1"} and ends at
@{term "p+d+1+h"}; the exact residual height @{term h} remains the suffix
weight. This bridge is independent of how the summary provider is built.\<close>

theorem comma_semantic_boundary_crossing_suffix:
  assumes provider: "comma_semantic_decade_provider_exact provider"
    and close:
      "comma_round_close r source=(n,terminal,Comma_Round_Cross target)"
    and source_valid: "comma_round_admitted source"
    and source_delta: "comma_round_delta source=d"
    and target_shape: "target=Comma_Entry 1 (Suc d) x"
    and offset: "x\<le>90"
    and phase: "r mod 924=p mod 924"
    and exponent: "5\<le>p"
  obtains h tau prefix_weight suffix_weight t where
    "provider (Comma_Decade ((r+d+1) mod 924) x)=Some (h,tau)"
    "h\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade ((r+d+1) mod 924) x) h tau"
    "comma_unique_literal_path (Suc prefix_weight+suffix_weight)
      (comma_chart_value p source)
      (comma_chart_value (p+d+1+h) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+d+1+h) mod 924) t=comma_summary_terminal_move tau"
proof -
  have summary_source:
    "comma_decade_admitted (Comma_Decade ((r+d+1) mod 924) x)"
    using offset by simp
  obtain h tau where selected:
      "provider (Comma_Decade ((r+d+1) mod 924) x)=Some (h,tau)"
    and height: "h\<le>26"
    and exact:
      "comma_decade_exact_summary
        (Comma_Decade ((r+d+1) mod 924) x) h tau"
    by (rule comma_semantic_decade_provider_lookup[OF provider summary_source])
  have start_rebase:
    "comma_chart_value p target=
      comma_chart_value (p+d+1) (Comma_Entry 1 0 x)"
    using target_shape by (simp add: comma_chart_value_def)
  have phase_rebase:
    "((r+d+1) mod 924)=((p+d+1) mod 924)"
  proof -
    have shifted:
      "((r mod 924)+(d+1)) mod 924 =
        ((p mod 924)+(d+1)) mod 924"
      using phase by (rule arg_cong)
    have r_rebase: "((r+d+1) mod 924)=((r mod 924)+(d+1)) mod 924"
      by (simp only: add.assoc; rule mod_add_left_eq[symmetric])
    have p_rebase: "((p+d+1) mod 924)=((p mod 924)+(d+1)) mod 924"
      by (simp only: add.assoc; rule mod_add_left_eq[symmetric])
    show ?thesis using r_rebase p_rebase shifted by simp
  qed
  have summary_binding:
    "Comma_Decade ((r+d+1) mod 924) x=
      Comma_Decade ((p+d+1) mod 924) x"
    using phase_rebase by simp
  have resumed_exponent: "5\<le>p+d+1" using exponent by arith
  obtain suffix_weight t where suffix:
      "comma_unique_literal_path suffix_weight
        (comma_chart_value (p+d+1) (Comma_Entry 1 0 x))
        (comma_chart_value (p+d+1+h) t)"
    and terminal_valid: "comma_round_admitted t"
    and terminal_zero: "comma_round_delta t=0"
    and terminal_move:
      "comma_finite_step ((p+d+1+h) mod 924) t=
        comma_summary_terminal_move tau"
    using comma_decade_summary_unique_occurrence_exists
      [OF exact summary_source resumed_exponent summary_binding] by blast
  obtain prefix_weight where prefix:
      "comma_unique_literal_path (Suc prefix_weight)
        (comma_chart_value p source) (comma_chart_value p target)"
    by (rule comma_round_crossing_unique_literal_prefix
      [OF close phase exponent source_valid])
  have rebased_prefix:
    "comma_unique_literal_path (Suc prefix_weight)
      (comma_chart_value p source)
      (comma_chart_value (p+d+1) (Comma_Entry 1 0 x))"
    using prefix start_rebase by simp
  have joined:
    "comma_unique_literal_path (Suc prefix_weight+suffix_weight)
      (comma_chart_value p source) (comma_chart_value (p+d+1+h) t)"
    by (rule comma_unique_literal_path_append[OF rebased_prefix suffix])
  show thesis
    by (rule that[OF selected height exact joined terminal_valid terminal_zero terminal_move])
qed

lemma comma_semantic_boundary_fork_children_admitted:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and digit: "2\<le>a" "a\<le>9"
  shows "distinct (comma_native_boundary_children q (Comma_Fork_At a d))"
    "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      comma_boundary_valid child \<and>
      5\<le>p+d \<and> (p+d) mod 924=snd (snd child)"
proof -
  obtain kind source_a r where q: "q=(kind,source_a,r)"
    by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have phase_r: "p mod 924=r" using phase q by simp
  have r_mod: "r mod 924=r" using r_bound by simp
  have phase_mod: "p mod 924=r mod 924"
    using phase_r r_mod by simp
  have phase_child: "(p+d) mod 924=(r+d) mod 924"
  proof -
    have shifted:
      "((p mod 924)+d) mod 924=((r mod 924)+d) mod 924"
      using phase_mod by (rule arg_cong)
    have p_rebase: "(p+d) mod 924=((p mod 924)+d) mod 924"
      by (rule mod_add_left_eq[symmetric])
    have r_rebase: "(r+d) mod 924=((r mod 924)+d) mod 924"
      by (rule mod_add_left_eq[symmetric])
    show ?thesis using p_rebase r_rebase shifted by simp
  qed
  show "distinct (comma_native_boundary_children q (Comma_Fork_At a d))"
    by (simp add: q comma_native_boundary_children_def)
  show "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      comma_boundary_valid child \<and>
      5\<le>p+d \<and> (p+d) mod 924=snd (snd child)"
    using valid exponent phase_child digit
    by (auto simp: q comma_native_boundary_children_def
      comma_boundary_valid_def)
qed

lemma comma_semantic_boundary_direct_fork:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q)=
        (n,terminal,Comma_Round_Fork a d)"
  obtains weight where
    "comma_semantic_boundary_step provider q=Some (Comma_Fork_At a d)"
    "comma_unique_literal_path weight (comma_boundary_value q p)
      (comma_chart_value p terminal)"
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
        v=comma_boundary_value child (p+d))"
proof -
  obtain kind source_a r where q: "q=(kind,source_a,r)"
    by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have phase_r: "r mod 924=p mod 924"
    using phase q r_bound by simp
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  have close_r:
    "comma_round_close r (comma_finite_initial q)=
      (n,terminal,Comma_Round_Fork a d)"
    using close q by simp
  have step:
    "comma_semantic_boundary_step provider q=Some (Comma_Fork_At a d)"
    using valid q close_r
    by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps)
  obtain weight where unique:
    "comma_unique_literal_path weight
      (comma_chart_value p (comma_finite_initial q))
      (comma_chart_value p terminal)"
    by (rule comma_round_close_unique_prefix
      [OF close_r phase_r exponent source_valid])
  have unique_start:
    "comma_unique_literal_path weight (comma_boundary_value q p)
      (comma_chart_value p terminal)"
    using unique comma_chart_initial_refines_boundary[OF valid] by simp
  have event_children:
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      v=comma_near_boundary a (p+d) \<or>
      v=comma_zero_boundary a (p+d)"
    using comma_boundary_fork_occurrence[OF valid exponent phase close]
    by blast
  have rendered:
    "set (map (\<lambda>child. comma_boundary_value child (p+d))
        (comma_native_boundary_children q (Comma_Fork_At a d))) =
      {comma_near_boundary a (p+d),comma_zero_boundary a (p+d)}"
    by (rule comma_native_boundary_fork_children_render[OF q])
  have endpoint_children:
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      v\<in>set [comma_near_boundary a (p+d),comma_zero_boundary a (p+d)]"
    using event_children by auto
  have children:
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
        v=comma_boundary_value child (p+d))"
    using endpoint_children rendered by auto
  show thesis by (rule that[OF step unique_start children])
qed

lemma comma_semantic_boundary_direct_landmine:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q)=
        (n,terminal,Comma_Round_Landmine d)"
  obtains weight where
    "comma_semantic_boundary_step provider q=Some (Comma_Landmine_At d)"
    "comma_unique_literal_path weight (comma_boundary_value q p)
      (comma_chart_value p terminal)"
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q (Comma_Landmine_At d)).
        v=comma_boundary_value child (p+d))"
proof -
  obtain kind source_a r where q: "q=(kind,source_a,r)"
    by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have phase_r: "r mod 924=p mod 924"
    using phase q r_bound by simp
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  have close_r:
    "comma_round_close r (comma_finite_initial q)=
      (n,terminal,Comma_Round_Landmine d)"
    using close q by simp
  have step:
    "comma_semantic_boundary_step provider q=Some (Comma_Landmine_At d)"
    using valid q close_r
    by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps)
  obtain weight where unique:
    "comma_unique_literal_path weight
      (comma_chart_value p (comma_finite_initial q))
      (comma_chart_value p terminal)"
    by (rule comma_round_close_unique_prefix
      [OF close_r phase_r exponent source_valid])
  have unique_start:
    "comma_unique_literal_path weight (comma_boundary_value q p)
      (comma_chart_value p terminal)"
    using unique comma_chart_initial_refines_boundary[OF valid] by simp
  have no_child:
    "\<nexists>v. comma_child (comma_chart_value p terminal) v"
    using comma_boundary_landmine_occurrence[OF valid exponent phase close] by blast
  have children:
    "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q (Comma_Landmine_At d)).
        v=comma_boundary_value child (p+d))"
    using no_child q by (simp add: comma_native_boundary_children_def)
  show thesis by (rule that[OF step unique_start children])
qed

lemma comma_semantic_boundary_crossing:
  assumes provider: "comma_semantic_decade_provider_exact provider"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and close:
      "comma_round_close (snd (snd q)) (comma_finite_initial q)=
        (n,terminal,Comma_Round_Cross target)"
  obtains x h tau weight t where
    "x\<le>90"
    "target=Comma_Entry 1 1 x"
    "comma_decade_exact_summary
      (Comma_Decade ((snd (snd q)+1) mod 924) x) h tau"
    "h\<le>26"
    "comma_semantic_boundary_step provider q=
      Some (comma_summary_outcome (h+1) tau)"
    "comma_unique_literal_path weight (comma_boundary_value q p)
      (comma_chart_value (p+(h+1)) t)"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+(h+1)) mod 924) t=
      comma_summary_terminal_move tau"
    "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v
      \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q
        (comma_summary_outcome (h+1) tau)).
        v=comma_boundary_value child (p+(h+1)))"
proof -
  obtain kind source_a r where q: "q=(kind,source_a,r)"
    by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  have source_zero: "comma_round_delta (comma_finite_initial q)=0"
    by (cases kind) (simp_all add: q comma_finite_initial_def)
  have phase_r: "r mod 924=p mod 924"
    using phase q r_bound by simp
  have close_r:
    "comma_round_close r (comma_finite_initial q)=
      (n,terminal,Comma_Round_Cross target)"
    using close q by simp
  obtain x where x_bound: "x\<le>90"
    and target_shape:
      "target=Comma_Entry 1 (Suc (comma_round_delta (comma_finite_initial q))) x"
    using comma_round_close_crossing_phase[OF close_r source_valid] by blast
  have target_entry: "target=Comma_Entry 1 1 x"
    using target_shape source_zero by simp
  have target_shape0: "target=Comma_Entry 1 (Suc 0) x"
    using target_entry by simp
  obtain h tau prefix_weight suffix_weight t where suffix_data:
      "provider (Comma_Decade ((r+0+1) mod 924) x)=Some (h,tau)"
    and height: "h\<le>26"
    and suffix_exact:
      "comma_decade_exact_summary (Comma_Decade ((r+0+1) mod 924) x) h tau"
    and full_path:
      "comma_unique_literal_path (Suc prefix_weight+suffix_weight)
        (comma_chart_value p (comma_finite_initial q))
        (comma_chart_value (p+0+1+h) t)"
    and terminal_valid: "comma_round_admitted t"
    and terminal_zero: "comma_round_delta t=0"
    and terminal_move:
      "comma_finite_step ((p+0+1+h) mod 924) t=
        comma_summary_terminal_move tau"
    apply (rule comma_semantic_boundary_crossing_suffix
      [where d=0, OF provider close_r source_valid source_zero target_shape0
        x_bound phase_r exponent])
    apply (rule that)
    by (simp add: add_0)
  have suffix_data':
    "provider (Comma_Decade ((r+1) mod 924) x)=Some (h,tau)"
    using suffix_data by simp
  have exact:
    "comma_decade_exact_summary (Comma_Decade ((r+1) mod 924) x) h tau"
    using suffix_exact by simp
  have full_path':
    "comma_unique_literal_path (Suc prefix_weight+suffix_weight)
      (comma_chart_value p (comma_finite_initial q))
      (comma_chart_value (p+1+h) t)"
    using full_path by simp
  have terminal_move':
    "comma_finite_step ((p+1+h) mod 924) t=
      comma_summary_terminal_move tau"
    using terminal_move by simp
  have outcome:
    "comma_semantic_boundary_step provider q=
      Some (comma_summary_outcome (h+1) tau)"
    using valid q close_r target_entry suffix_data' x_bound
    by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps)
  have exact_q:
    "comma_decade_exact_summary
      (Comma_Decade ((snd (snd q)+1) mod 924) x) h tau"
    using exact q by simp
  have boundary_start:
    "comma_chart_value p (comma_finite_initial q)=comma_boundary_value q p"
    by (rule comma_chart_initial_refines_boundary[OF valid])
  have exponent_eq: "p+1+h=p+(h+1)" by arith
  have unique_path:
    "comma_unique_literal_path (Suc prefix_weight+suffix_weight)
      (comma_boundary_value q p) (comma_chart_value (p+(h+1)) t)"
    using full_path' boundary_start exponent_eq by simp
  have end_admitted: "5\<le>p+(h+1)" using exponent by arith
  have end_phase: "(p+1+h) mod 924=(p+(h+1)) mod 924"
    using exponent_eq by simp
  have end_move:
    "comma_finite_step ((p+(h+1)) mod 924) t=
      comma_summary_terminal_move tau"
    using terminal_move' exponent_eq by simp
  have terminal_children:
    "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v
      \<longleftrightarrow> v\<in>set (comma_summary_ordered_children tau (p+(h+1)))"
    using comma_summary_terminal_children_exact(2)
      [OF terminal_valid terminal_zero end_admitted end_move] by simp
  have rendered:
    "set (map (\<lambda>child. comma_boundary_value child (p+(h+1)))
        (comma_native_boundary_children q (comma_summary_outcome (h+1) tau))) =
      set (comma_summary_ordered_children tau (p+(h+1)))"
    using comma_native_boundary_children_render_summary
      [where p=p and d="h+1" and terminal=tau, OF q]
    by simp
  have child_relation:
    "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v
      \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q
        (comma_summary_outcome (h+1) tau)).
        v=comma_boundary_value child (p+(h+1)))"
    using terminal_children rendered by auto
  show thesis
    by (rule that[where x=x, OF x_bound target_entry exact_q height outcome
      unique_path terminal_valid terminal_zero end_move child_relation])
qed

lemma comma_semantic_boundary_unique_occurrence:
  assumes unique: "comma_unique_literal_path weight source endpoint"
  shows "comma_literal_path weight source endpoint"
    "\<forall>other. comma_literal_path weight source other \<longrightarrow>
      other=endpoint"
  using comma_unique_literal_path_literal[OF unique]
    comma_unique_literal_path_endpoint[OF unique]
  by blast+

theorem comma_semantic_boundary_strong_occurrence_bridge:
  assumes provider: "comma_semantic_decade_provider_exact provider"
  shows "comma_semantic_strong_occurrence_bridge comma_boundary_valid
    (\<lambda>q. snd (snd q)) comma_boundary_value
    (comma_semantic_boundary_exponent_delta provider)
    (comma_semantic_boundary_children provider)
    (comma_semantic_boundary_control_step provider)"
proof -
  show ?thesis
    unfolding comma_semantic_strong_occurrence_bridge_def
  proof (intro allI impI)
    fix q p
    assume state_valid: "comma_boundary_valid q"
      and exponent: "5\<le>p"
      and phase_match: "p mod 924=snd (snd q)"
    obtain kind source_a r where q: "q=(kind,source_a,r)"
      by (cases q) auto
    have r_bound: "r<924" using state_valid by (simp add: q comma_boundary_valid_def)
    have source_valid: "comma_round_admitted (comma_finite_initial q)"
      using state_valid by (cases kind)
        (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
    have phase_r: "r mod 924=p mod 924"
      using phase_match q r_bound by simp
    obtain n terminal event where close:
      "comma_round_close r (comma_finite_initial q)=(n,terminal,event)"
      by (cases "comma_round_close r (comma_finite_initial q)") auto
    have event_valid: "event\<noteq>Comma_Round_Invalid"
      using comma_round_close_admitted(2)[OF close source_valid] .
    ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-close"\<close>
    show "\<exists>control endpoint weight.
      comma_semantic_boundary_control_step provider q=Some control \<and>
      comma_unique_literal_path weight (comma_boundary_value q p) endpoint \<and>
      distinct (comma_semantic_boundary_children provider q control) \<and>
      (\<forall>child\<in>set (comma_semantic_boundary_children provider q control).
        comma_boundary_valid child \<and>
        5\<le>p+comma_semantic_boundary_exponent_delta provider q control \<and>
        (p+comma_semantic_boundary_exponent_delta provider q control) mod 924=
          snd (snd child)) \<and>
      (case control of Comma_Future_Fork a \<Rightarrow>
        length (comma_semantic_boundary_children provider q control)=2
       | Comma_Future_Landmine \<Rightarrow>
        comma_semantic_boundary_children provider q control=[]) \<and>
      (\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_semantic_boundary_children provider q control).
          v=comma_boundary_value child
            (p+comma_semantic_boundary_exponent_delta provider q control)))"
    proof (cases event)
      case (Comma_Round_Fork a d)
      have close_fork:
        "comma_round_close r (comma_finite_initial q)=
          (n,terminal,Comma_Round_Fork a d)"
        using close Comma_Round_Fork by simp
      have close_fork_q:
        "comma_round_close (snd (snd q)) (comma_finite_initial q)=
          (n,terminal,Comma_Round_Fork a d)"
        using close_fork q by simp
      obtain weight where step:
          "comma_semantic_boundary_step provider q=Some (Comma_Fork_At a d)"
        and unique:
          "comma_unique_literal_path weight (comma_boundary_value q p)
            (comma_chart_value p terminal)"
        and child_relation:
          "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
            (\<exists>child\<in>set (comma_native_boundary_children q
              (Comma_Fork_At a d)).
              v=comma_boundary_value child (p+d))"
        by (rule comma_semantic_boundary_direct_fork
          [where provider=provider, OF state_valid exponent phase_match close_fork_q])
      have finite_fork:
        "comma_finite_step (r mod 924) terminal=Comma_Fork a d"
        using comma_round_close_refines_trace[OF close] Comma_Round_Fork by simp
      have digit_bounds: "2\<le>a" "a\<le>9"
        using comma_finite_fork_digit_bounds[OF finite_fork] by auto
      have distinct_children:
        "distinct (comma_native_boundary_children q (Comma_Fork_At a d))"
        using comma_semantic_boundary_fork_children_admitted(1)
          [OF state_valid exponent phase_match digit_bounds] .
      have admitted_children:
        "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
          comma_boundary_valid child \<and>
          5\<le>p+d \<and> (p+d) mod 924=snd (snd child)"
        using comma_semantic_boundary_fork_children_admitted(2)
          [OF state_valid exponent phase_match digit_bounds] .
      have payload:
          "comma_literal_path weight (comma_boundary_value q p)
            (comma_chart_value p terminal)"
        using comma_semantic_boundary_unique_occurrence(1)[OF unique] .
      have unique_endpoint:
          "\<forall>other. comma_literal_path weight (comma_boundary_value q p) other
            \<longrightarrow> other=comma_chart_value p terminal"
        using comma_semantic_boundary_unique_occurrence(2)[OF unique] .
      have control_step:
        "comma_semantic_boundary_control_step provider q=
          Some (Comma_Future_Fork a)"
        using step by (simp add: comma_semantic_boundary_control_step_def)
      have exponent_delta:
        "comma_semantic_boundary_exponent_delta provider q (Comma_Future_Fork a)=d"
        using step by (simp add: comma_semantic_boundary_exponent_delta_def
          comma_native_outcome_delta_def)
      have children:
        "comma_semantic_boundary_children provider q (Comma_Future_Fork a)=
          comma_native_boundary_children q (Comma_Fork_At a d)"
        using step by (simp add: comma_semantic_boundary_children_def)
      have length_children:
        "length (comma_semantic_boundary_children provider q (Comma_Future_Fork a))=2"
        using children q by (simp add: comma_native_boundary_children_def)
      ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-direct-fork-ready"\<close>
      show ?thesis
      proof (rule exI[where x="Comma_Future_Fork a"],
          rule exI[where x="comma_chart_value p terminal"],
          rule exI[where x=weight], intro conjI)
        show "comma_semantic_boundary_control_step provider q=
            Some (Comma_Future_Fork a)" by (rule control_step)
        show "comma_unique_literal_path weight (comma_boundary_value q p)
            (comma_chart_value p terminal)" by (rule unique)
        show "distinct (comma_semantic_boundary_children provider q
            (Comma_Future_Fork a))"
          using distinct_children children by simp
        show "\<forall>child\<in>set (comma_semantic_boundary_children provider q
              (Comma_Future_Fork a)).
            comma_boundary_valid child \<and>
            5\<le>p+comma_semantic_boundary_exponent_delta provider q
              (Comma_Future_Fork a) \<and>
            (p+comma_semantic_boundary_exponent_delta provider q
              (Comma_Future_Fork a)) mod 924=snd (snd child)"
          using admitted_children children exponent_delta by simp
        show "(case Comma_Future_Fork a of
              Comma_Future_Fork ignored \<Rightarrow>
                length (comma_semantic_boundary_children provider q
                  (Comma_Future_Fork a))=2
             | Comma_Future_Landmine \<Rightarrow>
                comma_semantic_boundary_children provider q
                  (Comma_Future_Fork a)=[])"
          using length_children by simp
        show "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
            (\<exists>child\<in>set (comma_semantic_boundary_children provider q
              (Comma_Future_Fork a)).
              v=comma_boundary_value child
                (p+comma_semantic_boundary_exponent_delta provider q
                  (Comma_Future_Fork a)))"
          using child_relation children exponent_delta by simp
      qed
    next
      case (Comma_Round_Landmine d)
      have close_landmine:
        "comma_round_close r (comma_finite_initial q)=
          (n,terminal,Comma_Round_Landmine d)"
        using close Comma_Round_Landmine by simp
      have close_landmine_q:
        "comma_round_close (snd (snd q)) (comma_finite_initial q)=
          (n,terminal,Comma_Round_Landmine d)"
        using close_landmine q by simp
      obtain weight where step:
          "comma_semantic_boundary_step provider q=Some (Comma_Landmine_At d)"
        and unique:
          "comma_unique_literal_path weight (comma_boundary_value q p)
            (comma_chart_value p terminal)"
        and child_relation:
          "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
            (\<exists>child\<in>set (comma_native_boundary_children q
              (Comma_Landmine_At d)).
              v=comma_boundary_value child (p+d))"
        by (rule comma_semantic_boundary_direct_landmine
          [where provider=provider, OF state_valid exponent phase_match close_landmine_q])
      have literal:
        "comma_literal_path weight (comma_boundary_value q p)
          (comma_chart_value p terminal)"
        using comma_semantic_boundary_unique_occurrence(1)[OF unique] .
      have unique_endpoint:
        "\<forall>other. comma_literal_path weight (comma_boundary_value q p) other
          \<longrightarrow> other=comma_chart_value p terminal"
        using comma_semantic_boundary_unique_occurrence(2)[OF unique] .
      have control_step:
        "comma_semantic_boundary_control_step provider q=
          Some Comma_Future_Landmine"
        using step by (simp add: comma_semantic_boundary_control_step_def)
      have exponent_delta:
        "comma_semantic_boundary_exponent_delta provider q Comma_Future_Landmine=d"
        using step by (simp add: comma_semantic_boundary_exponent_delta_def
          comma_native_outcome_delta_def)
      ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-direct-landmine-ready"\<close>
        have children:
          "comma_semantic_boundary_children provider q Comma_Future_Landmine=[]"
          using step q by (simp add: comma_semantic_boundary_children_def
            comma_native_boundary_children_def)
      show ?thesis
      proof (rule exI[where x=Comma_Future_Landmine],
          rule exI[where x="comma_chart_value p terminal"],
          rule exI[where x=weight], intro conjI)
        show "comma_semantic_boundary_control_step provider q=
            Some Comma_Future_Landmine" by (rule control_step)
        show "comma_unique_literal_path weight (comma_boundary_value q p)
            (comma_chart_value p terminal)" by (rule unique)
        show "distinct (comma_semantic_boundary_children provider q
            Comma_Future_Landmine)"
          using children by simp
        show "\<forall>child\<in>set (comma_semantic_boundary_children provider q
              Comma_Future_Landmine).
            comma_boundary_valid child \<and>
            5\<le>p+comma_semantic_boundary_exponent_delta provider q
              Comma_Future_Landmine \<and>
            (p+comma_semantic_boundary_exponent_delta provider q
              Comma_Future_Landmine) mod 924=snd (snd child)"
          using children by simp
        show "(case Comma_Future_Landmine of
              Comma_Future_Fork a \<Rightarrow>
                length (comma_semantic_boundary_children provider q
                  Comma_Future_Landmine)=2
             | Comma_Future_Landmine \<Rightarrow>
                comma_semantic_boundary_children provider q
                  Comma_Future_Landmine=[])"
          using children by simp
        show "\<forall>v. comma_child (comma_chart_value p terminal) v \<longleftrightarrow>
            (\<exists>child\<in>set (comma_semantic_boundary_children provider q
              Comma_Future_Landmine).
              v=comma_boundary_value child
                (p+comma_semantic_boundary_exponent_delta provider q
                  Comma_Future_Landmine))"
          using child_relation children exponent_delta q
          by (simp add: comma_native_boundary_children_def)
      qed
    next
      case (Comma_Round_Cross target)
      have close_cross:
        "comma_round_close r (comma_finite_initial q)=
          (n,terminal,Comma_Round_Cross target)"
        using close Comma_Round_Cross by simp
      have close_cross_q:
        "comma_round_close (snd (snd q)) (comma_finite_initial q)=
          (n,terminal,Comma_Round_Cross target)"
        using close_cross q by simp
      obtain x h tau weight t where x_bound: "x\<le>90"
        and target_entry: "target=Comma_Entry 1 1 x"
        and exact:
          "comma_decade_exact_summary
            (Comma_Decade ((snd (snd q)+1) mod 924) x) h tau"
        and height: "h\<le>26"
        and step:
          "comma_semantic_boundary_step provider q=
            Some (comma_summary_outcome (h+1) tau)"
        and unique:
          "comma_unique_literal_path weight (comma_boundary_value q p)
            (comma_chart_value (p+(h+1)) t)"
        and terminal_valid: "comma_round_admitted t"
        and terminal_zero: "comma_round_delta t=0"
        and terminal_move:
          "comma_finite_step ((p+(h+1)) mod 924) t=
            comma_summary_terminal_move tau"
        and child_relation:
          "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v \<longleftrightarrow>
            (\<exists>child\<in>set (comma_native_boundary_children q
              (comma_summary_outcome (h+1) tau)).
              v=comma_boundary_value child (p+(h+1)))"
        by (rule comma_semantic_boundary_crossing
          [OF provider state_valid exponent phase_match close_cross_q])
      have literal:
        "comma_literal_path weight (comma_boundary_value q p)
          (comma_chart_value (p+(h+1)) t)"
        using comma_semantic_boundary_unique_occurrence(1)[OF unique] .
      have unique_endpoint:
        "\<forall>other. comma_literal_path weight (comma_boundary_value q p) other
          \<longrightarrow> other=comma_chart_value (p+(h+1)) t"
        using comma_semantic_boundary_unique_occurrence(2)[OF unique] .
      ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-cross-summary-ready"\<close>
      show ?thesis
      proof (cases tau)
        case (Comma_Terminal_Fork a)
        have step_fork:
          "comma_semantic_boundary_step provider q=
            Some (Comma_Fork_At a (h+1))"
          using step Comma_Terminal_Fork by simp
        have fork_bounds: "2\<le>a" "a\<le>9"
          using comma_decade_terminal_fork_bounds[OF exact] Comma_Terminal_Fork
          by simp_all
        have children:
          "comma_semantic_boundary_children provider q
              (Comma_Future_Fork a)=
            comma_native_boundary_children q (Comma_Fork_At a (h+1))"
          using step_fork by (simp add: comma_semantic_boundary_children_def)
        have control_step:
          "comma_semantic_boundary_control_step provider q=
            Some (Comma_Future_Fork a)"
          using step_fork by (simp add: comma_semantic_boundary_control_step_def)
        have exponent_delta:
          "comma_semantic_boundary_exponent_delta provider q
              (Comma_Future_Fork a)=h+1"
          using step_fork by (simp add: comma_semantic_boundary_exponent_delta_def
            comma_native_outcome_delta_def)
        have distinct_children:
          "distinct (comma_native_boundary_children q (Comma_Fork_At a (h+1)))"
          using q by (simp add: comma_native_boundary_children_def)
        have admitted_children:
          "\<forall>child\<in>set (comma_native_boundary_children q
              (Comma_Fork_At a (h+1))).
            comma_boundary_valid child \<and>
            5\<le>p+(h+1) \<and>
            (p+(h+1)) mod 924=snd (snd child)"
          by (rule comma_semantic_boundary_fork_children_admitted(2)
            [OF state_valid exponent phase_match fork_bounds])
        have length_children:
          "length (comma_semantic_boundary_children provider q
              (Comma_Future_Fork a))=2"
          using children q by (simp add: comma_native_boundary_children_def)
        ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-cross-fork-ready"\<close>
        show ?thesis
        proof (rule exI[where x="Comma_Future_Fork a"],
            rule exI[where x="comma_chart_value (p+(h+1)) t"],
            rule exI[where x=weight], intro conjI)
          show "comma_semantic_boundary_control_step provider q=
              Some (Comma_Future_Fork a)" by (rule control_step)
          show "comma_unique_literal_path weight (comma_boundary_value q p)
              (comma_chart_value (p+(h+1)) t)" by (rule unique)
          show "distinct (comma_semantic_boundary_children provider q
              (Comma_Future_Fork a))"
            using distinct_children children by simp
          show "\<forall>child\<in>set (comma_semantic_boundary_children provider q
                (Comma_Future_Fork a)).
              comma_boundary_valid child \<and>
              5\<le>p+comma_semantic_boundary_exponent_delta provider q
                (Comma_Future_Fork a) \<and>
              (p+comma_semantic_boundary_exponent_delta provider q
                (Comma_Future_Fork a)) mod 924=snd (snd child)"
            using admitted_children children exponent_delta by simp
          show "(case Comma_Future_Fork a of
                Comma_Future_Fork ignored \<Rightarrow>
                  length (comma_semantic_boundary_children provider q
                    (Comma_Future_Fork a))=2
               | Comma_Future_Landmine \<Rightarrow>
                  comma_semantic_boundary_children provider q
                    (Comma_Future_Fork a)=[])"
            using length_children by simp
          show "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v \<longleftrightarrow>
              (\<exists>child\<in>set (comma_semantic_boundary_children provider q
                (Comma_Future_Fork a)).
                v=comma_boundary_value child
                  (p+comma_semantic_boundary_exponent_delta provider q
                    (Comma_Future_Fork a)))"
            using child_relation children exponent_delta Comma_Terminal_Fork by simp
        qed
      next
        case Comma_Terminal_Landmine
        have step_landmine:
          "comma_semantic_boundary_step provider q=
            Some (Comma_Landmine_At (h+1))"
          using step Comma_Terminal_Landmine by simp
        have children:
          "comma_semantic_boundary_children provider q Comma_Future_Landmine=[]"
          using step_landmine q by (simp add: comma_semantic_boundary_children_def
            comma_native_boundary_children_def)
        have control_step:
          "comma_semantic_boundary_control_step provider q=
            Some Comma_Future_Landmine"
          using step_landmine by (simp add: comma_semantic_boundary_control_step_def)
        have exponent_delta:
          "comma_semantic_boundary_exponent_delta provider q
              Comma_Future_Landmine=h+1"
          using step_landmine by (simp add: comma_semantic_boundary_exponent_delta_def
            comma_native_outcome_delta_def)
        ML_prf \<open>Comma_Proof_Profile.report "semantic-boundary-bridge-cross-landmine-ready"\<close>
        show ?thesis
        proof (rule exI[where x=Comma_Future_Landmine],
            rule exI[where x="comma_chart_value (p+(h+1)) t"],
            rule exI[where x=weight], intro conjI)
          show "comma_semantic_boundary_control_step provider q=
              Some Comma_Future_Landmine" by (rule control_step)
          show "comma_unique_literal_path weight (comma_boundary_value q p)
              (comma_chart_value (p+(h+1)) t)" by (rule unique)
          show "distinct (comma_semantic_boundary_children provider q
              Comma_Future_Landmine)"
            using children by simp
          show "\<forall>child\<in>set (comma_semantic_boundary_children provider q
                Comma_Future_Landmine).
              comma_boundary_valid child \<and>
              5\<le>p+comma_semantic_boundary_exponent_delta provider q
                Comma_Future_Landmine \<and>
              (p+comma_semantic_boundary_exponent_delta provider q
                Comma_Future_Landmine) mod 924=snd (snd child)"
            using children exponent_delta by simp
          show "(case Comma_Future_Landmine of
                Comma_Future_Fork a \<Rightarrow>
                  length (comma_semantic_boundary_children provider q
                    Comma_Future_Landmine)=2
               | Comma_Future_Landmine \<Rightarrow>
                  comma_semantic_boundary_children provider q
                    Comma_Future_Landmine=[])"
            using children by simp
          show "\<forall>v. comma_child (comma_chart_value (p+(h+1)) t) v \<longleftrightarrow>
              (\<exists>child\<in>set (comma_semantic_boundary_children provider q
                Comma_Future_Landmine).
                v=comma_boundary_value child
                  (p+comma_semantic_boundary_exponent_delta provider q
                    Comma_Future_Landmine))"
            using child_relation children exponent_delta q Comma_Terminal_Landmine
          by (simp add: comma_native_boundary_children_def)
        qed
      qed
    next
      case Comma_Round_Invalid
      then show ?thesis using event_valid by contradiction
    qed
  qed
qed

theorem comma_semantic_boundary_occurrence_bridge:
  assumes provider: "comma_semantic_decade_provider_exact provider"
  shows "comma_semantic_occurrence_bridge comma_boundary_valid
    (\<lambda>q. snd (snd q)) comma_boundary_value
    (comma_semantic_boundary_exponent_delta provider)
    (comma_semantic_boundary_children provider)
    (comma_semantic_boundary_control_step provider)"
  by (rule comma_semantic_strong_occurrence_bridge_implies
      [OF comma_semantic_boundary_strong_occurrence_bridge[OF provider]])


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_boundary_step_direct_fork
    comma_semantic_boundary_step_direct_landmine
    comma_semantic_boundary_rejects_noncanonical_crossing
    comma_semantic_decade_provider_lookup
    comma_semantic_boundary_crossing_suffix
    comma_semantic_boundary_fork_children_admitted
    comma_semantic_boundary_direct_fork
    comma_semantic_boundary_direct_landmine
    comma_semantic_boundary_crossing
    comma_semantic_boundary_unique_occurrence
    comma_semantic_boundary_strong_occurrence_bridge
    comma_semantic_boundary_occurrence_bridge
  }) then ()
  else error "Comma_Semantic_Boundary local oracle audit failed"
\<close>
end
