theory Comma_Native_Boundary
  imports Comma_Native_Summary_Occurrence.Comma_Native_Summary_Occurrence
begin

ML_file "../shared/Proof_Dependency_Audit.ML"

ML \<open>
  structure Comma_Native_Boundary_Profile =
  struct
    val started = Time.now ()
    fun checkpoint stage = Comma_Proof_Profile.report
      ("Native boundary stage=" ^ stage ^ " elapsed_ms=" ^
        Comma_Proof_Profile.elapsed_ms started)
  end
  val _ = Comma_Native_Boundary_Profile.checkpoint "theory-entered"
\<close>

text \<open>Fuel-free boundary dynamics are defined from the admitted native
sparse decade response and literal round closure. This theory keeps the
classifier parameterized: concrete B32 rows are supplied only by a checked
child instance.\<close>

definition comma_native_infinite_literal_path ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_native_infinite_literal_path source path \<longleftrightarrow>
    path 0=source \<and> (\<forall>j. comma_child (path j) (path (Suc j)))"

text \<open>Any infinite literal path must follow the unique admitted boundary
occurrence up to its endpoint. Its next literal is therefore one of the
exact ordered child occurrences returned by the same native action, and the
remaining tail is again an infinite literal path. The exponent and phase are
transported as occurrence data, not folded into the action identity.\<close>

theorem comma_native_infinite_path_projects:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  obtains outcome endpoint w child where
    "comma_native_boundary_step rows q=Some outcome"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q outcome)"
    "stream (Suc w)=comma_boundary_value child
      (p+comma_native_outcome_delta outcome)"
    "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
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
    have start: "stream 0=comma_boundary_value q p"
      using path by (simp add: comma_native_infinite_literal_path_def)
    have edges: "comma_child (stream j) (stream (Suc j))" for j
      using path by (simp add: comma_native_infinite_literal_path_def)
    have prefix: "comma_literal_path w (stream 0) (stream w)"
      by (rule comma_infinite_literal_prefix[where path=stream and n=w, OF edges])
    have endpoint: "stream w=endpoint"
      using comma_unique_literal_path_endpoint[OF occurrence] prefix start by simp
    have next_child: "comma_child endpoint (stream (Suc w))"
      using edges[of w] endpoint by simp
    obtain child where member:
      "child\<in>set (comma_native_boundary_children q outcome)"
      and next_value: "stream (Suc w)=comma_boundary_value child
        (p+comma_native_outcome_delta outcome)"
      using child_relation next_child by blast
    have tail_start:
      "(\<lambda>j. stream (w+Suc j)) 0=
        comma_boundary_value child (p+comma_native_outcome_delta outcome)"
      using next_value by simp
    have tail_edges:
      "comma_child ((\<lambda>j. stream (w+Suc j)) j)
        ((\<lambda>j. stream (w+Suc j)) (Suc j))" for j
      using edges[of "w+Suc j"] by (simp add: add.assoc)
    have tail:
      "comma_native_infinite_literal_path
        (comma_boundary_value child (p+comma_native_outcome_delta outcome))
        (\<lambda>j. stream (w+Suc j))"
      using tail_start tail_edges
      by (simp add: comma_native_infinite_literal_path_def)
    show thesis by (rule that[OF step occurrence member next_value tail])
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "infinite-path-projects"\<close>

lemma comma_native_sparse_summary_fork_bounds:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and admitted: "comma_decade_admitted s"
    and result: "comma_sparse_decade_summary rows s=Some (h,terminal)"
  shows "(case terminal of Comma_Terminal_Fork a \<Rightarrow> 2\<le>a \<and> a\<le>9
    | Comma_Terminal_Landmine \<Rightarrow> True)"
proof -
  obtain exact_height exact_terminal where exact:
    "comma_decade_exact_summary s exact_height exact_terminal"
    and produced: "comma_sparse_decade_summary rows s=
      Some (exact_height,exact_terminal)"
    using comma_sparse_decade_summary_total_exact[OF powers stops admitted]
    by blast
  have terminal_eq: "terminal=exact_terminal" using result produced by simp
  show ?thesis
    using comma_decade_terminal_fork_bounds[OF exact] terminal_eq
    by simp
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "sparse-summary-fork-bounds"\<close>

text \<open>Every produced fork state is inside the boundary-state domain.
This is derived from the actual native step: direct forks refine the finite
comma transition, and crossings refine the checked decade terminal. The
phase equation is then transported by modular addition from the source
exponent to the exact outcome delta.\<close>

lemma comma_native_boundary_step_fork_digit_bounds:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and result: "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
  shows "2\<le>a \<and> a\<le>9"
proof -
  obtain kind b r where q: "q=(kind,b,r)" by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (auto simp: q comma_boundary_valid_def comma_finite_initial_def)
  have source_delta: "comma_round_delta (comma_finite_initial q)=0"
    by (cases kind; simp add: q comma_finite_initial_def)
  obtain n terminal event where close:
    "comma_round_close r (comma_finite_initial q)=(n,terminal,event)"
    by (cases "comma_round_close r (comma_finite_initial q)") auto
  have event_result:
    "comma_sparse_boundary_event_outcome rows r event=Some (Comma_Fork_At a d)"
    using result q valid close
    by (simp only: comma_native_boundary_step_def q valid close if_True prod.case)
  show ?thesis
  proof (cases event)
    case (Comma_Round_Fork fork_a fork_delta)
    have same: "a=fork_a" "d=fork_delta"
      using event_result Comma_Round_Fork by simp_all
    have close_fork:
      "comma_round_close r (comma_finite_initial q)=
        (n,terminal,Comma_Round_Fork fork_a fork_delta)"
      using close Comma_Round_Fork by simp
    have finite: "comma_finite_step (r mod 924) terminal=Comma_Fork a d"
      using comma_round_close_refines_trace[OF close_fork] same
      by simp
    show ?thesis by (rule comma_finite_fork_digit_bounds[OF finite])
  next
    case (Comma_Round_Landmine delta)
    then show ?thesis using event_result by simp
  next
    case (Comma_Round_Cross target)
    have close_cross:
      "comma_round_close r (comma_finite_initial q)=
        (n,terminal,Comma_Round_Cross target)"
      using close Comma_Round_Cross by simp
    obtain x where x_bound: "x\<le>90"
      and target_shape:
        "target=Comma_Entry 1 (Suc (comma_round_delta (comma_finite_initial q))) x"
      using comma_round_close_crossing_phase[OF close_cross source_valid]
      by blast
    have target_eq: "target=Comma_Entry 1 1 x"
      using target_shape source_delta by simp
    have decade: "comma_decade_admitted (Comma_Decade ((r+1) mod 924) x)"
      using x_bound by simp
    obtain h tau where summary:
      "comma_sparse_decade_summary rows (Comma_Decade ((r+1) mod 924) x)=Some (h,tau)"
      and produced_outcome:
      "comma_summary_outcome (h+1) tau=Comma_Fork_At a d"
      using event_result Comma_Round_Cross target_eq
      by (cases "comma_sparse_decade_summary rows (Comma_Decade ((r+1) mod 924) x)")
        (auto simp: comma_sparse_boundary_event_outcome.simps target_eq)
    have terminal_bounds:
      "(case tau of Comma_Terminal_Fork z \<Rightarrow> 2\<le>z \<and> z\<le>9
        | Comma_Terminal_Landmine \<Rightarrow> True)"
      by (rule comma_native_sparse_summary_fork_bounds[OF powers stops decade summary])
    show ?thesis using produced_outcome terminal_bounds by (cases tau) simp_all
  next
    case Comma_Round_Invalid
    then show ?thesis using event_result by simp
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "boundary-step-fork-digit-bounds"\<close>

lemma comma_native_boundary_children_valid_phase:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and bounds: "2\<le>a" "a\<le>9"
  shows "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      comma_boundary_valid child \<and>
      (p+d) mod 924=snd (snd child)"
proof -
  obtain kind source_a r where q: "q=(kind,source_a,r)" by (cases q) auto
  have r_bound: "r<924" using valid by (simp add: q comma_boundary_valid_def)
  have physical_phase: "p mod 924=r" using phase by (simp only: q prod.sel)
  have target_phase: "(p+d) mod 924=(r+d) mod 924"
  proof -
    have "(p+d) mod 924=(p mod 924+d) mod 924"
      by (rule mod_add_left_eq[symmetric])
    also have "...=(r+d) mod 924" by (simp only: physical_phase)
    finally show ?thesis .
  qed
  show ?thesis
    using bounds target_phase r_bound q
    by (auto simp: comma_native_boundary_children_def comma_boundary_valid_def)
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "boundary-children-valid-phase"\<close>

theorem comma_native_boundary_step_children_valid_phase:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  obtains outcome where
    "comma_native_boundary_step rows q=Some outcome"
    "\<forall>child\<in>set (comma_native_boundary_children q outcome).
      comma_boundary_valid child \<and>
      (p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
proof -
  show thesis
  proof (rule comma_sparse_boundary_ordered_occurrence_step
      [OF powers stops valid exponent phase])
    fix outcome endpoint weight
    assume step: "comma_native_boundary_step rows q=Some outcome"
      and children: "comma_native_boundary_children q outcome =
        (case outcome of Comma_Landmine_At d \<Rightarrow> []
         | Comma_Fork_At a d \<Rightarrow>
            [(Comma_N,a,(snd (snd q)+d) mod 924),
             (Comma_Z,a,(snd (snd q)+d) mod 924)])"
      and occurrence:
        "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
      and child_relation: "\<And>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q outcome).
          v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    have children_valid:
      "\<forall>child\<in>set (comma_native_boundary_children q outcome).
        comma_boundary_valid child \<and>
        (p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    proof (cases outcome)
      case (Comma_Landmine_At delta)
      then show ?thesis by (simp add: comma_native_boundary_children_def)
    next
      case (Comma_Fork_At a delta)
      have fork_step:
        "comma_native_boundary_step rows q=Some (Comma_Fork_At a delta)"
        using step Comma_Fork_At by simp
      have bounds: "2\<le>a \<and> a\<le>9"
        by (rule comma_native_boundary_step_fork_digit_bounds
          [OF powers stops valid fork_step])
      then have bounds_parts: "2\<le>a" "a\<le>9" by auto
      have phase_children:
        "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a delta)).
          comma_boundary_valid child \<and> (p+delta) mod 924=snd (snd child)"
        by (rule comma_native_boundary_children_valid_phase
          [OF valid exponent phase bounds_parts])
      show ?thesis
        using phase_children Comma_Fork_At
        by (simp add: comma_native_outcome_delta_def)
    qed
    show thesis by (rule that[OF step children_valid])
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "boundary-step-children-valid-phase"\<close>

theorem comma_native_infinite_path_projects_admitted_child:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  obtains outcome endpoint w child where
    "comma_native_boundary_step rows q=Some outcome"
    "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q outcome)"
    "stream (Suc w)=comma_boundary_value child
      (p+comma_native_outcome_delta outcome)"
    "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
    "comma_boundary_valid child"
    "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
proof -
  show thesis
  proof (rule comma_native_infinite_path_projects
      [OF powers stops valid exponent phase path])
    fix outcome endpoint w child
    assume step: "comma_native_boundary_step rows q=Some outcome"
      and occurrence: "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
      and member: "child\<in>set (comma_native_boundary_children q outcome)"
      and next_value: "stream (Suc w)=comma_boundary_value child
        (p+comma_native_outcome_delta outcome)"
      and tail: "comma_native_infinite_literal_path
        (comma_boundary_value child (p+comma_native_outcome_delta outcome))
        (\<lambda>j. stream (w+Suc j))"
    have children:
      "\<forall>c\<in>set (comma_native_boundary_children q outcome).
        comma_boundary_valid c \<and>
        (p+comma_native_outcome_delta outcome) mod 924=snd (snd c)"
    proof (rule comma_native_boundary_step_children_valid_phase
        [OF powers stops valid exponent phase])
      fix produced
      assume produced_step: "comma_native_boundary_step rows q=Some produced"
        and produced_children:
        "\<forall>c\<in>set (comma_native_boundary_children q produced).
          comma_boundary_valid c \<and>
          (p+comma_native_outcome_delta produced) mod 924=snd (snd c)"
      have same: "produced=outcome" using step produced_step by simp
      show ?thesis using produced_children by (simp only: same)
    qed
    have child_valid: "comma_boundary_valid child"
      and child_phase:
      "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
      using children member by blast+
    show thesis
      by (rule that[OF step occurrence member next_value tail child_valid child_phase])
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "infinite-path-projects-admitted-child"\<close>

text \<open>For the converse, survival is stated at an actual child of the
same completed native boundary action. The native occurrence supplies the
unique literal prefix and the complete child relation. Appending that child
edge makes the source literal path unbounded; the generic finite-branching
theorem then yields an infinite path. This is conditional on the supplied
checked row semantics and does not assert that a particular concrete root
survives.\<close>

theorem comma_native_surviving_child_has_infinite_path:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and successor_survives:
      "\<exists>outcome child.
        comma_native_boundary_step rows q=Some outcome \<and>
        child\<in>set (comma_native_boundary_children q outcome) \<and>
        comma_literal_unbounded
          (comma_boundary_value child (p+comma_native_outcome_delta outcome))"
  shows "\<exists>stream. comma_native_infinite_literal_path
    (comma_boundary_value q p) stream"
proof -
  show ?thesis
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
    obtain selected child where selected_step:
        "comma_native_boundary_step rows q=Some selected"
      and selected_member:
        "child\<in>set (comma_native_boundary_children q selected)"
      and selected_survives: "comma_literal_unbounded
        (comma_boundary_value child (p+comma_native_outcome_delta selected))"
      using successor_survives by blast
    have same: "selected=outcome" using selected_step step by simp
    have actual_member: "child\<in>set (comma_native_boundary_children q outcome)"
      using selected_member same by simp
    let ?child_value =
      "comma_boundary_value child (p+comma_native_outcome_delta outcome)"
    have actual_survives: "comma_literal_unbounded ?child_value"
      using selected_survives same by simp
    have child_edge: "comma_child endpoint ?child_value"
      using child_relation[of ?child_value] actual_member by blast
    have literal_prefix:
      "comma_literal_path w (comma_boundary_value q p) endpoint"
      by (rule comma_unique_literal_path_literal[OF occurrence])
    have prefix_to_child:
      "comma_literal_path (Suc w) (comma_boundary_value q p) ?child_value"
      by (rule comma_literal_path_snoc[OF literal_prefix child_edge])
    have source_unbounded:
      "comma_literal_unbounded (comma_boundary_value q p)"
      by (rule comma_literal_unbounded_prefix[OF prefix_to_child actual_survives])
    obtain stream where start: "stream 0=comma_boundary_value q p"
      and edges: "\<And>j. comma_child (stream j) (stream (Suc j))"
      using comma_literal_unbounded_infinite_path[OF source_unbounded] by blast
    have native_path:
      "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
      using start edges by (simp add: comma_native_infinite_literal_path_def)
    show ?thesis using native_path by blast
  qed
qed

theorem comma_native_infinite_path_iff_successor_survival:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "(\<exists>stream. comma_native_infinite_literal_path
      (comma_boundary_value q p) stream) \<longleftrightarrow>
    (\<exists>outcome child.
      comma_native_boundary_step rows q=Some outcome \<and>
      child\<in>set (comma_native_boundary_children q outcome) \<and>
      comma_literal_unbounded
        (comma_boundary_value child (p+comma_native_outcome_delta outcome)))"
proof
  assume parent_survives:
    "\<exists>stream. comma_native_infinite_literal_path
      (comma_boundary_value q p) stream"
  then obtain stream where path:
      "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
    by blast
  obtain outcome endpoint w child where step:
      "comma_native_boundary_step rows q=Some outcome"
    and occurrence:
      "comma_unique_literal_path w (comma_boundary_value q p) endpoint"
    and member: "child\<in>set (comma_native_boundary_children q outcome)"
    and next_value: "stream (Suc w)=comma_boundary_value child
      (p+comma_native_outcome_delta outcome)"
    and tail: "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
    and child_valid: "comma_boundary_valid child"
    and child_phase:
      "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    using comma_native_infinite_path_projects_admitted_child
      [OF powers stops valid exponent phase path] .
  have tail_start:
    "(\<lambda>j. stream (w+Suc j)) 0 =
      comma_boundary_value child (p+comma_native_outcome_delta outcome)"
    and tail_edges: "\<And>j. comma_child
      ((\<lambda>j. stream (w+Suc j)) j)
      ((\<lambda>j. stream (w+Suc j)) (Suc j))"
    using tail by (auto simp: comma_native_infinite_literal_path_def)
  have child_unbounded:
    "comma_literal_unbounded
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    by (rule comma_literal_infinite_path_unbounded[OF tail_start tail_edges])
  show "\<exists>outcome child. comma_native_boundary_step rows q=Some outcome \<and>
      child\<in>set (comma_native_boundary_children q outcome) \<and>
      comma_literal_unbounded
        (comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    using step member child_unbounded by blast
next
  assume successor_survives:
    "\<exists>outcome child. comma_native_boundary_step rows q=Some outcome \<and>
      child\<in>set (comma_native_boundary_children q outcome) \<and>
      comma_literal_unbounded
        (comma_boundary_value child (p+comma_native_outcome_delta outcome))"
  show "\<exists>stream. comma_native_infinite_literal_path
      (comma_boundary_value q p) stream"
    by (rule comma_native_surviving_child_has_infinite_path
      [OF powers stops valid exponent phase successor_survives])
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint
  "surviving-child-infinite-path-bridge"\<close>

ML \<open>
  val checked = @{thms comma_native_boundary_step_def
    comma_finite_fork_digit_bounds
    comma_decade_terminal_fork_bounds
    comma_native_sparse_summary_fork_bounds
    comma_native_boundary_step_fork_digit_bounds
    comma_native_boundary_children_valid_phase
    comma_native_boundary_step_children_valid_phase
    comma_native_infinite_path_projects
    comma_native_infinite_path_projects_admitted_child
    comma_native_surviving_child_has_infinite_path
    comma_native_infinite_path_iff_successor_survival
}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native boundary projection and ranked-path proofs" checked
\<close>

end
