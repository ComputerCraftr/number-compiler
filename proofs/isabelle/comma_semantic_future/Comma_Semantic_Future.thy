theory Comma_Semantic_Future
  imports Comma_Cylinder.Comma_Finite_Transition
    Comma_Arithmetic.Comma_Boundary_Primitives
begin

text \<open>
This theory is the provider-neutral induction layer for comma safety.  A
provider publishes control (fork target or landmine), complete successor
alternatives, and a source-occurrence bridge.  The exact exponent increment
belongs to that bridge, not to control identity.  Consequently a quotient may
share control while each concrete occurrence transports its own exponent and
phase.
\<close>

datatype comma_future_control =
    Comma_Future_Fork nat
  | Comma_Future_Landmine

definition comma_semantic_infinite_path ::
  "('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_semantic_infinite_path value q p stream \<longleftrightarrow>
    stream 0 = value q p \<and>
    (\<forall>j. comma_child (stream j) (stream (Suc j)))"

definition comma_semantic_occurrence_bridge ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> 's list) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control option) \<Rightarrow> bool" where
  "comma_semantic_occurrence_bridge valid phase value exponent_delta children control_step
    \<longleftrightarrow> (\<forall>q p. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
      p mod 924 = phase q \<longrightarrow>
      (\<exists>control endpoint weight.
        control_step q = Some control \<and>
        comma_literal_path weight (value q p) endpoint \<and>
        (\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
          other = endpoint) \<and>
        distinct (children q control) \<and>
        (\<forall>child\<in>set (children q control).
          valid child \<and> 5 \<le> p + exponent_delta q control \<and>
          (p + exponent_delta q control) mod 924 = phase child) \<and>
        (case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
          | Comma_Future_Landmine \<Rightarrow> children q control = []) \<and>
        (\<forall>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>child\<in>set (children q control).
            v = value child (p + exponent_delta q control)))))"

lemma comma_semantic_occurrence_bridgeD:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
  obtains control endpoint weight where
    "control_step q = Some control"
    "comma_literal_path weight (value q p) endpoint"
    "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
      other = endpoint"
    "distinct (children q control)"
    "\<forall>child\<in>set (children q control).
      valid child \<and> 5 \<le> p + exponent_delta q control \<and>
      (p + exponent_delta q control) mod 924 = phase child"
    "case control of Comma_Future_Fork a \<Rightarrow>
        length (children q control) = 2
      | Comma_Future_Landmine \<Rightarrow> children q control = []"
    "\<forall>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (children q control).
        v = value child (p + exponent_delta q control))"
proof -
  have all_states:
    "\<forall>q p. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
      p mod 924 = phase q \<longrightarrow>
      (\<exists>control endpoint weight.
        control_step q = Some control \<and>
        comma_literal_path weight (value q p) endpoint \<and>
        (\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
          other = endpoint) \<and>
        distinct (children q control) \<and>
        (\<forall>child\<in>set (children q control).
          valid child \<and> 5 \<le> p + exponent_delta q control \<and>
          (p + exponent_delta q control) mod 924 = phase child) \<and>
        (case control of Comma_Future_Fork a \<Rightarrow>
            length (children q control) = 2
          | Comma_Future_Landmine \<Rightarrow> children q control = []) \<and>
        (\<forall>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>child\<in>set (children q control).
            v = value child (p + exponent_delta q control))))"
    using bridge by (simp only: comma_semantic_occurrence_bridge_def)
  note at_source = spec[where x=q, OF all_states]
  note at_exponent = spec[where x=p, OF at_source]
  let ?selected = "(\<exists>control endpoint weight.
    control_step q = Some control \<and>
    comma_literal_path weight (value q p) endpoint \<and>
    (\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
      other = endpoint) \<and>
    distinct (children q control) \<and>
    (\<forall>child\<in>set (children q control).
      valid child \<and> 5 \<le> p + exponent_delta q control \<and>
      (p + exponent_delta q control) mod 924 = phase child) \<and>
    (case control of Comma_Future_Fork a \<Rightarrow>
        length (children q control) = 2
      | Comma_Future_Landmine \<Rightarrow> children q control = []) \<and>
    (\<forall>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (children q control).
        v = value child (p + exponent_delta q control))))"
  have height_clause:
    "5 \<le> p \<longrightarrow> p mod 924 = phase q \<longrightarrow> ?selected"
    by (rule mp[OF at_exponent state_valid])
  have phase_clause:
    "p mod 924 = phase q \<longrightarrow> ?selected"
    by (rule mp[OF height_clause exponent])
  have selected_occurrence: ?selected
    by (rule mp[OF phase_clause phase_match])
  obtain control endpoint weight where facts:
      "control_step q = Some control"
    and occurrence: "comma_literal_path weight (value q p) endpoint"
    and unique_endpoint:
      "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
        other = endpoint"
    and alternatives: "distinct (children q control)"
    and children_admitted:
      "\<forall>child\<in>set (children q control).
        valid child \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase child"
    and complete_control:
      "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    and child_relation:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (children q control).
          v = value child (p + exponent_delta q control))"
    using selected_occurrence by blast
  show thesis
    by (rule that[OF facts occurrence unique_endpoint alternatives
      children_admitted complete_control child_relation])
qed

definition comma_semantic_rank_row_checked ::
  "('s \<Rightarrow> nat option) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> 's list) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control option) \<Rightarrow> 's \<Rightarrow> bool" where
  "comma_semantic_rank_row_checked rank children control_step q =
    (case control_step q of
       None \<Rightarrow> False
     | Some Comma_Future_Landmine \<Rightarrow>
         rank q \<noteq> None \<and> children q Comma_Future_Landmine = []
     | Some (Comma_Future_Fork a) \<Rightarrow>
         (case rank q of
            None \<Rightarrow> length (filter (\<lambda>child. rank child = None)
              (children q (Comma_Future_Fork a))) = 1
          | Some k \<Rightarrow> list_all (\<lambda>child. \<exists>j<k. rank child = Some j)
              (children q (Comma_Future_Fork a))))"

definition comma_semantic_rank_check ::
  "('s \<Rightarrow> bool) \<Rightarrow>
   ('s \<Rightarrow> nat option) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> 's list) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control option) \<Rightarrow> bool" where
  "comma_semantic_rank_check valid rank children control_step =
    (\<forall>q. valid q \<longrightarrow>
      comma_semantic_rank_row_checked rank children control_step q)"

lemma comma_semantic_rank_check_row:
  assumes checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
  shows "comma_semantic_rank_row_checked rank children control_step q"
  using checked state_valid by (simp add: comma_semantic_rank_check_def)

lemma comma_semantic_rank_check_fork_decreases:
  assumes checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and ranked: "rank q = Some k"
    and fork: "control_step q = Some (Comma_Future_Fork a)"
  shows "\<forall>child\<in>set (children q (Comma_Future_Fork a)).
    \<exists>j<k. rank child = Some j"
  using comma_semantic_rank_check_row[OF checked state_valid] ranked fork
  by (auto simp: comma_semantic_rank_row_checked_def list_all_iff
      split: option.splits
      comma_future_control.splits)

lemma comma_semantic_rank_check_unranked_fork_unique:
  assumes checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and unranked: "rank q = None"
    and fork: "control_step q = Some (Comma_Future_Fork a)"
    and distinct_children: "distinct (children q (Comma_Future_Fork a))"
  shows "\<exists>!child. child \<in> set (children q (Comma_Future_Fork a))
    \<and> rank child = None"
proof -
  let ?alternatives = "children q (Comma_Future_Fork a)"
  let ?survivors = "filter (\<lambda>child. rank child = None) ?alternatives"
  have count: "length ?survivors = 1"
    using comma_semantic_rank_check_row[OF checked state_valid] unranked fork
    by (simp add: comma_semantic_rank_row_checked_def)
  obtain child rest where survivors: "?survivors = child # rest"
    using count by (cases ?survivors) auto
  have rest_empty: "rest = []" using count survivors by simp
  have child_survivor: "child \<in> set ?survivors"
    using survivors by simp
  have child_member: "child \<in> set ?alternatives"
    using child_survivor by (auto simp: set_filter)
  have child_unranked: "rank child = None"
    using child_survivor by (auto simp: set_filter)
  have unique: "other = child"
    if member: "other \<in> set ?alternatives" and other_unranked: "rank other = None"
    for other
  proof -
    have other_member: "other \<in> set ?survivors"
      using member other_unranked by simp
    show ?thesis using other_member survivors rest_empty by simp
  qed
  show ?thesis
    using child_member child_unranked unique by blast
qed

lemma comma_semantic_rank_check_unranked_landmine_false:
  assumes checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and unranked: "rank q = None"
  shows "control_step q \<noteq> Some Comma_Future_Landmine"
  using comma_semantic_rank_check_row[OF checked state_valid] unranked
  by (auto simp: comma_semantic_rank_row_checked_def split: option.splits
      comma_future_control.splits)

lemma comma_semantic_infinite_path_projects_occurrence:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
    and path: "comma_semantic_infinite_path value q p stream"
  obtains control endpoint weight child where
    "control_step q = Some control"
    "comma_literal_path weight (value q p) endpoint"
    "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
      other = endpoint"
    "distinct (children q control)"
    "child \<in> set (children q control)"
    "stream (Suc weight) = value child (p + exponent_delta q control)"
    "valid child"
    "5 \<le> p + exponent_delta q control"
    "(p + exponent_delta q control) mod 924 = phase child"
    "\<forall>candidate\<in>set (children q control).
      valid candidate \<and> 5 \<le> p + exponent_delta q control \<and>
      (p + exponent_delta q control) mod 924 = phase candidate"
    "(case control of Comma_Future_Fork a \<Rightarrow>
        length (children q control) = 2
      | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    "\<forall>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>candidate\<in>set (children q control).
        v = value candidate (p + exponent_delta q control))"
    "comma_semantic_infinite_path value child (p + exponent_delta q control)
      (\<lambda>j. stream (weight + Suc j))"
proof -
  obtain control endpoint weight where step:
      "control_step q = Some control"
    and occurrence: "comma_literal_path weight (value q p) endpoint"
    and unique_endpoint:
      "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
        other = endpoint"
    and alternatives: "distinct (children q control)"
    and children_admitted:
      "\<forall>child\<in>set (children q control).
        valid child \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase child"
    and complete_control:
      "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    and child_relation:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (children q control).
          v = value child (p + exponent_delta q control))"
    by (rule comma_semantic_occurrence_bridgeD
      [OF bridge state_valid exponent phase_match])
  have start: "stream 0 = value q p"
    using path by (simp add: comma_semantic_infinite_path_def)
  have edges: "comma_child (stream j) (stream (Suc j))" for j
    using path by (simp add: comma_semantic_infinite_path_def)
  have prefix: "comma_literal_path weight (stream 0) (stream weight)"
    by (rule comma_infinite_literal_prefix
      [where path=stream and n=weight, OF edges])
  have prefix_at_source:
    "comma_literal_path weight (value q p) (stream weight)"
    using prefix start by (simp only: start)
  note endpoint_eq = unique_endpoint[rule_format, of "stream weight"]
  have endpoint: "stream weight = endpoint"
    by (rule endpoint_eq[OF prefix_at_source])
  have next_edge: "comma_child endpoint (stream (Suc weight))"
    using edges[of weight] endpoint by simp
  have child_relation_at:
    "comma_child endpoint (stream (Suc weight)) \<longleftrightarrow>
      (\<exists>child\<in>set (children q control).
        stream (Suc weight) = value child (p + exponent_delta q control))"
    using child_relation by (rule spec[where x="stream (Suc weight)"])
  have child_candidate:
    "\<exists>child\<in>set (children q control).
      stream (Suc weight) = value child (p + exponent_delta q control)"
    by (rule iffD1[OF child_relation_at next_edge])
  obtain child where child_member: "child \<in> set (children q control)"
    and child_value: "stream (Suc weight) = value child (p + exponent_delta q control)"
    using child_candidate by blast
  have child_valid: "valid child"
    and child_exponent: "5 \<le> p + exponent_delta q control"
    and child_phase: "(p + exponent_delta q control) mod 924 = phase child"
    using children_admitted child_member by blast+
  have tail_start:
    "(\<lambda>j. stream (weight + Suc j)) 0 =
      value child (p + exponent_delta q control)"
    using child_value by simp
  have tail_edges:
    "comma_child ((\<lambda>j. stream (weight + Suc j)) j)
      ((\<lambda>j. stream (weight + Suc j)) (Suc j))" for j
    using edges[of "weight + Suc j"] by (simp add: add.assoc)
  have tail:
    "comma_semantic_infinite_path value child (p + exponent_delta q control)
      (\<lambda>j. stream (weight + Suc j))"
    using tail_start tail_edges by (simp add: comma_semantic_infinite_path_def)
  show thesis by (rule that[OF step occurrence unique_endpoint alternatives
    child_member child_value child_valid child_exponent child_phase
    children_admitted complete_control child_relation tail])
qed

definition comma_semantic_rank_decrease_relation ::
  "('s \<Rightarrow> nat option) \<Rightarrow> ('s \<times> 's) set" where
  "comma_semantic_rank_decrease_relation rank =
    {(child,source). \<exists>j k. rank child = Some j \<and>
      rank source = Some k \<and> j < k}"

lemma comma_semantic_rank_decrease_relation_wf:
  "wf (comma_semantic_rank_decrease_relation rank)"
proof -
  let ?rank_value = "\<lambda>q. case rank q of None \<Rightarrow> 0 | Some n \<Rightarrow> n"
  have measure_wf:
    "wf (inv_image {(m,n::nat). m < n} ?rank_value)"
    by (rule wf_inv_image[OF wf_less])
  have relation_subset:
    "comma_semantic_rank_decrease_relation rank \<subseteq>
      inv_image {(m,n::nat). m < n} ?rank_value"
    unfolding comma_semantic_rank_decrease_relation_def inv_image_def by auto
  show ?thesis by (rule wf_subset[OF measure_wf relation_subset])
qed

lemma comma_semantic_ranked_state_no_infinite_path:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
    and ranked: "rank q = Some k"
  shows "\<not> comma_semantic_infinite_path value q p stream"
proof
  assume infinite: "comma_semantic_infinite_path value q p stream"
  let ?Q = "{source. \<exists>e trace n. valid source \<and> 5 \<le> e \<and>
      e mod 924 = phase source \<and> rank source = Some n \<and>
      comma_semantic_infinite_path value source e trace}"
  have q_in_Q: "q \<in> ?Q"
    using state_valid exponent phase_match ranked infinite by blast
  have Q_closed_predecessor:
    "?Q \<subseteq> comma_semantic_rank_decrease_relation rank `` ?Q"
  proof
    fix source
    assume source_in_Q: "source \<in> ?Q"
    then obtain e trace n where source_valid: "valid source"
      and e_bound: "5 \<le> e"
      and source_phase: "e mod 924 = phase source"
      and source_rank: "rank source = Some n"
      and source_path: "comma_semantic_infinite_path value source e trace"
      by blast
    obtain control endpoint weight child where step:
        "control_step source = Some control"
      and occurrence: "comma_literal_path weight (value source e) endpoint"
      and unique_endpoint:
        "\<forall>other. comma_literal_path weight (value source e) other \<longrightarrow>
          other = endpoint"
      and alternatives: "distinct (children source control)"
      and member: "child \<in> set (children source control)"
      and next_value: "trace (Suc weight) = value child (e + exponent_delta source control)"
      and child_valid: "valid child"
      and child_bound: "5 \<le> e + exponent_delta source control"
      and child_phase: "(e + exponent_delta source control) mod 924 = phase child"
      and children_admitted:
        "\<forall>candidate\<in>set (children source control).
          valid candidate \<and> 5 \<le> e + exponent_delta source control \<and>
          (e + exponent_delta source control) mod 924 = phase candidate"
      and complete_control:
        "(case control of Comma_Future_Fork a \<Rightarrow>
            length (children source control) = 2
          | Comma_Future_Landmine \<Rightarrow> children source control = [])"
      and child_relation:
        "\<forall>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>candidate\<in>set (children source control).
            v = value candidate (e + exponent_delta source control))"
      and tail: "comma_semantic_infinite_path value child
        (e + exponent_delta source control) (\<lambda>j. trace (weight + Suc j))"
      by (rule comma_semantic_infinite_path_projects_occurrence
        [OF bridge source_valid e_bound source_phase source_path])
    have not_landmine:
      "control_step source \<noteq> Some Comma_Future_Landmine"
    proof
      assume landmine: "control_step source = Some Comma_Future_Landmine"
      have control_eq: "control = Comma_Future_Landmine"
        using step landmine by simp
      have no_children: "children source Comma_Future_Landmine = []"
        using complete_control control_eq by simp
      show False using member no_children landmine step by simp
    qed
    obtain a where control_fork: "control = Comma_Future_Fork a"
      using not_landmine step by (cases control) auto
    have fork_outcome: "control_step source = Some (Comma_Future_Fork a)"
      using step control_fork by simp
    note all_children_lower = comma_semantic_rank_check_fork_decreases
      [OF checked source_valid source_rank fork_outcome]
    have fork_member: "child \<in> set (children source (Comma_Future_Fork a))"
      using member control_fork by simp
    have child_lower: "\<exists>j<n. rank child = Some j"
      by (rule bspec[OF all_children_lower fork_member])
    obtain j where lower: "j < n" and child_rank: "rank child = Some j"
      using child_lower by blast
    have child_in_Q: "child \<in> ?Q"
    proof (rule CollectI)
      show "\<exists>child_exponent child_trace child_rank_value.
          valid child \<and> 5 \<le> child_exponent \<and>
          child_exponent mod 924 = phase child \<and>
          rank child = Some child_rank_value \<and>
          comma_semantic_infinite_path value child child_exponent child_trace"
        apply (rule exI[of _ "e + exponent_delta source control"])
        apply (rule exI[of _ "\<lambda>j. trace (weight + Suc j)"])
        apply (rule exI[of _ j])
        using child_valid child_bound child_phase child_rank tail by simp
    qed
    have lower_state:
      "(child,source) \<in> comma_semantic_rank_decrease_relation rank"
      using child_rank source_rank lower
      by (auto simp: comma_semantic_rank_decrease_relation_def)
    show "source \<in> comma_semantic_rank_decrease_relation rank `` ?Q"
      using child_in_Q lower_state by blast
  qed
  have Q_empty: "?Q = {}"
    by (rule wfE_pf[OF comma_semantic_rank_decrease_relation_wf
      Q_closed_predecessor])
  have q_in_empty: "q \<in> {}"
    using q_in_Q by (simp only: Q_empty)
  show False using q_in_empty by simp
qed

lemma comma_semantic_unranked_fork:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
    and unranked: "rank q = None"
  obtains a child where
    "control_step q = Some (Comma_Future_Fork a)"
    "child \<in> set (children q (Comma_Future_Fork a))"
    "rank child = None"
    "\<And>other. other \<in> set (children q (Comma_Future_Fork a)) \<Longrightarrow>
      rank other = None \<Longrightarrow> other = child"
proof -
  obtain control endpoint prefix_weight where step:
      "control_step q = Some control"
    and occurrence: "comma_literal_path prefix_weight (value q p) endpoint"
    and unique_endpoint:
      "\<forall>other. comma_literal_path prefix_weight (value q p) other \<longrightarrow>
        other = endpoint"
    and distinct_control_children: "distinct (children q control)"
    and children_admitted:
      "\<forall>candidate\<in>set (children q control).
        valid candidate \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase candidate"
    and complete_control:
      "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    and child_relation:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>candidate\<in>set (children q control).
          v = value candidate (p + exponent_delta q control))"
    by (rule comma_semantic_occurrence_bridgeD
      [OF bridge state_valid exponent phase_match])
  have not_landmine:
    "control_step q \<noteq> Some Comma_Future_Landmine"
    by (rule comma_semantic_rank_check_unranked_landmine_false
      [OF checked state_valid unranked])
  obtain a where fork: "control_step q = Some (Comma_Future_Fork a)"
    using step not_landmine by (cases control) auto
  have control_eq: "control = Comma_Future_Fork a"
    using step fork by simp
  have distinct_children: "distinct (children q (Comma_Future_Fork a))"
    using distinct_control_children control_eq by simp
  obtain child where child_member:
      "child \<in> set (children q (Comma_Future_Fork a))"
    and child_unranked: "rank child = None"
    and child_unique: "\<And>other. other \<in> set (children q (Comma_Future_Fork a)) \<Longrightarrow>
      rank other = None \<Longrightarrow> other = child"
    using comma_semantic_rank_check_unranked_fork_unique
      [OF checked state_valid unranked fork distinct_children]
    by blast
  show thesis by (rule that[OF fork child_member child_unranked child_unique])
qed

theorem comma_semantic_unranked_state_has_unbounded_literal_paths:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
  shows "\<forall>n q p. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
    p mod 924 = phase q \<longrightarrow> rank q = None \<longrightarrow>
    (\<exists>weight\<ge>n. \<exists>target. comma_literal_path weight (value q p) target)"
proof (rule allI)
  fix n
  show "\<forall>q p. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
    p mod 924 = phase q \<longrightarrow> rank q = None \<longrightarrow>
    (\<exists>weight\<ge>n. \<exists>target. comma_literal_path weight (value q p) target)"
  proof (induction n)
    case 0
    then show ?case by (auto intro: comma_literal_path.zero)
  next
    case (Suc n)
    show ?case
    proof (intro allI impI)
      fix q p
      assume valid: "valid q" and exponent: "5 \<le> p"
        and phase_match: "p mod 924 = phase q" and unranked: "rank q = None"
      obtain a child where fork:
          "control_step q = Some (Comma_Future_Fork a)"
        and member: "child \<in> set (children q (Comma_Future_Fork a))"
        and child_unranked: "rank child = None"
        and child_unique:
          "\<And>other. other \<in> set (children q (Comma_Future_Fork a)) \<Longrightarrow>
            rank other = None \<Longrightarrow> other = child"
        using comma_semantic_unranked_fork
          [OF bridge checked valid exponent phase_match unranked]
        by blast
      obtain chart_control endpoint head_weight where chart_step:
          "control_step q = Some chart_control"
        and chart_prefix: "comma_literal_path head_weight (value q p) endpoint"
        and chart_unique_endpoint:
          "\<forall>other. comma_literal_path head_weight (value q p) other \<longrightarrow>
            other = endpoint"
        and chart_distinct_children: "distinct (children q chart_control)"
        and chart_children_admitted:
          "\<forall>candidate\<in>set (children q chart_control).
            valid candidate \<and> 5 \<le> p + exponent_delta q chart_control \<and>
            (p + exponent_delta q chart_control) mod 924 = phase candidate"
        and chart_complete_control:
          "(case chart_control of Comma_Future_Fork a \<Rightarrow>
              length (children q chart_control) = 2
            | Comma_Future_Landmine \<Rightarrow> children q chart_control = [])"
        and chart_relation:
          "\<forall>v. comma_child endpoint v \<longleftrightarrow>
            (\<exists>candidate\<in>set (children q chart_control).
              v = value candidate (p + exponent_delta q chart_control))"
        by (rule comma_semantic_occurrence_bridgeD
          [OF bridge valid exponent phase_match])
      have chart_control_is_fork: "chart_control = Comma_Future_Fork a"
        using chart_step fork by simp
      have step: "control_step q = Some (Comma_Future_Fork a)" by (rule fork)
      have prefix: "comma_literal_path head_weight (value q p) endpoint"
        by (rule chart_prefix)
      have unique_endpoint:
        "\<forall>other. comma_literal_path head_weight (value q p) other \<longrightarrow>
          other = endpoint"
        by (rule chart_unique_endpoint)
      have distinct_children: "distinct (children q (Comma_Future_Fork a))"
        using chart_distinct_children chart_control_is_fork by simp
      have children_admitted:
        "\<forall>candidate\<in>set (children q (Comma_Future_Fork a)).
          valid candidate \<and> 5 \<le> p + exponent_delta q (Comma_Future_Fork a) \<and>
          (p + exponent_delta q (Comma_Future_Fork a)) mod 924 = phase candidate"
        using chart_children_admitted chart_control_is_fork by simp
      have relation:
        "\<forall>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>candidate\<in>set (children q (Comma_Future_Fork a)).
            v = value candidate (p + exponent_delta q (Comma_Future_Fork a)))"
        using chart_relation chart_control_is_fork by simp
      let ?child_exponent = "p + exponent_delta q (Comma_Future_Fork a)"
      have child_inputs:
        "valid child \<and> 5 \<le> ?child_exponent \<and>
          ?child_exponent mod 924 = phase child"
        by (rule bspec[OF children_admitted member])
      have child_valid: "valid child"
        using child_inputs by simp
      have child_exponent: "5 \<le> ?child_exponent"
        using child_inputs by simp
      have child_phase: "?child_exponent mod 924 = phase child"
        using child_inputs by simp
      have child_candidate:
        "\<exists>candidate\<in>set (children q (Comma_Future_Fork a)).
          value child ?child_exponent = value candidate ?child_exponent"
      proof
        show "child \<in> set (children q (Comma_Future_Fork a))"
          by fact
        show "value child ?child_exponent = value child ?child_exponent"
          by (rule refl)
      qed
      have relation_at:
        "comma_child endpoint (value child ?child_exponent) \<longleftrightarrow>
          (\<exists>candidate\<in>set (children q (Comma_Future_Fork a)).
            value child ?child_exponent = value candidate ?child_exponent)"
        using relation by (rule spec[where x="value child ?child_exponent"])
      have child_edge:
        "comma_child endpoint (value child ?child_exponent)"
        by (rule iffD2[OF relation_at child_candidate])
      have positive_prefix:
        "comma_literal_path (Suc head_weight) (value q p)
          (value child ?child_exponent)"
        by (rule comma_literal_path_snoc[OF prefix child_edge])
      have child_path_bound:
        "\<exists>tail_weight\<ge>n. \<exists>target.
          comma_literal_path tail_weight (value child ?child_exponent) target"
      proof (rule Suc.IH[rule_format, of child ?child_exponent])
        show "valid child" by (rule child_valid)
        show "5 \<le> ?child_exponent" by (rule child_exponent)
        show "?child_exponent mod 924 = phase child" by (rule child_phase)
        show "rank child = None" by (rule child_unranked)
      qed
      obtain tail_weight target where tail_bound: "n \<le> tail_weight"
        and tail_path: "comma_literal_path tail_weight
          (value child ?child_exponent) target"
        using child_path_bound by blast
      have joined:
        "comma_literal_path (Suc head_weight + tail_weight) (value q p) target"
        by (rule comma_literal_path_append[OF positive_prefix tail_path])
      have bound: "Suc n \<le> Suc head_weight + tail_weight"
        using tail_bound by arith
      show "\<exists>weight\<ge>Suc n. \<exists>target.
          comma_literal_path weight (value q p) target"
      proof (rule exI[of _ "Suc head_weight + tail_weight"])
        show "Suc n \<le> Suc head_weight + tail_weight \<and>
            (\<exists>target. comma_literal_path
              (Suc head_weight + tail_weight) (value q p) target)"
        proof (rule conjI)
          show "Suc n \<le> Suc head_weight + tail_weight"
            by (rule bound)
          show "\<exists>target. comma_literal_path
              (Suc head_weight + tail_weight) (value q p) target"
            by (rule exI[of _ target]; rule joined)
        qed
      qed
    qed
  qed
qed

theorem comma_semantic_unranked_state_has_infinite_path:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
    and unranked: "rank q = None"
  shows "\<exists>stream. comma_semantic_infinite_path value q p stream"
proof -
  have unbounded: "comma_literal_unbounded (value q p)"
    unfolding comma_literal_unbounded_def
  proof (intro allI)
    fix bound
    note all_bounds = comma_semantic_unranked_state_has_unbounded_literal_paths
      [OF bridge checked]
    note at_bound = spec[where x=bound, OF all_bounds]
    note at_source = spec[where x=q, OF at_bound]
    note at_exponent = spec[where x=p, OF at_source]
    obtain weight target where enough: "bound \<le> weight"
      and path: "comma_literal_path weight (value q p) target"
      using at_exponent state_valid exponent phase_match unranked by blast
    show "\<exists>weight\<ge>bound. \<exists>target.
        comma_literal_path weight (value q p) target"
      using enough path by blast
  qed
  obtain stream where path: "stream 0 = value q p"
    and edges: "\<And>j. comma_child (stream j) (stream (Suc j))"
    using comma_literal_unbounded_infinite_path[OF unbounded] by blast
  show ?thesis
    unfolding comma_semantic_infinite_path_def
    by (rule exI[of _ stream], use path edges in blast)
qed

theorem comma_semantic_infinite_path_forces_unique_unranked_child:
  assumes bridge: "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
    and path: "comma_semantic_infinite_path value q p stream"
  obtains control endpoint weight child tail where
    "control_step q = Some control"
    "comma_literal_path weight (value q p) endpoint"
    "child \<in> set (children q control)"
    "stream (Suc weight) = value child (p + exponent_delta q control)"
    "valid child"
    "5 \<le> p + exponent_delta q control"
    "(p + exponent_delta q control) mod 924 = phase child"
    "comma_semantic_infinite_path value child (p + exponent_delta q control) tail"
    "rank q = None"
    "rank child = None"
    "\<forall>other\<in>set (children q control).
      other \<noteq> child \<longrightarrow> rank other \<noteq> None"
proof -
  have source_unranked: "rank q = None"
  proof (cases "rank q")
    case None
    then show ?thesis .
  next
    case (Some k)
    have no_path: "\<not> comma_semantic_infinite_path value q p stream"
      by (rule comma_semantic_ranked_state_no_infinite_path
        [OF bridge checked state_valid exponent phase_match Some])
    show ?thesis using no_path path by contradiction
  qed
  obtain control endpoint weight child where step:
      "control_step q = Some control"
    and occurrence: "comma_literal_path weight (value q p) endpoint"
    and unique_endpoint:
      "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
        other = endpoint"
    and alternatives: "distinct (children q control)"
    and member: "child \<in> set (children q control)"
    and next_value: "stream (Suc weight) = value child (p + exponent_delta q control)"
    and child_valid: "valid child"
    and child_exponent: "5 \<le> p + exponent_delta q control"
    and child_phase: "(p + exponent_delta q control) mod 924 = phase child"
    and children_admitted:
      "\<forall>candidate\<in>set (children q control).
        valid candidate \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase candidate"
    and complete_control:
      "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    and child_relation:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>candidate\<in>set (children q control).
          v = value candidate (p + exponent_delta q control))"
    and tail: "comma_semantic_infinite_path value child
      (p + exponent_delta q control) (\<lambda>j. stream (weight + Suc j))"
    by (rule comma_semantic_infinite_path_projects_occurrence
      [OF bridge state_valid exponent phase_match path])
  have control_not_landmine:
    "control \<noteq> Comma_Future_Landmine"
  proof
    assume landmine: "control = Comma_Future_Landmine"
    have no_children: "children q Comma_Future_Landmine = []"
      using complete_control landmine by simp
    show False using member no_children landmine by simp
  qed
  obtain a where fork: "control = Comma_Future_Fork a"
    using control_not_landmine by (cases control) auto
  have fork_step: "control_step q = Some (Comma_Future_Fork a)"
    using step fork by simp
  have child_unranked: "rank child = None"
  proof (cases "rank child")
    case None
    then show ?thesis .
  next
    case (Some j)
    have no_tail:
      "\<not> comma_semantic_infinite_path value child
        (p + exponent_delta q control) (\<lambda>j. stream (weight + Suc j))"
      by (rule comma_semantic_ranked_state_no_infinite_path
        [OF bridge checked child_valid child_exponent child_phase Some])
    show ?thesis using no_tail tail by contradiction
  qed
  have distinct_children: "distinct (children q (Comma_Future_Fork a))"
    using alternatives fork by simp
  have fork_member: "child \<in> set (children q (Comma_Future_Fork a))"
    using member fork by simp
  have unique_unranked:
    "\<exists>!candidate. candidate \<in> set (children q (Comma_Future_Fork a))
      \<and> rank candidate = None"
    by (rule comma_semantic_rank_check_unranked_fork_unique
      [OF checked state_valid source_unranked fork_step distinct_children])
  have child_unranked_member:
    "child \<in> set (children q (Comma_Future_Fork a)) \<and>
      rank child = None"
    using fork_member child_unranked by simp
  have child_unique:
    "\<And>other. other \<in> set (children q (Comma_Future_Fork a)) \<Longrightarrow>
      rank other = None \<Longrightarrow> other = child"
  proof -
    fix other
    assume other_member: "other \<in> set (children q (Comma_Future_Fork a))"
      and other_unranked: "rank other = None"
    have other_unranked_member:
      "other \<in> set (children q (Comma_Future_Fork a)) \<and>
        rank other = None"
      using other_member other_unranked by simp
    show "other = child"
      using unique_unranked child_unranked_member other_unranked_member by blast
  qed
  have control_eq: "control = Comma_Future_Fork a" by (rule fork)
  have sibling_ranked:
    "\<forall>other\<in>set (children q (Comma_Future_Fork a)).
      other \<noteq> child \<longrightarrow> rank other \<noteq> None"
  proof (intro ballI impI)
    fix other
    assume other_member: "other \<in> set (children q (Comma_Future_Fork a))"
      and different: "other \<noteq> child"
    show "rank other \<noteq> None"
    proof
      assume other_unranked: "rank other = None"
      have same: "other = child" by (rule child_unique[OF other_member other_unranked])
      show False using same different by simp
    qed
  qed
  have sibling_ranked_control:
    "\<forall>other\<in>set (children q control).
      other \<noteq> child \<longrightarrow> rank other \<noteq> None"
    using sibling_ranked control_eq by simp
  show thesis
    by (rule that[OF step occurrence member next_value child_valid child_exponent
      child_phase tail source_unranked child_unranked sibling_ranked_control])
qed

lemma comma_semantic_rank_check_lifts_through_class_map:
  fixes valid_occurrence :: "'s \<Rightarrow> bool"
    and rank_class :: "'c \<Rightarrow> nat option"
    and children_class :: "'c \<Rightarrow> comma_future_control \<Rightarrow> 'c list"
    and step_class :: "'c \<Rightarrow> comma_future_control option"
    and class_of :: "'s \<Rightarrow> 'c"
    and children_occurrence :: "'s \<Rightarrow> comma_future_control \<Rightarrow> 's list"
    and step_occurrence :: "'s \<Rightarrow> comma_future_control option"
  assumes class_checked:
      "comma_semantic_rank_check valid_class rank_class children_class step_class"
    and maps_valid: "\<And>q. valid_occurrence q \<Longrightarrow> valid_class (class_of q)"
    and maps_step: "\<And>q. valid_occurrence q \<Longrightarrow>
      step_occurrence q = step_class (class_of q)"
    and maps_children: "\<And>q control. valid_occurrence q \<Longrightarrow>
      map class_of (children_occurrence q control) =
        children_class (class_of q) control"
  shows "comma_semantic_rank_check valid_occurrence
      (rank_class \<circ> class_of) children_occurrence step_occurrence"
proof (unfold comma_semantic_rank_check_def, intro allI impI)
  fix q
  assume q_valid: "valid_occurrence q"
  have c_valid: "valid_class (class_of q)" using maps_valid[OF q_valid] .
  have row_class:
    "comma_semantic_rank_row_checked rank_class children_class step_class (class_of q)"
    by (rule comma_semantic_rank_check_row[OF class_checked c_valid])
  have children_eq:
    "children_class (class_of q) control =
      map class_of (children_occurrence q control)"
    for control
    using maps_children[OF q_valid, of control] by simp
  show "comma_semantic_rank_row_checked (rank_class \<circ> class_of)
      children_occurrence step_occurrence q"
    using row_class maps_step[OF q_valid] children_eq
    by (cases "step_class (class_of q)")
      (auto simp: comma_semantic_rank_row_checked_def list_all_iff comp_def
        filter_map split: comma_future_control.splits option.splits)
qed

ML \<open>
  val checked = @{thms comma_semantic_occurrence_bridgeD
    comma_semantic_infinite_path_projects_occurrence
    comma_semantic_rank_check_fork_decreases
    comma_semantic_rank_check_unranked_fork_unique
    comma_semantic_rank_check_unranked_landmine_false
    comma_semantic_ranked_state_no_infinite_path
    comma_semantic_unranked_fork
    comma_semantic_unranked_state_has_unbounded_literal_paths
    comma_semantic_unranked_state_has_infinite_path
    comma_semantic_infinite_path_forces_unique_unranked_child
    comma_semantic_rank_check_lifts_through_class_map}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Semantic future safety depends on a theorem oracle"
\<close>

end
