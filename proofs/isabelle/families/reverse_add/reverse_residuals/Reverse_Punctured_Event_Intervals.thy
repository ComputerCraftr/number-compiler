theory Reverse_Punctured_Event_Intervals
  imports Reverse_Punctured_Run_Pairing
begin

text \<open>The temporal pullback samples each coefficient at the beginning of
an event interval and at its last cell. The runtime event cuts surround every
source-run boundary and carry-switch boundary, together with their reflected
positions, by two cells. The next lemmas state that cut rule over the exact
source and carry prefix functions used by the pointwise coefficient theorem.
They prove local interval constancy; they do not prove the separate temporal
choice of the no-growth/growth branch.\<close>

definition punctured_source_change_points :: "nat list \<Rightarrow> nat set" where
  "punctured_source_change_points ss =
    {p. 0 < p \<and> p < length ss \<and> ss ! (p - 1) \<noteq> ss ! p}"

definition punctured_carry_change_points :: "nat list \<Rightarrow> nat set" where
  "punctured_carry_change_points ss =
    {p. 0 < p \<and> p \<le> length ss \<and>
      punctured_prefix_carry ss (p - 1) \<noteq> punctured_prefix_carry ss p}"

definition punctured_event_centres :: "nat list \<Rightarrow> nat set" where
  "punctured_event_centres ss =
    {0, length ss} \<union>
      punctured_source_change_points ss \<union>
      punctured_carry_change_points ss \<union>
      (\<lambda>p. length ss - p) `
        (punctured_source_change_points ss \<union>
          punctured_carry_change_points ss)"

definition punctured_event_positions :: "nat list \<Rightarrow> nat \<Rightarrow> nat set" where
  "punctured_event_positions ss extent =
    {p. p \<le> extent \<and>
      (\<exists>centre\<in>punctured_event_centres ss.
        centre \<le> p + 2 \<and> p \<le> centre + 2)}"

lemma punctured_event_position_near_centre:
  assumes centre: "c \<in> punctured_event_centres ss"
      and above: "c \<le> p + 2"
      and below: "p \<le> c + 2"
      and bound: "p \<le> extent"
  shows "p \<in> punctured_event_positions ss extent"
  using assms by (auto simp: punctured_event_positions_def)

definition punctured_consecutive_events :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "punctured_consecutive_events events start stop \<longleftrightarrow>
    start \<in> events \<and> stop \<in> events \<and> start < stop \<and>
      (\<forall>p\<in>events. p \<le> start \<or> stop \<le> p)"

definition punctured_no_growth_control :: "nat list \<Rightarrow> nat \<Rightarrow>
    nat \<times> (bool \<times> (bool \<times> (bool \<times> bool)))" where
  "punctured_no_growth_control ss i =
    (ss ! i,
      (punctured_prefix_carry ss i,
        (punctured_prefix_carry ss (length ss - Suc i),
          (punctured_prefix_carry ss (Suc i),
            punctured_prefix_carry ss (length ss - i)))))"

definition punctured_growth_control :: "nat list \<Rightarrow> nat \<Rightarrow>
    nat \<times> (nat \<times> (bool \<times> (bool \<times> (bool \<times> bool))))" where
  "punctured_growth_control ss i =
    (ss ! (i - 1),
      (ss ! i,
        (punctured_prefix_carry ss i,
          (punctured_prefix_carry ss (length ss - i),
            (punctured_prefix_carry ss (Suc i),
              punctured_prefix_carry ss (Suc (length ss - i)))))))"

lemma punctured_no_growth_control_change_is_event:
  assumes bound: "Suc i < length ss"
      and extent: "length ss \<le> output_extent"
      and changed: "punctured_no_growth_control ss i \<noteq>
        punctured_no_growth_control ss (Suc i)"
  shows "Suc i \<in> punctured_event_positions ss output_extent"
proof -
  let ?event = "Suc i"
  have different:
    "ss ! i \<noteq> ss ! Suc i \<or>
      punctured_prefix_carry ss i \<noteq> punctured_prefix_carry ss (Suc i) \<or>
      punctured_prefix_carry ss (length ss - Suc i) \<noteq>
        punctured_prefix_carry ss (length ss - Suc (Suc i)) \<or>
      punctured_prefix_carry ss (Suc i) \<noteq>
        punctured_prefix_carry ss (Suc (Suc i)) \<or>
      punctured_prefix_carry ss (length ss - i) \<noteq>
        punctured_prefix_carry ss (length ss - Suc i)"
    using changed by (auto simp: punctured_no_growth_control_def)
  from different consider
    (source) "ss ! i \<noteq> ss ! Suc i" |
    (incoming) "punctured_prefix_carry ss i \<noteq>
      punctured_prefix_carry ss (Suc i)" |
    (reflected_incoming) "punctured_prefix_carry ss (length ss - Suc i) \<noteq>
      punctured_prefix_carry ss (length ss - Suc (Suc i))" |
    (outgoing) "punctured_prefix_carry ss (Suc i) \<noteq>
      punctured_prefix_carry ss (Suc (Suc i))" |
    (reflected_outgoing) "punctured_prefix_carry ss (length ss - i) \<noteq>
      punctured_prefix_carry ss (length ss - Suc i)"
    by blast
  then have event: "?event \<in> punctured_event_positions ss output_extent"
  proof cases
    case source
    have centre: "Suc i \<in> punctured_event_centres ss"
      using source bound
      by (auto simp: punctured_event_centres_def
          punctured_source_change_points_def)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case incoming
    have centre: "Suc i \<in> punctured_event_centres ss"
      using incoming bound
      by (auto simp: punctured_event_centres_def
          punctured_carry_change_points_def punctured_prefix_carry_def)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case reflected_incoming
    let ?p = "length ss - Suc i"
    have previous: "?p - 1 = length ss - Suc (Suc i)"
      using bound by arith
    have carry_point: "?p \<in> punctured_carry_change_points ss"
      using reflected_incoming bound previous
      by (auto simp: punctured_carry_change_points_def
          punctured_prefix_carry_def; arith)
    have centre: "length ss - ?p \<in> punctured_event_centres ss"
      using carry_point by (auto simp: punctured_event_centres_def)
    have reflected: "length ss - ?p = Suc i"
      using bound by arith
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use reflected bound extent in arith)
  next
    case outgoing
    let ?p = "Suc (Suc i)"
    have centre: "?p \<in> punctured_event_centres ss"
      using outgoing bound
      by (auto simp: punctured_event_centres_def
          punctured_carry_change_points_def punctured_prefix_carry_def; arith)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case reflected_outgoing
    let ?p = "length ss - i"
    have previous: "?p - 1 = length ss - Suc i"
      using bound by arith
    have carry_point: "?p \<in> punctured_carry_change_points ss"
      using reflected_outgoing bound previous
      by (auto simp: punctured_carry_change_points_def
          punctured_prefix_carry_def; arith)
    have centre: "length ss - ?p \<in> punctured_event_centres ss"
      using carry_point by (auto simp: punctured_event_centres_def)
    have reflected: "length ss - ?p = i" using bound by arith
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use reflected bound extent in arith)
  qed
  from event show ?thesis .
qed

lemma punctured_growth_control_change_is_event:
  assumes bound: "0 < i" "Suc i < length ss"
      and extent: "length ss \<le> output_extent"
      and changed: "punctured_growth_control ss i \<noteq>
        punctured_growth_control ss (Suc i)"
  shows "Suc i \<in> punctured_event_positions ss output_extent"
proof -
  let ?event = "Suc i"
  have different:
    "ss ! (i - 1) \<noteq> ss ! i \<or>
      ss ! i \<noteq> ss ! Suc i \<or>
      punctured_prefix_carry ss i \<noteq> punctured_prefix_carry ss (Suc i) \<or>
      punctured_prefix_carry ss (length ss - i) \<noteq>
        punctured_prefix_carry ss (length ss - Suc i) \<or>
      punctured_prefix_carry ss (Suc i) \<noteq>
        punctured_prefix_carry ss (Suc (Suc i)) \<or>
      punctured_prefix_carry ss (Suc (length ss - i)) \<noteq>
        punctured_prefix_carry ss (Suc (length ss - Suc i))"
    using changed by (auto simp: punctured_growth_control_def)
  from different consider
    (left_source) "ss ! (i - 1) \<noteq> ss ! i" |
    (right_source) "ss ! i \<noteq> ss ! Suc i" |
    (incoming) "punctured_prefix_carry ss i \<noteq>
      punctured_prefix_carry ss (Suc i)" |
    (reflected_incoming) "punctured_prefix_carry ss (length ss - i) \<noteq>
      punctured_prefix_carry ss (length ss - Suc i)" |
    (outgoing) "punctured_prefix_carry ss (Suc i) \<noteq>
      punctured_prefix_carry ss (Suc (Suc i))" |
    (reflected_outgoing) "punctured_prefix_carry ss (Suc (length ss - i)) \<noteq>
      punctured_prefix_carry ss (Suc (length ss - Suc i))"
    by blast
  then have event: "?event \<in> punctured_event_positions ss output_extent"
  proof cases
    case left_source
    have centre: "i \<in> punctured_event_centres ss"
      using left_source bound
      by (auto simp: punctured_event_centres_def
          punctured_source_change_points_def)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case right_source
    have centre: "Suc i \<in> punctured_event_centres ss"
      using right_source bound
      by (auto simp: punctured_event_centres_def
          punctured_source_change_points_def)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case incoming
    have centre: "Suc i \<in> punctured_event_centres ss"
      using incoming bound
      by (auto simp: punctured_event_centres_def
          punctured_carry_change_points_def punctured_prefix_carry_def)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case reflected_incoming
    let ?p = "length ss - i"
    have previous: "?p - 1 = length ss - Suc i"
      using bound by arith
    have carry_point: "?p \<in> punctured_carry_change_points ss"
      using reflected_incoming bound previous
      by (auto simp: punctured_carry_change_points_def
          punctured_prefix_carry_def; arith)
    have centre: "length ss - ?p \<in> punctured_event_centres ss"
      using carry_point by (auto simp: punctured_event_centres_def)
    have reflected: "length ss - ?p = i" using bound by arith
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use reflected bound extent in arith)
  next
    case outgoing
    let ?p = "Suc (Suc i)"
    have centre: "?p \<in> punctured_event_centres ss"
      using outgoing bound
      by (auto simp: punctured_event_centres_def
          punctured_carry_change_points_def punctured_prefix_carry_def; arith)
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use bound extent in arith)
  next
    case reflected_outgoing
    let ?p = "Suc (length ss - i)"
    have previous: "?p - 1 = length ss - i" by simp
    have following: "Suc (length ss - Suc i) = length ss - i"
      using bound by arith
    have carry_point: "?p \<in> punctured_carry_change_points ss"
      using reflected_outgoing bound previous following
      by (auto simp: punctured_carry_change_points_def
          punctured_prefix_carry_def; arith)
    have centre: "length ss - ?p \<in> punctured_event_centres ss"
      using carry_point by (auto simp: punctured_event_centres_def)
    have reflected: "length ss - ?p = i - 1" using bound by arith
    show ?thesis
      by (rule punctured_event_position_near_centre[OF centre];
         use reflected bound extent in arith)
  qed
  show ?thesis using event extent
    by (auto simp: punctured_event_positions_def)
qed

theorem punctured_no_growth_event_interval_refines_step:
  assumes valid: "valid_pair ss"
      and no_growth: "\<not> carry_out False ss"
      and interval: "punctured_consecutive_events
        (punctured_event_positions ss (length ss)) start stop"
      and output_bound: "stop \<le> length ss"
  shows "\<forall>i\<in>{start..<stop - 1}. step ss ! i = step ss ! Suc i"
proof (intro ballI)
  fix i
  assume index: "i \<in> {start..<stop - 1}"
  have i_bound: "i < length ss" using index output_bound interval
    by (auto simp: punctured_consecutive_events_def; arith)
  have next_bound: "Suc i < length ss" using index output_bound interval
    by (auto simp: punctured_consecutive_events_def; arith)
  have internal_event: "start < Suc i \<and> Suc i < stop"
    using index by auto
  have controls: "punctured_no_growth_control ss i =
      punctured_no_growth_control ss (Suc i)"
  proof (rule ccontr)
    assume different: "punctured_no_growth_control ss i \<noteq>
        punctured_no_growth_control ss (Suc i)"
    have is_event: "Suc i \<in> punctured_event_positions ss (length ss)"
      by (rule punctured_no_growth_control_change_is_event
          [OF next_bound _ different]) simp
    from interval internal_event is_event show False
      by (auto simp: punctured_consecutive_events_def)
  qed
  have coefficients:
    "punctured_no_growth_coefficient ss i =
      punctured_no_growth_coefficient ss (Suc i)"
    using controls by (simp add: punctured_no_growth_control_def
      punctured_no_growth_coefficient_def)
  have left:
    "punctured_no_growth_coefficient ss i = step ss ! i"
    by (rule punctured_no_growth_coefficient_refines_step[OF valid no_growth i_bound])
  have right:
    "punctured_no_growth_coefficient ss (Suc i) = step ss ! Suc i"
    by (rule punctured_no_growth_coefficient_refines_step[OF valid no_growth next_bound])
  show "step ss ! i = step ss ! Suc i"
    using left right coefficients by simp
qed

theorem punctured_growth_event_interval_refines_step:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
      and interval: "punctured_consecutive_events
        (punctured_event_positions ss (Suc (length ss))) start stop"
      and interior: "0 < start"
      and output_bound: "stop \<le> length ss"
  shows "\<forall>i\<in>{start..<stop - 1}. step ss ! i = step ss ! Suc i"
proof (intro ballI)
  fix i
  assume index: "i \<in> {start..<stop - 1}"
  have i_positive: "0 < i" using interior index by simp
  have i_bound: "i < length ss" using index output_bound interval
    by (auto simp: punctured_consecutive_events_def; arith)
  have next_bound: "Suc i < length ss" using index output_bound interval
    by (auto simp: punctured_consecutive_events_def; arith)
  have internal_event: "start < Suc i \<and> Suc i < stop"
    using index by auto
  have controls: "punctured_growth_control ss i =
      punctured_growth_control ss (Suc i)"
  proof (rule ccontr)
    assume different: "punctured_growth_control ss i \<noteq>
        punctured_growth_control ss (Suc i)"
    have is_event: "Suc i \<in> punctured_event_positions ss (Suc (length ss))"
      by (rule punctured_growth_control_change_is_event
          [OF i_positive next_bound _ different]) simp
    from interval internal_event is_event show False
      by (auto simp: punctured_consecutive_events_def)
  qed
  have coefficients:
    "punctured_growth_interior_coefficient ss i =
      punctured_growth_interior_coefficient ss (Suc i)"
    using controls by (simp add: punctured_growth_control_def
      punctured_growth_interior_coefficient_def)
  have left:
    "punctured_growth_interior_coefficient ss i = step ss ! i"
    by (rule punctured_growth_interior_coefficient_refines_step
        [OF valid growth i_positive i_bound])
  have right:
    "punctured_growth_interior_coefficient ss (Suc i) = step ss ! Suc i"
    by (rule punctured_growth_interior_coefficient_refines_step[OF valid growth])
       (simp_all add: next_bound)
  show "step ss ! i = step ss ! Suc i"
    using left right coefficients by simp
qed

ML \<open>
  val checked = @{thms punctured_no_growth_control_change_is_event
    punctured_growth_control_change_is_event
    punctured_no_growth_event_interval_refines_step
    punctured_growth_event_interval_refines_step};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Punctured event intervals depend on a theorem oracle";
\<close>

end
