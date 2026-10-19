theory Double_Reverse_Packed_Request_Refinement
  imports Double_Reverse_Source_Slice_Refinement
begin

text \<open>This theory connects the bounded packed digit consumer's request
coordinates to the already-proved full-halo source-window refinement.  The
source grammar below denotes the admitted finite source row; it does not
model HashLife arena issuance, cache ownership, or worklist execution.

The runtime computes a request's causal interval from the exact border birth
count, merges overlapping intervals, extracts the entire merged interval
(with one extra right source cell when its length is even), and then indexes
the shrunken output row.  The lemmas here prove those coordinate conversions,
including the even-request one-cell displacement, before invoking the
bitplane/ring theorem.  A periodic row certificate is still required for the
whole extracted source interval, including its halo.\<close>

definition double_reverse_runtime_growth_ports ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_runtime_growth_ports phase steps =
    (steps div 2 +
       (if phase mod 4 = 2 \<or> phase mod 4 = 3 then steps mod 2 else 0),
     steps div 2 +
       (if phase mod 4 = 0 \<or> phase mod 4 = 3 then steps mod 2 else 0))"

lemma double_reverse_runtime_growth_ports_exact:
  assumes phase: "phase < 4"
  shows "double_reverse_runtime_growth_ports phase steps =
    double_reverse_growth_trace steps phase"
proof (cases "even steps")
  case True
  then obtain returns where steps_eq: "steps = 2 * returns"
    by (rule evenE)
  show ?thesis
    unfolding double_reverse_runtime_growth_ports_def steps_eq
    using double_reverse_growth_trace_even[OF phase, of returns]
    by simp
next
  case False
  then obtain returns where steps_eq: "steps = 2 * returns + 1"
    by (rule oddE)
  have trace_sum:
    "double_reverse_growth_trace (2*returns+1) phase =
      double_reverse_growth_then
        (double_reverse_growth_trace (2*returns) phase)
        (double_reverse_growth_trace 1
          (double_reverse_phase_after (2*returns) phase))"
    by (rule double_reverse_growth_trace_add)
  have phase_return:
    "double_reverse_phase_after (2*returns) phase = phase"
    using phase unfolding double_reverse_phase_after_def by presburger
  have even_trace:
    "double_reverse_growth_trace (2*returns) phase = (returns,returns)"
    by (rule double_reverse_growth_trace_even[OF phase])
  have one_trace:
    "double_reverse_growth_trace 1 phase =
       (double_reverse_left_birth phase, double_reverse_right_birth phase)"
    by (simp add: double_reverse_growth_then_def)
  have trace_formula:
    "double_reverse_growth_trace steps phase =
      (returns + double_reverse_left_birth phase,
       returns + double_reverse_right_birth phase)"
    using steps_eq trace_sum phase_return even_trace one_trace
    by (simp add: double_reverse_growth_then_def)
  have phase_cases:
    "phase = 0 \<or> phase = 1 \<or> phase = 2 \<or> phase = 3"
    using phase by presburger
  have ports_formula:
    "double_reverse_runtime_growth_ports phase steps =
      (returns + double_reverse_left_birth phase,
       returns + double_reverse_right_birth phase)"
    using phase_cases
    unfolding double_reverse_runtime_growth_ports_def steps_eq
    by (auto simp: double_reverse_left_birth_def
        double_reverse_right_birth_def)
  show ?thesis
    by (rule trans[OF ports_formula trace_formula[symmetric]])
qed

definition double_reverse_packed_request_padding :: "nat \<Rightarrow> nat" where
  "double_reverse_packed_request_padding count =
    (if even count then 1 else 0)"

definition double_reverse_packed_request_begin ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_request_begin phase steps start count =
    int start - int (fst (double_reverse_runtime_growth_ports phase steps)) -
      int steps - int (double_reverse_packed_request_padding count)"

definition double_reverse_packed_request_end ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_request_end phase steps start count =
    int start - int (fst (double_reverse_runtime_growth_ports phase steps)) +
      int count + int steps"

definition double_reverse_packed_request_center ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_request_center phase steps start count =
    int start - int (fst (double_reverse_runtime_growth_ports phase steps)) +
      int ((count - 1) div 2)"

definition double_reverse_packed_request_radius ::
    "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_packed_request_radius steps count = steps + count div 2"

definition double_reverse_packed_runtime_request_begin ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_runtime_request_begin phase steps start count =
    double_reverse_packed_request_center phase steps start count -
      int (double_reverse_packed_request_radius steps count)"

definition double_reverse_packed_runtime_request_end ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_runtime_request_end phase steps start count =
    double_reverse_packed_request_center phase steps start count +
      int (double_reverse_packed_request_radius steps count) + 1"

lemma double_reverse_packed_request_geometry:
  assumes positive: "0 < count"
  shows "double_reverse_packed_request_center phase steps start count -
      int (double_reverse_packed_request_radius steps count) =
        double_reverse_packed_request_begin phase steps start count"
    and "double_reverse_packed_request_center phase steps start count +
      int (double_reverse_packed_request_radius steps count) + 1 =
        double_reverse_packed_request_end phase steps start count"
proof -
  have even_split:
    "even count \<Longrightarrow> count = 2 * (count div 2)"
    by presburger
  have odd_split:
    "\<not> even count \<Longrightarrow> count = 2 * (count div 2) + 1"
    by presburger
  have padded_quotient:
    "(count - 1) div 2 + double_reverse_packed_request_padding count =
      count div 2"
  proof (cases "even count")
    case True
    have quotient: "(count - 1) div 2 + 1 = count div 2"
      using positive True by presburger
    show ?thesis using True quotient
      by (simp add: double_reverse_packed_request_padding_def)
  next
    case False
    have quotient: "(count - 1) div 2 = count div 2"
      using False by presburger
    show ?thesis using False quotient
      by (simp add: double_reverse_packed_request_padding_def)
  qed
  have padded_quotient_int:
    "int ((count - 1) div 2) +
        int (double_reverse_packed_request_padding count) =
      int (count div 2)"
  proof -
    have lifted:
      "int ((count - 1) div 2 + double_reverse_packed_request_padding count) =
        int (count div 2)"
      by (rule arg_cong[where f="int", OF padded_quotient])
    show ?thesis using lifted by (simp only: of_nat_add)
  qed
  have center_quotient:
    "(count - 1) div 2 + count div 2 + 1 = count"
  proof (cases "even count")
    case True
    have decomposition: "count = 2 * (count div 2)"
      using True by presburger
    have quotient: "(count - 1) div 2 + 1 = count div 2"
      using positive True by presburger
    show ?thesis using decomposition quotient by arith
  next
    case False
    have decomposition: "count = 2 * (count div 2) + 1"
      using False by presburger
    have quotient: "(count - 1) div 2 = count div 2"
      using False by presburger
    show ?thesis using decomposition quotient by arith
  qed
  have center_quotient_int:
    "int ((count - 1) div 2) + int (count div 2) + 1 = int count"
  proof -
    have lifted:
      "int ((count - 1) div 2 + count div 2 + 1) = int count"
      by (rule arg_cong[where f="int", OF center_quotient])
    show ?thesis using lifted
      by (simp only: of_nat_add of_nat_numeral)
  qed
  show first:
    "double_reverse_packed_request_center phase steps start count -
      int (double_reverse_packed_request_radius steps count) =
        double_reverse_packed_request_begin phase steps start count"
    unfolding double_reverse_packed_request_center_def
      double_reverse_packed_request_radius_def
      double_reverse_packed_request_begin_def
    using padded_quotient_int
    by (simp only: of_nat_add; linarith)
  show second:
    "double_reverse_packed_request_center phase steps start count +
      int (double_reverse_packed_request_radius steps count) + 1 =
        double_reverse_packed_request_end phase steps start count"
    unfolding double_reverse_packed_request_center_def
      double_reverse_packed_request_radius_def
      double_reverse_packed_request_end_def
    using center_quotient_int
    by (simp only: of_nat_add; linarith)
qed

lemma double_reverse_packed_runtime_request_geometry:
  assumes positive: "0 < count"
  shows "double_reverse_packed_runtime_request_begin phase steps start count =
      double_reverse_packed_request_begin phase steps start count"
    and "double_reverse_packed_runtime_request_end phase steps start count =
      double_reverse_packed_request_end phase steps start count"
  using double_reverse_packed_request_geometry[OF positive, of phase steps start]
  unfolding double_reverse_packed_runtime_request_begin_def
    double_reverse_packed_runtime_request_end_def by simp_all

definition double_reverse_packed_merged_radius :: "nat \<Rightarrow> nat" where
  "double_reverse_packed_merged_radius span = span div 2"

definition double_reverse_packed_merged_source_cells :: "nat \<Rightarrow> nat" where
  "double_reverse_packed_merged_source_cells span =
    2 * double_reverse_packed_merged_radius span + 1"

definition double_reverse_packed_merged_output_cells ::
    "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_packed_merged_output_cells span steps =
    double_reverse_packed_merged_source_cells span - 2 * steps"

definition double_reverse_packed_row_position ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_packed_row_position phase steps start count merged_begin position =
    nat (int start -
      int (fst (double_reverse_runtime_growth_ports phase steps)) -
      merged_begin - int steps) + position"

definition double_reverse_packed_runtime_output_start ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "double_reverse_packed_runtime_output_start phase steps start merged_begin =
    int start - int (fst (double_reverse_runtime_growth_ports phase steps)) -
      merged_begin - int steps"

lemma double_reverse_packed_merged_source_cells_bounds:
  "span \<le> double_reverse_packed_merged_source_cells span"
    "double_reverse_packed_merged_source_cells span \<le> span + 1"
  unfolding double_reverse_packed_merged_source_cells_def
    double_reverse_packed_merged_radius_def
  by presburger+

lemma double_reverse_packed_output_position_valid:
  fixes merged_begin :: int
  assumes phase: "phase < 4"
      and count: "0 < count"
      and position: "position < count"
      and left_cover: "merged_begin \<le>
        double_reverse_packed_request_begin phase steps start count"
      and right_cover: "double_reverse_packed_request_end phase steps start count \<le>
        merged_begin + int span"
      and output_positive:
        "2 * double_reverse_packed_merged_radius span + 1 > 2 * steps"
  shows
    "double_reverse_packed_row_position phase steps start count
       merged_begin position <
      double_reverse_packed_merged_output_cells span steps"
proof -
  let ?births = "fst (double_reverse_runtime_growth_ports phase steps)"
  let ?pad = "double_reverse_packed_request_padding count"
  let ?begin = "double_reverse_packed_request_begin phase steps start count"
  let ?end = "double_reverse_packed_request_end phase steps start count"
  let ?source_cells = "double_reverse_packed_merged_source_cells span"
  let ?output_cells = "double_reverse_packed_merged_output_cells span steps"
  have runtime_geometry:
    "?begin = int start - int ?births - int steps - int ?pad"
    "?end = int start - int ?births + int count + int steps"
    by (simp_all add: double_reverse_packed_request_begin_def
        double_reverse_packed_request_end_def)
  have row_start_nonnegative:
    "0 \<le> int start - int ?births - merged_begin - int steps"
  proof -
    have "merged_begin \<le> int start - int ?births - int steps - int ?pad"
      using left_cover runtime_geometry by simp
    moreover have "0 \<le> int ?pad" by simp
    ultimately show ?thesis by linarith
  qed
  have row_position_nat:
    "int (double_reverse_packed_row_position phase steps start count
       merged_begin position) =
      int start - int ?births - merged_begin - int steps + int position"
    unfolding double_reverse_packed_row_position_def
    using row_start_nonnegative by simp
  have end_bound:
    "int start - int ?births - merged_begin - int steps + int position + 1
      \<le> int ?source_cells - int (2*steps)"
  proof -
    have selected_end:
      "int start - int ?births + int count + int steps \<le>
        merged_begin + int span"
      using right_cover runtime_geometry by simp
    have source_bound: "int span \<le> int ?source_cells"
      using double_reverse_packed_merged_source_cells_bounds(1)[of span]
      by simp
    have pos_bound: "int position < int count"
      using position by simp
    have "int start - int ?births - merged_begin - int steps +
        int position + 1 \<le>
      int start - int ?births - merged_begin - int steps + int count"
      using pos_bound by linarith
    also have "... \<le> int ?source_cells - int (2*steps)"
      using selected_end source_bound by linarith
    finally show ?thesis .
  qed
  have output_positive_geometry:
    "2 * steps < 2 * (span div 2) + 1"
    using output_positive
    by (simp only: double_reverse_packed_merged_radius_def)
  have source_cells_value:
    "?source_cells = 2 * (span div 2) + 1"
    by (simp only: double_reverse_packed_merged_source_cells_def
        double_reverse_packed_merged_radius_def)
  have source_cells_enough: "2 * steps \<le> ?source_cells"
    using output_positive_geometry source_cells_value by arith
  have output_cells_int:
    "int ?output_cells = int ?source_cells - int (2*steps)"
    unfolding double_reverse_packed_merged_output_cells_def
    using source_cells_enough
    by (simp add: of_nat_diff)
  have nonnegative:
    "0 \<le> int start - int ?births - merged_begin - int steps + int position"
    using row_start_nonnegative by linarith
  have result:
    "int (double_reverse_packed_row_position phase steps start count
       merged_begin position) < int ?output_cells"
    using row_position_nat end_bound output_cells_int nonnegative by linarith
  show ?thesis using result by simp
qed

lemma double_reverse_packed_request_to_merged_row:
  fixes merged_begin :: int
  assumes count: "0 < count"
      and left_cover: "merged_begin \<le>
        double_reverse_packed_request_begin phase steps start count"
  shows "int (double_reverse_packed_row_position phase steps start count
      merged_begin position) =
    double_reverse_packed_runtime_output_start phase steps start merged_begin +
      int position"
proof -
  let ?births = "fst (double_reverse_runtime_growth_ports phase steps)"
  have nonnegative:
    "0 \<le> int start - int ?births - merged_begin - int steps"
  proof -
    have "merged_begin \<le>
        int start - int ?births - int steps -
          int (double_reverse_packed_request_padding count)"
      using left_cover
      by (simp add: double_reverse_packed_request_begin_def)
    moreover have "0 \<le> int (double_reverse_packed_request_padding count)"
      by simp
    ultimately show ?thesis by linarith
  qed
  show ?thesis
    unfolding double_reverse_packed_row_position_def
    using nonnegative
    by (simp add: double_reverse_packed_runtime_output_start_def)
qed

theorem double_reverse_packed_request_point_refines_ring:
  fixes source :: "double_reverse_source_slp"
    and merged_begin :: int
    and phase steps start count position span digit :: nat
    and motif :: "nat list"
    and source_word :: "nat list"
    and radius source_cells output_cells middle_length first :: nat
    and origin :: int
    and middle window_slp :: "double_reverse_source_slp"
  defines "source_word \<equiv> double_reverse_source_slp_word source"
      and "radius \<equiv> double_reverse_packed_merged_radius span"
      and "source_cells \<equiv> double_reverse_packed_merged_source_cells span"
      and "output_cells \<equiv>
        double_reverse_packed_merged_output_cells span steps"
      and "origin \<equiv> merged_begin + int radius"
      and "middle_length \<equiv>
        double_reverse_source_window_middle_length source_word merged_begin source_cells"
      and "first \<equiv> double_reverse_source_window_first merged_begin"
      and "middle \<equiv>
        (if middle_length = 0 then Double_Reverse_Source_Empty
         else double_reverse_source_slp_part source first
           (first + middle_length))"
      and "window_slp \<equiv>
        double_reverse_source_window_slp source_word merged_begin source_cells middle"
  assumes phase: "phase < 4"
      and count: "0 < count"
      and position: "position < count"
      and merged_left_cover: "merged_begin \<le>
        double_reverse_packed_runtime_request_begin phase steps start count"
      and merged_right_cover: "double_reverse_packed_runtime_request_end
        phase steps start count \<le>
        merged_begin + int span"
      and output_positive: "0 < output_cells"
      and motif: "motif \<noteq> []"
      and certificate:
        "double_reverse_source_slp_phase_certificate motif window_slp 0"
      and decimal:
        "double_reverse_decimal_row
          (double_reverse_pointed_source_window source_word origin radius)"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes
        (double_reverse_pointed_source_window source_word origin radius))
      source_cells ! digit)
      (double_reverse_packed_row_position phase steps start count
        merged_begin position) \<longleftrightarrow>
    double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
      (double_reverse_packed_row_position phase steps start count
        merged_begin position) = digit"
proof -
  have runtime_cover:
    "merged_begin \<le>
       double_reverse_packed_request_begin phase steps start count"
    "double_reverse_packed_request_end phase steps start count \<le>
       merged_begin + int span"
    using merged_left_cover merged_right_cover
      double_reverse_packed_runtime_request_geometry[OF count]
    by simp_all
  have output_positive_value:
    "0 < double_reverse_packed_merged_output_cells span steps"
    using output_positive by (simp only: output_cells_def)
  have output_positive_arith:
    "0 < 2 * (span div 2) + 1 - 2 * steps"
    using output_positive_value
    by (simp only: double_reverse_packed_merged_output_cells_def
        double_reverse_packed_merged_source_cells_def
        double_reverse_packed_merged_radius_def)
  have source_cells_value: "source_cells = 2 * (span div 2) + 1"
    unfolding source_cells_def double_reverse_packed_merged_source_cells_def
      radius_def double_reverse_packed_merged_radius_def
    by simp
  have source_cells_enough: "2 * steps \<le> source_cells"
    using output_positive_arith source_cells_value by presburger
  have source_radius: "radius = steps + output_cells div 2"
    unfolding radius_def output_cells_def
      double_reverse_packed_merged_output_cells_def source_cells_def
      double_reverse_packed_merged_source_cells_def
      double_reverse_packed_merged_radius_def
    using output_positive_arith by presburger
  have output_cells_odd: "\<not> even output_cells"
    unfolding output_cells_def double_reverse_packed_merged_output_cells_def
      source_cells_def double_reverse_packed_merged_source_cells_def
      double_reverse_packed_merged_radius_def
    using output_positive_arith by presburger
  have positive_cone:
    "2 * double_reverse_packed_merged_radius span + 1 > 2 * steps"
    using output_positive_arith
    unfolding double_reverse_packed_merged_radius_def
    by simp
  have row_bound:
    "double_reverse_packed_row_position phase steps start count
       merged_begin position < output_cells"
  proof -
    have row_bound_raw:
      "double_reverse_packed_row_position phase steps start count
         merged_begin position <
       double_reverse_packed_merged_output_cells span steps"
      by (rule double_reverse_packed_output_position_valid
        [OF phase count position runtime_cover(1) runtime_cover(2) positive_cone])
    show ?thesis using row_bound_raw output_cells_def by simp
  qed
  have middle_bound:
    "middle_length = 0 \<or> first + middle_length \<le> length source_word"
    unfolding middle_length_def first_def source_word_def
    by (rule double_reverse_source_window_fragment_geometry(2))
  have part:
    "double_reverse_source_slp_word middle =
      take middle_length (drop first source_word)"
  proof (cases "middle_length = 0")
    case True
    then show ?thesis by (simp add: middle_def)
  next
    case False
    have part_bound: "first + middle_length \<le> length source_word"
      using middle_bound False by blast
    have part_exact_raw:
      "double_reverse_source_slp_word
        (double_reverse_source_slp_part source first
          (first + middle_length)) =
        take ((first + middle_length) - first)
          (drop first (double_reverse_source_slp_word source))"
    proof (rule double_reverse_source_slp_part_exact)
      show "first \<le> first + middle_length" by simp
      show "first + middle_length \<le> double_reverse_source_slp_length source"
        using part_bound source_word_def by (simp add: source_word_def
          double_reverse_source_slp_word_length)
    qed
    have part_exact:
      "double_reverse_source_slp_word
        (double_reverse_source_slp_part source first
          (first + middle_length)) =
        take middle_length (drop first source_word)"
      using part_exact_raw by (simp add: source_word_def)
    show ?thesis using False part_exact by (simp add: middle_def)
  qed
  have origin_geometry: "origin - int radius = merged_begin"
    by (simp add: origin_def)
  have source_count: "source_cells = 2 * radius + 1"
    unfolding source_cells_def radius_def
      double_reverse_packed_merged_source_cells_def
      double_reverse_packed_merged_radius_def by simp
  have point:
    "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes
        (double_reverse_pointed_source_window source_word origin radius))
      source_cells ! digit)
       (double_reverse_packed_row_position phase steps start count
         merged_begin position) \<longleftrightarrow>
      double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
       (double_reverse_packed_row_position phase steps start count
         merged_begin position) = digit"
  proof -
    have rowpart:
      "double_reverse_source_slp_word middle =
        take (double_reverse_source_window_middle_length source_word
          (origin - int radius) (2 * radius + 1))
        (drop (double_reverse_source_window_first (origin - int radius))
          source_word)"
      using part origin_geometry source_count
      unfolding middle_length_def first_def by simp
    have cert:
      "double_reverse_source_slp_phase_certificate motif
        (double_reverse_source_window_slp source_word
          (origin - int radius) (2*radius+1) middle) 0"
      using certificate origin_geometry source_count
      unfolding window_slp_def by simp
    have point_result_with_padding:
      "bit (double_reverse_bitplane_row_run steps
        (double_reverse_decimal_planes
          (double_reverse_pointed_source_window source_word origin radius))
        (length (double_reverse_pointed_source_window source_word origin radius)) ! digit)
        (double_reverse_packed_row_position phase steps start count
          merged_begin position + (if even output_cells then 1 else 0)) \<longleftrightarrow>
       double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
         (double_reverse_packed_row_position phase steps start count
           merged_begin position + (if even output_cells then 1 else 0)) = digit"
      by (rule double_reverse_source_window_bitplane_point_refines_ring
        [where middle=middle and count=output_cells
          and origin=origin and radius=radius and i=
            "double_reverse_packed_row_position phase steps start count
              merged_begin position"])
        (use rowpart motif cert output_positive output_cells_odd source_radius
          row_bound decimal digit in auto)
    have point_result:
      "bit (double_reverse_bitplane_row_run steps
        (double_reverse_decimal_planes
          (double_reverse_pointed_source_window source_word origin radius))
        (length (double_reverse_pointed_source_window source_word origin radius)) ! digit)
        (double_reverse_packed_row_position phase steps start count
          merged_begin position) \<longleftrightarrow>
       double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
         (double_reverse_packed_row_position phase steps start count
           merged_begin position) = digit"
      using point_result_with_padding output_cells_odd by simp
    have source_window_length:
      "length (double_reverse_pointed_source_window source_word origin radius) =
        source_cells"
      unfolding source_cells_def radius_def
        double_reverse_packed_merged_source_cells_def
        double_reverse_packed_merged_radius_def
      by (simp add: double_reverse_pointed_source_window_length)
    show ?thesis using point_result source_window_length by simp
  qed
  show ?thesis using point .
qed

ML \<open>
  val checked = @{thms double_reverse_runtime_growth_ports_exact
    double_reverse_packed_request_geometry
    double_reverse_packed_runtime_request_geometry
    double_reverse_packed_merged_source_cells_bounds
    double_reverse_packed_output_position_valid
    double_reverse_packed_request_to_merged_row
    double_reverse_packed_runtime_output_start_def
    double_reverse_packed_request_point_refines_ring};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed request refinement depends on an oracle";
\<close>

end
