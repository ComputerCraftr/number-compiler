theory Comma_Semantic_B1_Future_Bridge
  imports Comma_Semantic_B1.Comma_Semantic_B1_Power
    Comma_Native_Summary_Occurrence.Comma_Native_Summary_Occurrence
begin

ML_file "../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

text \<open>
This is a provider-neutral bridge from a powered semantic Stop payload to
the exact physical decade occurrence.  A future provider supplies only the
extensional B32 refinement below; this theory does not mention sparse rows,
rank tables, or a concrete forest publisher.
\<close>

lemmas comma_semantic_block_stop_summary = comma_decade_block_power_stop(2)

theorem comma_semantic_b32_stop_exact_occurrence_for_offset:
  fixes provider :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
  assumes exact_orbit:
      "\<And>r i. r<924 \<Longrightarrow> i<46 \<Longrightarrow>
        provider r i = comma_semantic_b1_of_word (comma_orbit_word 5 r i)"
    and phase: "r<924"
    and offset: "x\<le>90"
    and exponent: "5\<le>p"
    and phase_match: "p mod 924=r"
    and stopped: "provider r (comma_offset_orbit x)=Comma_Semantic_B1_Stop D"
    and weight_bound: "D\<le>242"
  obtains h terminal weight t endpoint where
    "comma_terminal_weight_decode D=(h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade r x) h terminal"
    "comma_unique_literal_path weight
      (comma_chart_value p
        (Comma_Entry 1 0 x)) endpoint"
    "endpoint=comma_chart_value (p+h) t"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    "comma_large_children (comma_sector_number t) (p+h) endpoint =
      comma_summary_ordered_children terminal (p+h)"
    "\<forall>v. comma_child endpoint v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children terminal (p+h))"
proof -
  let ?i = "comma_offset_orbit x"
  let ?source = "Comma_Decade r x"
  have admitted: "comma_decade_admitted ?source"
    using phase offset by simp
  have root: "?i<46"
    by (rule comma_offset_orbit_bound)
  have result:
    "comma_semantic_b1_of_word (comma_orbit_word 5 r ?i)=
      Comma_Semantic_B1_Stop D"
    using exact_orbit[OF phase root] stopped by simp
  obtain h terminal where word_stop:
      "comma_orbit_word 5 r ?i=Comma_Word_Stop h terminal"
    and encoded: "D=comma_terminal_weight_encode h terminal"
    using result by (cases "comma_orbit_word 5 r ?i") auto
  have projected:
    "comma_word_project comma_offset_orbit
        (comma_decade_block_power 5 ?source)=Comma_Word_Stop h terminal"
    using comma_orbit_word_refines[OF admitted] word_stop by simp
  have block_stop:
    "comma_decade_block_power 5 ?source=Comma_Block_Stop h terminal"
    using projected by (simp only: comma_word_project_stop_iff)
  have summary:
    "comma_decade_exact_summary ?source h terminal"
    by (rule comma_semantic_block_stop_summary[OF block_stop])
  have terminal_admitted:
    "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have decoded:
    "comma_terminal_weight_decode D=(h,terminal)"
    using encoded comma_terminal_weight_decode_encode[OF terminal_admitted]
    by simp
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
  have height_bound: "h\<le>26"
    using weight_bound encoded digit_bound
    by (simp add: comma_terminal_weight_encode_def; arith)
  have binding: "?source=Comma_Decade (p mod 924) x"
    using phase_match by simp
  obtain weight round_state where occurrence:
      "comma_unique_literal_path weight
        (comma_chart_value p (Comma_Entry 1 0 x))
        (comma_chart_value (p+h) round_state)"
    and round_valid: "comma_round_admitted round_state"
    and round_zero: "comma_round_delta round_state=0"
    and round_move:
      "comma_finite_step ((p+h) mod 924) round_state=
        comma_summary_terminal_move terminal"
    using comma_decade_summary_unique_occurrence_exists
      [OF summary admitted exponent binding] by blast
  have endpoint_exponent: "5\<le>p+h" using exponent by arith
  have child_list:
    "comma_large_children (comma_sector_number round_state) (p+h)
        (comma_chart_value (p+h) round_state) =
      comma_summary_ordered_children terminal (p+h)"
    by (rule comma_summary_terminal_children_exact(1)[OF round_valid round_zero
          endpoint_exponent round_move])
  have child_membership:
    "\<And>v. comma_child (comma_chart_value (p+h) round_state) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children terminal (p+h))"
    by (rule comma_summary_terminal_children_exact(2)[OF round_valid round_zero
          endpoint_exponent round_move])
  have children:
    "comma_large_children (comma_sector_number round_state) (p+h)
        (comma_chart_value (p+h) round_state) =
      comma_summary_ordered_children terminal (p+h)"
    "\<forall>v. comma_child (comma_chart_value (p+h) round_state) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children terminal (p+h))"
  proof -
    show "comma_large_children (comma_sector_number round_state) (p+h)
        (comma_chart_value (p+h) round_state) =
      comma_summary_ordered_children terminal (p+h)"
      by (rule child_list)
    show "\<forall>v. comma_child (comma_chart_value (p+h) round_state) v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children terminal (p+h))"
      by (intro allI; rule child_membership)
  qed
  show thesis
    by (rule that[OF decoded height_bound summary occurrence refl round_valid
          round_zero round_move children])
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint
  "semantic-b32-entry-projection-start"\<close>

theorem comma_semantic_b32_entry_infinite_path_projects_summary_child:
  fixes provider :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
  assumes exact_orbit:
      "\<And>r i. r<924 \<Longrightarrow> i<46 \<Longrightarrow>
        provider r i = comma_semantic_b1_of_word (comma_orbit_word 5 r i)"
    and phase: "r<924"
    and offset: "x\<le>90"
    and exponent: "5\<le>p"
    and phase_match: "p mod 924=r"
    and stopped: "provider r (comma_offset_orbit x)=Comma_Semantic_B1_Stop D"
    and weight_bound: "D\<le>242"
    and path_start:
      "stream 0=comma_chart_value p (Comma_Entry 1 0 x)"
    and path_edges: "\<And>j. comma_child (stream j) (stream (Suc j))"
  obtains h terminal weight t endpoint successor tail where
    "comma_terminal_weight_decode D=(h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary (Comma_Decade r x) h terminal"
    "comma_unique_literal_path weight
      (comma_chart_value p (Comma_Entry 1 0 x)) endpoint"
    "endpoint=comma_chart_value (p+h) t"
    "comma_round_admitted t"
    "comma_round_delta t=0"
    "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    "comma_large_children (comma_sector_number t) (p+h) endpoint =
      comma_summary_ordered_children terminal (p+h)"
    "\<forall>v. comma_child endpoint v \<longleftrightarrow>
      v \<in> set (comma_summary_ordered_children terminal (p+h))"
    "stream weight=endpoint"
    "successor=stream (Suc weight)"
    "successor \<in> set (comma_summary_ordered_children terminal (p+h))"
    "tail 0=successor"
    "\<forall>j. comma_child (tail j) (tail (Suc j))"
proof -
  show thesis
  proof (rule comma_semantic_b32_stop_exact_occurrence_for_offset
      [OF exact_orbit phase offset exponent phase_match stopped weight_bound])
    fix h terminal weight t endpoint
    assume decoded:
      "comma_terminal_weight_decode D=(h,terminal)"
    and height: "h\<le>26"
    and summary: "comma_decade_exact_summary (Comma_Decade r x) h terminal"
    and unique:
      "comma_unique_literal_path weight
        (comma_chart_value p (Comma_Entry 1 0 x)) endpoint"
    and endpoint_eq: "endpoint=comma_chart_value (p+h) t"
    and terminal_admitted: "comma_round_admitted t"
    and terminal_delta: "comma_round_delta t=0"
    and terminal_move:
      "comma_finite_step ((p+h) mod 924) t=comma_summary_terminal_move terminal"
    and children_eq:
      "comma_large_children (comma_sector_number t) (p+h) endpoint =
        comma_summary_ordered_children terminal (p+h)"
    and complete_children:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        v \<in> set (comma_summary_ordered_children terminal (p+h))"
    have prefix: "comma_literal_path weight (stream 0) (stream weight)"
      by (rule comma_infinite_literal_prefix
        [where path=stream and n=weight, OF path_edges])
    have prefix_at_entry:
      "comma_literal_path weight
        (comma_chart_value p (Comma_Entry 1 0 x)) (stream weight)"
      using prefix path_start by simp
    have selected_endpoint: "stream weight=endpoint"
      by (rule comma_unique_literal_path_endpoint[OF unique prefix_at_entry])
    have next_edge: "comma_child endpoint (stream (Suc weight))"
      using path_edges[of weight] selected_endpoint by simp
    have next_edge_complete:
      "comma_child endpoint (stream (Suc weight)) \<longleftrightarrow>
        stream (Suc weight) \<in>
          set (comma_summary_ordered_children terminal (p+h))"
      using complete_children by (rule spec[where x="stream (Suc weight)"])
    have selected_child:
      "stream (Suc weight) \<in>
        set (comma_summary_ordered_children terminal (p+h))"
      by (rule iffD1[OF next_edge_complete next_edge])
    let ?successor = "stream (Suc weight)"
    let ?tail = "\<lambda>j. stream (weight + Suc j)"
    have tail_start: "?tail 0=?successor" by simp
    have tail_edges: "comma_child (?tail j) (?tail (Suc j))" for j
      using path_edges[of "weight+Suc j"] by (simp add: add.assoc)
    have tail_edges_all: "\<forall>j. comma_child (?tail j) (?tail (Suc j))"
      by (intro allI; rule tail_edges)
    show thesis
      by (rule that[OF decoded height summary unique endpoint_eq terminal_admitted
            terminal_delta terminal_move children_eq complete_children
            selected_endpoint refl selected_child tail_start tail_edges_all])
  qed
qed

ML \<open>Comma_Native_Occurrence_Profile.checkpoint
  "semantic-b32-entry-projection-end"\<close>

ML \<open>
  val checked = @{thms comma_semantic_b32_stop_exact_occurrence_for_offset
    comma_semantic_b32_entry_infinite_path_projects_summary_child};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B32 Stop physical occurrence bridge" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Semantic B32 Stop to exact decade occurrence"
    ["comma_terminal_weight_decode_encode",
      "comma_word_project_stop_iff",
      "comma_orbit_word_refines",
      "comma_decade_power_orbit_congruent",
      "comma_decade_control_orbit_congruent",
      "comma_semantic_block_stop_summary",
      "comma_decade_summary_unique_occurrence_exists",
      "comma_summary_terminal_children_exact",
      "comma_offset_orbit_bound",
      "comma_semantic_b32_stop_exact_occurrence_for_offset",
      "comma_infinite_literal_prefix",
      "comma_unique_literal_path_endpoint"] checked;
\<close>

end
