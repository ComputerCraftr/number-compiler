theory Comma_Phase_Class_Rank_Local_Coverage
  imports Comma_Phase_Class_Rank_Source_Bridge
begin

text \<open>
The finite rank table is checked by local source ports.  A terminal port's
phase-class guard must lie in its labelled parent column.  A Goto port's
piece for a child row is the original-phase intersection of that guard with
the child row; a nonempty piece must lie in the parent column carrying the
same label.  A decreasing-sector induction proves child lookup correctness
for the whole finite source domain, so it is not an unproved premise of the
final lookup theorem.
\<close>

definition comma_rank_local_column ::
    "(nat \<times> comma_phase_rank_mask_action) list \<Rightarrow>
      comma_phase_rank_mask_action \<Rightarrow> nat option" where
  "comma_rank_local_column rows label =
    map_of (map (\<lambda>row. (snd row, fst row)) rows) label"

definition comma_rank_local_piece_covered where
  "comma_rank_local_piece_covered rows label piece \<longleftrightarrow>
    (case comma_rank_local_column rows label of
       None \<Rightarrow> piece=0
     | Some column \<Rightarrow> piece AND column=piece)"

definition comma_rank_local_family_well_formed ::
    "(nat \<times> comma_phase_rank_mask_action) list \<Rightarrow> bool" where
  "comma_rank_local_family_well_formed rows \<longleftrightarrow>
    comma_phase_mask_rows_partition rows \<and>
    (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      snd left=snd right \<longrightarrow> left=right)"

definition comma_rank_source_local_coverage where
  "comma_rank_source_local_coverage sources families source \<longleftrightarrow>
    (\<forall>slot<comma_decisive_sector_period source.
      (case comma_semantic_b1_source_port_action source slot of
         Comma_Continuation_Goto child shift \<Rightarrow>
           shift=0 \<and> child\<in>set sources \<and>
           (\<forall>childrow\<in>set (families child).
             (let piece=comma_phase_class
                  (comma_decisive_sector_period source) 0 slot AND fst childrow
              in comma_rank_local_piece_covered (families source)
                   (snd childrow) piece))
       | action \<Rightarrow>
           (\<exists>terminal.
             comma_semantic_b1_terminal_action_result action=Some terminal \<and>
             (let piece=comma_phase_class
                   (comma_decisive_sector_period source) 0 slot AND mask 924
              in comma_rank_local_piece_covered (families source)
                   (comma_rank_mask_action_of_b1_result terminal) piece))))"

definition comma_rank_source_domain_contract where
  "comma_rank_source_domain_contract sources families \<longleftrightarrow>
    (\<forall>source\<in>set sources.
      comma_round_admitted source \<and>
      source=comma_source_continuation_base source \<and>
      comma_rank_local_family_well_formed (families source) \<and>
      comma_rank_source_local_coverage sources families source)"

lemma comma_rank_local_column_someE:
  assumes column: "comma_rank_local_column rows label=Some bits"
  obtains row where "row\<in>set rows" and "snd row=label"
    and "fst row=bits"
proof -
  have pair: "(label,bits)\<in>set (map (\<lambda>row. (snd row,fst row)) rows)"
    using column by (auto simp: comma_rank_local_column_def dest: map_of_SomeD)
  then obtain row where row: "row\<in>set rows"
      "(snd row,fst row)=(label,bits)"
    by (auto simp: set_map)
  show thesis
  proof (rule that[of row])
    show "row\<in>set rows" by (rule row(1))
    show "snd row=label" using row(2) by simp
    show "fst row=bits" using row(2) by simp
  qed
qed

lemma comma_rank_local_piece_covered_member:
  assumes piece_nonzero: "piece\<noteq>0"
    and piece_member: "comma_phase_member piece phase"
    and covered: "comma_rank_local_piece_covered rows label piece"
  obtains column where "comma_rank_local_column rows label=Some column"
    and "comma_phase_member column phase"
proof (cases "comma_rank_local_column rows label")
  case None
  then have "piece=0" using covered
    by (simp add: comma_rank_local_piece_covered_def)
  with piece_nonzero show thesis by contradiction
next
  case (Some column)
  then have subset: "piece AND column=piece" using covered
    by (simp add: comma_rank_local_piece_covered_def)
  have intersection:
    "comma_phase_member (piece AND column) phase"
    using piece_member subset by simp
  have column_member: "comma_phase_member column phase"
    using intersection by (simp add: comma_phase_member_and)
  show thesis by (rule that[OF Some column_member])
qed

lemma comma_rank_local_row_at_column_label:
  assumes partition: "comma_phase_mask_rows_partition rows"
    and phase: "phase<924"
    and column_lookup: "comma_rank_local_column rows label=Some bits"
    and column_member: "comma_phase_member bits phase"
  shows "map_option snd (comma_phase_mask_row_at rows phase)=Some label"
proof -
  obtain witness where witness: "witness\<in>set rows" "snd witness=label"
    "fst witness=bits"
    by (rule comma_rank_local_column_someE[OF column_lookup])
  have witness_phase: "comma_phase_member (fst witness) phase"
    using witness(3) column_member by simp
  obtain selected where selected: "selected\<in>set rows"
    "comma_phase_member (fst selected) phase"
    "comma_phase_mask_row_at rows phase=Some selected"
    by (rule comma_phase_mask_row_at_some[OF partition phase])
  have unique: "\<exists>!row. row\<in>set rows \<and>
      comma_phase_member (fst row) phase"
    by (rule comma_phase_mask_rows_partition_ex1[OF partition phase])
  have selected_eq: "selected=witness"
    using unique selected witness witness_phase by blast
  show ?thesis using selected_eq witness(2) selected(3) by simp
qed

lemma comma_rank_local_guard_member:
  assumes phase: "phase<924"
    and period: "0<period"
    and slot: "slot<period"
    and congruent: "phase mod period=slot"
  shows "comma_phase_member (comma_phase_class period 0 slot) phase"
  using phase congruent by (simp add: comma_phase_class_member)

lemma comma_rank_local_piece_at_phase_nonzero:
  assumes member: "comma_phase_member piece phase"
  shows "piece\<noteq>0"
proof
  assume empty: "piece=0"
  have "comma_phase_member 0 phase" using member by (simp only: empty)
  then show False by (simp add: comma_phase_member_zero)
qed

theorem comma_rank_source_domain_lookup_exact:
  assumes contract:
      "comma_rank_source_domain_contract sources families"
  shows "\<forall>source\<in>set sources. \<forall>phase<924.
    map_option snd (comma_phase_mask_row_at (families source) phase) =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase source))"
proof (intro ballI allI impI)
  fix source
  fix phase :: nat
  assume source_mem: "source\<in>set sources"
    and phase_bound: "phase<924"
  show "map_option snd (comma_phase_mask_row_at (families source) phase) =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase source))"
    using source_mem phase_bound
  proof (induction "9-comma_sector_number source"
      arbitrary: source phase rule: less_induct)
    case less
    note source_member = less.prems(1)
    note phase_ok = less.prems(2)
    note sector_induction = less.hyps
    have domain_facts:
      "comma_round_admitted source"
      "source=comma_source_continuation_base source"
      "comma_rank_local_family_well_formed (families source)"
      "comma_rank_source_local_coverage sources families source"
      using contract source_member
      by (auto simp: comma_rank_source_domain_contract_def)
    note admitted = domain_facts(1)
    note normalized = domain_facts(2)
    note family_wf = domain_facts(3)
    note coverage_fact = domain_facts(4)
    have parent_partition:
      "comma_phase_mask_rows_partition (families source)"
      using family_wf by (simp add: comma_rank_local_family_well_formed_def)
    have period_pair:
      "0<comma_decisive_sector_period source \<and>
        comma_decisive_sector_period source dvd 924"
      by (rule comma_decisive_sector_period_admitted_pair[OF admitted])
    have positive: "0<comma_decisive_sector_period source"
      using period_pair by simp
    let ?period = "comma_decisive_sector_period source"
    let ?slot = "phase mod ?period"
    have slot_bound: "?slot<?period" using positive by simp
    have phase_slot: "phase mod ?period=?slot" by simp
    have guard_member: "comma_phase_member (comma_phase_class ?period 0 ?slot) phase"
      by (rule comma_rank_local_guard_member[OF phase_ok positive slot_bound phase_slot])
    have local_slot:
      "case comma_semantic_b1_source_port_action source ?slot of
        Comma_Continuation_Goto child shift \<Rightarrow>
          shift=0 \<and> child\<in>set sources \<and>
          (\<forall>childrow\<in>set (families child).
            (let piece=comma_phase_class ?period 0 ?slot AND fst childrow
             in comma_rank_local_piece_covered (families source)
                 (snd childrow) piece))
      | action \<Rightarrow> \<exists>terminal.
          comma_semantic_b1_terminal_action_result action=Some terminal \<and>
          (let piece=comma_phase_class ?period 0 ?slot AND mask 924
           in comma_rank_local_piece_covered (families source)
                (comma_rank_mask_action_of_b1_result terminal) piece)"
      using coverage_fact slot_bound
      by (simp add: comma_rank_source_local_coverage_def)
    have slot_source_action:
      "comma_semantic_b1_source_slot_action source ?slot =
        comma_semantic_b1_source_port_action source ?slot"
    proof -
      have at_port:
        "comma_source_continuation_action_at source ?slot =
          comma_semantic_b1_source_port_action source ?slot"
        by (rule comma_guarded_source_action_at_port[OF admitted normalized])
      have slot_refines:
        "comma_semantic_b1_source_slot_action source ?slot =
          comma_source_continuation_action_at source ?slot"
        by (rule comma_semantic_b1_source_slot_action_refines[OF admitted])
      show ?thesis using at_port slot_refines by simp
    qed
    have source_round:
      "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action source ?slot) =
        comma_semantic_b1_round_output phase source"
      using comma_semantic_b1_source_slot_round_output
        [OF normalized admitted slot_bound phase_slot] slot_source_action
      by simp
    show ?case
    proof (cases "\<exists>child shift. comma_semantic_b1_source_port_action
        source ?slot=Comma_Continuation_Goto child shift")
      case True
      then obtain child shift where action:
        "comma_semantic_b1_source_port_action source ?slot=
          Comma_Continuation_Goto child shift"
        by blast
      have shift_zero: "shift=0" and child_norm:
        "child=comma_source_continuation_base child"
        and child_decrease:
          "9-comma_sector_number child < 9-comma_sector_number source"
        and child_admitted: "comma_round_admitted child"
        by (rule comma_guarded_source_mask_goto_decreases
          [OF admitted normalized slot_bound action])+
      have child_domain: "child\<in>set sources"
        using local_slot action shift_zero by simp
      have child_exact:
        "map_option snd (comma_phase_mask_row_at (families child) phase) =
          Some (comma_rank_mask_action_of_b1_result
            (comma_semantic_b1_round_output phase child))"
        using sector_induction[OF child_decrease child_domain phase_ok] .
      have child_family_wf:
        "comma_rank_local_family_well_formed (families child)"
        using contract child_domain
        by (auto simp: comma_rank_source_domain_contract_def)
      have child_partition:
        "comma_phase_mask_rows_partition (families child)"
        using child_family_wf
        by (simp add: comma_rank_local_family_well_formed_def)
      obtain childrow where childrow_member: "childrow\<in>set (families child)"
        and childrow_phase: "comma_phase_member (fst childrow) phase"
        and childrow_lookup:
          "comma_phase_mask_row_at (families child) phase=Some childrow"
        by (rule comma_phase_mask_row_at_some[OF child_partition phase_ok])
      have child_label:
        "snd childrow=comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase child)"
        using child_exact childrow_lookup by simp
      have local_piece:
        "comma_rank_local_piece_covered (families source)
          (snd childrow) (comma_phase_class ?period 0 ?slot AND fst childrow)"
        using local_slot action shift_zero childrow_member by (auto simp: Let_def)
      let ?piece = "comma_phase_class ?period 0 ?slot AND fst childrow"
      have piece_phase: "comma_phase_member ?piece phase"
        using guard_member childrow_phase by (simp add: comma_phase_member_and)
      have piece_nonzero: "?piece\<noteq>0"
        by (rule comma_rank_local_piece_at_phase_nonzero[OF piece_phase])
      obtain parent_column where parent_column_lookup:
          "comma_rank_local_column (families source) (snd childrow)=
            Some parent_column"
        and parent_column_member: "comma_phase_member parent_column phase"
        by (rule comma_rank_local_piece_covered_member
          [OF piece_nonzero piece_phase local_piece])
      have parent_lookup:
        "map_option snd (comma_phase_mask_row_at (families source) phase) =
          Some (snd childrow)"
        by (rule comma_rank_local_row_at_column_label
          [OF parent_partition phase_ok parent_column_lookup
            parent_column_member])
      have source_child_output:
        "comma_semantic_b1_round_output phase source =
          comma_semantic_b1_round_output phase child"
        using source_round action shift_zero
        by (simp add: comma_semantic_b1_source_slot_output_def)
      show ?thesis
        using parent_lookup child_label source_child_output by simp
    next
      case False
      let ?action = "comma_semantic_b1_source_port_action source ?slot"
      have non_goto:
        "\<not>(\<exists>child shift. ?action=Comma_Continuation_Goto child shift)"
        using False by blast
      obtain terminal where terminal:
        "comma_semantic_b1_terminal_action_result ?action=Some terminal"
        using comma_semantic_b1_terminal_action_result_present[OF non_goto]
        by blast
      have terminal_output:
        "terminal=comma_semantic_b1_round_output phase source"
        using source_round terminal non_goto
        by (cases ?action) (auto simp: comma_semantic_b1_source_slot_output_def)
      have local_terminal:
        "comma_rank_local_piece_covered (families source)
          (comma_rank_mask_action_of_b1_result terminal)
          (comma_phase_class ?period 0 ?slot AND mask 924)"
        using local_slot terminal non_goto by (cases ?action) (auto simp: Let_def)
      let ?piece = "comma_phase_class ?period 0 ?slot AND mask 924"
      have full_phase: "comma_phase_member (mask 924) phase"
        using phase_ok by (simp add: comma_phase_member_def bit_simps)
      have piece_phase: "comma_phase_member ?piece phase"
        using guard_member full_phase by (simp add: comma_phase_member_and)
      have piece_nonzero: "?piece\<noteq>0"
        by (rule comma_rank_local_piece_at_phase_nonzero[OF piece_phase])
      obtain parent_column where parent_column_lookup:
          "comma_rank_local_column (families source)
            (comma_rank_mask_action_of_b1_result terminal)=Some parent_column"
        and parent_column_member: "comma_phase_member parent_column phase"
        by (rule comma_rank_local_piece_covered_member
          [OF piece_nonzero piece_phase local_terminal])
      show ?thesis
        using comma_rank_local_row_at_column_label
          [OF parent_partition phase_ok parent_column_lookup
            parent_column_member] terminal_output by simp
    qed
  qed
qed

theorem comma_rank_source_domain_action_exact:
  assumes contract:
      "comma_rank_source_domain_contract sources families"
  shows "\<forall>source\<in>set sources. \<forall>phase<924.
    comma_phase_mask_action_total [families source] phase 0 =
      comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase source))"
proof (intro ballI allI impI)
  fix source
  fix phase :: nat
  assume source: "source\<in>set sources" and phase: "phase<924"
  have selected:
    "map_option snd (comma_phase_mask_row_at (families source) phase) =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase source))"
    using comma_rank_source_domain_lookup_exact[OF contract] source phase by blast
  obtain row where row:
    "comma_phase_mask_row_at (families source) phase=Some row"
    "snd row=comma_rank_mask_action_of_b1_result
      (comma_semantic_b1_round_output phase source)"
    using selected by (cases "comma_phase_mask_row_at (families source) phase") auto
  show "comma_phase_mask_action_total [families source] phase 0 =
      comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase source))"
    using row by (simp add: comma_phase_mask_action_total_def
      comma_phase_mask_action_at_option_def)
qed

lemma comma_rank_local_swapped_odd_label_rejected:
  fixes even_bits odd_bits odd_piece_bits :: nat
    and swapped_rows :: "(nat \<times> comma_phase_rank_mask_action) list"
  defines "even_bits \<equiv> comma_phase_class 2 0 0"
    and "odd_bits \<equiv> comma_phase_class 2 0 1"
    and "swapped_rows \<equiv>
      [(even_bits, Comma_Phase_Rank_Mask_Fork 3 0),
       (odd_bits, Comma_Phase_Rank_Mask_Fork 2 0)]"
    and "odd_piece_bits \<equiv> odd_bits AND mask 924"
  shows "comma_phase_mask_rows_partition swapped_rows \<and>
      comma_rank_local_family_well_formed swapped_rows \<and>
      \<not> comma_rank_local_piece_covered swapped_rows
        (Comma_Phase_Rank_Mask_Fork 3 0) odd_piece_bits"
proof -
  have even_bounded: "take_bit 924 even_bits=even_bits"
    unfolding even_bits_def by (rule comma_mask_phase_class_bounded[OF refl])
  have odd_bounded: "take_bit 924 odd_bits=odd_bits"
    unfolding odd_bits_def by (rule comma_mask_phase_class_bounded[OF refl])
  have disjoint: "even_bits AND odd_bits=0"
    unfolding even_bits_def odd_bits_def
    by (rule comma_phase_class_disjoint) simp
  have disjoint_sym: "odd_bits AND even_bits=0"
    unfolding even_bits_def odd_bits_def
    by (rule comma_phase_class_disjoint) simp
  have cover: "comma_mask_union [even_bits,odd_bits]=mask 924"
  proof -
    have "comma_mask_union
        (map (comma_phase_class 2 0) [0..<2])=mask 924"
      by (rule comma_phase_class_partition) simp
    then show ?thesis by (simp add: even_bits_def odd_bits_def upt_rec)
  qed
  have partition: "comma_phase_mask_rows_partition swapped_rows"
    unfolding swapped_rows_def
    using even_bounded odd_bounded disjoint disjoint_sym cover
    by (auto simp: comma_phase_mask_rows_partition_def)
  have well_formed: "comma_rank_local_family_well_formed swapped_rows"
    using partition by (auto simp: comma_rank_local_family_well_formed_def
      swapped_rows_def)
  have odd_at_one: "comma_phase_member odd_bits 1"
    unfolding odd_bits_def by (simp add: comma_phase_class_member)
  have even_not_at_one: "\<not> comma_phase_member even_bits 1"
    unfolding even_bits_def by (simp add: comma_phase_class_member)
  have full_at_one: "comma_phase_member (mask 924) 1"
    by (simp add: comma_phase_member_def bit_simps)
  have piece_at_one: "comma_phase_member odd_piece_bits 1"
    unfolding odd_piece_bits_def
    using odd_at_one full_at_one by (simp add: comma_phase_member_and)
  have piece_nonzero: "odd_piece_bits\<noteq>0"
    by (rule comma_rank_local_piece_at_phase_nonzero[OF piece_at_one])
  have fork3_column:
    "comma_rank_local_column swapped_rows
      (Comma_Phase_Rank_Mask_Fork 3 0)=Some even_bits"
    unfolding comma_rank_local_column_def swapped_rows_def by simp
  have no_odd_piece_coverage:
    "\<not> comma_rank_local_piece_covered swapped_rows
      (Comma_Phase_Rank_Mask_Fork 3 0) odd_piece_bits"
  proof
    assume covered: "comma_rank_local_piece_covered swapped_rows
      (Comma_Phase_Rank_Mask_Fork 3 0) odd_piece_bits"
    obtain column where column:
      "comma_rank_local_column swapped_rows
        (Comma_Phase_Rank_Mask_Fork 3 0)=Some column"
      "comma_phase_member column 1"
      by (rule comma_rank_local_piece_covered_member
        [OF piece_nonzero piece_at_one covered])
    have "column=even_bits" using column(1) fork3_column by simp
    with column(2) even_not_at_one show False by simp
  qed
  show ?thesis using partition well_formed no_odd_piece_coverage by blast
qed

ML \<open>
  val checked = @{thms comma_rank_local_column_someE
    comma_rank_local_piece_covered_member
    comma_rank_local_row_at_column_label comma_rank_source_domain_lookup_exact
    comma_rank_source_domain_action_exact
    comma_rank_local_swapped_odd_label_rejected};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Local source coverage depends on an oracle";
\<close>

end
