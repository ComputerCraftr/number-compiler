theory Comma_Phase_Class_Rank_Source_Family_Adapter
  imports Comma_Phase_Class_Rank_Rotation
begin

text \<open>
A source binding points to one canonical row template and carries the
source's cyclic origin separately.  The source-facing family is the inverse
rotation, so its phase lookup remains in the original source clock.  Missing
or invalid bindings stay `None`; the list adapter below uses the empty list
only as a fail-closed value, which cannot satisfy the full-partition part of
the source-source_domain contract.
\<close>

definition comma_rank_local_source_family_option ::
  "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
    ('source \<times> (nat \<times> nat)) list \<Rightarrow> 'source \<Rightarrow>
    ((nat \<times> comma_phase_rank_mask_action) list) option"
where
  "comma_rank_local_source_family_option table bindings source =
    (case map_of bindings source of
       None \<Rightarrow> None
     | Some (template,origin) \<Rightarrow>
         if template<length table \<and> origin<924
         then Some (comma_rank_local_rotate_rows (924-origin) (table!template))
         else None)"

definition comma_rank_local_source_family ::
  "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
    ('source \<times> (nat \<times> nat)) list \<Rightarrow> 'source \<Rightarrow>
    (nat \<times> comma_phase_rank_mask_action) list"
where
  "comma_rank_local_source_family table bindings source =
    (case comma_rank_local_source_family_option table bindings source of
       None \<Rightarrow> []
     | Some rows \<Rightarrow> rows)"

lemma comma_rank_local_source_family_option_exact:
  assumes binding: "map_of bindings source=Some (template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
  shows "comma_rank_local_source_family_option table bindings source =
    Some (comma_rank_local_rotate_rows (924-origin) (table!template))"
  using binding template_bound origin_bound
  by (simp add: comma_rank_local_source_family_option_def)

lemma comma_rank_local_source_family_template_well_formed:
  assumes binding: "map_of bindings source=Some (template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    and template_well_formed:
      "comma_rank_local_family_well_formed (table!template)"
  shows "comma_rank_local_source_family_option table bindings source =
      Some (comma_rank_local_rotate_rows (924-origin) (table!template))"
    and "comma_rank_local_family_well_formed
      (comma_rank_local_rotate_rows (924-origin) (table!template))"
    and "comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
proof -
  show option_exact:
    "comma_rank_local_source_family_option table bindings source =
      Some (comma_rank_local_rotate_rows (924-origin) (table!template))"
    by (rule comma_rank_local_source_family_option_exact
      [OF binding template_bound origin_bound])
  have rotated_well_formed:
    "comma_rank_local_family_well_formed
      (comma_rank_local_rotate_rows (924-origin) (table!template))"
    by (rule comma_rank_local_rotate_rows_well_formed[OF template_well_formed])
  show "comma_rank_local_family_well_formed
      (comma_rank_local_rotate_rows (924-origin) (table!template))"
    by (rule rotated_well_formed)
  show "comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
    using option_exact rotated_well_formed
    by (simp add: comma_rank_local_source_family_def)
qed

lemma comma_rank_local_source_family_lookup:
  assumes binding: "map_of bindings source=Some (template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    and phase_bound: "phase<924"
    and template_well_formed:
      "comma_rank_local_family_well_formed (table!template)"
  shows "map_option snd (comma_phase_mask_row_at
      (comma_rank_local_source_family table bindings source) phase) =
    map_option snd (comma_phase_mask_row_at (table!template)
      (comma_rank_local_canonical_phase origin phase))"
proof -
  have option_exact:
    "comma_rank_local_source_family_option table bindings source =
      Some (comma_rank_local_rotate_rows (924-origin) (table!template))"
    by (rule comma_rank_local_source_family_option_exact
      [OF binding template_bound origin_bound])
  have source_family:
    "comma_rank_local_source_family table bindings source =
      comma_rank_local_rotate_rows (924-origin) (table!template)"
    using option_exact by (simp add: comma_rank_local_source_family_def)
  have lookup:
    "map_option snd (comma_phase_mask_row_at
      (comma_rank_local_rotate_rows (924-origin) (table!template)) phase) =
      map_option snd (comma_phase_mask_row_at (table!template)
        ((phase+(924-origin)) mod 924))"
    by (rule comma_rank_local_rotate_rows_lookup
      [OF template_well_formed phase_bound, of "924-origin"])
  show ?thesis
    using source_family lookup
    by (simp only: comma_rank_local_canonical_phase_def)
qed

lemma comma_rank_local_source_family_live_successor_lookup:
  assumes binding: "map_of bindings source=Some (template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    and phase_bound: "phase<924"
    and template_well_formed:
      "comma_rank_local_family_well_formed (table!template)"
  shows "map_option snd (comma_phase_mask_row_at
      (comma_rank_local_source_family table bindings source)
      ((phase+1) mod 924)) =
    map_option snd (comma_phase_mask_row_at (table!template)
      (comma_rank_local_canonical_phase origin ((phase+1) mod 924)))"
  by (rule comma_rank_local_source_family_lookup
    [OF binding template_bound origin_bound, of "(phase+1) mod 924"])
    (use phase_bound template_well_formed in auto)

lemma comma_rank_local_catalog_source_family_well_formed:
  assumes catalog: "bindings=zip sources values"
    and lengths: "length sources=length values"
    and distinct_sources: "distinct sources"
    and index: "index<length values"
    and source: "source=sources!index"
    and binding_entry: "values!index=(template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    and template_well_formed:
      "comma_rank_local_family_well_formed (table!template)"
  shows "comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
proof -
  have binding: "map_of bindings source=Some (template,origin)"
    using comma_rank_local_catalog_binding_nth
      [OF catalog lengths distinct_sources index]
      source binding_entry by simp
  show ?thesis
    by (rule comma_rank_local_source_family_template_well_formed(3)
      [OF binding template_bound origin_bound template_well_formed])
qed

lemma comma_rank_local_catalog_domain_families_well_formed:
  assumes catalog: "bindings=zip sources values"
    and lengths: "length sources=length values"
    and distinct_sources: "distinct sources"
    and domain_covered:
      "\<And>source. source\<in>set source_domain \<Longrightarrow>
        \<exists>index template origin. index<length values \<and>
          source=sources!index \<and> values!index=(template,origin) \<and>
          template<length table \<and> origin<924"
    and template_well_formed:
      "\<And>template. template<length table \<Longrightarrow>
        comma_rank_local_family_well_formed (table!template)"
  shows "\<forall>source\<in>set source_domain.
    comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
proof (intro ballI)
  fix source
  assume source_member: "source\<in>set source_domain"
  obtain index template origin where index_bound: "index<length values"
    and source_index: "source=sources!index"
    and binding_entry: "values!index=(template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    using domain_covered[OF source_member] by blast
  have template_wf:
    "comma_rank_local_family_well_formed (table!template)"
    by (rule template_well_formed[OF template_bound])
  show "comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
    by (rule comma_rank_local_catalog_source_family_well_formed
      [OF catalog lengths distinct_sources index_bound source_index binding_entry
        template_bound origin_bound template_wf])
qed

definition comma_rank_local_canonical_entry_sources where
  "comma_rank_local_canonical_entry_sources =
    map (\<lambda>index. Comma_Entry 1 0 (comma_offset_representatives!index))
      [0..<46]"

lemma comma_rank_local_canonical_entry_sources_member:
  assumes catalog: "set comma_rank_local_canonical_entry_sources\<subseteq>set sources"
  shows "\<And>index. index<46 \<Longrightarrow>
    Comma_Entry 1 0 (comma_offset_representatives!index)\<in>set sources"
  using catalog
  by (auto simp: comma_rank_local_canonical_entry_sources_def set_map)

lemma comma_rank_local_catalog_domain_contract:
  assumes catalog: "bindings=zip catalog_sources values"
    and lengths: "length catalog_sources=length values"
    and distinct_sources: "distinct catalog_sources"
    and domain_covered:
      "\<And>source. source\<in>set source_domain \<Longrightarrow>
        \<exists>index template origin. index<length values \<and>
          source=catalog_sources!index \<and> values!index=(template,origin) \<and>
          template<length table \<and> origin<924"
    and template_well_formed:
      "\<And>template. template<length table \<Longrightarrow>
        comma_rank_local_family_well_formed (table!template)"
    and local_source_facts:
      "\<And>source. source\<in>set source_domain \<Longrightarrow>
        comma_round_admitted source \<and>
        source=comma_source_continuation_base source \<and>
        comma_rank_source_local_coverage source_domain
          (comma_rank_local_source_family table bindings) source"
  shows "comma_rank_source_domain_contract source_domain
    (comma_rank_local_source_family table bindings)"
proof -
  have all_families_well_formed:
    "\<forall>source\<in>set source_domain.
      comma_rank_local_family_well_formed
        (comma_rank_local_source_family table bindings source)"
    by (rule comma_rank_local_catalog_domain_families_well_formed
      [OF catalog lengths distinct_sources domain_covered template_well_formed])
  show ?thesis
    unfolding comma_rank_source_domain_contract_def
    using all_families_well_formed local_source_facts by blast
qed

lemma comma_rank_local_bindings_nth_lookup:
  assumes distinct_keys: "distinct (map fst bindings)"
    and index: "index<length bindings"
  shows "map_of bindings (fst (bindings!index))=Some (snd (bindings!index))"
proof -
  have lengths:
    "length (map fst bindings)=length (map snd bindings)"
    by simp
  have index_values: "index<length (map snd bindings)"
    using index by simp
  have zipped:
    "map_of (zip (map fst bindings) (map snd bindings))
      ((map fst bindings)!index)=Some ((map snd bindings)!index)"
    by (rule map_of_zip_nth[OF lengths distinct_keys index_values])
  have bindings_as_zip:
    "bindings=zip (map fst bindings) (map snd bindings)"
    by (rule zip_map_fst_snd[symmetric])
  show ?thesis using zipped bindings_as_zip index by simp
qed

lemma comma_rank_local_bindings_nth_family_well_formed:
  assumes distinct_keys: "distinct (map fst bindings)"
    and index: "index<length bindings"
    and binding_entry: "snd (bindings!index)=(template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    and template_well_formed:
      "comma_rank_local_family_well_formed (table!template)"
  shows "comma_rank_local_family_well_formed
    (comma_rank_local_source_family table bindings (fst (bindings!index)))"
proof -
  have lookup:
    "map_of bindings (fst (bindings!index))=Some (template,origin)"
    using comma_rank_local_bindings_nth_lookup[OF distinct_keys index]
      binding_entry by simp
  show ?thesis
    by (rule comma_rank_local_source_family_template_well_formed(3)
      [OF lookup template_bound origin_bound template_well_formed])
qed

lemma comma_rank_local_bindings_nth_family_exact:
  assumes distinct_keys: "distinct (map fst bindings)"
    and index: "index<length bindings"
    and template_bound: "fst (snd (bindings!index))<length table"
    and origin_bound: "snd (snd (bindings!index))<924"
  shows "comma_rank_local_source_family table bindings (fst (bindings!index)) =
    comma_rank_local_rotate_rows (924-snd (snd (bindings!index)))
      (table!fst (snd (bindings!index)))"
proof -
  let ?template = "fst (snd (bindings!index))"
  let ?origin = "snd (snd (bindings!index))"
  have lookup:
    "map_of bindings (fst (bindings!index))=Some (?template,?origin)"
    using comma_rank_local_bindings_nth_lookup[OF distinct_keys index]
    by (simp only: prod.collapse)
  have option_exact:
    "comma_rank_local_source_family_option table bindings (fst (bindings!index)) =
      Some (comma_rank_local_rotate_rows (924-?origin) (table!?template))"
    by (rule comma_rank_local_source_family_option_exact
      [OF lookup template_bound origin_bound])
  show ?thesis
    using option_exact by (simp add: comma_rank_local_source_family_def)
qed

lemma comma_rank_local_bindings_all_families_exact:
  assumes distinct_keys: "distinct (map fst bindings)"
    and entries_bounded:
      "\<And>index. index<length bindings \<Longrightarrow>
        fst (snd (bindings!index))<length table \<and>
        snd (snd (bindings!index))<924"
  shows "\<forall>index<length bindings.
    comma_rank_local_source_family table bindings (fst (bindings!index)) =
      comma_rank_local_rotate_rows (924-snd (snd (bindings!index)))
        (table!fst (snd (bindings!index)))"
proof (intro allI impI)
  fix index
  assume index: "index<length bindings"
  obtain template_bound origin_bound where
    bounds: "fst (snd (bindings!index))<length table"
      "snd (snd (bindings!index))<924"
    using entries_bounded[OF index] by blast
  show "comma_rank_local_source_family table bindings (fst (bindings!index)) =
    comma_rank_local_rotate_rows (924-snd (snd (bindings!index)))
      (table!fst (snd (bindings!index)))"
    by (rule comma_rank_local_bindings_nth_family_exact
      [OF distinct_keys index bounds(1) bounds(2)])
qed

lemma comma_rank_local_bindings_domain_families_well_formed:
  assumes distinct_keys: "distinct (map fst bindings)"
    and domain_covered:
      "\<And>source. source\<in>set source_domain \<Longrightarrow>
        \<exists>index template origin. index<length bindings \<and>
          source=fst (bindings!index) \<and>
          snd (bindings!index)=(template,origin) \<and>
          template<length table \<and> origin<924"
    and template_well_formed:
      "\<And>template. template<length table \<Longrightarrow>
        comma_rank_local_family_well_formed (table!template)"
  shows "\<forall>source\<in>set source_domain.
    comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
proof (intro ballI)
  fix source
  assume source_member: "source\<in>set source_domain"
  obtain index template origin where index_bound: "index<length bindings"
    and source_index: "source=fst (bindings!index)"
    and binding_entry: "snd (bindings!index)=(template,origin)"
    and template_bound: "template<length table"
    and origin_bound: "origin<924"
    using domain_covered[OF source_member] by blast
  have template_wf:
    "comma_rank_local_family_well_formed (table!template)"
    by (rule template_well_formed[OF template_bound])
  show "comma_rank_local_family_well_formed
      (comma_rank_local_source_family table bindings source)"
    unfolding source_index
    by (rule comma_rank_local_bindings_nth_family_well_formed
      [OF distinct_keys index_bound binding_entry template_bound origin_bound
        template_wf])
qed

lemma comma_rank_local_bindings_canonical_roots_member:
  assumes roots_covered:
    "set comma_rank_local_canonical_entry_sources\<subseteq>set (map fst bindings)"
  shows "\<And>index. index<46 \<Longrightarrow>
    Comma_Entry 1 0 (comma_offset_representatives!index)\<in>
      set (map fst bindings)"
  by (rule comma_rank_local_canonical_entry_sources_member[OF roots_covered])

lemma comma_rank_local_bindings_indexed_fact_transfer:
  fixes property :: "'source \<Rightarrow> bool"
  assumes indexed: "\<And>index. index<length bindings \<Longrightarrow>
      property (fst (bindings!index))"
  shows "\<And>source. source\<in>set (map fst bindings) \<Longrightarrow>
      property source"
proof -
  fix source
  assume member: "source\<in>set (map fst bindings)"
  obtain index where index: "index<length bindings"
    and selected: "source=fst (bindings!index)"
    using member by (auto simp: in_set_conv_nth nth_map)
  show "property source"
    using indexed[OF index] selected by simp
qed

lemma comma_rank_local_bindings_domain_contract:
  assumes distinct_keys: "distinct (map fst bindings)"
    and entries_bounded:
      "\<And>index. index<length bindings \<Longrightarrow>
        fst (snd (bindings!index))<length table \<and>
        snd (snd (bindings!index))<924"
    and template_well_formed:
      "\<And>template. template<length table \<Longrightarrow>
        comma_rank_local_family_well_formed (table!template)"
    and local_source_facts:
      "\<And>index. index<length bindings \<Longrightarrow>
        comma_round_admitted (fst (bindings!index)) \<and>
        fst (bindings!index)=comma_source_continuation_base
          (fst (bindings!index)) \<and>
        comma_rank_source_local_coverage (map fst bindings)
          (comma_rank_local_source_family table bindings)
          (fst (bindings!index))"
  shows "comma_rank_source_domain_contract (map fst bindings)
    (comma_rank_local_source_family table bindings)"
proof -
  have indexed_well_formed:
    "\<And>index. index<length bindings \<Longrightarrow>
      comma_rank_local_family_well_formed
        (comma_rank_local_source_family table bindings (fst (bindings!index)))"
  proof -
    fix index
    assume index: "index<length bindings"
    let ?template = "fst (snd (bindings!index))"
    let ?origin = "snd (snd (bindings!index))"
    have bounds: "?template<length table" "?origin<924"
      using entries_bounded[OF index] by auto
    have binding_entry: "snd (bindings!index)=(?template,?origin)" by simp
    have template_wf: "comma_rank_local_family_well_formed (table!?template)"
      by (rule template_well_formed[OF bounds(1)])
    show "comma_rank_local_family_well_formed
        (comma_rank_local_source_family table bindings (fst (bindings!index)))"
      by (rule comma_rank_local_bindings_nth_family_well_formed
        [OF distinct_keys index binding_entry bounds(1) bounds(2) template_wf])
  qed
  have all_families_well_formed:
    "\<forall>source\<in>set (map fst bindings).
      comma_rank_local_family_well_formed
        (comma_rank_local_source_family table bindings source)"
    by (intro ballI)
      (rule comma_rank_local_bindings_indexed_fact_transfer
        [where bindings=bindings and property="\<lambda>source.
          comma_rank_local_family_well_formed
            (comma_rank_local_source_family table bindings source)",
         OF indexed_well_formed], assumption)
  have local_facts:
    "\<And>source. source\<in>set (map fst bindings) \<Longrightarrow>
      comma_round_admitted source \<and>
      source=comma_source_continuation_base source \<and>
      comma_rank_source_local_coverage (map fst bindings)
        (comma_rank_local_source_family table bindings) source"
    by (rule comma_rank_local_bindings_indexed_fact_transfer
      [where bindings=bindings and property="\<lambda>source.
        comma_round_admitted source \<and>
        source=comma_source_continuation_base source \<and>
        comma_rank_source_local_coverage (map fst bindings)
          (comma_rank_local_source_family table bindings) source",
       OF local_source_facts])
  show ?thesis
    unfolding comma_rank_source_domain_contract_def
    using all_families_well_formed local_facts by blast
qed


lemma comma_rank_local_list_all_map_fst_nth:
  fixes property :: "'source \<Rightarrow> bool"
  assumes checked: "list_all property (map fst bindings)"
  shows "\<And>index. index<length bindings \<Longrightarrow>
      property (fst (bindings!index))"
proof -
  fix index
  assume index: "index<length bindings"
  have member: "fst (bindings!index)\<in>set (map fst bindings)"
    using nth_mem[OF index] by (auto simp: set_map)
  show "property (fst (bindings!index))"
    using checked member by (auto simp: list_all_iff set_map)
qed

lemma comma_rank_local_list_all_nth:
  fixes property :: "'entry \<Rightarrow> bool"
  assumes checked: "list_all property entries"
  shows "\<And>index. index<length entries \<Longrightarrow>
      property (entries!index)"
proof -
  fix index
  assume index: "index<length entries"
  have member: "entries!index\<in>set entries"
    by (rule nth_mem[OF index])
  show "property (entries!index)"
    using checked member by (simp add: list_all_iff)
qed

ML \<open>
  val checked = @{thms comma_rank_local_source_family_option_exact
    comma_rank_local_source_family_template_well_formed
    comma_rank_local_source_family_lookup
    comma_rank_local_source_family_live_successor_lookup
    comma_rank_local_catalog_source_family_well_formed
    comma_rank_local_catalog_domain_families_well_formed
    comma_rank_local_canonical_entry_sources_member
    comma_rank_local_catalog_domain_contract
    comma_rank_local_bindings_nth_lookup
    comma_rank_local_bindings_nth_family_well_formed
    comma_rank_local_bindings_nth_family_exact
    comma_rank_local_bindings_all_families_exact
    comma_rank_local_bindings_domain_families_well_formed
    comma_rank_local_bindings_canonical_roots_member
    comma_rank_local_bindings_indexed_fact_transfer
    comma_rank_local_bindings_domain_contract};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Canonical source-family adapter depends on an oracle";
\<close>

end
