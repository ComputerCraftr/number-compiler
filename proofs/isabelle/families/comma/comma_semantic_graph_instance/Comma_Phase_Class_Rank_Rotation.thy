theory Comma_Phase_Class_Rank_Rotation
  imports Comma_Phase_Class_Rank_Local_Coverage
begin

text \<open>
Clock translation acts on a family's mask rows as a single geometry
operation.  It preserves the partition and unique labels, while option row
lookup at receiver phase r is the unrotated lookup at (r+delta) mod 924.
The row list is never expanded into phase cells.
\<close>

definition comma_rank_local_rotate_rows ::
  "nat \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list" where
  "comma_rank_local_rotate_rows delta rows =
    map (\<lambda>row. (comma_rotate_phase delta (fst row), snd row)) rows"

lemma comma_rank_local_rotate_phase_bounded:
  "take_bit 924 (comma_rotate_phase delta bits)=comma_rotate_phase delta bits"
  by (simp add: comma_rotate_phase_def Let_def)

lemma comma_rank_local_rotate_phase_zero [simp]:
  "comma_rotate_phase delta 0=0"
  by (simp add: comma_rotate_phase_def Let_def bit_simps)

lemma comma_rank_local_rotate_phase_and:
  "comma_rotate_phase delta (left AND right) =
    comma_rotate_phase delta left AND comma_rotate_phase delta right"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_rotate_phase delta (left AND right)) phase =
      bit (comma_rotate_phase delta left AND comma_rotate_phase delta right) phase"
  proof (cases "phase<924")
    case True
    have lhs:
      "comma_phase_member (comma_rotate_phase delta (left AND right)) phase =
        comma_phase_member (left AND right) ((phase+delta) mod 924)"
      by (rule comma_rotate_phase_member[OF True])
    have rhs:
      "comma_phase_member
          (comma_rotate_phase delta left AND comma_rotate_phase delta right) phase =
        comma_phase_member (left AND right) ((phase+delta) mod 924)"
      by (simp add: comma_phase_member_and comma_rotate_phase_member True)
    show ?thesis using lhs rhs True
      by (simp add: comma_phase_member_def)
  next
    case False
    show ?thesis using False
      by (simp add: comma_rotate_phase_def Let_def bit_simps)
  qed
qed

lemma comma_rank_local_rotate_phase_or:
  "comma_rotate_phase delta (left OR right) =
    comma_rotate_phase delta left OR comma_rotate_phase delta right"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_rotate_phase delta (left OR right)) phase =
      bit (comma_rotate_phase delta left OR comma_rotate_phase delta right) phase"
  proof (cases "phase<924")
    case True
    have lhs:
      "comma_phase_member (comma_rotate_phase delta (left OR right)) phase =
        comma_phase_member (left OR right) ((phase+delta) mod 924)"
      by (rule comma_rotate_phase_member[OF True])
    have rhs:
      "comma_phase_member
          (comma_rotate_phase delta left OR comma_rotate_phase delta right) phase =
        comma_phase_member (left OR right) ((phase+delta) mod 924)"
      by (simp add: comma_phase_member_or comma_rotate_phase_member True)
    show ?thesis using lhs rhs True
      by (simp add: comma_phase_member_def)
  next
    case False
    show ?thesis using False
      by (simp add: comma_rotate_phase_def Let_def bit_simps)
  qed
qed

lemma comma_rank_local_rotate_phase_union:
  "comma_rotate_phase delta (comma_mask_union masks) =
    comma_mask_union (map (comma_rotate_phase delta) masks)"
  by (induction masks) (simp_all add: comma_rank_local_rotate_phase_or)

lemma comma_rank_local_rotate_phase_full:
  "comma_rotate_phase delta (mask 924)=mask 924"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_rotate_phase delta (mask 924)) phase=bit (mask 924::nat) phase"
  proof (cases "phase<924")
    case True
    have member:
      "comma_phase_member (comma_rotate_phase delta (mask 924)) phase =
        comma_phase_member (mask 924) ((phase+delta) mod 924)"
      by (rule comma_rotate_phase_member[OF True])
    show ?thesis using member True
      by (simp add: comma_phase_member_def bit_simps)
  next
    case False
    show ?thesis using False
      by (simp add: comma_rotate_phase_def Let_def bit_simps)
  qed
qed

lemma comma_rank_local_rotate_rows_partition:
  assumes partition: "comma_phase_mask_rows_partition rows"
  shows "comma_phase_mask_rows_partition
      (comma_rank_local_rotate_rows delta rows)"
proof -
  let ?rotated = "comma_rank_local_rotate_rows delta rows"
  have rotated_bounded:
    "list_all (\<lambda>bits. take_bit 924 bits=bits) (map fst ?rotated)"
  proof (unfold list_all_iff, intro ballI)
    fix bits
    assume bits_member: "bits\<in>set (map fst ?rotated)"
    then obtain row where row: "row\<in>set rows"
        "bits=comma_rotate_phase delta (fst row)"
      by (auto simp: comma_rank_local_rotate_rows_def set_map)
    show "take_bit 924 bits=bits"
      unfolding row(2) by (rule comma_rank_local_rotate_phase_bounded)
  qed
  have rotated_disjoint:
    "\<forall>left\<in>set ?rotated. \<forall>right\<in>set ?rotated.
      left\<noteq>right \<longrightarrow> fst left AND fst right=0"
  proof (intro ballI impI)
    fix left right
    assume left_member: "left\<in>set ?rotated"
      and right_member: "right\<in>set ?rotated"
      and different: "left\<noteq>right"
    obtain left_source where left_source: "left_source\<in>set rows"
      "left=(comma_rotate_phase delta (fst left_source),snd left_source)"
      using left_member by (auto simp: comma_rank_local_rotate_rows_def set_map)
    obtain right_source where right_source: "right_source\<in>set rows"
      "right=(comma_rotate_phase delta (fst right_source),snd right_source)"
      using right_member by (auto simp: comma_rank_local_rotate_rows_def set_map)
    have source_different: "left_source\<noteq>right_source"
    proof
      assume same: "left_source=right_source"
      show False using different left_source right_source same by simp
    qed
    have source_disjoint: "fst left_source AND fst right_source=0"
      using partition left_source right_source source_different
      by (auto simp: comma_phase_mask_rows_partition_def)
    have rotated_masks_disjoint:
      "comma_rotate_phase delta (fst left_source) AND
        comma_rotate_phase delta (fst right_source)=0"
      using source_disjoint
      by (simp only: comma_rank_local_rotate_phase_and[symmetric]
        source_disjoint comma_rank_local_rotate_phase_zero)
    show "fst left AND fst right=0"
      using rotated_masks_disjoint left_source right_source by simp
  qed
  have source_cover:
    "comma_mask_union (map fst rows)=mask 924"
    using partition by (simp add: comma_phase_mask_rows_partition_def)
  have rotated_fsts:
    "map fst ?rotated=map (comma_rotate_phase delta) (map fst rows)"
    by (simp add: comma_rank_local_rotate_rows_def)
  have rotated_cover:
    "comma_mask_union (map fst ?rotated)=mask 924"
  proof -
    have union_rotation:
      "comma_mask_union (map (comma_rotate_phase delta) (map fst rows)) =
        comma_rotate_phase delta (comma_mask_union (map fst rows))"
      by (rule comma_rank_local_rotate_phase_union[symmetric])
    show ?thesis
      unfolding rotated_fsts
      using union_rotation source_cover comma_rank_local_rotate_phase_full
      by simp
  qed
  show ?thesis
    using rotated_bounded rotated_disjoint rotated_cover
    by (simp add: comma_phase_mask_rows_partition_def list_all_iff)
qed

lemma comma_rank_local_rotate_rows_well_formed:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
  shows "comma_rank_local_family_well_formed
      (comma_rank_local_rotate_rows delta rows)"
proof -
  have partition: "comma_phase_mask_rows_partition rows"
    using well_formed
    by (simp add: comma_rank_local_family_well_formed_def)
  have rotated_partition:
    "comma_phase_mask_rows_partition (comma_rank_local_rotate_rows delta rows)"
    by (rule comma_rank_local_rotate_rows_partition[OF partition])
  have labels_unique:
    "\<forall>left\<in>set (comma_rank_local_rotate_rows delta rows).
      \<forall>right\<in>set (comma_rank_local_rotate_rows delta rows).
        snd left=snd right \<longrightarrow> left=right"
  proof (intro ballI impI)
    fix left right
    assume left_member: "left\<in>set (comma_rank_local_rotate_rows delta rows)"
      and right_member: "right\<in>set (comma_rank_local_rotate_rows delta rows)"
      and same_label: "snd left=snd right"
    obtain left_source where left_source: "left_source\<in>set rows"
      "left=(comma_rotate_phase delta (fst left_source),snd left_source)"
      using left_member by (auto simp: comma_rank_local_rotate_rows_def set_map)
    obtain right_source where right_source: "right_source\<in>set rows"
      "right=(comma_rotate_phase delta (fst right_source),snd right_source)"
      using right_member by (auto simp: comma_rank_local_rotate_rows_def set_map)
    have same_source_label: "snd left_source=snd right_source"
      using same_label left_source right_source by simp
    have source_same: "left_source=right_source"
      using well_formed left_source(1) right_source(1) same_source_label
      by (auto simp: comma_rank_local_family_well_formed_def)
    show "left=right" using left_source right_source source_same by simp
  qed
  show ?thesis
    using rotated_partition labels_unique
    by (simp add: comma_rank_local_family_well_formed_def)
qed

lemma comma_rank_local_rotate_rows_row_at:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
    and phase: "phase<924"
  shows "comma_phase_mask_row_at
      (comma_rank_local_rotate_rows delta rows) phase =
    map_option (\<lambda>row. (comma_rotate_phase delta (fst row),snd row))
      (comma_phase_mask_row_at rows ((phase+delta) mod 924))"
proof -
  let ?shifted = "(phase+delta) mod 924"
  let ?rotated = "comma_rank_local_rotate_rows delta rows"
  have partition: "comma_phase_mask_rows_partition rows"
    using well_formed
    by (simp add: comma_rank_local_family_well_formed_def)
  have rotated_well_formed:
    "comma_rank_local_family_well_formed ?rotated"
    by (rule comma_rank_local_rotate_rows_well_formed[OF well_formed])
  have rotated_partition: "comma_phase_mask_rows_partition ?rotated"
    using rotated_well_formed
    by (simp add: comma_rank_local_family_well_formed_def)
  have shifted_phase: "?shifted<924" by simp
  obtain original where original: "original\<in>set rows"
    "comma_phase_member (fst original) ?shifted"
    "comma_phase_mask_row_at rows ?shifted=Some original"
    by (rule comma_phase_mask_row_at_some[OF partition shifted_phase])
  let ?rotated_row = "(comma_rotate_phase delta (fst original),snd original)"
  have rotated_row_member: "?rotated_row\<in>set ?rotated"
    using original(1) by (auto simp: comma_rank_local_rotate_rows_def set_map)
  have rotated_row_phase: "comma_phase_member (fst ?rotated_row) phase"
  proof -
    have "comma_phase_member (comma_rotate_phase delta (fst original)) phase =
        comma_phase_member (fst original) ?shifted"
      by (rule comma_rotate_phase_member[OF phase])
    with original(2) show ?thesis by simp
  qed
  obtain selected where selected: "selected\<in>set ?rotated"
    "comma_phase_member (fst selected) phase"
    "comma_phase_mask_row_at ?rotated phase=Some selected"
    by (rule comma_phase_mask_row_at_some[OF rotated_partition phase])
  have unique: "\<exists>!row. row\<in>set ?rotated \<and>
      comma_phase_member (fst row) phase"
    by (rule comma_phase_mask_rows_partition_ex1[OF rotated_partition phase])
  have selected_is_rotated: "selected=?rotated_row"
    using unique selected rotated_row_member rotated_row_phase by blast
  have selected_lookup:
    "comma_phase_mask_row_at ?rotated phase=Some ?rotated_row"
    using selected(3) selected_is_rotated by simp
  have source_lookup:
    "map_option (\<lambda>row. (comma_rotate_phase delta (fst row),snd row))
        (comma_phase_mask_row_at rows ?shifted)=Some ?rotated_row"
    using original(3) by simp
  show ?thesis by (rule trans[OF selected_lookup source_lookup[symmetric]])
qed

lemma comma_rank_local_rotate_rows_lookup:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
    and phase: "phase<924"
  shows "map_option snd
      (comma_phase_mask_row_at (comma_rank_local_rotate_rows delta rows) phase) =
    map_option snd (comma_phase_mask_row_at rows ((phase+delta) mod 924))"
  using comma_rank_local_rotate_rows_row_at[OF well_formed phase]
  by (cases "comma_phase_mask_row_at rows ((phase+delta) mod 924)") simp_all

definition comma_rank_local_canonical_phase :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_rank_local_canonical_phase origin phase =
    (phase+(924-origin)) mod 924"

lemma comma_rank_local_canonical_phase_bound:
  assumes phase: "phase<924" and origin: "origin<924"
  shows "comma_rank_local_canonical_phase origin phase<924"
  using phase origin by (simp add: comma_rank_local_canonical_phase_def)

lemma comma_rank_local_canonical_phase_rebase:
  assumes phase: "phase<924" and origin: "origin<924"
  shows "(comma_rank_local_canonical_phase origin phase+origin) mod 924=phase"
proof -
  have origin_le: "origin\<le>924" using origin by arith
  have offset_sum:
    "phase+(924-origin)+origin=phase+924"
    using origin_le by arith
  have remainder_sum:
    "((phase+(924-origin)) mod 924+origin) mod 924 =
      (phase+(924-origin)+origin) mod 924"
    by (rule mod_add_left_eq)
  show ?thesis
    using phase remainder_sum offset_sum
    by (simp add: comma_rank_local_canonical_phase_def)
qed

text \<open>
If a canonical row mask is the raw mask evaluated at q+origin, looking up
the canonical table at p-origin recovers the raw table's label at p.  The
mask itself remains rotated; this theorem transports only the selected
typed label, so no equality of unrelated columns is assumed.
\<close>
lemma comma_rank_local_canonical_source_binding_lookup:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
    and phase: "phase<924"
    and origin: "origin<924"
  shows "map_option snd
      (comma_phase_mask_row_at
        (comma_rank_local_rotate_rows origin rows)
        (comma_rank_local_canonical_phase origin phase)) =
    map_option snd (comma_phase_mask_row_at rows phase)"
proof -
  have canonical_phase:
    "comma_rank_local_canonical_phase origin phase<924"
    by (rule comma_rank_local_canonical_phase_bound[OF phase origin])
  have shifted_phase:
    "(comma_rank_local_canonical_phase origin phase+origin) mod 924=phase"
    by (rule comma_rank_local_canonical_phase_rebase[OF phase origin])
  show ?thesis
    using comma_rank_local_rotate_rows_lookup
      [OF well_formed canonical_phase, of origin]
    by (simp only: shifted_phase)
qed

lemma comma_rank_local_canonical_source_row_binding:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
    and phase: "phase<924"
    and origin: "origin<924"
  shows "comma_phase_mask_row_at
      (comma_rank_local_rotate_rows origin rows)
      (comma_rank_local_canonical_phase origin phase) =
    map_option (\<lambda>row. (comma_rotate_phase origin (fst row),snd row))
      (comma_phase_mask_row_at rows phase)"
proof -
  have canonical_phase:
    "comma_rank_local_canonical_phase origin phase<924"
    by (rule comma_rank_local_canonical_phase_bound[OF phase origin])
  have shifted_phase:
    "(comma_rank_local_canonical_phase origin phase+origin) mod 924=phase"
    by (rule comma_rank_local_canonical_phase_rebase[OF phase origin])
  show ?thesis
    using comma_rank_local_rotate_rows_row_at
      [OF well_formed canonical_phase, of origin]
    by (simp only: shifted_phase)
qed

lemma comma_rank_local_canonical_live_successor_lookup:
  assumes well_formed: "comma_rank_local_family_well_formed rows"
    and phase: "phase<924"
    and origin: "origin<924"
  shows "map_option snd
      (comma_phase_mask_row_at
        (comma_rank_local_rotate_rows origin rows)
        (comma_rank_local_canonical_phase origin ((phase+1) mod 924))) =
    map_option snd
      (comma_phase_mask_row_at rows ((phase+1) mod 924))"
proof -
  have next_phase: "(phase+1) mod 924<924" by simp
  show ?thesis
    by (rule comma_rank_local_canonical_source_binding_lookup
      [OF well_formed next_phase origin])
qed

lemma comma_rank_local_catalog_binding_nth:
  assumes catalog: "bindings=zip sources values"
    and lengths: "length sources=length values"
    and distinct_sources: "distinct sources"
    and index: "index<length values"
  shows "map_of bindings (sources!index)=Some (values!index)"
proof -
  have zipped:
    "map_of (zip sources values) (sources!index)=Some (values!index)"
    by (rule map_of_zip_nth[OF lengths distinct_sources index])
  show ?thesis using catalog zipped by simp
qed

ML \<open>
  val checked = @{thms comma_rank_local_rotate_phase_bounded
    comma_rank_local_rotate_phase_and comma_rank_local_rotate_phase_or
    comma_rank_local_rotate_phase_union comma_rank_local_rotate_phase_full
    comma_rank_local_rotate_rows_partition comma_rank_local_rotate_rows_well_formed
    comma_rank_local_rotate_rows_row_at comma_rank_local_rotate_rows_lookup
    comma_rank_local_canonical_phase_bound
    comma_rank_local_canonical_phase_rebase
    comma_rank_local_canonical_source_binding_lookup
    comma_rank_local_canonical_source_row_binding
    comma_rank_local_canonical_live_successor_lookup
    comma_rank_local_catalog_binding_nth};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Rank-mask row rotation depends on an oracle";
\<close>

end
