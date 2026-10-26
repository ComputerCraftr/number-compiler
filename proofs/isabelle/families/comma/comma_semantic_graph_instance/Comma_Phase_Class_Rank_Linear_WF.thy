theory Comma_Phase_Class_Rank_Linear_WF
  imports Comma_Phase_Class_Rank_Source_Family_Adapter
begin

text \<open>
This checker admits a row family by a single left-to-right mask fold.  Its
accumulator is the union of every preceding column.  Each next mask is
bounded, disjoint from that accumulator, and has a label not seen earlier;
the final accumulator must be the complete 924-phase mask.
\<close>

fun comma_rank_local_linear_partition_check ::
  "(nat \<times> 'label) list \<Rightarrow> nat \<Rightarrow> 'label set \<Rightarrow> bool"
where
  "comma_rank_local_linear_partition_check [] accumulated seen =
    (accumulated=mask 924)"
| "comma_rank_local_linear_partition_check ((bits,label)#rows) accumulated seen =
    (take_bit 924 bits=bits \<and> accumulated AND bits=0 \<and>
      label\<notin>seen \<and>
      comma_rank_local_linear_partition_check rows (accumulated OR bits)
        (insert label seen))"

lemma comma_rank_local_and_or_zeroD:
  fixes left right bits_mask :: nat
  assumes zero: "(left OR right) AND bits_mask=0"
  shows "left AND bits_mask=0" and "right AND bits_mask=0"
proof -
  show "left AND bits_mask=0"
  proof (rule bit_eqI)
    fix bit_index
    have zero_bit: "\<not>bit ((left OR right) AND bits_mask) bit_index"
      using zero by simp
    show "bit (left AND bits_mask) bit_index=bit 0 bit_index"
      using zero_bit by (auto simp: bit_simps)
  qed
  show "right AND bits_mask=0"
  proof (rule bit_eqI)
    fix bit_index
    have zero_bit: "\<not>bit ((left OR right) AND bits_mask) bit_index"
      using zero by simp
    show "bit (right AND bits_mask) bit_index=bit 0 bit_index"
      using zero_bit by (auto simp: bit_simps)
  qed
qed

lemma comma_rank_local_nat_and_commute:
  fixes left right :: nat
  shows "left AND right=right AND left"
  by (rule bit_eqI) (auto simp: bit_simps)

lemma comma_rank_local_nat_or_rearrange:
  fixes left right accumulated :: nat
  shows "(left OR right) OR accumulated = right OR (accumulated OR left)"
  by (rule bit_eqI) (auto simp: bit_simps)

lemma comma_rank_local_linear_partition_check_sound_conjunction:
  assumes checked:
    "comma_rank_local_linear_partition_check rows accumulated seen"
  shows "(\<forall>row\<in>set rows. take_bit 924 (fst row)=fst row) \<and>
      (\<forall>row\<in>set rows. accumulated AND fst row=0) \<and>
      (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
        left\<noteq>right \<longrightarrow> fst left AND fst right=0) \<and>
      (comma_mask_union (map fst rows) OR accumulated=mask 924) \<and>
      (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
        snd left=snd right \<longrightarrow> left=right) \<and>
      (set (map snd rows) \<inter> seen={})"
  using checked
proof (induction rows arbitrary: accumulated seen)
  case Nil
  then show ?case by simp
next
  case (Cons head rows)
  obtain bits label where head: "head=(bits,label)"
    by (cases head) blast
  have local:
    "take_bit 924 bits=bits \<and> accumulated AND bits=0 \<and>
      label\<notin>seen \<and>
      comma_rank_local_linear_partition_check rows (accumulated OR bits)
        (insert label seen)"
    using Cons.prems head by simp
  have row_bounded: "take_bit 924 bits=bits" using local by blast
  have head_disjoint: "accumulated AND bits=0" using local by blast
  have label_fresh: "label\<notin>seen" using local by blast
  have tail_checked:
    "comma_rank_local_linear_partition_check rows (accumulated OR bits)
      (insert label seen)"
    using local by blast
  have tail_bounded:
    "\<forall>row\<in>set rows. take_bit 924 (fst row)=fst row"
    using Cons.IH[OF tail_checked] by blast
  have tail_disjoint_accumulated:
    "\<forall>row\<in>set rows. (accumulated OR bits) AND fst row=0"
    using Cons.IH[OF tail_checked] by blast
  have tail_pairwise:
    "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left AND fst right=0"
    using Cons.IH[OF tail_checked] by blast
  have tail_complete:
    "comma_mask_union (map fst rows) OR (accumulated OR bits)=mask 924"
    using Cons.IH[OF tail_checked] by blast
  have tail_labels_unique:
    "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      snd left=snd right \<longrightarrow> left=right"
    using Cons.IH[OF tail_checked] by blast
  have tail_labels_fresh:
    "set (map snd rows) \<inter> insert label seen={}"
    using Cons.IH[OF tail_checked] by blast
  have bits_disjoint_tail:
    "\<forall>row\<in>set rows. bits AND fst row=0"
  proof (intro ballI)
    fix row
    assume row_member: "row\<in>set rows"
    have accumulated_disjoint:
      "(accumulated OR bits) AND fst row=0"
      using tail_disjoint_accumulated row_member by blast
    show "bits AND fst row=0"
      by (rule comma_rank_local_and_or_zeroD(2)[OF accumulated_disjoint])
  qed
  have accumulated_disjoint_tail:
    "\<forall>row\<in>set rows. accumulated AND fst row=0"
  proof (intro ballI)
    fix row
    assume row_member: "row\<in>set rows"
    have accumulated_disjoint:
      "(accumulated OR bits) AND fst row=0"
      using tail_disjoint_accumulated row_member by blast
    show "accumulated AND fst row=0"
      by (rule comma_rank_local_and_or_zeroD(1)[OF accumulated_disjoint])
  qed
  have head_label_not_tail: "label\<notin>set (map snd rows)"
    using tail_labels_fresh by auto
  show ?case
  proof (intro conjI)
    show "\<forall>row\<in>set (head#rows). take_bit 924 (fst row)=fst row"
      using row_bounded tail_bounded head by auto
    show "\<forall>row\<in>set (head#rows). accumulated AND fst row=0"
      using head_disjoint accumulated_disjoint_tail head by auto
    show "\<forall>left\<in>set (head#rows). \<forall>right\<in>set (head#rows).
      left\<noteq>right \<longrightarrow> fst left AND fst right=0"
      using tail_pairwise bits_disjoint_tail head
      by (auto simp: comma_rank_local_nat_and_commute)
    show "comma_mask_union (map fst (head#rows)) OR accumulated=mask 924"
      using tail_complete head
      by (simp add: comma_rank_local_nat_or_rearrange)
    show "\<forall>left\<in>set (head#rows). \<forall>right\<in>set (head#rows).
      snd left=snd right \<longrightarrow> left=right"
      using tail_labels_unique head_label_not_tail head by auto
    show "set (map snd (head#rows)) \<inter> seen={}"
      using tail_labels_fresh label_fresh head by auto
  qed
qed


lemma comma_rank_local_linear_partition_check_sound_aux:
  assumes checked:
    "comma_rank_local_linear_partition_check rows accumulated seen"
  shows "\<forall>row\<in>set rows. take_bit 924 (fst row)=fst row"
    and "\<forall>row\<in>set rows. accumulated AND fst row=0"
    and "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left AND fst right=0"
    and "comma_mask_union (map fst rows) OR accumulated=mask 924"
    and "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      snd left=snd right \<longrightarrow> left=right"
    and "set (map snd rows) \<inter> seen={}"
  using comma_rank_local_linear_partition_check_sound_conjunction[OF checked]
  by blast+

theorem comma_rank_local_linear_partition_check_sound:
  assumes checked:
    "comma_rank_local_linear_partition_check rows 0 {}"
  shows "comma_rank_local_family_well_formed rows"
proof -
  have bounded:
    "\<forall>row\<in>set rows. take_bit 924 (fst row)=fst row"
    by (rule comma_rank_local_linear_partition_check_sound_aux(1)[OF checked])
  have pairwise:
    "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left AND fst right=0"
    by (rule comma_rank_local_linear_partition_check_sound_aux(3)[OF checked])
  have full:
    "comma_mask_union (map fst rows)=mask 924"
    using comma_rank_local_linear_partition_check_sound_aux(4)[OF checked]
    by simp
  have partition:
    "comma_phase_mask_rows_partition rows"
    using bounded pairwise full
    by (simp add: comma_phase_mask_rows_partition_def)
  have labels:
    "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      snd left=snd right \<longrightarrow> left=right"
    by (rule comma_rank_local_linear_partition_check_sound_aux(5)[OF checked])
  show ?thesis
    using partition labels
    by (simp add: comma_rank_local_family_well_formed_def)
qed

lemma comma_rank_local_linear_check_list_all_nth:
  assumes checked:
    "list_all (\<lambda>rows. comma_rank_local_linear_partition_check rows 0 {}) table"
  shows "\<And>index. index<length table \<Longrightarrow>
    comma_rank_local_family_well_formed (table!index)"
proof -
  fix index
  assume index: "index<length table"
  have member: "table!index\<in>set table"
    by (rule nth_mem[OF index])
  have check:
    "comma_rank_local_linear_partition_check (table!index) 0 {}"
    using checked member by (simp add: list_all_iff)
  show "comma_rank_local_family_well_formed (table!index)"
    by (rule comma_rank_local_linear_partition_check_sound[OF check])
qed

ML \<open>
  val checked = @{thms comma_rank_local_and_or_zeroD
    comma_rank_local_nat_and_commute comma_rank_local_nat_or_rearrange
    comma_rank_local_linear_partition_check_sound_aux
    comma_rank_local_linear_partition_check_sound};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Linear phase-mask partition checker depends on an oracle";
\<close>

end
