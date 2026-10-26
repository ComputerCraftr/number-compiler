theory Comma_Phase_Class_Rank_Masks
  imports Comma_Phase_Class_Rank Comma_Symbolic_Phase_Masks
begin

text \<open>
Rank and one-step actions are stored as disjoint 924-bit guard rows, not
phase/control cells.  A separate premise at the final bridge authenticates
the action masks against the admitted source control.
\<close>

datatype comma_phase_rank_mask_action =
    Comma_Phase_Rank_Mask_Invalid
  | Comma_Phase_Rank_Mask_Fork nat nat
  | Comma_Phase_Rank_Mask_Landmine nat
  | Comma_Phase_Rank_Mask_Continue nat

fun comma_phase_rank_mask_lift ::
    "nat \<Rightarrow> comma_phase_rank_mask_action \<Rightarrow>
      nat comma_phase_class_action"
where
  "comma_phase_rank_mask_lift phase Comma_Phase_Rank_Mask_Invalid =
    Comma_Phase_Class_Invalid"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Fork a d) =
    Comma_Phase_Class_Fork a d"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Landmine d) =
    Comma_Phase_Class_Landmine d"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Continue c) =
    Comma_Phase_Class_Continue ((phase+1) mod 924) c"

definition comma_phase_mask_rows_partition :: "(nat \<times> 'a) list \<Rightarrow> bool" where
  "comma_phase_mask_rows_partition rows \<longleftrightarrow>
    (\<forall>row\<in>set rows. take_bit 924 (fst row)=fst row) \<and>
    (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left AND fst right=0) \<and>
    comma_mask_union (map fst rows)=mask 924"

definition comma_phase_mask_row_at ::
    "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) option" where
  "comma_phase_mask_row_at rows phase =
    (if phase<924 \<and>
        (\<exists>!row. row\<in>set rows \<and> comma_phase_member (fst row) phase)
     then Some (SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)
     else None)"

lemma comma_phase_mask_row_at_outside [simp]:
  assumes "924\<le>phase"
  shows "comma_phase_mask_row_at rows phase=None"
  using assms by (simp add: comma_phase_mask_row_at_def)

lemma comma_phase_mask_row_at_ambiguous_none:
  assumes phase: "phase<924"
    and left: "left\<in>set rows"
    and left_bit: "comma_phase_member (fst left) phase"
    and right: "right\<in>set rows"
    and right_bit: "comma_phase_member (fst right) phase"
    and distinct: "left\<noteq>right"
  shows "comma_phase_mask_row_at rows phase=None"
proof -
  have not_unique:
    "\<not>(\<exists>!row. row\<in>set rows \<and> comma_phase_member (fst row) phase)"
    using left left_bit right right_bit distinct by blast
  show ?thesis
    unfolding comma_phase_mask_row_at_def using phase not_unique by simp
qed

lemma comma_phase_mask_rows_partition_ex1:
  assumes partition: "comma_phase_mask_rows_partition rows"
    and phase: "phase<924"
  shows "\<exists>!row. row\<in>set rows \<and> comma_phase_member (fst row) phase"
proof -
  have cover: "comma_mask_union (map fst rows)=mask 924"
    using partition by (simp add: comma_phase_mask_rows_partition_def)
  have covered: "comma_phase_member (comma_mask_union (map fst rows)) phase"
    using phase cover by (simp add: comma_phase_member_def bit_simps)
  have member: "\<exists>bits\<in>set (map fst rows). comma_phase_member bits phase"
    using covered by (simp only: comma_mask_union_member)
  then obtain bits where bits: "bits\<in>set (map fst rows)"
      and bit: "comma_phase_member bits phase" by blast
  then obtain row where row: "row\<in>set rows" "fst row=bits"
    by (auto simp: set_map)
  have exists: "\<exists>row. row\<in>set rows \<and> comma_phase_member (fst row) phase"
    using row bit by blast
  show ?thesis
  proof (rule ex1I[of _ "SOME row. row\<in>set rows \<and>
      comma_phase_member (fst row) phase"])
    show " (SOME row. row\<in>set rows \<and>
        comma_phase_member (fst row) phase)\<in>set rows \<and>
        comma_phase_member
          (fst (SOME row. row\<in>set rows \<and>
            comma_phase_member (fst row) phase)) phase"
      by (rule someI_ex[OF exists])
  next
    fix other
    assume other: "other\<in>set rows \<and> comma_phase_member (fst other) phase"
    show "other = (SOME row. row\<in>set rows \<and>
        comma_phase_member (fst row) phase)"
    proof (rule ccontr)
      assume different: "other\<noteq>(SOME row. row\<in>set rows \<and>
        comma_phase_member (fst row) phase)"
      have chosen:
        "(SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)\<in>set rows \<and>
         comma_phase_member
           (fst (SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)) phase"
        by (rule someI_ex[OF exists])
      have disjoint:
        "fst other AND
          fst (SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)=0"
        using partition other chosen different
        by (auto simp: comma_phase_mask_rows_partition_def)
      have overlap:
        "comma_phase_member
          (fst other AND
            fst (SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)) phase"
        using other chosen by (auto simp: comma_phase_member_and)
      show False using overlap disjoint by (simp add: comma_phase_member_zero)
    qed
  qed
qed

lemma comma_phase_mask_row_at_some:
  assumes partition: "comma_phase_mask_rows_partition rows"
    and phase: "phase<924"
  obtains row where "row\<in>set rows"
    and "comma_phase_member (fst row) phase"
    and "comma_phase_mask_row_at rows phase=Some row"
proof -
  have unique: "\<exists>!row. row\<in>set rows \<and> comma_phase_member (fst row) phase"
    by (rule comma_phase_mask_rows_partition_ex1[OF partition phase])
  obtain row where selected:
    "row\<in>set rows \<and> comma_phase_member (fst row) phase"
    using unique by blast
  have selected_ex:
    "\<exists>row. row\<in>set rows \<and> comma_phase_member (fst row) phase"
    using selected by blast
  have chosen:
    "(SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)\<in>set rows \<and>
      comma_phase_member
        (fst (SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)) phase"
    by (rule someI_ex[OF selected_ex])
  have choice_eq:
    "(SOME row. row\<in>set rows \<and> comma_phase_member (fst row) phase)=row"
    using unique chosen selected by blast
  have exact:
    "comma_phase_mask_row_at rows phase=Some row"
    unfolding comma_phase_mask_row_at_def
    using phase unique choice_eq by simp
  show thesis
    by (rule that[OF conjunct1[OF selected] conjunct2[OF selected] exact])
qed

definition comma_phase_mask_rank_at_option ::
    "(nat \<times> nat) list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_phase_mask_rank_at_option rows phase control =
    (if control<length rows then
      map_option snd (comma_phase_mask_row_at (rows!control) phase)
     else None)"

definition comma_phase_mask_action_at_option ::
    "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action option" where
  "comma_phase_mask_action_at_option rows phase control =
    (if control<length rows then
      map_option (comma_phase_rank_mask_lift phase \<circ> snd)
        (comma_phase_mask_row_at (rows!control) phase)
     else None)"

lemma comma_phase_mask_action_at_option_outside [simp]:
  assumes "924\<le>phase"
  shows "comma_phase_mask_action_at_option rows phase control=None"
  using assms by (simp add: comma_phase_mask_action_at_option_def)

lemma comma_phase_mask_rank_at_option_outside [simp]:
  assumes "924\<le>phase"
  shows "comma_phase_mask_rank_at_option rows phase control=None"
  using assms by (simp add: comma_phase_mask_rank_at_option_def)

lemma comma_phase_mask_action_at_option_class_outside [simp]:
  assumes "length rows\<le>control"
  shows "comma_phase_mask_action_at_option rows phase control=None"
  using assms by (simp add: comma_phase_mask_action_at_option_def)

lemma comma_phase_mask_rank_at_option_class_outside [simp]:
  assumes "length rows\<le>control"
  shows "comma_phase_mask_rank_at_option rows phase control=None"
  using assms by (simp add: comma_phase_mask_rank_at_option_def)

definition comma_phase_mask_rank_transition ::
    "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
     (nat \<times> nat) list list \<Rightarrow> bool" where
  "comma_phase_mask_rank_transition actions ranks \<longleftrightarrow>
    (\<forall>source<46. \<forall>action_row\<in>set (actions!source).
      \<forall>rank_row\<in>set (ranks!source).
        (let support=fst action_row AND fst rank_row in
          if support=0 then True else
          case snd action_row of
            Comma_Phase_Rank_Mask_Invalid \<Rightarrow> False
          | Comma_Phase_Rank_Mask_Fork a d \<Rightarrow>
              2\<le>a \<and> a\<le>9 \<and> d=0 \<and> snd rank_row=0
          | Comma_Phase_Rank_Mask_Landmine d \<Rightarrow> d=0 \<and> snd rank_row=0
          | Comma_Phase_Rank_Mask_Continue target \<Rightarrow>
              target<46 \<and> snd rank_row>0 \<and>
              support AND comma_rotate_phase 1
                (fst (ranks!target!(snd rank_row-1)))=support))"

definition comma_phase_mask_rank_certificate ::
    "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
     (nat \<times> nat) list list \<Rightarrow> bool" where
  "comma_phase_mask_rank_certificate actions ranks \<longleftrightarrow>
    length actions=46 \<and> length ranks=46 \<and>
    (\<forall>control<46. comma_phase_mask_rows_partition (actions!control) \<and>
      length (ranks!control)=27 \<and>
      map snd (ranks!control)=[0..<27] \<and>
      (\<forall>row\<in>set (ranks!control). snd row\<le>26) \<and>
      comma_phase_mask_rows_partition (ranks!control)) \<and>
    comma_phase_mask_rank_transition actions ranks"

lemma comma_phase_mask_rank_choice_of_some:
  assumes selection: "comma_phase_mask_rank_at_option rows phase control=Some rank"
  shows "(THE chosen. comma_phase_mask_rank_at_option rows phase control=Some chosen)=rank"
  by (rule the_equality) (use selection in auto)

definition comma_phase_mask_action_total ::
    "(nat \<times> comma_phase_rank_mask_action) list list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action" where
  "comma_phase_mask_action_total rows phase control =
    (case comma_phase_mask_action_at_option rows phase control of Some action \<Rightarrow> action
     | None \<Rightarrow> Comma_Phase_Class_Invalid)"

lemma comma_phase_mask_rank_certificate_partition:
  assumes certificate: "comma_phase_mask_rank_certificate actions ranks"
    and control: "control<46"
  shows "comma_phase_mask_rows_partition (actions!control)"
    and "comma_phase_mask_rows_partition (ranks!control)"
    and "length (ranks!control)=27"
    and "map snd (ranks!control)=[0..<27]"
  using certificate control by (auto simp: comma_phase_mask_rank_certificate_def)

lemma comma_phase_mask_rank_certificate_checked:
  assumes certificate: "comma_phase_mask_rank_certificate actions ranks"
  shows "comma_phase_class_rank_check
    (\<lambda>phase control. phase<924 \<and> control<46)
    (\<lambda>phase control.
      THE chosen. comma_phase_mask_rank_at_option ranks phase control=Some chosen)
    (comma_phase_mask_action_total actions)"
proof (unfold comma_phase_class_rank_check_def, intro allI impI)
  let ?rank = "\<lambda>phase control.
    THE chosen. comma_phase_mask_rank_at_option ranks phase control=Some chosen"
  fix phase control :: nat
  assume valid: "phase<924 \<and> control<46"
  have phase: "phase<924" and control: "control<46" using valid by auto
  have action_partition:
    "comma_phase_mask_rows_partition (actions!control)"
    by (rule comma_phase_mask_rank_certificate_partition(1)[OF certificate control])
  have rank_partition:
    "comma_phase_mask_rows_partition (ranks!control)"
    by (rule comma_phase_mask_rank_certificate_partition(2)[OF certificate control])
  obtain action_row where action_member:
    "action_row\<in>set (actions!control)"
    and action_bit: "comma_phase_member (fst action_row) phase"
    and action_lookup:
      "comma_phase_mask_row_at (actions!control) phase=Some action_row"
    by (rule comma_phase_mask_row_at_some[OF action_partition phase])
  obtain rank_row where rank_member:
    "rank_row\<in>set (ranks!control)"
    and rank_bit: "comma_phase_member (fst rank_row) phase"
    and rank_lookup:
      "comma_phase_mask_row_at (ranks!control) phase=Some rank_row"
    by (rule comma_phase_mask_row_at_some[OF rank_partition phase])
  have overlap:
    "comma_phase_member (fst action_row AND fst rank_row) phase"
    using action_bit rank_bit by (simp add: comma_phase_member_and)
  have overlap_nonzero: "fst action_row AND fst rank_row\<noteq>0"
  proof
    assume empty: "fst action_row AND fst rank_row=0"
    have "comma_phase_member 0 phase"
      using overlap by (simp only: empty)
    then show False by (simp add: comma_phase_member_zero)
  qed
  have transition: "comma_phase_mask_rank_transition actions ranks"
    using certificate by (simp add: comma_phase_mask_rank_certificate_def)
  have action_table_length: "length actions=46"
    using certificate by (simp add: comma_phase_mask_rank_certificate_def)
  have rank_table_length: "length ranks=46"
    using certificate by (simp add: comma_phase_mask_rank_certificate_def)
  have row_law:
    "case snd action_row of
       Comma_Phase_Rank_Mask_Invalid \<Rightarrow> False
     | Comma_Phase_Rank_Mask_Fork a d \<Rightarrow>
         2\<le>a \<and> a\<le>9 \<and> d=0 \<and> snd rank_row=0
     | Comma_Phase_Rank_Mask_Landmine d \<Rightarrow> d=0 \<and> snd rank_row=0
     | Comma_Phase_Rank_Mask_Continue target \<Rightarrow>
         target<46 \<and> snd rank_row>0 \<and>
         (fst action_row AND fst rank_row) AND
           comma_rotate_phase 1
             (fst (ranks!target!(snd rank_row-1)))=
           fst action_row AND fst rank_row"
    using transition control action_member rank_member overlap_nonzero
    by (auto simp: comma_phase_mask_rank_transition_def Let_def)
  have action_value:
    "comma_phase_mask_action_at_option actions phase control =
      Some (comma_phase_rank_mask_lift phase (snd action_row))"
    using control action_table_length action_lookup
    by (simp add: comma_phase_mask_action_at_option_def)
  have rank_value:
    "comma_phase_mask_rank_at_option ranks phase control=Some (snd rank_row)"
    using control rank_table_length rank_lookup
    by (simp add: comma_phase_mask_rank_at_option_def)
  have current_rank:
    "?rank phase control=snd rank_row"
    using comma_phase_mask_rank_choice_of_some[OF rank_value] by simp
  show "case comma_phase_mask_action_total actions phase control of
      Comma_Phase_Class_Invalid \<Rightarrow> False
    | Comma_Phase_Class_Fork a d \<Rightarrow> True
    | Comma_Phase_Class_Landmine d \<Rightarrow> True
    | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
        (next_phase<924 \<and> next_class<46) \<and>
          ?rank next_phase next_class < ?rank phase control"
  proof (cases "snd action_row")
    case Comma_Phase_Rank_Mask_Invalid
    then show ?thesis using row_law action_value by
      (simp add: comma_phase_mask_action_total_def)
  next
    case (Comma_Phase_Rank_Mask_Fork a d)
    then show ?thesis using row_law action_value by
      (simp add: comma_phase_mask_action_total_def)
  next
    case (Comma_Phase_Rank_Mask_Landmine d)
    then show ?thesis using row_law action_value by
      (simp add: comma_phase_mask_action_total_def)
  next
    case (Comma_Phase_Rank_Mask_Continue target)
    have target_bound: "target<46" and rank_positive: "snd rank_row>0"
      using row_law Comma_Phase_Rank_Mask_Continue by auto
    have rank_bound: "snd rank_row\<le>26"
      using certificate control rank_member
      by (auto simp: comma_phase_mask_rank_certificate_def)
    let ?next_phase = "(phase+1) mod 924"
    have next_phase_bound: "?next_phase<924" by simp
    have target_partition:
      "comma_phase_mask_rows_partition (ranks!target)"
      by (rule comma_phase_mask_rank_certificate_partition(2)[OF certificate target_bound])
    have target_level_bound: "snd rank_row-1<27"
      using rank_bound rank_positive by arith
    let ?target_row = "ranks!target!(snd rank_row-1)"
    have target_length: "length (ranks!target)=27"
      using certificate target_bound
      by (auto simp: comma_phase_mask_rank_certificate_def)
    have target_levels: "map snd (ranks!target)=[0..<27]"
      using certificate target_bound
      by (auto simp: comma_phase_mask_rank_certificate_def)
    have target_level: "snd ?target_row=snd rank_row-1"
    proof -
      have nth_map_eq:
        "map snd (ranks!target)!(snd rank_row-1)=snd ?target_row"
        using target_length target_level_bound by (simp add: nth_map)
      show ?thesis using nth_map_eq target_levels target_level_bound by simp
    qed
    have target_member: "?target_row\<in>set (ranks!target)"
      by (rule nth_mem) (use target_length target_level_bound in simp)
    have support_in_target:
      "(fst action_row AND fst rank_row) AND
        comma_rotate_phase 1 (fst ?target_row)=
        fst action_row AND fst rank_row"
      using row_law Comma_Phase_Rank_Mask_Continue by simp
    have target_bit:
      "comma_phase_member (comma_rotate_phase 1 (fst ?target_row)) phase"
    proof -
      have combined:
        "comma_phase_member
          ((fst action_row AND fst rank_row) AND
            comma_rotate_phase 1 (fst ?target_row)) phase"
        using overlap support_in_target by simp
      from combined show ?thesis
        by (simp add: comma_phase_member_and)
    qed
    have target_phase_bit:
      "comma_phase_member (fst ?target_row) ?next_phase"
      using target_bit phase
      by (simp only: comma_rotate_phase_member)
    have target_lookup:
      "comma_phase_mask_row_at (ranks!target) ?next_phase=Some ?target_row"
    proof -
      have unique:
        "\<exists>!row. row\<in>set (ranks!target) \<and> comma_phase_member (fst row) ?next_phase"
        by (rule comma_phase_mask_rows_partition_ex1[OF target_partition next_phase_bound])
      have chosen:
        "(SOME row. row\<in>set (ranks!target) \<and>
          comma_phase_member (fst row) ?next_phase)=?target_row"
        using unique target_member target_phase_bit by blast
      show ?thesis
        unfolding comma_phase_mask_row_at_def
        using next_phase_bound unique chosen by simp
    qed
    have next_rank:
      "?rank ?next_phase target=snd rank_row-1"
    proof -
      have target_class_bound: "target<length ranks"
        using target_bound rank_table_length by simp
      have target_value:
        "comma_phase_mask_rank_at_option ranks ?next_phase target=
          Some (snd ?target_row)"
        using target_class_bound target_lookup
        by (simp add: comma_phase_mask_rank_at_option_def)
      show ?thesis
        using comma_phase_mask_rank_choice_of_some[OF target_value]
          target_level by simp
    qed
    show ?thesis
      using Comma_Phase_Rank_Mask_Continue action_value current_rank
        target_bound next_phase_bound rank_positive next_rank
      by (simp add: comma_phase_mask_action_total_def)
  qed
qed

theorem comma_phase_mask_rank_certificate_B32:
  fixes class_of :: "nat \<Rightarrow> nat"
  assumes certificate: "comma_phase_mask_rank_certificate actions ranks"
    and source_valid: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      phase<924 \<and> class_of x<46"
    and source_refines: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      comma_phase_mask_action_total actions phase (class_of x) =
        comma_phase_classify_decade_control class_of
          (comma_decade_control (Comma_Decade phase x))"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>h tau. h\<le>26 \<and>
    comma_decade_block_power 5 s=Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau)=Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary s h tau"
proof -
  let ?valid = "\<lambda>phase control. phase<924 \<and> control<46"
  let ?rank = "\<lambda>phase control.
    THE chosen. comma_phase_mask_rank_at_option ranks phase control=Some chosen"
  let ?step = "comma_phase_mask_action_total actions"
  have checked: "comma_phase_class_rank_check ?valid ?rank ?step"
    by (rule comma_phase_mask_rank_certificate_checked[OF certificate])
  have class_bound: "\<And>phase control. ?valid phase control \<Longrightarrow> ?rank phase control\<le>26"
  proof -
    fix phase control :: nat
    assume valid: "?valid phase control"
    then have phase: "phase<924" and control: "control<46" by auto
    have part: "comma_phase_mask_rows_partition (ranks!control)"
      by (rule comma_phase_mask_rank_certificate_partition(2)[OF certificate control])
    obtain row where row:
      "row\<in>set (ranks!control)"
      "comma_phase_member (fst row) phase"
      "comma_phase_mask_row_at (ranks!control) phase=Some row"
      by (rule comma_phase_mask_row_at_some[OF part phase])
    have row_bound: "snd row\<le>26"
      using row certificate control
      by (auto simp: comma_phase_mask_rank_certificate_def)
    have class_table_bound: "control<length ranks"
      using certificate control
      by (auto simp: comma_phase_mask_rank_certificate_def)
    have option_value:
      "comma_phase_mask_rank_at_option ranks phase control=Some (snd row)"
      using row class_table_bound by (simp add: comma_phase_mask_rank_at_option_def)
    show "?rank phase control\<le>26"
      using comma_phase_mask_rank_choice_of_some[OF option_value] row_bound by simp
  qed
  have control_refinement:
    "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      ?step phase (class_of x) = comma_phase_classify_decade_control class_of
        (comma_decade_control (Comma_Decade phase x))"
    using source_refines by blast
  show ?thesis
    by (rule comma_phase_class_rank_B32
      [where class_of=class_of and valid="?valid" and rank="?rank" and step="?step",
       OF checked source_valid control_refinement class_bound admitted])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_mask_rows_partition_ex1 comma_phase_mask_row_at_some
      comma_phase_mask_rank_certificate_checked comma_phase_mask_rank_certificate_B32})
    then () else error "Phase-mask rank witness depends on an oracle";
\<close>

end
