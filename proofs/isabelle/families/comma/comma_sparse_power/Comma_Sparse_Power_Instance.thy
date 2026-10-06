theory Comma_Sparse_Power_Instance
  imports Comma_Sparse_Base_Instance.Comma_Sparse_Base_Instance
    Comma_Sparse_Power_Algebra.Comma_Sparse_Power_Algebra
begin

unbundle bit_operations_syntax

ML_file "../comma_sparse_power_algebra/sparse_power_constructor.ML"

text \<open>The concrete B32 table is built from the checked B1 word data.
Intermediate levels retain plain canonical row data only. One kernel-checked equation per whole table relates each level to the shared
recursive data power. No intermediate fiber equations or per-cell proof trees
are retained.\<close>

local_setup \<open>
  fn lthy =>
    Comma_Sparse_Power_Constructor.publish
      {base = @{term comma_sparse_base_data},
       definition = @{thm comma_sparse_base_data_def}} lthy
\<close>

lemma comma_checked_sparse_B32_fiber_count [simp]:
  "length comma_checked_sparse_B32_rows_table=46"
  by (simp only: comma_sparse_power_B32_data_equation
    comma_sparse_table_power_length[OF comma_sparse_base_data_length])

definition comma_checked_sparse_B32_rows_at ::
    "nat \<Rightarrow> comma_sparse_word option" where
  "comma_checked_sparse_B32_rows_at i =
    (if comma_sparse_table_valid comma_checked_sparse_B32_rows_table \<and> i<46
     then Some (comma_checked_sparse_B32_rows_table!i) else None)"

definition comma_checked_sparse_B32_rows :: "nat \<Rightarrow> comma_sparse_word" where
  "comma_checked_sparse_B32_rows i =
    (case comma_checked_sparse_B32_rows_at i of
      Some row \<Rightarrow> row
    | None \<Rightarrow> [(Comma_Word_Invalid,mask 924)])"

lemma comma_checked_sparse_B32_rows_at_valid:
  assumes "i<46"
  shows "comma_checked_sparse_B32_rows_at i =
    Some (comma_checked_sparse_B32_rows_table!i)"
  using assms by (simp add: comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_checked_sparse_B32_rows_at_invalid:
  assumes "46\<le>i"
  shows "comma_checked_sparse_B32_rows_at i=None"
  using assms by (simp add: comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_checked_sparse_B32_rows_valid:
  assumes "i<46"
  shows "comma_checked_sparse_B32_rows i=comma_checked_sparse_B32_rows_table!i"
  using assms by (simp add: comma_checked_sparse_B32_rows_def
    comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_checked_sparse_B32_rows_invalid:
  assumes "46\<le>i"
  shows "comma_checked_sparse_B32_rows i=[(Comma_Word_Invalid,mask 924)]"
  using assms by (simp add: comma_checked_sparse_B32_rows_def
    comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_sparse_power_B32_data_equation_at:
  assumes index: "i<46"
  shows "comma_checked_sparse_B32_rows_table!i =
    comma_sparse_data_power (comma_sparse_table_lookup comma_sparse_base_data) 5 i"
proof -
  have size: "length comma_sparse_base_data=46"
    by (rule comma_sparse_base_data_length)
  note equation = fun_cong[OF comma_sparse_table_power_lookup[OF size, of 5], of i]
  show ?thesis using equation index size comma_sparse_power_B32_data_equation
    by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def)
qed

lemma comma_checked_sparse_B32_refines:
  assumes index: "i<46"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word 5 r i)
    (comma_checked_sparse_B32_rows i)"
proof -
  have base: "\<And>j. j<46 \<Longrightarrow>
      comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r j)
        (comma_sparse_table_lookup comma_sparse_base_data j)"
    using comma_sparse_base_data_refines
    by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def comma_sparse_base_data_row_def)
  have power: "comma_sparse_refines (\<lambda>r. comma_orbit_word 5 r i)
    (comma_sparse_data_power (comma_sparse_table_lookup comma_sparse_base_data) 5 i)"
    by (rule comma_sparse_data_power_refines[OF base])
  show ?thesis
    using power comma_sparse_power_B32_data_equation_at[OF index]
    by (simp add: comma_checked_sparse_B32_rows_valid[OF index])
qed

lemma comma_checked_sparse_B32_row_count:
  "sum_list (map length comma_checked_sparse_B32_rows_table)=4535"
  by (simp add: comma_checked_sparse_B32_rows_table_def)

lemma comma_checked_sparse_B32_height26_witness:
  "comma_sparse_has (comma_checked_sparse_B32_rows_table!24) 42
    (Comma_Word_Stop 26 (Comma_Terminal_Fork 5))"
  by (simp add: comma_checked_sparse_B32_rows_table_def comma_sparse_has_def
    comma_phase_member_def)

lemma comma_checked_sparse_B32_stop26_all:
  "list_all comma_sparse_power_rows_stop26 comma_checked_sparse_B32_rows_table"
  by (simp add: comma_checked_sparse_B32_rows_table_def
      comma_sparse_power_rows_stop26_def comma_sparse_power_label_stop26.simps
      list_all_iff)

lemma comma_checked_sparse_B32_stop26:
  assumes index: "i<46"
  shows "comma_sparse_power_rows_stop26 (comma_checked_sparse_B32_rows i)"
proof -
  have at_index: "comma_sparse_power_rows_stop26
      (comma_checked_sparse_B32_rows_table!i)"
    using comma_checked_sparse_B32_stop26_all index
    by (auto simp: list_all_conv_all_nth)
  show ?thesis
    using at_index by (simp add: comma_checked_sparse_B32_rows_valid[OF index])
qed

lemma comma_checked_sparse_B32_rows_at_zero:
  "comma_checked_sparse_B32_rows_at 0 =
    Some (comma_checked_sparse_B32_rows_table!0)"
  by (simp add: comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_checked_sparse_B32_rows_at_last:
  "comma_checked_sparse_B32_rows_at 45 =
    Some (comma_checked_sparse_B32_rows_table!45)"
  by (simp add: comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

lemma comma_checked_sparse_B32_rows_at_first_invalid:
  "comma_checked_sparse_B32_rows_at 46=None"
  by (simp add: comma_checked_sparse_B32_rows_at_def comma_sparse_table_valid_def)

ML \<open>
  val checked = @{thms comma_sparse_power_B32_data_equation
    comma_sparse_power_B32_data_equation_at comma_checked_sparse_B32_refines
    comma_checked_sparse_B32_stop26_all comma_checked_sparse_B32_stop26
    comma_checked_sparse_B32_rows_at_valid comma_checked_sparse_B32_rows_at_invalid
    comma_checked_sparse_B32_rows_at_zero comma_checked_sparse_B32_rows_at_last
    comma_checked_sparse_B32_rows_at_first_invalid
    comma_checked_sparse_B32_fiber_count comma_checked_sparse_B32_row_count
    comma_checked_sparse_B32_height26_witness}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "B32 sparse data and fiber refinement depend on an oracle"
\<close>

end
