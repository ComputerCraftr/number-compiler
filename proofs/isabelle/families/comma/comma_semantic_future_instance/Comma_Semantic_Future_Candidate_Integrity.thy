theory Comma_Semantic_Future_Candidate_Integrity
  imports Comma_Semantic_Future_Candidate_Data
begin

text \<open>
The source-ID vector is untrusted input.  Its length is checked with the
candidate table, and this vector-level maximum check authenticates the range
of all labels without expanding source/phase provider obligations.
\<close>

fun comma_semantic_future_nat_list_max :: "nat list \<Rightarrow> nat" where
  "comma_semantic_future_nat_list_max [] = 0"
| "comma_semantic_future_nat_list_max (value # values) =
    max value (comma_semantic_future_nat_list_max values)"

definition comma_semantic_future_candidate_id_vector_in_range ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_id_vector_in_range values bound \<longleftrightarrow>
    comma_semantic_future_nat_list_max values < bound"

lemma comma_semantic_future_nat_list_max_bounded:
  assumes bound: "comma_semantic_future_nat_list_max values < limit"
  shows "list_all (\<lambda>value. value < limit) values"
  using bound
proof (induction values)
  case Nil
  then show ?case by simp
next
  case (Cons value values)
  have value_bound:
    "value \<le> max value (comma_semantic_future_nat_list_max values)"
    by simp
  have tail_bound:
    "comma_semantic_future_nat_list_max values \<le>
      max value (comma_semantic_future_nat_list_max values)"
    by simp
  have head_lt:
    "value < limit"
    by (rule le_less_trans[OF value_bound]) (use Cons.prems in simp)
  have tail_lt:
    "comma_semantic_future_nat_list_max values < limit"
    by (rule le_less_trans[OF tail_bound]) (use Cons.prems in simp)
  show ?case using head_lt Cons.IH[OF tail_lt] by simp
qed

lemma comma_semantic_future_candidate_id_vector_all_in_range:
  assumes range:
    "comma_semantic_future_candidate_id_vector_in_range values limit"
  shows "list_all (\<lambda>value. value < limit) values"
  using comma_semantic_future_nat_list_max_bounded[of values limit]
    range
  by (simp add: comma_semantic_future_candidate_id_vector_in_range_def)

lemma comma_semantic_future_nat_list_max_ge_member:
  assumes member: "value \<in> set values"
  shows "value \<le> comma_semantic_future_nat_list_max values"
  using member by (induction values) auto

lemma comma_semantic_future_nat_list_max_rejects_appended_bound:
  "\<not> comma_semantic_future_nat_list_max (values @ [bound]) < bound"
proof -
  have member: "bound \<in> set (values @ [bound])" by simp
  have "bound \<le> comma_semantic_future_nat_list_max (values @ [bound])"
    by (rule comma_semantic_future_nat_list_max_ge_member[OF member])
  then show ?thesis by arith
qed

lemma comma_semantic_future_candidate_id_vector_rejects_malformed_append:
  "\<not> comma_semantic_future_candidate_id_vector_in_range
      (comma_semantic_future_candidate_class_ids @
        [length comma_semantic_future_candidate_controls])
      (length comma_semantic_future_candidate_controls)"
  by (simp add: comma_semantic_future_candidate_id_vector_in_range_def
      comma_semantic_future_nat_list_max_rejects_appended_bound)

definition comma_semantic_future_candidate_class_index ::
    "comma_boundary_state \<Rightarrow> nat" where
  "comma_semantic_future_candidate_class_index q =
    (case q of (kind,a,r) \<Rightarrow>
      (if kind=Comma_N then 0 else 8*924) + (a-2)*924 + r)"

definition comma_semantic_future_candidate_class_of ::
    "comma_boundary_state \<Rightarrow> nat" where
  "comma_semantic_future_candidate_class_of q =
    (let index = comma_semantic_future_candidate_class_index q in
      if comma_boundary_valid q \<and>
          index < length comma_semantic_future_candidate_class_ids
      then comma_semantic_future_candidate_class_ids ! index
      else length comma_semantic_future_candidate_class_ids +
        length comma_semantic_future_candidate_controls +
        length comma_semantic_future_candidate_children +
        length comma_semantic_future_candidate_ranks + 1)"

definition comma_semantic_future_candidate_class_valid :: "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_valid c \<longleftrightarrow>
    c < length comma_semantic_future_candidate_controls"

definition comma_semantic_future_candidate_class_step ::
    "nat \<Rightarrow> comma_future_control option" where
  "comma_semantic_future_candidate_class_step c =
    (if comma_semantic_future_candidate_class_valid c then
       Some (comma_semantic_future_candidate_controls ! c)
     else None)"

definition comma_semantic_future_candidate_class_rank ::
    "nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_class_rank c =
    (if c < length comma_semantic_future_candidate_ranks
     then comma_semantic_future_candidate_ranks ! c else None)"

definition comma_semantic_future_candidate_class_children ::
    "nat \<Rightarrow> comma_future_control \<Rightarrow> nat list" where
  "comma_semantic_future_candidate_class_children c control =
    (if comma_semantic_future_candidate_class_step c = Some control then
       (if c < length comma_semantic_future_candidate_children then
         (case control of
            Comma_Future_Fork a \<Rightarrow>
              (case comma_semantic_future_candidate_children ! c of
                 (left,right) \<Rightarrow> map_filter id [left,right])
          | Comma_Future_Landmine \<Rightarrow> [])
        else [])
     else [])"

definition comma_semantic_future_candidate_class_output ::
    "nat \<Rightarrow> (comma_future_control \<times> nat list) option" where
  "comma_semantic_future_candidate_class_output c =
    (case comma_semantic_future_candidate_class_step c of
       None \<Rightarrow> None
     | Some control \<Rightarrow>
         Some (control,comma_semantic_future_candidate_class_children c control))"

lemma comma_semantic_future_candidate_class_output_on_valid:
  assumes valid: "comma_semantic_future_candidate_class_valid c"
  obtains control children where
    "comma_semantic_future_candidate_class_output c = Some (control,children)"
    "comma_semantic_future_candidate_class_step c = Some control"
    "children=comma_semantic_future_candidate_class_children c control"
proof -
  obtain control where step:
      "comma_semantic_future_candidate_class_step c = Some control"
    using valid by (auto simp: comma_semantic_future_candidate_class_step_def
        comma_semantic_future_candidate_class_valid_def)
  let ?children = "comma_semantic_future_candidate_class_children c control"
  have output_fact:
      "comma_semantic_future_candidate_class_output c =
        Some (control,?children)"
    using step by (simp add: comma_semantic_future_candidate_class_output_def)
  show thesis
    apply (rule that[OF output_fact step])
    by simp
qed

definition comma_semantic_future_candidate_output_tree ::
    "nat comma_semantic_weighted_crt_dag \<Rightarrow>
      (comma_future_control \<times> nat list) option
        comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_candidate_output_tree tree =
    comma_semantic_future_crt_map_control
      comma_semantic_future_candidate_class_output tree"

lemma comma_semantic_future_candidate_output_tree_exact:
  "comma_weighted_crt_eval
      (comma_semantic_future_candidate_output_tree tree) phase =
    map_option (\<lambda>(class_id,weight).
      (comma_semantic_future_candidate_class_output class_id,weight))
      (comma_weighted_crt_eval tree phase)"
  by (simp add: comma_semantic_future_candidate_output_tree_def
      comma_semantic_future_crt_map_control_eval)

lemma comma_semantic_future_candidate_output_tree_shape:
  "comma_weighted_crt_shape lower
      (comma_semantic_future_candidate_output_tree tree) =
    comma_weighted_crt_shape lower tree"
  by (simp add: comma_semantic_future_candidate_output_tree_def
      comma_semantic_future_crt_map_control_shape)

definition comma_semantic_future_candidate_class_row_shape ::
    "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_row_shape c =
    (case comma_semantic_future_candidate_class_step c of
       None \<Rightarrow> False
     | Some control \<Rightarrow>
         (if c < length comma_semantic_future_candidate_children then
            (case (control, comma_semantic_future_candidate_children ! c) of
              (Comma_Future_Fork a, (Some left, Some right)) \<Rightarrow>
                2 \<le> a \<and> a \<le> 9 \<and>
                comma_semantic_future_candidate_class_valid left \<and>
                comma_semantic_future_candidate_class_valid right
            | (Comma_Future_Landmine, (None, None)) \<Rightarrow> True
            | _ \<Rightarrow> False)
          else False))"

definition comma_semantic_future_candidate_class_row_checked ::
    "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_row_checked c =
    (comma_semantic_future_candidate_class_row_shape c \<and>
     comma_semantic_rank_row_checked
       comma_semantic_future_candidate_class_rank
       comma_semantic_future_candidate_class_children
       comma_semantic_future_candidate_class_step c)"

definition comma_semantic_future_candidate_class_ids_range_check :: bool where
  "comma_semantic_future_candidate_class_ids_range_check \<longleftrightarrow>
    comma_semantic_future_candidate_id_vector_in_range
      comma_semantic_future_candidate_class_ids
      (length comma_semantic_future_candidate_controls)"

definition comma_semantic_future_candidate_class_table_check :: bool where
  "comma_semantic_future_candidate_class_table_check \<longleftrightarrow>
    length comma_semantic_future_candidate_class_ids =
      length comma_boundary_states \<and>
    comma_semantic_future_candidate_class_ids_range_check \<and>
    length comma_semantic_future_candidate_controls =
      length comma_semantic_future_candidate_children \<and>
    length comma_semantic_future_candidate_controls =
      length comma_semantic_future_candidate_ranks \<and>
    list_all comma_semantic_future_candidate_class_row_checked
      [0..<length comma_semantic_future_candidate_controls]"


ML \<open>
  val checked = @{thms
    comma_semantic_future_nat_list_max_bounded
    comma_semantic_future_candidate_id_vector_all_in_range
    comma_semantic_future_nat_list_max_ge_member
    comma_semantic_future_candidate_id_vector_rejects_malformed_append};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future candidate source-ID vector range and malformed-label rejection"
    checked;
\<close>

end
