theory Comma_Semantic_B1_CRT_Column_DAG
  imports Comma_CRT_Columns
begin

text \<open>
  A global column table is split into bounded, closed CID blocks.  Each block
  is a balanced lookup tree of at most 512 shallow node rows.  A second shallow
  balanced directory contains each block's base CID, extent, and named
  constant.  Lookup visits one directory path and one block path.  The column
  interpreter exposes one row and leaves child CIDs as canonical named
  applications.
\<close>

datatype comma_semantic_b1_crt_column_block =
    Comma_B1_CRT_Column_Block_Empty
  | Comma_B1_CRT_Column_Block_Node nat nat "nat list"
      comma_semantic_b1_crt_column_block comma_semantic_b1_crt_column_block

datatype comma_semantic_b1_crt_column_dag =
    Comma_B1_CRT_Column_DAG_Empty
  | Comma_B1_CRT_Column_DAG_Block nat nat comma_semantic_b1_crt_column_block
  | Comma_B1_CRT_Column_DAG_Branch nat
      comma_semantic_b1_crt_column_dag comma_semantic_b1_crt_column_dag

fun comma_semantic_b1_crt_column_block_lookup ::
    "comma_semantic_b1_crt_column_block \<Rightarrow> nat \<Rightarrow>
      (nat \<times> nat list) option" where
  "comma_semantic_b1_crt_column_block_lookup
      Comma_B1_CRT_Column_Block_Empty cid = None"
| "comma_semantic_b1_crt_column_block_lookup
      (Comma_B1_CRT_Column_Block_Node key level children left right) cid =
    (if cid=key then Some (level,children)
     else if cid<key then comma_semantic_b1_crt_column_block_lookup left cid
     else comma_semantic_b1_crt_column_block_lookup right cid)"

fun comma_semantic_b1_crt_column_dag_lookup ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow> nat \<Rightarrow>
      (nat \<times> nat list) option" where
  "comma_semantic_b1_crt_column_dag_lookup Comma_B1_CRT_Column_DAG_Empty cid = None"
| "comma_semantic_b1_crt_column_dag_lookup
      (Comma_B1_CRT_Column_DAG_Block base extent block) cid =
    (if cid<base then None
     else if cid<base+extent then
       comma_semantic_b1_crt_column_block_lookup block cid
     else None)"
| "comma_semantic_b1_crt_column_dag_lookup
      (Comma_B1_CRT_Column_DAG_Branch split left right) cid =
    (if cid<split then comma_semantic_b1_crt_column_dag_lookup left cid
     else comma_semantic_b1_crt_column_dag_lookup right cid)"

definition comma_semantic_b1_crt_guarded_node ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow> comma_crt_column" where
  "comma_semantic_b1_crt_guarded_node level children =
    (if comma_crt_admitted 0 (Comma_CRT_Node level children)
     then Comma_CRT_Node level children else Comma_CRT_Bool False)"

function comma_semantic_b1_crt_column_at ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow> nat \<Rightarrow>
      comma_crt_column" where
  "comma_semantic_b1_crt_column_at dag cid =
    (if cid=0 then Comma_CRT_Bool False
     else if cid=1 then Comma_CRT_Bool True
     else case comma_semantic_b1_crt_column_dag_lookup dag cid of
       None \<Rightarrow> Comma_CRT_Bool False
     | Some (level,children) \<Rightarrow>
         if list_all (\<lambda>child. child<cid) children then
           comma_semantic_b1_crt_guarded_node level
             (map (comma_semantic_b1_crt_column_at dag) children)
         else Comma_CRT_Bool False)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(dag,cid). cid)") (auto simp: list_all_iff)

lemma comma_semantic_b1_crt_guarded_node_admitted:
  "comma_crt_admitted 0 (comma_semantic_b1_crt_guarded_node level children)"
  unfolding comma_semantic_b1_crt_guarded_node_def
  by (cases "comma_crt_admitted 0 (Comma_CRT_Node level children)") simp_all

lemma comma_semantic_b1_crt_guarded_node_admitted_at:
  "lower\<le>level \<Longrightarrow>
    comma_crt_admitted lower (comma_semantic_b1_crt_guarded_node level children)"
  unfolding comma_semantic_b1_crt_guarded_node_def
  by (cases "comma_crt_admitted 0 (Comma_CRT_Node level children)") auto

ML \<open>
  val comma_semantic_b1_column_at_admitted_timer =
    Comma_Proof_Profile.timer "B1 generic column DAG column_at_admitted"
  val _ = comma_semantic_b1_column_at_admitted_timer "proof-start"
\<close>

lemma comma_semantic_b1_crt_column_at_admitted:
  "comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid)"
proof -
  let ?one_step = "(if cid=0 then Comma_CRT_Bool False
    else if cid=1 then Comma_CRT_Bool True
    else case comma_semantic_b1_crt_column_dag_lookup dag cid of
      None \<Rightarrow> Comma_CRT_Bool False
    | Some (level,children) \<Rightarrow>
        if list_all (\<lambda>child. child<cid) children then
          comma_semantic_b1_crt_guarded_node level
            (map (comma_semantic_b1_crt_column_at dag) children)
        else Comma_CRT_Bool False)"
  have column_equation: "comma_semantic_b1_crt_column_at dag cid=?one_step"
    by (rule comma_semantic_b1_crt_column_at.simps)
  show ?thesis
  proof (cases "cid=0")
    case True
    then show ?thesis by (simp add: comma_semantic_b1_crt_column_at.simps)
  next
    case False
    have cid_nonzero: "cid\<noteq>0" by fact
    show ?thesis
    proof (cases "cid=1")
      case True
      with cid_nonzero show ?thesis
        by (simp add: comma_semantic_b1_crt_column_at.simps)
    next
      case False
      have cid_nonone: "cid\<noteq>1" by fact
      show ?thesis
      proof (cases "comma_semantic_b1_crt_column_dag_lookup dag cid")
        case None
        with cid_nonzero cid_nonone show ?thesis
          by (simp add: comma_semantic_b1_crt_column_at.simps)
      next
        case (Some result)
        obtain level children where result_pair:
            "result=(level,children)"
          by (cases result) auto
        show ?thesis
        proof (cases "list_all (\<lambda>child. child<cid) children")
          case False
          with Some result_pair cid_nonzero cid_nonone show ?thesis
            by (simp add: comma_semantic_b1_crt_column_at.simps)
        next
          case True
          have selected_case:
              "?one_step=comma_semantic_b1_crt_guarded_node level
                (map (comma_semantic_b1_crt_column_at dag) children)"
            using cid_nonzero cid_nonone Some result_pair True
            by (simp only: if_True if_False option.simps prod.simps)
          have decoded:
              "comma_semantic_b1_crt_column_at dag cid=
                comma_semantic_b1_crt_guarded_node level
                  (map (comma_semantic_b1_crt_column_at dag) children)"
            by (rule trans[OF column_equation selected_case])
          show ?thesis
            by (subst decoded; rule comma_semantic_b1_crt_guarded_node_admitted)
        qed
      qed
    qed
  qed
qed

lemma comma_semantic_b1_crt_column_at_admitted_at:
  assumes lookup:
      "comma_semantic_b1_crt_column_dag_lookup dag cid = Some (level, children)"
    and lower: "lower\<le>level"
  shows "comma_crt_admitted lower (comma_semantic_b1_crt_column_at dag cid)"
proof (cases "cid=0")
  case True
  then show ?thesis by (simp add: comma_semantic_b1_crt_column_at.simps)
next
  case False
  then show ?thesis
  proof (cases "cid=1")
    case True
    then show ?thesis by (simp add: comma_semantic_b1_crt_column_at.simps)
  next
    case False
    then show ?thesis
      using lookup lower
      by (simp add: comma_semantic_b1_crt_column_at.simps
          comma_semantic_b1_crt_guarded_node_admitted_at)
  qed
qed

ML \<open>comma_semantic_b1_column_at_admitted_timer "proof-submitted"\<close>

lemma comma_semantic_b1_crt_column_at_false:
  "comma_semantic_b1_crt_column_at dag 0=Comma_CRT_Bool False"
  by (simp add: comma_semantic_b1_crt_column_at.simps)

lemma comma_semantic_b1_crt_column_at_true:
  "comma_semantic_b1_crt_column_at dag 1=Comma_CRT_Bool True"
  by (simp add: comma_semantic_b1_crt_column_at.simps)

(* Keep canonical child applications opaque in subsequent list and
   converter-facing facts.  Unfold the decoder only at controlled
   one-node conversion sites. *)
declare comma_semantic_b1_crt_column_at.simps [simp del]

definition comma_semantic_b1_crt_columns_for ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow> nat \<Rightarrow> comma_crt_column list" where
  "comma_semantic_b1_crt_columns_for dag extent =
    map (comma_semantic_b1_crt_column_at dag) [0..<extent]"

lemma comma_semantic_b1_crt_columns_for_length:
  "length (comma_semantic_b1_crt_columns_for dag extent) = extent"
  by (simp add: comma_semantic_b1_crt_columns_for_def)

lemma comma_semantic_b1_crt_columns_for_nth:
  "index < extent \<Longrightarrow>
    comma_semantic_b1_crt_columns_for dag extent ! index =
      comma_semantic_b1_crt_column_at dag index"
  by (simp add: comma_semantic_b1_crt_columns_for_def)

lemma comma_semantic_b1_crt_columns_for_admitted:
  "list_all (comma_crt_admitted 0)
    (comma_semantic_b1_crt_columns_for dag extent)"
  unfolding comma_semantic_b1_crt_columns_for_def list_all_iff
  using comma_semantic_b1_crt_column_at_admitted by auto

lemma comma_semantic_b1_crt_column_templates_nth:
  "index < length ids \<Longrightarrow>
    map (map (comma_semantic_b1_crt_column_at dag)) ids ! index =
      map (comma_semantic_b1_crt_column_at dag) (ids ! index)"
  by (rule nth_map)

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_columns_for_length
    comma_semantic_b1_crt_columns_for_nth
    comma_semantic_b1_crt_column_templates_nth
    comma_semantic_b1_crt_guarded_node_admitted
    comma_semantic_b1_crt_guarded_node_admitted_at
    comma_semantic_b1_crt_column_at_admitted
    comma_semantic_b1_crt_column_at_admitted_at
    comma_semantic_b1_crt_columns_for_admitted}
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_guarded_node_admitted
    comma_semantic_b1_crt_column_at_admitted
    comma_semantic_b1_crt_guarded_node_admitted_at
    comma_semantic_b1_crt_column_at_admitted_at
    comma_semantic_b1_crt_column_at_false
    comma_semantic_b1_crt_column_at_true
    comma_semantic_b1_crt_column_templates_nth
    comma_semantic_b1_crt_columns_for_length
    comma_semantic_b1_crt_columns_for_nth
    comma_semantic_b1_crt_columns_for_admitted
  }) then ()
  else error "Comma_Semantic_B1_CRT_Column_DAG local oracle audit failed"
  val _ = Comma_Proof_Profile.report
    "B1 generic column DAG stage=post-consolidation"
\<close>

end
