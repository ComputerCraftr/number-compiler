theory Comma_Native_Future_Instance
  imports Comma_Native_Summary_Instance.Comma_Native_Summary_Instance
    Comma_Native_Boundary.Comma_Native_Future
    Comma_Future_Rank_Data.Comma_Rank_Data
    Comma_Run_Cycle_Data.Comma_Run_Cycle_Data
    Comma_Source_Entry.Comma_Source_Entry
    Comma_Source_Uniqueness.Comma_Source_Unique
begin

ML_file "../shared/Proof_Dependency_Audit.ML"
ML_file "../shared/selected_list_conversion.ML"
ML_file "../comma_future_rank_data/rank_table_lookup.ML"

text \<open>The decimal rank rows are used only as candidate natural-valued
measures. The checked transition and complete ordered child set come from the
native B32 boundary action. This owner reindexes the raw data directly and
never depends on the legacy rank lookup or structural checker theorems.\<close>

definition comma_native_rank_table_code ::
  "nat list list list list \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_native_rank_table_code table i =
    table ! (i div 4096) ! ((i div 256) mod 16) !
      ((i div 16) mod 16) ! (i mod 16)"

definition comma_native_rank_decode :: "nat \<Rightarrow> nat option" where
  "comma_native_rank_decode code =
    (if code=0 then None else Some (code-1))"

definition comma_native_rank_measure :: "comma_boundary_state \<Rightarrow> nat option" where
  "comma_native_rank_measure q =
    (if comma_boundary_valid q then
       (case q of (kind,a,r) \<Rightarrow>
         (let i=(a-2)*924+r in
           if kind=Comma_N then
             comma_native_rank_decode (comma_native_rank_table_code comma_rank_codes_N i)
           else
             comma_native_rank_decode (comma_native_rank_table_code comma_rank_codes_Z i)))
     else None)"

definition comma_native_rank_table_full_shape :: "nat list list list list \<Rightarrow> bool" where
  "comma_native_rank_table_full_shape table =
    (length table=2 \<and>
     list_all (\<lambda>outer. length outer=16 \<and>
       list_all (\<lambda>middle. length middle=16 \<and>
         list_all (\<lambda>inner. length inner=16) middle) outer) table)"

lemma comma_native_rank_codes_N_full_shape:
  "comma_native_rank_table_full_shape comma_rank_codes_N"
  unfolding comma_native_rank_table_full_shape_def comma_rank_codes_N_def
  by code_simp

lemma comma_native_rank_codes_Z_full_shape:
  "comma_native_rank_table_full_shape comma_rank_codes_Z"
  unfolding comma_native_rank_table_full_shape_def comma_rank_codes_Z_def
  by code_simp

lemma comma_native_rank_tables_full_shape:
  "comma_native_rank_table_full_shape comma_rank_codes_N \<and>
   comma_native_rank_table_full_shape comma_rank_codes_Z"
  using comma_native_rank_codes_N_full_shape comma_native_rank_codes_Z_full_shape
  by blast

ML_file "native_future_instance.ML"

local_setup \<open>Comma_Native_Future_Instance_Check.publish_rank_check\<close>

lemma comma_native_rank_check_checked:
  "comma_native_rank_check comma_native_rank_measure
    comma_native_B32_boundary_step"
  by (rule conjunct2[OF comma_native_rank_shape_and_check_checked])

lemma comma_native_ranked_boundary_children_decrease:
  assumes checked: "comma_native_rank_check comma_native_rank_measure
      comma_native_B32_boundary_step"
    and valid: "comma_boundary_valid q"
    and ranked: "comma_native_rank_measure q=Some k"
    and step: "comma_native_B32_boundary_step q=Some (Comma_Fork_At a d)"
  shows "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
    \<exists>j<k. comma_native_rank_measure child=Some j"
  by (rule comma_native_rank_check_fork_decreases[OF checked valid ranked step])

theorem comma_native_ranked_boundary_no_infinite_path:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and ranked: "comma_native_rank_measure q=Some k"
  shows "\<not>comma_native_infinite_literal_path
    (comma_boundary_value q p) stream"
proof (rule comma_native_ranked_state_no_infinite_path
    [OF comma_native_B32_refines_all comma_native_B32_stop26_all])
  show "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd source) \<Longrightarrow>
      comma_native_rank_measure source=Some k \<Longrightarrow>
      comma_native_B32_boundary_step source=Some (Comma_Fork_At a d) \<Longrightarrow>
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow>
      (\<exists>j<k. comma_native_rank_measure child=Some j)"
  proof -
    fix source exponent k a d child
    assume source_valid: "comma_boundary_valid source"
      and exponent_bound: "5\<le>exponent"
      and source_phase: "exponent mod 924=snd (snd source)"
      and source_rank: "comma_native_rank_measure source=Some k"
      and source_step:
        "comma_native_B32_boundary_step source=Some (Comma_Fork_At a d)"
      and child_member:
        "child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d))"
    show "\<exists>j<k. comma_native_rank_measure child=Some j"
      using comma_native_ranked_boundary_children_decrease
        [OF comma_native_rank_check_checked source_valid source_rank source_step]
        child_member by blast
  qed
  show "comma_boundary_valid q" by fact
  show "5\<le>p" by fact
  show "p mod 924=snd (snd q)" by fact
  show "comma_native_rank_measure q=Some k" by fact
qed

theorem comma_native_B32_infinite_path_forces_unique_unranked_child:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  obtains a d endpoint weight child tail where
    "comma_native_B32_boundary_step q=Some (Comma_Fork_At a d)"
    "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
    "stream (Suc weight)=comma_boundary_value child (p+d)"
    "comma_boundary_valid child"
    "5\<le>p+d"
    "(p+d) mod 924=snd (snd child)"
    "comma_native_infinite_literal_path (comma_boundary_value child (p+d)) tail"
    "comma_native_rank_measure q=None"
    "comma_native_rank_measure child=None"
    "\<forall>other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      other\<noteq>child \<longrightarrow> comma_native_rank_measure other\<noteq>None"
proof (rule comma_native_infinite_path_forces_unique_unranked_child
    [where rows=comma_checked_sparse_B32_rows
      and rank=comma_native_rank_measure])
  show "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (comma_checked_sparse_B32_rows i)"
    by (rule comma_native_B32_refines_all)
  show "\<forall>i<46. \<forall>out bits.
      (out,bits)\<in>set (comma_checked_sparse_B32_rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    by (rule comma_native_B32_stop26_all)
  show "comma_native_rank_check comma_native_rank_measure
      (comma_native_boundary_step comma_checked_sparse_B32_rows)"
    by (simp only: comma_native_B32_boundary_step_def comma_native_rank_check_checked)
  show "\<And>state exponent k trace. comma_boundary_valid state \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd state) \<Longrightarrow>
      comma_native_rank_measure state=Some k \<Longrightarrow>
      \<not>comma_native_infinite_literal_path
        (comma_boundary_value state exponent) trace"
  proof -
    fix state exponent k trace
    assume state_valid: "comma_boundary_valid state"
      and exponent_bound: "5\<le>exponent"
      and state_phase: "exponent mod 924=snd (snd state)"
      and state_rank: "comma_native_rank_measure state=Some k"
    show "\<not>comma_native_infinite_literal_path
        (comma_boundary_value state exponent) trace"
      by (rule comma_native_ranked_boundary_no_infinite_path
        [OF state_valid exponent_bound state_phase state_rank])
  qed
  show "comma_boundary_valid q" by fact
  show "5\<le>p" by fact
  show "p mod 924=snd (snd q)" by fact
  show "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
    by fact
qed

lemma comma_native_near_child_unranked:
  "comma_native_rank_measure (Comma_N,2,10)=None"
  by (rule comma_native_near_child_unranked_checked)

lemma comma_native_zero_child_ranked:
  "comma_native_rank_measure (Comma_Z,2,10)=Some 7"
  by (rule comma_native_zero_child_ranked_checked)

lemma comma_native_run_entry_result:
  "comma_native_safe_runs_execute comma_native_B32_boundary_step
    comma_native_rank_measure [(False,1)] (Comma_N,2,10)=
      Some ((Comma_N,7,12),2)"
  by (rule comma_native_run_entry_checked)

lemma comma_native_run_cycle_result:
  "comma_native_safe_runs_execute comma_native_B32_boundary_step
    comma_native_rank_measure comma_nine_run_cycle
    (Comma_N,7,12)=Some ((Comma_N,7,12),924)"
  by (rule comma_native_run_cycle_checked)

lemma comma_native_run_cycle_literal_segment:
  assumes exponent: "5\<le>p"
    and phase: "p mod 924=12"
  obtains weight where
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,7,12) p)
      (comma_boundary_value (Comma_N,7,12) (p+924))"
proof -
  have valid: "comma_boundary_valid (Comma_N,7,12)" by simp
  show thesis using comma_native_safe_runs_execute_literal
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all
        comma_native_run_cycle_result valid exponent phase] by blast
qed

lemma comma_native_run_cycle_segment_positive:
  assumes exponent: "5\<le>p"
    and phase: "p mod 924=12"
  obtains weight where
    "0<weight"
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,7,12) p)
      (comma_boundary_value (Comma_N,7,12) (p+924))"
proof -
  obtain weight where path:
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,7,12) p)
      (comma_boundary_value (Comma_N,7,12) (p+924))"
    by (rule comma_native_run_cycle_literal_segment[OF exponent phase])
  have distinct:
    "comma_boundary_value (Comma_N,7,12) p \<noteq>
      comma_boundary_value (Comma_N,7,12) (p+924)"
  proof -
    have exponent: "p<p+924" by simp
    have powers: "10^p < (10::nat)^(p+924)"
      by (rule power_strict_increasing[OF exponent]) simp
    have products: "7*10^p < 7*10^(p+924)"
      using powers by simp
    show ?thesis
      using products by (simp add: comma_boundary_value_def; arith)
  qed
  have positive: "0<weight"
  proof (rule ccontr)
    assume "\<not>0<weight"
    then have "weight=0" by simp
    with path distinct show False by (cases rule: comma_literal_path.cases) auto
  qed
  show thesis by (rule that[OF positive path])
qed

lemma comma_native_run_cycle_repeated_prefix:
  "\<exists>weight\<ge>t. comma_literal_path weight
    (comma_boundary_value (Comma_N,7,12) 12)
    (comma_boundary_value (Comma_N,7,12) (12+924*t))"
proof (induction t)
  case 0
  show ?case by (intro exI[of _ 0]) (simp add: comma_literal_path.zero)
next
  case (Suc t)
  obtain old_weight where old:
    "old_weight\<ge>t"
    "comma_literal_path old_weight
      (comma_boundary_value (Comma_N,7,12) 12)
      (comma_boundary_value (Comma_N,7,12) (12+924*t))"
    using Suc.IH by blast
  obtain next_weight where next_positive:
    "0<next_weight"
    and next_path:
      "comma_literal_path next_weight
        (comma_boundary_value (Comma_N,7,12) (12+924*t))
        (comma_boundary_value (Comma_N,7,12) (12+924*Suc t))"
    by (rule comma_native_run_cycle_segment_positive)
      (simp_all add: mod_add_right_eq)
  let ?weight = "old_weight+next_weight"
  have joined: "comma_literal_path ?weight
      (comma_boundary_value (Comma_N,7,12) 12)
      (comma_boundary_value (Comma_N,7,12) (12+924*Suc t))"
    using comma_literal_path_append[OF old(2) next_path] by (simp add: add.assoc)
  have lower: "Suc t\<le>?weight" using old(1) next_positive by arith
  show ?case using joined lower by blast
qed

theorem comma_native_cycle_boundary_unbounded:
  "comma_literal_unbounded (comma_boundary_value (Comma_N,7,12) 12)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  obtain weight where lower: "bound\<le>weight"
    and path: "comma_literal_path weight
      (comma_boundary_value (Comma_N,7,12) 12)
      (comma_boundary_value (Comma_N,7,12) (12+924*bound))"
    using comma_native_run_cycle_repeated_prefix[of bound] by blast
  show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight
        (comma_boundary_value (Comma_N,7,12) 12) target"
    using lower path by blast
qed

theorem comma_native_near_child_unbounded:
  "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
proof -
  have near_valid: "comma_boundary_valid (Comma_N,2,10)" by simp
  have entry:
    "comma_native_safe_runs_execute comma_native_B32_boundary_step
      comma_native_rank_measure [(False,1)] (Comma_N,2,10)=
        Some ((Comma_N,7,12),2)"
    by (rule comma_native_run_entry_result)
  obtain weight where prefix:
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,2,10) 10)
      (comma_boundary_value (Comma_N,7,12) 12)"
    using comma_native_safe_runs_execute_literal
      [OF comma_native_B32_refines_all comma_native_B32_stop26_all
        entry near_valid] by blast
  show ?thesis
    by (rule comma_literal_unbounded_prefix[OF prefix comma_native_cycle_boundary_unbounded])
qed

theorem comma_native_source20_infinite_path:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have prefix: "comma_literal_path 412987859 20 19999999999"
  proof -
    have fork: "comma_unique_literal_path 412987858 20 19999999918"
      by (rule comma_source20_to_fork_unique)
    have first: "comma_child 19999999918 19999999999"
      by (simp add: comma_source20_first_fork_children)
    show ?thesis
      by (rule comma_literal_path_snoc
        [OF comma_unique_literal_path_literal[OF fork] first])
  qed
  have near: "comma_boundary_value (Comma_N,2,10) 10=19999999999"
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
  have unbounded:
    "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    by (rule comma_native_near_child_unbounded)
  have source_unbounded: "comma_literal_unbounded 20"
    using comma_literal_unbounded_prefix[OF prefix] unbounded near by simp
  show ?thesis
    by (rule comma_literal_unbounded_infinite_path[OF source_unbounded])
qed

ML \<open>
  val checked = @{thms comma_native_rank_check_checked
    comma_native_rank_shape_and_check_checked
    comma_native_near_child_unranked_checked
    comma_native_zero_child_ranked_checked
    comma_native_run_entry_checked comma_native_run_cycle_checked
    comma_native_ranked_boundary_children_decrease
    comma_native_ranked_boundary_no_infinite_path
    comma_native_B32_infinite_path_forces_unique_unranked_child
    comma_native_run_cycle_literal_segment
    comma_native_cycle_boundary_unbounded
    comma_native_near_child_unbounded
    comma_native_source20_infinite_path}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native future-safety instance depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native B32 global future-safety instance" checked
\<close>

end
