theory Comma_Sparse_Power_Algebra
  imports Comma_Sparse_Core.Comma_Sparse_Checked_Algebra
begin

unbundle bit_operations_syntax

text \<open>The power constructor operates on finite row data.  A single generic
normalization theorem preserves the extensional phase/output relation, and a
single inductive theorem lifts that relation through all dyadic powers.  The
concrete instance checks its row data separately; intermediate powers do not
retain theorem objects for individual cells.\<close>

text \<open>Intermediate powers are plain row data.  A row list is normalized
by its complete semantic output label, with one phase mask per label.  The
ordering key is only a deterministic serialization order; semantic
equivalence is established separately below.\<close>

fun comma_sparse_label_key :: "comma_word_result \<Rightarrow> nat list" where
  "comma_sparse_label_key (Comma_Word_Live j) = [1,j]"
| "comma_sparse_label_key (Comma_Word_Stop h (Comma_Terminal_Fork a)) = [2,h,0,a]"
| "comma_sparse_label_key (Comma_Word_Stop h Comma_Terminal_Landmine) = [2,h,1]"
| "comma_sparse_label_key Comma_Word_Invalid = [0]"

text \<open>B1 response rows and temporal sparse words use the same
polymorphic phase-mask normalizer. Only their output-label keys differ.\<close>

definition comma_sparse_normalize :: "comma_sparse_word \<Rightarrow> comma_sparse_word" where
  "comma_sparse_normalize rows =
    comma_mask_rows_normalize comma_sparse_label_key rows"

lemma comma_sparse_normalize_has:
  "comma_sparse_has (comma_sparse_normalize rows) r out =
    comma_sparse_has rows r out"
  unfolding comma_sparse_normalize_def
  using comma_mask_rows_normalize_has[of comma_sparse_label_key rows r out]
  by (simp only: comma_sparse_has_def comma_mask_rows_has_def)

lemma comma_sparse_normalize_refines:
  "comma_sparse_refines F (comma_sparse_normalize rows) =
    comma_sparse_refines F rows"
  by (simp only: comma_sparse_refines_def comma_sparse_normalize_has)

definition comma_sparse_data_compose ::
  "nat \<Rightarrow> comma_sparse_word \<Rightarrow>
    (nat \<Rightarrow> comma_sparse_word) \<Rightarrow> comma_sparse_word" where
  "comma_sparse_data_compose n left right =
    comma_sparse_normalize (comma_sparse_compose n left right)"

lemma comma_sparse_data_compose_refines:
  assumes left: "comma_sparse_refines (\<lambda>r. A r i) rows"
    and right: "\<And>j. comma_sparse_refines (\<lambda>r. B r j) (tails j)"
  shows "comma_sparse_refines (\<lambda>r. comma_word_then n A B r i)
    (comma_sparse_data_compose n rows tails)"
  using comma_sparse_compose_refines[where A=A and B=B and i=i and n=n
      and rows=rows and tails=tails, OF left right]
  by (simp only: comma_sparse_data_compose_def comma_sparse_normalize_refines)

primrec comma_sparse_data_power ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_data_power base 0 i =
    comma_sparse_normalize (comma_sparse_admit base i)"
| "comma_sparse_data_power base (Suc k) i =
    comma_sparse_data_compose (2^k) (comma_sparse_data_power base k i)
      (comma_sparse_data_power base k)"

theorem comma_sparse_data_power_refines:
  assumes base: "\<And>i. i<46 \<Longrightarrow>
      comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (base i)"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_data_power base k i)"
proof (induction k arbitrary: i)
  case 0
  have admitted: "comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i)
      (comma_sparse_admit base i)"
    by (rule comma_sparse_admit_refines[where base=base, OF base])
  show ?case using admitted
    by (simp only: comma_sparse_data_power.simps comma_sparse_normalize_refines)
next
  case (Suc k)
  have left: "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
      (comma_sparse_data_power base k i)" by (rule Suc.IH)
  have right: "\<And>j. comma_sparse_refines (\<lambda>r. comma_orbit_word k r j)
      (comma_sparse_data_power base k j)" by (rule Suc.IH)
  have composed: "comma_sparse_refines
      (\<lambda>r. comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r i)
      (comma_sparse_data_compose (2^k) (comma_sparse_data_power base k i)
        (comma_sparse_data_power base k))"
    by (rule comma_sparse_data_compose_refines[where A="comma_orbit_word k"
      and B="comma_orbit_word k" and i=i and n="2^k", OF left right])
  show ?case using composed
    by (simp add: comma_sparse_refines_def comma_orbit_word_square_all
      comma_sparse_data_power.simps)
qed


text \<open>Concrete certification uses one complete table equation per square.
The out-of-domain value is explicit, so table lookup and functional powering
have the same total semantics, including malformed live indices.\<close>

definition comma_sparse_table_valid :: "comma_sparse_word list \<Rightarrow> bool" where
  "comma_sparse_table_valid rows \<longleftrightarrow> length rows=46"

definition comma_sparse_table_lookup ::
  "comma_sparse_word list \<Rightarrow> nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_table_lookup rows i =
    (if comma_sparse_table_valid rows \<and> i<46 then rows!i
     else [(Comma_Word_Invalid,mask 924)])"

definition comma_sparse_table_square ::
  "nat \<Rightarrow> comma_sparse_word list \<Rightarrow> comma_sparse_word list" where
  "comma_sparse_table_square n rows =
    (if comma_sparse_table_valid rows then
      map (\<lambda>left. comma_sparse_data_compose n left
        (comma_sparse_table_lookup rows)) rows
     else [])"

primrec comma_sparse_table_power ::
  "comma_sparse_word list \<Rightarrow> nat \<Rightarrow> comma_sparse_word list" where
  "comma_sparse_table_power base 0 =
    (if comma_sparse_table_valid base then map comma_sparse_normalize base else [])"
| "comma_sparse_table_power base (Suc k) =
    comma_sparse_table_square (2^k) (comma_sparse_table_power base k)"

lemma comma_sparse_normalize_invalid [simp]:
  "comma_sparse_normalize [(Comma_Word_Invalid,mask 924)] =
    [(Comma_Word_Invalid,mask 924)]"
  by (simp add: comma_sparse_normalize_def comma_sparse_prune_def
    comma_mask_rows_normalize_def comma_mask_rows_prune_def
    comma_mask_rows_sort.simps comma_mask_rows_merge_sorted.simps)

lemma comma_sparse_data_compose_invalid [simp]:
  "comma_sparse_data_compose n [(Comma_Word_Invalid,mask 924)] right =
    [(Comma_Word_Invalid,mask 924)]"
  by (simp add: comma_sparse_data_compose_def comma_sparse_compose_def
    comma_sparse_prune_def comma_sparse_normalize_def
    comma_mask_rows_normalize_def comma_mask_rows_prune_def
    comma_mask_rows_sort.simps comma_mask_rows_merge_sorted.simps)

lemma comma_sparse_data_power_invalid:
  "46\<le>i \<Longrightarrow> comma_sparse_data_power base k i =
    [(Comma_Word_Invalid,mask 924)]"
  by (induction k) (simp_all add: comma_sparse_admit_def)

lemma comma_sparse_table_power_length [simp]:
  "length base=46 \<Longrightarrow> length (comma_sparse_table_power base k) = 46"
  by (induction k) (simp_all add: comma_sparse_table_square_def
    comma_sparse_table_valid_def)

lemma comma_sparse_table_lookup_valid:
  "i<46 \<Longrightarrow> length rows=46 \<Longrightarrow>
    comma_sparse_table_lookup rows i=rows!i"
  by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def)

lemma comma_sparse_table_lookup_malformed:
  "length rows\<noteq>46 \<Longrightarrow> comma_sparse_table_lookup rows i =
    [(Comma_Word_Invalid,mask 924)]"
  by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def)

lemma comma_sparse_table_lookup_missing:
  "length rows\<le>i \<Longrightarrow> comma_sparse_table_lookup rows i =
    [(Comma_Word_Invalid,mask 924)]"
  by (auto simp: comma_sparse_table_lookup_def comma_sparse_table_valid_def)

lemma comma_sparse_table_square_malformed:
  "length rows\<noteq>46 \<Longrightarrow> comma_sparse_table_square n rows=[]"
  by (simp add: comma_sparse_table_square_def comma_sparse_table_valid_def)

lemma comma_sparse_table_power_malformed:
  "length rows\<noteq>46 \<Longrightarrow> comma_sparse_table_power rows k=[]"
  by (induction k) (simp_all add: comma_sparse_table_square_def
    comma_sparse_table_valid_def)

lemma comma_sparse_table_power_lookup:
  assumes size: "length base=46"
  shows "comma_sparse_table_lookup (comma_sparse_table_power base k) =
    comma_sparse_data_power (comma_sparse_table_lookup base) k"
proof (induction k)
  case 0
  show ?case
    by (rule ext) (simp add: comma_sparse_table_lookup_def
      comma_sparse_admit_def comma_sparse_table_valid_def size)
next
  case (Suc k)
  show ?case
  proof (rule ext)
    fix i
    show "comma_sparse_table_lookup (comma_sparse_table_power base (Suc k)) i =
      comma_sparse_data_power (comma_sparse_table_lookup base) (Suc k) i"
    proof (cases "i<46")
      case True
      have table_size: "length (comma_sparse_table_power base k)=46"
        using size by simp
      have nth: "comma_sparse_table_power base k ! i =
        comma_sparse_data_power (comma_sparse_table_lookup base) k i"
        using fun_cong[OF Suc.IH, of i]
        by (simp only: comma_sparse_table_lookup_valid[OF True table_size])
      show ?thesis
        using True by (simp add: comma_sparse_table_lookup_valid
          comma_sparse_table_square_def
          comma_sparse_table_valid_def size nth Suc.IH)
    next
      case False
      then show ?thesis by (simp add: comma_sparse_table_lookup_def
        comma_sparse_data_power_invalid)
    qed
  qed
qed

theorem comma_sparse_table_power_refines:
  assumes size: "length base=46"
    and base: "\<And>i. i<46 \<Longrightarrow> comma_sparse_refines
      (\<lambda>r. comma_orbit_word 0 r i) (base!i)"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_table_lookup (comma_sparse_table_power base k) i)"
  unfolding comma_sparse_table_power_lookup[OF size]
  by (rule comma_sparse_data_power_refines)
    (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def size base)

fun comma_sparse_power_label_stop26 :: "comma_word_result \<Rightarrow> bool" where
  "comma_sparse_power_label_stop26 (Comma_Word_Stop h terminal) = (h\<le>26)"
| "comma_sparse_power_label_stop26 (Comma_Word_Live j) = False"
| "comma_sparse_power_label_stop26 Comma_Word_Invalid = False"

definition comma_sparse_power_rows_stop26 :: "comma_sparse_word \<Rightarrow> bool" where
  "comma_sparse_power_rows_stop26 rows = list_all
    (\<lambda>(out,bits). comma_sparse_power_label_stop26 out \<and> bits\<le>mask 924) rows"

lemma comma_sparse_power_rows_stop26_member:
  assumes rows: "comma_sparse_power_rows_stop26 rows" and member: "(out,bits)\<in>set rows"
  obtains h terminal where "out=Comma_Word_Stop h terminal" "h\<le>26"
proof -
  have label: "comma_sparse_power_label_stop26 out"
    using rows member
    by (auto simp: comma_sparse_power_rows_stop26_def list_all_iff)
  show thesis using label that by (cases out) auto
qed

lemma comma_sparse_power_rows_stop26_mask:
  assumes "comma_sparse_power_rows_stop26 rows" "(out,bits)\<in>set rows"
  shows "bits\<le>mask 924"
  using assms by (auto simp: comma_sparse_power_rows_stop26_def list_all_iff)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_normalize_has comma_sparse_normalize_refines
      comma_sparse_data_compose_refines comma_sparse_data_power_refines
      comma_sparse_table_lookup_missing comma_sparse_table_lookup_malformed
      comma_sparse_table_square_malformed comma_sparse_table_power_malformed
      comma_sparse_table_power_lookup comma_sparse_table_power_refines
      comma_sparse_power_rows_stop26_member comma_sparse_power_rows_stop26_mask}) then ()
    else error "Sparse power algebra depends on an oracle"
\<close>

end
