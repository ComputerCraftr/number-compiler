theory Comma_Semantic_B1_Rebase
  imports Comma_Semantic_Graph
begin

text \<open>
An occurrence may apply a complete labeled return at a translated phase.
The translation is a common clock offset on the whole return: roots and
Live/Stop/Invalid labels are preserved.  In a sequential composition, each
occurrence keeps its own offset, while the physical clock advances by the
decade-block span before the next occurrence is translated.  The duration
parameter is the number of decade blocks, so the terminal cocycle adds nine
times that count.
\<close>

type_synonym comma_semantic_b1_return =
  "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"

definition comma_semantic_b1_rebase ::
    "nat \<Rightarrow> comma_semantic_b1_return \<Rightarrow> comma_semantic_b1_return" where
  "comma_semantic_b1_rebase delta action = (\<lambda>clock root.
    action ((clock+delta) mod 924) root)"

definition comma_semantic_b1_root_rebase ::
    "(nat \<Rightarrow> nat) \<Rightarrow> comma_semantic_b1_return \<Rightarrow>
      comma_semantic_b1_return" where
  "comma_semantic_b1_root_rebase delta action = (\<lambda>clock root.
    action ((clock+delta root) mod 924) root)"

lemma comma_semantic_b1_rebase_apply:
  "comma_semantic_b1_rebase delta action clock root =
    action ((clock+delta) mod 924) root"
  by (simp add: comma_semantic_b1_rebase_def)

lemma comma_semantic_b1_rebase_zero [simp]:
  "comma_semantic_b1_rebase 0 action clock root = action (clock mod 924) root"
  by (simp add: comma_semantic_b1_rebase_def)

lemma comma_semantic_b1_phase_shift_add:
  fixes clock delta epsilon :: nat
  shows "(((clock+delta) mod 924 + epsilon) mod 924) =
    ((clock+(delta+epsilon)) mod 924)"
proof -
  have "(((clock+delta) mod 924 + epsilon) mod 924) =
      ((clock+delta+epsilon) mod 924)"
    by (simp only: mod_add_left_eq)
  also have "... = ((clock+(delta+epsilon)) mod 924)"
    by (simp add: add.assoc)
  finally show ?thesis .
qed

lemma comma_semantic_b1_rebase_add:
  "comma_semantic_b1_rebase delta
      (comma_semantic_b1_rebase epsilon action) clock root =
    comma_semantic_b1_rebase (delta+epsilon) action clock root"
proof -
  have phase:
    "(((clock+delta) mod 924 + epsilon) mod 924) =
      ((clock+(delta+epsilon)) mod 924)"
    using comma_semantic_b1_phase_shift_add[of clock delta epsilon]
    by simp
  show ?thesis
    unfolding comma_semantic_b1_rebase_def
    using phase by simp
qed

lemma comma_semantic_b1_root_rebase_add:
  "comma_semantic_b1_root_rebase delta
      (comma_semantic_b1_root_rebase epsilon action) clock root =
    comma_semantic_b1_root_rebase (\<lambda>i. delta i + epsilon i) action clock root"
proof -
  have phase:
    "(((clock+delta root) mod 924 + epsilon root) mod 924) =
      ((clock+(delta root + epsilon root)) mod 924)"
    using comma_semantic_b1_phase_shift_add[of clock "delta root" "epsilon root"]
    by simp
  show ?thesis
    unfolding comma_semantic_b1_root_rebase_def
    using phase by simp
qed

lemma comma_semantic_b1_rebase_inverse:
  "comma_semantic_b1_rebase (924-(delta mod 924))
      (comma_semantic_b1_rebase delta action) clock root =
    action (clock mod 924) root"
proof -
  let ?q = "delta div 924"
  let ?r = "delta mod 924"
  have remainder_bound: "?r<924" by simp
  have quotient_remainder: "?q*924+?r=delta"
    by (rule div_mult_mod_eq)
  have decomposition: "delta=924*?q+?r"
    using quotient_remainder by (simp add: mult.commute)
  have remainder_complement: "?r+(924-?r)=924"
    using remainder_bound by arith
  have complement:
    "delta + (924-?r) = 924*(?q+1)"
  proof -
    have "delta+(924-?r) = 924*?q+?r+(924-?r)"
      by (rule arg_cong[where f="\<lambda>n. n+(924-?r)", OF decomposition])
    also have "... = 924*?q+(?r+(924-?r))"
      by (rule add.assoc)
    also have "... = 924*?q+924"
      by (simp only: remainder_complement)
    also have "... = 924*(?q+1)"
      by (simp add: distrib_left)
    finally show ?thesis .
  qed
  have phase:
    "(((clock+(924-?r)) mod 924 + delta) mod 924) = clock mod 924"
  proof -
    have "(((clock+(924-?r)) mod 924+delta) mod 924) =
        ((clock+(924-?r)+delta) mod 924)"
      by (rule mod_add_left_eq)
    also have "... = ((clock+(delta+(924-?r))) mod 924)"
      by (simp add: add.assoc add.commute add.left_commute)
    also have "... = ((clock+924*(?q+1)) mod 924)"
      using complement by simp
    also have "... = clock mod 924"
    proof -
      have "((clock+924*(?q+1)) mod 924) =
          ((924*(?q+1)+clock) mod 924)"
        by (simp add: add.commute)
      also have "... = ((924*(?q+1) mod 924+clock) mod 924)"
        by (rule mod_add_left_eq[symmetric])
      also have "... = clock mod 924" by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding comma_semantic_b1_rebase_def
    using phase by simp
qed

lemma comma_semantic_b1_rebase_child_phase:
  fixes clock delta duration :: nat
  shows "((clock+delta) mod 924 + duration) mod 924 =
    ((clock+duration) mod 924 + delta) mod 924"
  by (simp only: mod_add_left_eq;
      simp only: add.assoc add.commute add.left_commute)

theorem comma_semantic_b1_rebase_word_then:
  "comma_semantic_b1_rebase delta (comma_semantic_word_then duration A B) =
    comma_semantic_word_then duration
      (comma_semantic_b1_rebase delta A)
      (comma_semantic_b1_rebase delta B)"
proof (rule ext)+
  fix clock root
  have child_phase:
    "((clock+delta) mod 924 + duration) mod 924 =
      ((clock+duration) mod 924 + delta) mod 924"
    by (rule comma_semantic_b1_rebase_child_phase)
  show "comma_semantic_b1_rebase delta
      (comma_semantic_word_then duration A B) clock root =
    comma_semantic_word_then duration
      (comma_semantic_b1_rebase delta A)
      (comma_semantic_b1_rebase delta B) clock root"
    using child_phase
    by (simp add: comma_semantic_b1_rebase_def comma_semantic_word_then_def
        split: comma_semantic_b1_result.splits)
qed

theorem comma_semantic_b1_independent_occurrence_offsets:
  "comma_semantic_word_then duration
      (comma_semantic_b1_rebase delta_a A)
      (comma_semantic_b1_rebase delta_b B) clock root =
    (case A ((clock+delta_a) mod 924) root of
       Comma_Semantic_B1_Live next_root \<Rightarrow>
         (case B (((clock+duration) mod 924 + delta_b) mod 924) next_root of
            Comma_Semantic_B1_Stop D \<Rightarrow>
              Comma_Semantic_B1_Stop (9*duration+D)
          | result \<Rightarrow> result)
     | result \<Rightarrow> result)"
  by (simp add: comma_semantic_b1_rebase_def comma_semantic_word_then_def)

theorem comma_semantic_b1_rooted_occurrence_offsets:
  "comma_semantic_word_then duration
      (comma_semantic_b1_root_rebase delta_a A)
      (comma_semantic_b1_root_rebase delta_b B) clock root =
    (case A ((clock+delta_a root) mod 924) root of
       Comma_Semantic_B1_Live next_root \<Rightarrow>
         (case B (((clock+duration) mod 924 + delta_b next_root) mod 924)
             next_root of
            Comma_Semantic_B1_Stop D \<Rightarrow>
              Comma_Semantic_B1_Stop (9*duration+D)
          | result \<Rightarrow> result)
     | result \<Rightarrow> result)"
  by (simp add: comma_semantic_b1_root_rebase_def
      comma_semantic_word_then_def)

theorem comma_semantic_b1_rebase_of_word_then:
  "comma_semantic_b1_rebase delta
      (\<lambda>clock root. comma_semantic_b1_of_word
        (comma_word_then duration A B clock root)) =
    comma_semantic_word_then duration
      (comma_semantic_b1_rebase delta
        (\<lambda>clock root. comma_semantic_b1_of_word (A clock root)))
      (comma_semantic_b1_rebase delta
        (\<lambda>clock root. comma_semantic_b1_of_word (B clock root)))"
proof -
  let ?A = "\<lambda>clock root. comma_semantic_b1_of_word (A clock root)"
  let ?B = "\<lambda>clock root. comma_semantic_b1_of_word (B clock root)"
  have exact_word:
    "(\<lambda>clock root. comma_semantic_b1_of_word
        (comma_word_then duration A B clock root)) =
      comma_semantic_word_then duration ?A ?B"
  proof (rule ext)+
    fix clock root
    show "comma_semantic_b1_of_word
        (comma_word_then duration A B clock root) =
      comma_semantic_word_then duration ?A ?B clock root"
      by (rule comma_semantic_b1_of_word_then)
  qed
  show ?thesis
    by (simp only: exact_word comma_semantic_b1_rebase_word_then)
qed

text \<open>The first theorem permits translating a whole return by one common
phase offset.  The independent-offset theorem is the occurrence boundary for
composition: the second action is evaluated at the physical successor clock
plus its own offset.  The rooted form permits the offsets to depend on the
input root; the second offset is selected by `next_root` after the physical
clock advance.  No theorem here merges distinct labels or claims a particular
quotient cardinality.\<close>

ML \<open>
  val checked = @{thms comma_semantic_b1_rebase_apply
    comma_semantic_b1_rebase_add comma_semantic_b1_root_rebase_add
    comma_semantic_b1_phase_shift_add
    comma_semantic_b1_rebase_inverse
    comma_semantic_b1_rebase_child_phase comma_semantic_b1_rebase_word_then
    comma_semantic_b1_independent_occurrence_offsets
    comma_semantic_b1_rooted_occurrence_offsets
    comma_semantic_b1_rebase_of_word_then};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Occurrence phase rebase for semantic B1" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "B1 word-to-semantic occurrence rebase"
    ["comma_semantic_b1_of_word_then"]
    @{thms comma_semantic_b1_rebase_of_word_then};
\<close>

end
