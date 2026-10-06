theory Comma_Rank_Data
  imports Comma_Rank_Data_N Comma_Rank_Data_Z
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

text \<open>Both side tables are untrusted candidate definitions. The checked
  instance compares every rank with complete children computed from the
  executable HOL transition. The public lookup distinguishes invalid input from
  an unranked boundary and a ranked boundary. The option adapter below exists
  only for theorem families whose domain is already restricted to valid states.\<close>

ML \<open>
  structure Comma_Rank_Data_Profile =
  struct
    val started = Time.now ()
    fun checkpoint stage =
      Comma_Proof_Profile.report
        ("Comma rank data stage=" ^ stage ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
  end
  val _ = Comma_Rank_Data_Profile.checkpoint "datatype-start"
\<close>

datatype comma_rank_lookup_result =
    Comma_Rank_Invalid
  | Comma_Rank_Unranked
  | Comma_Rank_Value nat

ML \<open>val _ = Comma_Rank_Data_Profile.checkpoint "datatype-finished"\<close>

definition comma_rank_code_at :: "nat \<Rightarrow> nat option" where
  "comma_rank_code_at i =
    (if i < 8 * 924 then
      Some (comma_rank_codes_N ! (i div 4096) ! ((i div 256) mod 16) !
        ((i div 16) mod 16) ! (i mod 16))
     else if i < 16 * 924 then
      (let j = i - 8 * 924 in
        Some (comma_rank_codes_Z ! (j div 4096) ! ((j div 256) mod 16) !
          ((j div 16) mod 16) ! (j mod 16)))
     else None)"

definition comma_rank_lookup ::
  "comma_boundary_state \<Rightarrow> comma_rank_lookup_result" where
  "comma_rank_lookup q =
    (if \<not> comma_boundary_valid q then Comma_Rank_Invalid else
      (case q of (kind,a,r) \<Rightarrow>
        (case comma_rank_code_at
          ((if kind = Comma_Z then 8 * 924 else 0) + (a - 2) * 924 + r) of
          None \<Rightarrow> Comma_Rank_Invalid
        | Some 0 \<Rightarrow> Comma_Rank_Unranked
        | Some (Suc n) \<Rightarrow> Comma_Rank_Value n)))"

definition comma_rank_candidate_on_valid :: "comma_boundary_state \<Rightarrow> nat option" where
  "comma_rank_candidate_on_valid q =
    (if comma_boundary_valid q then
      (case comma_rank_lookup q of
        Comma_Rank_Value n \<Rightarrow> Some n
      | Comma_Rank_Unranked \<Rightarrow> None
     | Comma_Rank_Invalid \<Rightarrow> None)
     else None)"

ML \<open>val _ = Comma_Rank_Data_Profile.checkpoint "wrapper-refinement-start"\<close>

lemma comma_rank_code_at_some:
  assumes "i < 16 * 924"
  shows "\<exists>code. comma_rank_code_at i = Some code"
  using assms unfolding comma_rank_code_at_def
  by (cases "i < 8 * 924") (auto simp: Let_def)

lemma comma_rank_index_bound:
  fixes a r :: nat
  assumes "2 \<le> a" "a \<le> 9" "r < 924"
  shows "(if kind = Comma_Z then 8 * 924 else 0) + (a - 2) * 924 + r < 16 * 924"
  using assms by (cases kind; simp; presburger)

lemma comma_rank_lookup_valid_not_invalid:
  assumes valid: "comma_boundary_valid q"
  shows "comma_rank_lookup q \<noteq> Comma_Rank_Invalid"
proof -
  obtain kind a r where q: "q = (kind,a,r)" by (cases q) auto
  have components: "2 \<le> a" "a \<le> 9" "r < 924"
    using valid q by (simp_all add: comma_boundary_valid_def)
  have index:
    "(if kind = Comma_Z then 8 * 924 else 0) + (a - 2) * 924 + r < 16 * 924"
    by (rule comma_rank_index_bound[OF components])
  obtain code where code:
    "comma_rank_code_at
      ((if kind = Comma_Z then 8 * 924 else 0) + (a - 2) * 924 + r) = Some code"
    using comma_rank_code_at_some[OF index] by blast
  show ?thesis
    using valid q code
    by (auto simp: comma_rank_lookup_def comma_boundary_valid_def
        split: nat.splits)
qed

lemma comma_rank_candidate_on_valid_refines_lookup:
  assumes valid: "comma_boundary_valid q"
  shows "(comma_rank_candidate_on_valid q = None \<longleftrightarrow>
      comma_rank_lookup q = Comma_Rank_Unranked) \<and>
    (comma_rank_candidate_on_valid q = Some n \<longleftrightarrow>
      comma_rank_lookup q = Comma_Rank_Value n)"
proof -
  have not_invalid: "comma_rank_lookup q \<noteq> Comma_Rank_Invalid"
    by (rule comma_rank_lookup_valid_not_invalid[OF valid])
  show ?thesis
    using valid not_invalid
    by (cases "comma_rank_lookup q")
      (auto simp: comma_rank_candidate_on_valid_def)
qed

ML \<open>val _ = Comma_Rank_Data_Profile.checkpoint "wrapper-refinement-finished"\<close>

lemma comma_rank_lookup_invalid:
  assumes "\<not>comma_boundary_valid q"
  shows "comma_rank_lookup q = Comma_Rank_Invalid"
  using assms by (simp add: comma_rank_lookup_def)

lemma comma_rank_lookup_invalid_inputs:
  "comma_rank_lookup (Comma_N,1,0) = Comma_Rank_Invalid"
  "comma_rank_lookup (Comma_N,10,0) = Comma_Rank_Invalid"
  "comma_rank_lookup (Comma_N,2,924) = Comma_Rank_Invalid"
  "comma_rank_lookup (Comma_Z,1,0) = Comma_Rank_Invalid"
  "comma_rank_lookup (Comma_Z,10,0) = Comma_Rank_Invalid"
  by (simp_all add: comma_rank_lookup_def comma_boundary_valid_def)

lemma comma_rank_code_at_invalid_index:
  assumes "16 * 924 \<le> i"
  shows "comma_rank_code_at i = None"
proof -
  have "\<not>i < 8 * 924" using assms by linarith
  with assms show ?thesis by (simp add: comma_rank_code_at_def)
qed

lemma comma_rank_code_at_outside_table:
  "comma_rank_code_at (16 * 924) = None"
  by (simp add: comma_rank_code_at_def)

ML \<open>
  val _ = Comma_Rank_Data_Profile.checkpoint "invalid-regressions-finished";
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_rank_code_at_def comma_rank_lookup_def
      comma_rank_candidate_on_valid_def comma_rank_code_at_some
      comma_rank_index_bound comma_rank_lookup_valid_not_invalid
      comma_rank_candidate_on_valid_refines_lookup
      comma_rank_lookup_invalid comma_rank_lookup_invalid_inputs
      comma_rank_code_at_invalid_index comma_rank_code_at_outside_table})
    then () else error "Comma rank lookup depends on an oracle";
  val _ = Comma_Rank_Data_Profile.checkpoint "final-audit-finished";
\<close>

end
