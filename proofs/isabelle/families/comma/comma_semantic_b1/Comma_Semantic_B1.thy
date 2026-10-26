theory Comma_Semantic_B1
  imports Comma_Decisive_Endpoint_Quotient.Comma_Source_Continuation_DAG
    Comma_Terminal_Weight.Comma_Terminal_Weight
begin
ML \<open>Comma_Proof_Profile.report "Semantic B1 root theory stage=entered"\<close>

text \<open>
This theory gives the weighted observable algebra for a B1 action.  A live
result names its next admitted root; a stop is represented by the exact
terminal-position weight D=9H+J.  The cyclotomic phase remains an argument to
application.  These definitions establish an exact action/weight interface;
they do not claim that a finite semantic-ID table or production publisher has
already been installed.
\<close>

datatype comma_semantic_b1_result =
    Comma_Semantic_B1_Live nat
  | Comma_Semantic_B1_Stop nat
  | Comma_Semantic_B1_Invalid

fun comma_semantic_b1_of_word ::
    "comma_word_result \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_of_word (Comma_Word_Live root) = Comma_Semantic_B1_Live root"
| "comma_semantic_b1_of_word (Comma_Word_Stop height terminal) =
    Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
| "comma_semantic_b1_of_word Comma_Word_Invalid = Comma_Semantic_B1_Invalid"

definition comma_semantic_b1 :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1 r root = comma_semantic_b1_of_word (comma_decisive_B1 r root)"

text \<open>The semantic ID is its complete phase-to-action function.  It has
no source address or absolute clock field: callers apply it at a phase, and
equality is extensional equality of all admitted outputs.  The finite
certificate/interning implementation of this function remains a separate
consumer obligation.\<close>

type_synonym comma_semantic_b1_id = "nat \<Rightarrow> comma_semantic_b1_result"

definition comma_semantic_b1_id_of_root :: "nat \<Rightarrow> comma_semantic_b1_id" where
  "comma_semantic_b1_id_of_root root = (\<lambda>clock.
    comma_semantic_b1 (clock mod 924) root)"

definition comma_semantic_b1_apply ::
    "comma_semantic_b1_id \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_apply action clock = action (clock mod 924)"

lemma comma_semantic_b1_id_apply:
  "comma_semantic_b1_apply (comma_semantic_b1_id_of_root root) clock =
    comma_semantic_b1 (clock mod 924) root"
  by (simp add: comma_semantic_b1_apply_def comma_semantic_b1_id_of_root_def)
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_id_apply}];
  Comma_Proof_Profile.report "Semantic B1 root claim=id-apply checked"\<close>

lemma comma_semantic_b1_id_extensional:
  "comma_semantic_b1_id_of_root left = comma_semantic_b1_id_of_root right \<longleftrightarrow>
    (\<forall>clock<924. comma_semantic_b1 clock left = comma_semantic_b1 clock right)"
proof
  assume same: "comma_semantic_b1_id_of_root left = comma_semantic_b1_id_of_root right"
  show "\<forall>clock<924. comma_semantic_b1 clock left = comma_semantic_b1 clock right"
  proof (intro allI impI)
    fix clock :: nat
    assume clock_bound: "clock<924"
    have action_value:
      "comma_semantic_b1_id_of_root left clock =
        comma_semantic_b1_id_of_root right clock"
      by (rule fun_cong[OF same])
    show "comma_semantic_b1 clock left = comma_semantic_b1 clock right"
      using action_value clock_bound
      by (simp add: comma_semantic_b1_id_of_root_def)
  qed
next
  assume same: "\<forall>clock<924. comma_semantic_b1 clock left = comma_semantic_b1 clock right"
  show "comma_semantic_b1_id_of_root left = comma_semantic_b1_id_of_root right"
  proof (rule ext)
    fix clock :: nat
    have phase: "clock mod 924<924" by simp
    show "comma_semantic_b1_id_of_root left clock =
      comma_semantic_b1_id_of_root right clock"
      using same[rule_format, OF phase]
      by (simp add: comma_semantic_b1_id_of_root_def)
  qed
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_id_extensional}];
  Comma_Proof_Profile.report "Semantic B1 root claim=id-extensional checked"\<close>

definition comma_semantic_b1_source ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_source r offset =
    comma_semantic_b1_of_word (comma_decisive_B1_source r offset)"

definition comma_semantic_word_then ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow>
      (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_word_then n A B r root =
    (case A r root of
       Comma_Semantic_B1_Live next_root \<Rightarrow>
         (case B ((r+n) mod 924) next_root of
            Comma_Semantic_B1_Stop D \<Rightarrow>
              Comma_Semantic_B1_Stop (9*n+D)
          | result \<Rightarrow> result)
     | result \<Rightarrow> result)"

lemma comma_semantic_word_then_stop:
  assumes "first phase root = Comma_Semantic_B1_Stop height"
  shows "comma_semantic_word_then amount first second phase root =
    Comma_Semantic_B1_Stop height"
  using assms by (simp add: comma_semantic_word_then_def)

lemma comma_semantic_word_then_invalid:
  assumes "first phase root = Comma_Semantic_B1_Invalid"
  shows "comma_semantic_word_then amount first second phase root =
    Comma_Semantic_B1_Invalid"
  using assms by (simp add: comma_semantic_word_then_def)

lemma comma_semantic_b1_of_word_then:
  "comma_semantic_b1_of_word (comma_word_then n A B r root) =
    comma_semantic_word_then n
      (\<lambda>phase i. comma_semantic_b1_of_word (A phase i))
      (\<lambda>phase i. comma_semantic_b1_of_word (B phase i)) r root"
  by (cases "A r root")
    (simp_all add: comma_semantic_word_then_def comma_word_then_def
      comma_terminal_weight_encode_def algebra_simps
      split: comma_word_result.splits comma_semantic_b1_result.splits)
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_of_word_then}];
  Comma_Proof_Profile.report "Semantic B1 root claim=word-then checked"\<close>

lemma comma_semantic_b1_exact_orbit:
  assumes phase: "r<924" and root: "i<46"
  shows "comma_semantic_b1 r i =
    comma_semantic_b1_of_word (comma_orbit_word 0 r i)"
  using comma_decisive_B1_refines_orbit_word[OF phase root]
  by (simp add: comma_semantic_b1_def)
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_exact_orbit}];
  Comma_Proof_Profile.report "Semantic B1 root claim=exact-orbit checked"\<close>

lemma comma_semantic_b1_source_exact_atom:
  assumes phase: "r<924" and offset: "x\<le>90"
  shows "comma_semantic_b1_source r x =
    comma_semantic_b1_of_word
      (comma_word_project comma_offset_orbit
        (comma_decade_block_atom (Comma_Decade r x)))"
  using comma_decisive_B1_source_refines_atom[OF phase offset]
  by (simp add: comma_semantic_b1_source_def)
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_source_exact_atom}];
  Comma_Proof_Profile.report "Semantic B1 root claim=source-exact-atom checked"\<close>

theorem comma_semantic_b1_square:
  assumes phase: "r<924" and root: "i<46"
  shows "comma_semantic_b1_of_word (comma_orbit_word (Suc k) r i) =
    comma_semantic_word_then (2^k)
      (\<lambda>phase root. comma_semantic_b1_of_word (comma_orbit_word k phase root))
      (\<lambda>phase root. comma_semantic_b1_of_word (comma_orbit_word k phase root))
      r i"
  using comma_semantic_b1_of_word_then[of "2^k" "comma_orbit_word k"
      "comma_orbit_word k" r i]
    comma_orbit_word_square[OF phase root, of k]
  by simp
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_square}];
  Comma_Proof_Profile.report "Semantic B1 root claim=square checked"\<close>

theorem comma_semantic_b1_stop_decode:
  assumes admitted: "comma_terminal_weight_admitted terminal"
  shows "comma_semantic_b1_of_word (Comma_Word_Stop height terminal) =
      Comma_Semantic_B1_Stop D \<Longrightarrow>
    comma_terminal_weight_decode D=(height,terminal)"
proof -
  assume stopped:
    "comma_semantic_b1_of_word (Comma_Word_Stop height terminal) =
      Comma_Semantic_B1_Stop D"
  have encoded: "D = comma_terminal_weight_encode height terminal"
    using stopped
    by (metis comma_semantic_b1_of_word.simps comma_semantic_b1_result.inject)
  have decoded:
    "comma_terminal_weight_decode (comma_terminal_weight_encode height terminal) =
      (height, terminal)"
    by (rule comma_terminal_weight_decode_encode[OF admitted])
  show ?thesis using encoded decoded by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_stop_decode}];
  Comma_Proof_Profile.report "Semantic B1 root claim=stop-decode checked"\<close>

ML \<open>
  val checked = @{thms comma_semantic_word_then_stop comma_semantic_word_then_invalid
    comma_semantic_b1_of_word_then
    comma_semantic_b1_id_apply comma_semantic_b1_id_extensional
    comma_semantic_b1_exact_orbit comma_semantic_b1_source_exact_atom
    comma_semantic_b1_square comma_semantic_b1_stop_decode};
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=native entered";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted semantic B1 action" checked;
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=native checked";
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=endpoint paths entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "B1 exact endpoint and weighted composition"
    ["comma_decisive_B1_refines_orbit_word",
      "comma_decisive_B1_source_refines_atom",
      "comma_terminal_weight_decode_encode"]
    @{thms comma_semantic_b1_exact_orbit
      comma_semantic_b1_source_exact_atom comma_semantic_b1_stop_decode};
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=endpoint paths checked";
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=power path entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "B1 power composition" ["comma_orbit_word_square"]
    @{thms comma_semantic_b1_square};
  val _ = Comma_Proof_Profile.report "Semantic B1 root audit=power path checked";
\<close>

end
