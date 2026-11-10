theory Comma_CRT_Support
  imports Comma_CRT_Apply_Right_Quotient Shared_S_Arithmetic.CRT_Predicate
begin

text \<open>
Support is structural, not a test for the syntax \<^term>\<open>Comma_CRT_Bool False\<close>.
Admitted ordered columns can contain a node whose every branch is false, so
syntactic falsehood alone is not an emptiness test.  A supported node has at
least one supported child; the path below records one residue choice at each
successive CRT coordinate.  The finite CRT theorem realizes that path in the
external 924-clock without enumerating its phases.
\<close>

primrec comma_crt_supported :: "comma_crt_column \<Rightarrow> bool" where
  "comma_crt_supported (Comma_CRT_Bool value) = value"
| "comma_crt_supported (Comma_CRT_Node level children) =
    list_ex id (map comma_crt_supported children)"

declare comma_crt_supported.simps(2)[code drop]
declare comma_crt_supported.simps(1)[code]

lemma comma_crt_supported_node_short_circuit[code]:
  "comma_crt_supported (Comma_CRT_Node level children) =
    list_ex comma_crt_supported children"
  by (simp add: list_ex_iff)

primrec comma_crt_support_path :: "comma_crt_column \<Rightarrow> (nat \<times> nat) list" where
  "comma_crt_support_path (Comma_CRT_Bool value) = []"
| "comma_crt_support_path (Comma_CRT_Node level children) =
    (let digit = (SOME digit. digit<length children \<and>
        comma_crt_supported (children!digit))
     in (level,digit)#(map comma_crt_support_path children!digit))"

lemma comma_crt_supported_node_iff:
  "comma_crt_supported (Comma_CRT_Node level children) \<longleftrightarrow>
    (\<exists>digit<length children. comma_crt_supported (children!digit))"
  by (auto simp: list_ex_iff in_set_conv_nth intro: bexI[OF _ nth_mem])

lemma comma_crt_support_path_facts:
  assumes admitted: "comma_crt_admitted lower column"
    and supported: "comma_crt_supported column"
  shows "distinct (map fst (comma_crt_support_path column)) \<and>
    (\<forall>entry\<in>set (comma_crt_support_path column).
      lower\<le>fst entry \<and> fst entry<4 \<and>
      snd entry<comma_crt_period (fst entry))"
  using admitted supported
proof (induction column arbitrary: lower)
  case (Comma_CRT_Bool truth)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  let ?digit = "SOME digit. digit<length children \<and>
    comma_crt_supported (children!digit)"
  have lower: "lower\<le>level" and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems by (auto simp: list_all_iff)
  have selected_exists:
    "\<exists>digit. digit<length children \<and>
      comma_crt_supported (children!digit)"
    using Comma_CRT_Node.prems(2) comma_crt_supported_node_iff by blast
  have selected: "?digit<length children"
    and child_supported: "comma_crt_supported (children!?digit)"
    using someI_ex[OF selected_exists] by blast+
  have child_member: "children!?digit\<in>set children"
    by (rule nth_mem[OF selected])
  have child_admitted: "comma_crt_admitted (Suc level) (children!?digit)"
    using children_admitted child_member by blast
  have child_facts:
    "distinct (map fst (comma_crt_support_path (children!?digit))) \<and>
      (\<forall>entry\<in>set (comma_crt_support_path (children!?digit)).
        Suc level\<le>fst entry \<and> fst entry<4 \<and>
        snd entry<comma_crt_period (fst entry))"
    by (rule Comma_CRT_Node.IH[OF child_member child_admitted child_supported])
  have path:
    "comma_crt_support_path (Comma_CRT_Node level children) =
      (level,?digit)#comma_crt_support_path (children!?digit)"
    using selected by (simp add: Let_def nth_map)
  have digit_period: "?digit<comma_crt_period level"
    using selected width by simp
  show ?case using path child_facts lower level digit_period by auto
qed

lemma comma_crt_eval_supported:
  assumes admitted: "comma_crt_admitted lower column"
    and evaluates: "comma_crt_eval phase column"
  shows "comma_crt_supported column"
  using admitted evaluates
proof (induction column arbitrary: lower phase)
  case (Comma_CRT_Bool truth)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  have lower: "lower\<le>level" and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems(1) by (auto simp: list_all_iff)
  have digit: "phase mod comma_crt_period level<length children"
    using comma_crt_period_positive[OF level] width by simp
  have child_evaluates:
    "comma_crt_eval phase (children!(phase mod comma_crt_period level))"
    using Comma_CRT_Node.prems(2) level width digit by (simp add: nth_map)
  have child_admitted:
    "comma_crt_admitted (Suc level) (children!(phase mod comma_crt_period level))"
    using children_admitted nth_mem[OF digit] by blast
  have child_supported:
    "comma_crt_supported (children!(phase mod comma_crt_period level))"
    by (rule Comma_CRT_Node.IH[OF nth_mem[OF digit] child_admitted child_evaluates])
  show ?case using digit child_supported
    by (auto simp only: comma_crt_supported_node_iff)
qed

lemma comma_crt_period_pairwise_coprime:
  assumes levels: "left<4" "right<4" "left\<noteq>right"
  shows "coprime (comma_crt_period left) (comma_crt_period right)"
proof -
  have left_cases: "left=0 \<or> left=1 \<or> left=2 \<or> left=3"
    using levels(1) by arith
  have right_cases: "right=0 \<or> right=1 \<or> right=2 \<or> right=3"
    using levels(2) by arith
  show ?thesis using left_cases right_cases levels(3)
    by (auto simp: comma_crt_period_def; code_simp)
qed

lemma comma_crt_support_path_evaluates:
  assumes admitted: "comma_crt_admitted lower column"
    and supported: "comma_crt_supported column"
    and residues:
      "\<forall>entry\<in>set (comma_crt_support_path column).
        phase mod comma_crt_period (fst entry)=snd entry"
  shows "comma_crt_eval phase column"
  using admitted supported residues
proof (induction column arbitrary: lower phase)
  case (Comma_CRT_Bool truth)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  let ?digit = "SOME digit. digit<length children \<and>
    comma_crt_supported (children!digit)"
  have lower: "lower\<le>level" and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems(1) by (auto simp: list_all_iff)
  have selected_exists:
    "\<exists>digit. digit<length children \<and>
      comma_crt_supported (children!digit)"
    using Comma_CRT_Node.prems(2) comma_crt_supported_node_iff by blast
  have selected: "?digit<length children"
    and child_supported: "comma_crt_supported (children!?digit)"
    using someI_ex[OF selected_exists] by blast+
  have path:
    "comma_crt_support_path (Comma_CRT_Node level children) =
      (level,?digit)#comma_crt_support_path (children!?digit)"
    using selected by (simp add: Let_def nth_map)
  have parent_residue: "phase mod comma_crt_period level=?digit"
    using Comma_CRT_Node.prems(3) path by simp
  have child_admitted:
    "comma_crt_admitted (Suc level) (children!?digit)"
    using children_admitted selected by (meson in_set_conv_nth)
  have child_residues:
    "\<forall>entry\<in>set (comma_crt_support_path (children!?digit)).
      phase mod comma_crt_period (fst entry)=snd entry"
    using Comma_CRT_Node.prems(3) path by auto
  have child_evaluates:
    "comma_crt_eval phase (children!?digit)"
    by (rule Comma_CRT_Node.IH[OF nth_mem[OF selected] child_admitted child_supported child_residues])
  show ?case
    using level width selected parent_residue child_evaluates
    by (simp add: comma_crt_eval.simps nth_map)
qed

lemma comma_crt_supported_nonempty:
  assumes admitted: "comma_crt_admitted 0 column"
  shows "comma_crt_set column\<noteq>{} \<longleftrightarrow> comma_crt_supported column"
proof
  assume nonempty: "comma_crt_set column\<noteq>{}"
  then obtain phase where phase: "phase<924" and evaluates: "comma_crt_eval phase column"
    by (auto simp: comma_crt_set_def)
  show "comma_crt_supported column"
    by (rule comma_crt_eval_supported[OF admitted evaluates])
next
  assume supported: "comma_crt_supported column"
  have path_facts:
    "distinct (map fst (comma_crt_support_path column))"
    "\<forall>entry\<in>set (comma_crt_support_path column).
      fst entry<4 \<and> snd entry<comma_crt_period (fst entry)"
    using comma_crt_support_path_facts[OF admitted supported] by auto
  have pairwise:
    "\<forall>i\<in>set (comma_crt_support_path column).
      \<forall>j\<in>set (comma_crt_support_path column).
        i\<noteq>j \<longrightarrow>
          coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
  proof (intro ballI impI)
    fix i j
    assume i: "i\<in>set (comma_crt_support_path column)"
      and j: "j\<in>set (comma_crt_support_path column)"
      and distinct: "i\<noteq>j"
    have injective: "inj_on fst (set (comma_crt_support_path column))"
      using path_facts(1) by (auto simp: distinct_map)
    have levels_distinct: "fst i\<noteq>fst j"
    proof
      assume equal: "fst i=fst j"
      have "i=j" by (rule inj_onD[OF injective equal i j])
      with distinct show False by simp
    qed
    show "coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
      by (rule comma_crt_period_pairwise_coprime) (use path_facts(2) i j levels_distinct in auto)
  qed
  have crt:
    "\<exists>phase. \<forall>entry\<in>set (comma_crt_support_path column).
      [phase=snd entry] (mod comma_crt_period (fst entry))"
  proof (rule chinese_remainder_nat)
    show "finite (set (comma_crt_support_path column))" by simp
    show "\<forall>i\<in>set (comma_crt_support_path column).
        \<forall>j\<in>set (comma_crt_support_path column). i\<noteq>j \<longrightarrow>
          coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
      by (rule pairwise)
  qed
  then obtain witness where congruences:
    "\<forall>entry\<in>set (comma_crt_support_path column).
      [witness=snd entry] (mod comma_crt_period (fst entry))"
    by blast
  let ?phase = "witness mod 924"
  have phase_bound: "?phase<924" by simp
  have residues:
    "\<forall>entry\<in>set (comma_crt_support_path column).
      ?phase mod comma_crt_period (fst entry)=snd entry"
  proof (intro ballI)
    fix entry
    assume entry: "entry\<in>set (comma_crt_support_path column)"
    let ?period = "comma_crt_period (fst entry)"
    have level: "fst entry<4" and target: "snd entry<?period"
      using path_facts(2) entry by auto
    have divides: "?period dvd 924"
      by (rule comma_crt_period_divides[OF level])
    have congruent: "[witness=snd entry] (mod ?period)"
      using congruences entry by blast
    have witness_residue: "witness mod ?period=snd entry"
      using congruent target by (simp add: cong_def)
    have reduce: "(witness mod 924) mod ?period=witness mod ?period"
      by (rule mod_mod_cancel[OF divides])
    show "?phase mod ?period=snd entry"
      using reduce witness_residue by simp
  qed
  have evaluates: "comma_crt_eval ?phase column"
    by (rule comma_crt_support_path_evaluates[OF admitted supported residues])
  have member: "?phase\<in>comma_crt_set column"
    using phase_bound evaluates by (simp add: comma_crt_set_def)
  show "comma_crt_set column\<noteq>{}" using member by blast
qed

ML \<open>
  val checked = @{thms comma_crt_supported_nonempty};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Structural CRT support" checked;
\<close>

end
