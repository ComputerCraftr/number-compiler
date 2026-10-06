theory Comma_Semantic_B1_Publication
  imports Comma_Semantic_B1_Columns Shared_S_Arithmetic.CRT_Predicate
begin

text \<open>
The graph constructor carries phase columns as finite unions of CRT scopes.
This theory owns the checked set algebra used to turn those scopes into a
publication table.  In particular, coverage is derived by intersecting a
complete child partition with a parent slot; it is not accepted from a
counting claim made by the ML constructor.
\<close>

definition comma_semantic_b1_scope_admitted :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_scope_admitted period residue \<longleftrightarrow>
    0 < period \<and> period dvd 924 \<and> residue < period"

definition comma_semantic_b1_scope_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "comma_semantic_b1_scope_set period residue =
    {phase. phase < 924 \<and> phase mod period = residue}"

lemma comma_semantic_b1_scope_set_meet:
  assumes left: "comma_semantic_b1_scope_admitted p a"
    and right: "comma_semantic_b1_scope_admitted q b"
    and modulus: "l = lcm p q"
    and witness_bound: "c < l"
    and witness_left: "c mod p = a"
    and witness_right: "c mod q = b"
  shows "comma_semantic_b1_scope_set p a \<inter>
      comma_semantic_b1_scope_set q b = comma_semantic_b1_scope_set l c"
proof -
  have p_positive: "0 < p" and q_positive: "0 < q"
    using left right by (auto simp: comma_semantic_b1_scope_admitted_def)
  have result: "comma_semantic_b1_scope_admitted l c"
  proof -
    have p_divides: "p dvd 924" and q_divides: "q dvd 924"
      using left right by (auto simp: comma_semantic_b1_scope_admitted_def)
    have divides: "l dvd 924"
    proof -
      have "lcm p q dvd 924"
        by (rule lcm_least[OF p_divides q_divides])
      then show ?thesis using modulus by simp
    qed
    have positive: "0 < l"
      using modulus p_positive q_positive by (simp add: lcm_pos_nat)
    show ?thesis
      using positive divides witness_bound
      by (simp add: comma_semantic_b1_scope_admitted_def)
  qed
  have same_class:
      "(phase mod p = a \<and> phase mod q = b) \<longleftrightarrow>
        phase mod l = c"
    for phase :: nat
    by (rule residue_predicate_lcm[OF p_positive q_positive modulus
        witness_bound witness_left witness_right])
  show ?thesis
  proof (rule set_eqI)
    fix phase
    show "phase \<in> comma_semantic_b1_scope_set p a \<inter>
        comma_semantic_b1_scope_set q b \<longleftrightarrow>
      phase \<in> comma_semantic_b1_scope_set l c"
      using same_class[of phase] left right result
      by (auto simp: comma_semantic_b1_scope_set_def)
  qed
qed

lemma comma_semantic_b1_scope_set_disjoint:
  assumes left: "comma_semantic_b1_scope_admitted p a"
    and right: "comma_semantic_b1_scope_admitted q b"
    and incompatible: "a mod gcd p q \<noteq> b mod gcd p q"
  shows "comma_semantic_b1_scope_set p a \<inter>
    comma_semantic_b1_scope_set q b = {}"
proof -
  have p_positive: "0 < p" and q_positive: "0 < q"
    using left right by (auto simp: comma_semantic_b1_scope_admitted_def)
  have classes_empty:
      "{phase. phase mod p = a} \<inter> {phase. phase mod q = b} = {}"
    by (rule residue_predicates_gcd_disjoint[OF p_positive q_positive incompatible])
  show ?thesis
  proof (rule set_eqI)
    fix phase
    show "phase \<in> comma_semantic_b1_scope_set p a \<inter>
        comma_semantic_b1_scope_set q b \<longleftrightarrow> phase \<in> {}"
      using classes_empty
      by (auto simp: comma_semantic_b1_scope_set_def)
  qed
qed

lemma comma_semantic_b1_scope_slots_cover:
  assumes positive: "0 < period"
    and divides: "period dvd 924"
  shows "(\<Union> residue\<in>{..<period}.
      comma_semantic_b1_scope_set period residue) = {..<924}"
proof (rule set_eqI)
  fix phase
  show "phase \<in> (\<Union> residue\<in>{..<period}.
      comma_semantic_b1_scope_set period residue) \<longleftrightarrow>
    phase \<in> {..<924}"
  proof
    assume member:
      "phase \<in> (\<Union> residue\<in>{..<period}.
        comma_semantic_b1_scope_set period residue)"
    then obtain residue where residue: "residue < period"
      and member: "phase \<in> comma_semantic_b1_scope_set period residue"
      by blast
    show "phase \<in> {..<924}"
      using member by (auto simp: comma_semantic_b1_scope_set_def)
  next
    assume phase_member: "phase \<in> {..<924}"
    have phase: "phase < 924" using phase_member by simp
    have residue: "phase mod period \<in> {..<period}"
      using positive by simp
    have member:
      "phase \<in> comma_semantic_b1_scope_set period (phase mod period)"
      using phase by (simp add: comma_semantic_b1_scope_set_def)
    show "phase \<in> (\<Union> residue\<in>{..<period}.
        comma_semantic_b1_scope_set period residue)"
      by (rule UN_I[where A="{..<period}" and a="phase mod period"
        and B="comma_semantic_b1_scope_set period" and b=phase, OF residue member])
  qed
qed

lemma comma_semantic_b1_scope_slots_disjoint:
  assumes positive: "0 < period"
    and divides: "period dvd 924"
    and left: "left < period"
    and right: "right < period"
    and distinct: "left \<noteq> right"
  shows "comma_semantic_b1_scope_set period left \<inter>
    comma_semantic_b1_scope_set period right = {}"
proof (rule set_eqI)
  fix phase
  show "phase \<in> comma_semantic_b1_scope_set period left \<inter>
      comma_semantic_b1_scope_set period right \<longleftrightarrow> phase \<in> {}"
    using positive left right distinct
    by (auto simp: comma_semantic_b1_scope_set_def)
qed

definition comma_semantic_b1_restrict_rows ::
    "nat set \<Rightarrow> comma_semantic_b1_binding_row list \<Rightarrow>
      comma_semantic_b1_binding_row list" where
  "comma_semantic_b1_restrict_rows parent rows =
    filter (\<lambda>row. fst row \<inter> parent \<noteq> {})
      (map (\<lambda>row. (fst row \<inter> parent, snd row)) rows)"

definition comma_semantic_b1_local_binding_row_exact ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      nat set \<Rightarrow> comma_semantic_b1_binding_row \<Rightarrow> bool" where
  "comma_semantic_b1_local_binding_row_exact action shift domain row \<longleftrightarrow>
    fst row \<noteq> {} \<and> fst row \<subseteq> domain \<and>
    fst row = {phase. phase < 924 \<and> phase \<in> domain \<and>
      action ((phase+shift) mod 924) = snd row}"

lemma comma_semantic_b1_restrict_rows_cover:
  "(\<Union> (fst ` set (comma_semantic_b1_restrict_rows parent rows))) =
    parent \<inter> (\<Union> (fst ` set rows))"
proof (rule set_eqI)
  fix phase
  show "phase \<in> (\<Union> (fst ` set
      (comma_semantic_b1_restrict_rows parent rows))) \<longleftrightarrow>
    phase \<in> parent \<inter> (\<Union> (fst ` set rows))"
    by (auto simp: comma_semantic_b1_restrict_rows_def)
qed

lemma comma_semantic_b1_restrict_rows_disjoint:
  assumes disjoint:
    "\<And>left right. left \<in> set rows \<Longrightarrow> right \<in> set rows \<Longrightarrow>
      left \<noteq> right \<Longrightarrow> fst left \<inter> fst right = {}"
  shows "\<And>left right.
      left \<in> set (comma_semantic_b1_restrict_rows parent rows) \<Longrightarrow>
      right \<in> set (comma_semantic_b1_restrict_rows parent rows) \<Longrightarrow>
      left \<noteq> right \<Longrightarrow> fst left \<inter> fst right = {}"
proof -
  fix left right
  assume left_member:
      "left \<in> set (comma_semantic_b1_restrict_rows parent rows)"
    and right_member:
      "right \<in> set (comma_semantic_b1_restrict_rows parent rows)"
    and distinct_rows: "left \<noteq> right"
  obtain left_source where left_source: "left_source \<in> set rows"
    and left_eq: "left = (fst left_source \<inter> parent, snd left_source)"
    using left_member by (auto simp: comma_semantic_b1_restrict_rows_def)
  obtain right_source where right_source: "right_source \<in> set rows"
    and right_eq: "right = (fst right_source \<inter> parent, snd right_source)"
    using right_member by (auto simp: comma_semantic_b1_restrict_rows_def)
  have source_distinct: "left_source \<noteq> right_source"
  proof
    assume equal: "left_source = right_source"
    show False using distinct_rows left_eq right_eq equal by simp
  qed
  have source_disjoint: "fst left_source \<inter> fst right_source = {}"
    by (rule disjoint[OF left_source right_source source_distinct])
  show "fst left \<inter> fst right = {}"
    using source_disjoint by (simp only: left_eq right_eq) auto
qed

lemma comma_semantic_b1_restrict_rows_nonempty:
  assumes row: "row \<in> set (comma_semantic_b1_restrict_rows parent rows)"
  shows "fst row \<noteq> {}"
  using row by (auto simp: comma_semantic_b1_restrict_rows_def)

lemma comma_semantic_b1_restrict_rows_local_exact:
  assumes table:
      "comma_semantic_b1_binding_table_exact child_action shift rows"
    and agreement:
      "\<And>phase. phase < 924 \<Longrightarrow> phase \<in> parent \<Longrightarrow>
        parent_action ((phase+shift) mod 924) =
          child_action ((phase+shift) mod 924)"
    and row:
      "row \<in> set (comma_semantic_b1_restrict_rows parent rows)"
  shows "comma_semantic_b1_local_binding_row_exact
      parent_action shift parent row"
proof -
  obtain source_row where source_row: "source_row \<in> set rows"
    and row_eq:
      "row = (fst source_row \<inter> parent, snd source_row)"
    using row by (auto simp: comma_semantic_b1_restrict_rows_def)
  have source_exact:
      "comma_semantic_b1_binding_row_exact child_action shift source_row"
    using table source_row
    by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have source_nonempty: "fst source_row \<noteq> {}"
    using source_exact
    unfolding comma_semantic_b1_binding_row_exact_def by blast
  have source_key:
      "fst source_row = {phase. phase < 924 \<and>
        child_action ((phase+shift) mod 924) = snd source_row}"
    using source_exact
    unfolding comma_semantic_b1_binding_row_exact_def by blast
  have row_nonempty: "fst row \<noteq> {}"
    by (rule comma_semantic_b1_restrict_rows_nonempty[OF row])
  have row_subset: "fst row \<subseteq> parent"
    using row_eq by auto
  have row_extension:
      "fst row = {phase. phase < 924 \<and> phase \<in> parent \<and>
        parent_action ((phase+shift) mod 924) = snd row}"
  proof (rule set_eqI)
    fix phase
    show "phase \<in> fst row \<longleftrightarrow>
        phase \<in> {phase. phase < 924 \<and> phase \<in> parent \<and>
          parent_action ((phase+shift) mod 924) = snd row}"
    proof
      assume member: "phase \<in> fst row"
      have source_member: "phase \<in> fst source_row"
        and parent_member: "phase \<in> parent"
        using member row_eq by auto
      have phase_bound: "phase < 924"
        using source_key source_member by blast
      have child_value:
          "child_action ((phase+shift) mod 924) = snd source_row"
        using source_key source_member by blast
      have parent_value:
          "parent_action ((phase+shift) mod 924) = snd row"
        using agreement[OF phase_bound parent_member] child_value row_eq
        by simp
      show "phase \<in> {phase. phase < 924 \<and> phase \<in> parent \<and>
          parent_action ((phase+shift) mod 924) = snd row}"
        using phase_bound parent_member parent_value by blast
    next
      assume member:
          "phase \<in> {phase. phase < 924 \<and> phase \<in> parent \<and>
            parent_action ((phase+shift) mod 924) = snd row}"
      then have phase_bound: "phase < 924"
        and parent_member: "phase \<in> parent"
        and parent_value:
          "parent_action ((phase+shift) mod 924) = snd row"
        by auto
      have child_value:
          "child_action ((phase+shift) mod 924) = snd source_row"
        using agreement[OF phase_bound parent_member] parent_value row_eq
        by simp
      have source_member: "phase \<in> fst source_row"
        using source_key phase_bound child_value by blast
      show "phase \<in> fst row"
        using source_member parent_member row_eq by auto
    qed
  qed
  show ?thesis
    using row_nonempty row_subset row_extension
    by (simp add: comma_semantic_b1_local_binding_row_exact_def)
qed

lemma comma_semantic_b1_terminal_scope_row_exact:
  assumes scope: "scope = comma_semantic_b1_scope_set period residue"
    and admitted: "comma_semantic_b1_scope_admitted period residue"
    and terminal_value:
      "\<And>phase. phase < 924 \<Longrightarrow> phase \<in> scope \<Longrightarrow>
        action ((phase+shift) mod 924) = result"
  shows "comma_semantic_b1_local_binding_row_exact action shift scope
      (scope,result)"
proof -
  have residue_bound: "residue < 924"
  proof -
    have "residue < period"
      using admitted by (simp add: comma_semantic_b1_scope_admitted_def)
    also have "... \<le> 924"
      using admitted by (auto simp: comma_semantic_b1_scope_admitted_def
          dest: dvd_imp_le)
    finally show ?thesis .
  qed
  have residue_member: "residue \<in> scope"
    using residue_bound admitted
    by (simp add: scope comma_semantic_b1_scope_set_def
        comma_semantic_b1_scope_admitted_def)
  have nonempty: "scope \<noteq> {}"
    using residue_member by auto
  have terminal_key:
      "scope = {phase. phase < 924 \<and> phase \<in> scope \<and>
        action ((phase+shift) mod 924) = result}"
  proof (rule set_eqI)
    fix phase
    show "phase \<in> scope \<longleftrightarrow>
        phase \<in> {phase. phase < 924 \<and> phase \<in> scope \<and>
          action ((phase+shift) mod 924) = result}"
    proof
      assume phase: "phase \<in> scope"
      have phase_bound: "phase < 924"
        using phase scope by (auto simp: comma_semantic_b1_scope_set_def)
      have terminal:
          "action ((phase+shift) mod 924) = result"
        by (rule terminal_value[OF phase_bound phase])
      show "phase \<in> {phase. phase < 924 \<and> phase \<in> scope \<and>
          action ((phase+shift) mod 924) = result}"
        using phase_bound phase terminal by blast
    next
      assume "phase \<in> {phase. phase < 924 \<and> phase \<in> scope \<and>
          action ((phase+shift) mod 924) = result}"
      then show "phase \<in> scope" by blast
    qed
  qed
  show ?thesis
    using nonempty terminal_key
    by (simp add: comma_semantic_b1_local_binding_row_exact_def)
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_scope_set_meet
    comma_semantic_b1_scope_set_disjoint comma_semantic_b1_scope_slots_cover
    comma_semantic_b1_scope_slots_disjoint comma_semantic_b1_restrict_rows_cover
    comma_semantic_b1_restrict_rows_disjoint comma_semantic_b1_restrict_rows_nonempty
    comma_semantic_b1_restrict_rows_local_exact
    comma_semantic_b1_terminal_scope_row_exact};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "CRT predicate and local return publication" checked;
\<close>

end
