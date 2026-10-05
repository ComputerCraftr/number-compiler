theory Comma_Semantic_B1_CRT_Source_Binding
  imports Comma_Semantic_B1_Table_Transform Comma_CRT_Power
begin

text \<open>
Translate source-local residue scopes into the same four-level Boolean
columns used by the production CRT/MDD owner.  The six source periods are
projections of the external cyclotomic clock; phase remains occurrence data.
No list of 924 phase values or scoped-row observer is constructed here.
\<close>

definition comma_semantic_b1_crt_source_periods :: "nat set" where
  "comma_semantic_b1_crt_source_periods={1,2,3,6,22,28}"

lemma comma_semantic_b1_generated_source_period_six:
  assumes admitted: "comma_round_admitted source"
  shows "comma_decisive_sector_period
      (comma_source_continuation_base source) \<in>
    comma_semantic_b1_crt_source_periods"
proof (cases source)
  case (Comma_Entry f delta x)
  have sector: "1\<le>f" "f\<le>9"
    using admitted by (simp_all add: Comma_Entry)
  let ?P="comma_finite_period_fast f (x mod 10)"
  let ?C="comma_core_modulus ?P"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have lift: "comma_core_lift_admitted ?P"
    by (rule comma_core_lift_catalog[OF catalog])
  have core:
      "?C\<in>{1,3,7,11,13,21,23,27,29}"
    using lift by (auto simp: comma_core_lift_admitted_def Let_def)
  have period:
      "comma_core_period ?C\<in>comma_semantic_b1_crt_source_periods"
    using core by (auto simp: comma_core_period_def
      comma_semantic_b1_crt_source_periods_def)
  show ?thesis
    using period Comma_Entry
    by (simp add: comma_decisive_sector_period_def
      comma_source_continuation_base.simps)
next
  case (Comma_Near f delta h)
  then show ?thesis
    by (simp add: comma_decisive_sector_period_def
      comma_source_continuation_base.simps
      comma_semantic_b1_crt_source_periods_def)
qed

lemma comma_semantic_b1_generated_slot_scope_certified:
  assumes admitted: "comma_round_admitted source"
    and slot: "slot<comma_decisive_sector_period
      (comma_source_continuation_base source)"
  shows "comma_semantic_b1_crt_scope_admitted
      (comma_semantic_b1_source_slot_scope
        (comma_decisive_sector_period
          (comma_source_continuation_base source)) slot) \<and>
    fst (comma_semantic_b1_source_slot_scope
      (comma_decisive_sector_period
        (comma_source_continuation_base source)) slot) \<in>
      comma_semantic_b1_crt_source_periods"
proof -
  have scope_admitted: "comma_semantic_b1_crt_scope_admitted
      (comma_semantic_b1_source_slot_scope
        (comma_decisive_sector_period
          (comma_source_continuation_base source)) slot)"
    by (rule comma_semantic_b1_source_period_admitted[OF admitted slot])
  have period:
      "comma_decisive_sector_period
        (comma_source_continuation_base source) \<in>
          comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF admitted])
  show ?thesis using scope_admitted period
    by (simp add: comma_semantic_b1_source_slot_scope_def)
qed

definition comma_crt_source_axis_column ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_crt_column" where
  "comma_crt_source_axis_column level divisor residue =
    comma_crt_node level
      (map (\<lambda>digit. Comma_CRT_Bool
        (digit mod divisor=residue mod divisor))
        [0..<comma_crt_period level])"

lemma comma_crt_source_axis_column_admitted:
  assumes level: "level<4"
  shows "comma_crt_admitted 0
    (comma_crt_source_axis_column level divisor residue)"
proof -
  have children:
      "list_all (comma_crt_admitted (Suc level))
        (map (\<lambda>digit. Comma_CRT_Bool
          (digit mod divisor=residue mod divisor))
          [0..<comma_crt_period level])"
    by (simp add: list_all_iff)
  have width:
      "length (map (\<lambda>digit. Comma_CRT_Bool
          (digit mod divisor=residue mod divisor))
          [0..<comma_crt_period level])=comma_crt_period level"
    by simp
  show ?thesis
    unfolding comma_crt_source_axis_column_def
    by (rule comma_crt_node_admitted[OF _ level width children]) simp
qed

lemma comma_crt_source_axis_column_set:
  assumes level: "level<4"
    and divisor: "0<divisor" "divisor dvd comma_crt_period level"
  shows "comma_crt_set (comma_crt_source_axis_column level divisor residue) =
    {phase. phase<924 \<and> phase mod divisor=residue mod divisor}"
proof -
  have width:
      "length (map (\<lambda>digit. Comma_CRT_Bool
          (digit mod divisor=residue mod divisor))
          [0..<comma_crt_period level])=comma_crt_period level"
    by simp
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have divides: "divisor dvd comma_crt_period level"
    by (rule divisor(2))
  show ?thesis
  proof (rule set_eqI)
    fix phase
    have residue_reduce:
        "(phase mod comma_crt_period level) mod divisor=phase mod divisor"
      by (rule mod_mod_cancel[OF divides])
    have evaluation:
        "comma_crt_eval phase (comma_crt_source_axis_column level divisor residue) =
          (phase mod divisor=residue mod divisor)"
      using level comma_crt_node_eval[OF level width, of phase]
      comma_crt_source_axis_column_admitted[OF level, of residue]
        positive residue_reduce
      by (simp add: comma_crt_source_axis_column_def
        comma_crt_eval.simps nth_map)
    show "phase \<in> comma_crt_set
        (comma_crt_source_axis_column level divisor residue) \<longleftrightarrow>
      phase \<in> {phase. phase<924 \<and>
        phase mod divisor=residue mod divisor}"
      using evaluation by (simp add: comma_crt_set_def)
  qed
qed

definition comma_crt_source_scope_column ::
    "comma_semantic_b1_crt_scope \<Rightarrow> comma_crt_column" where
  "comma_crt_source_scope_column scope =
    (case scope of (period,residue) \<Rightarrow>
      if period=1 then Comma_CRT_Bool True
      else if period=2 then comma_crt_source_axis_column 0 2 residue
      else if period=3 then comma_crt_source_axis_column 1 3 residue
      else if period=6 then comma_crt_apply Comma_CRT_And
        (comma_crt_source_axis_column 0 2 residue)
        (comma_crt_source_axis_column 1 3 residue)
      else if period=22 then comma_crt_apply Comma_CRT_And
        (comma_crt_source_axis_column 0 2 residue)
        (comma_crt_source_axis_column 3 11 residue)
      else if period=28 then comma_crt_apply Comma_CRT_And
        (comma_crt_source_axis_column 0 4 residue)
        (comma_crt_source_axis_column 2 7 residue)
      else Comma_CRT_Bool False)"

lemma comma_crt_source_scope_column_admitted:
  assumes admitted: "comma_semantic_b1_crt_scope_admitted scope"
    and period: "fst scope\<in>comma_semantic_b1_crt_source_periods"
  shows "comma_crt_admitted 0 (comma_crt_source_scope_column scope)"
proof -
  show ?thesis using admitted period
    by (cases scope) (auto simp: comma_crt_source_scope_column_def
      comma_semantic_b1_crt_scope_admitted_def
      comma_semantic_b1_scope_admitted_def
      comma_semantic_b1_crt_source_periods_def
      comma_crt_period_def comma_crt_source_axis_column_admitted
      comma_crt_apply_admitted)
qed

lemma comma_crt_source_axis_pair_set:
  fixes level_a divisor_a level_b divisor_b period residue :: nat
  assumes level_a: "level_a<4"
    and level_b: "level_b<4"
    and divisor_a: "0<divisor_a"
    and divisor_b: "0<divisor_b"
    and divides_a: "divisor_a dvd comma_crt_period level_a"
    and divides_b: "divisor_b dvd comma_crt_period level_b"
    and modulus: "period=lcm divisor_a divisor_b"
    and residue: "residue<period"
  shows "comma_crt_set (comma_crt_apply Comma_CRT_And
      (comma_crt_source_axis_column level_a divisor_a residue)
      (comma_crt_source_axis_column level_b divisor_b residue)) =
    comma_semantic_b1_scope_set period residue"
proof -
  have axis_a_admitted:
      "comma_crt_admitted 0
        (comma_crt_source_axis_column level_a divisor_a residue)"
    by (rule comma_crt_source_axis_column_admitted[OF level_a])
  have axis_b_admitted:
      "comma_crt_admitted 0
        (comma_crt_source_axis_column level_b divisor_b residue)"
    by (rule comma_crt_source_axis_column_admitted[OF level_b])
  have axis_a_set:
      "comma_crt_set (comma_crt_source_axis_column level_a divisor_a residue) =
       comma_semantic_b1_scope_set divisor_a (residue mod divisor_a)"
    using comma_crt_source_axis_column_set[OF level_a divisor_a divides_a]
    by (simp add: comma_semantic_b1_scope_set_def)
  have axis_b_set:
      "comma_crt_set (comma_crt_source_axis_column level_b divisor_b residue) =
       comma_semantic_b1_scope_set divisor_b (residue mod divisor_b)"
    using comma_crt_source_axis_column_set[OF level_b divisor_b divides_b]
    by (simp add: comma_semantic_b1_scope_set_def)
  have level_a_divides: "comma_crt_period level_a dvd 924"
    by (rule comma_crt_period_divides[OF level_a])
  have level_b_divides: "comma_crt_period level_b dvd 924"
    by (rule comma_crt_period_divides[OF level_b])
  have divisor_a_divides: "divisor_a dvd 924"
    by (rule dvd_trans[OF divides_a level_a_divides])
  have divisor_b_divides: "divisor_b dvd 924"
    by (rule dvd_trans[OF divides_b level_b_divides])
  have left_scope:
      "comma_semantic_b1_scope_admitted divisor_a
        (residue mod divisor_a)"
    using divisor_a divisor_a_divides
    by (simp add: comma_semantic_b1_scope_admitted_def)
  have right_scope:
      "comma_semantic_b1_scope_admitted divisor_b
        (residue mod divisor_b)"
    using divisor_b divisor_b_divides
    by (simp add: comma_semantic_b1_scope_admitted_def)
  have scopes_meet:
      "comma_semantic_b1_scope_set divisor_a (residue mod divisor_a) \<inter>
       comma_semantic_b1_scope_set divisor_b (residue mod divisor_b) =
       comma_semantic_b1_scope_set period residue"
    by (rule comma_semantic_b1_scope_set_meet
      [where p=divisor_a and a="residue mod divisor_a"
        and q=divisor_b and b="residue mod divisor_b"
        and l=period and c=residue])
      (use left_scope right_scope modulus residue in simp_all)
  show ?thesis
    using axis_a_admitted axis_b_admitted axis_a_set axis_b_set scopes_meet
    by (simp add: comma_crt_apply_and_set)
qed

lemma comma_crt_source_scope_column_set:
  assumes admitted: "comma_semantic_b1_crt_scope_admitted scope"
    and period: "fst scope\<in>comma_semantic_b1_crt_source_periods"
  shows "comma_crt_set (comma_crt_source_scope_column scope) =
    {phase. phase<924 \<and>
      comma_semantic_b1_crt_scope_holds scope phase}"
proof -
  have true_set:
      "comma_crt_set (Comma_CRT_Bool True)={phase. phase<924}"
    by (simp add: comma_crt_set_def)
  obtain p r where scope_eq: "scope=(p,r)"
    by (cases scope) auto
  have canonical: "r<p"
    using admitted scope_eq
    by (simp add: comma_semantic_b1_crt_scope_admitted_def
      comma_semantic_b1_scope_admitted_def)
  have source_period:
      "p=1 \<or> p=2 \<or> p=3 \<or> p=6 \<or> p=22 \<or> p=28"
    using period scope_eq
    by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have target_scope:
      "{phase. phase<924 \<and>
          comma_semantic_b1_crt_scope_holds (p,r) phase} =
        comma_semantic_b1_scope_set p r"
    by (simp add: comma_semantic_b1_crt_scope_holds_def
      comma_semantic_b1_scope_set_def)
  show ?thesis
  proof (cases p)
    case 0
    then show ?thesis using canonical by simp
  next
    case (Suc p0)
    from source_period show ?thesis
    proof (elim disjE)
      assume p1: "p=1"
      have r0: "r=0" using canonical p1 by simp
      show ?thesis
        using true_set p1 r0 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def
          comma_semantic_b1_scope_set_def)
    next
      assume p2: "p=2"
      have axis:
          "comma_crt_set (comma_crt_source_axis_column 0 2 r) =
            comma_semantic_b1_scope_set 2 r"
        using comma_crt_source_axis_column_set[of 0 2 r] canonical p2
        by (simp add: comma_crt_period_def comma_semantic_b1_scope_set_def)
      show ?thesis
        using axis p2 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def)
    next
      assume p3: "p=3"
      have axis:
          "comma_crt_set (comma_crt_source_axis_column 1 3 r) =
            comma_semantic_b1_scope_set 3 r"
        using comma_crt_source_axis_column_set[of 1 3 r] canonical p3
        by (simp add: comma_crt_period_def comma_semantic_b1_scope_set_def)
      show ?thesis
        using axis p3 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def)
    next
      assume p6: "p=6"
      have modulus: "(6::nat)=lcm 2 3" by code_simp
      have pair:
          "comma_crt_set (comma_crt_apply Comma_CRT_And
            (comma_crt_source_axis_column 0 2 r)
            (comma_crt_source_axis_column 1 3 r)) =
           comma_semantic_b1_scope_set 6 r"
        using comma_crt_source_axis_pair_set[where level_a=0 and divisor_a=2
          and level_b=1 and divisor_b=3 and period=6 and residue=r] canonical p6 modulus
        by (simp add: comma_crt_period_def)
      show ?thesis using pair p6 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def)
    next
      assume p22: "p=22"
      have modulus: "(22::nat)=lcm 2 11" by code_simp
      have pair:
          "comma_crt_set (comma_crt_apply Comma_CRT_And
            (comma_crt_source_axis_column 0 2 r)
            (comma_crt_source_axis_column 3 11 r)) =
           comma_semantic_b1_scope_set 22 r"
        using comma_crt_source_axis_pair_set[where level_a=0 and divisor_a=2
          and level_b=3 and divisor_b=11 and period=22 and residue=r] canonical p22 modulus
        by (simp add: comma_crt_period_def)
      show ?thesis using pair p22 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def)
    next
      assume p28: "p=28"
      have modulus: "(28::nat)=lcm 4 7" by code_simp
      have pair:
          "comma_crt_set (comma_crt_apply Comma_CRT_And
            (comma_crt_source_axis_column 0 4 r)
            (comma_crt_source_axis_column 2 7 r)) =
           comma_semantic_b1_scope_set 28 r"
        using comma_crt_source_axis_pair_set[where level_a=0 and divisor_a=4
          and level_b=2 and divisor_b=7 and period=28 and residue=r] canonical p28 modulus
        by (simp add: comma_crt_period_def)
      show ?thesis using pair p28 scope_eq target_scope
        by (simp add: comma_crt_source_scope_column_def)
    qed
  qed
qed

definition comma_semantic_b1_crt_source_scope_certified ::
    "comma_semantic_b1_crt_scope \<Rightarrow> bool" where
  "comma_semantic_b1_crt_source_scope_certified scope \<longleftrightarrow>
    comma_semantic_b1_crt_scope_admitted scope \<and>
    fst scope\<in>comma_semantic_b1_crt_source_periods"

lemma comma_semantic_b1_crt_source_slot_scope_certified:
  assumes admitted: "comma_round_admitted source"
    and normalized:
      "source=comma_source_continuation_base source"
    and slot: "slot<comma_decisive_sector_period source"
  shows "comma_semantic_b1_crt_source_scope_certified
      (comma_semantic_b1_source_slot_scope
        (comma_decisive_sector_period source) slot)"
proof -
  have base_eq: "comma_source_continuation_base source=source"
    by (rule sym[OF normalized])
  have slot_bound:
      "slot<comma_decisive_sector_period
        (comma_source_continuation_base source)"
    using slot by (simp only: base_eq)
  have scope_facts:
      "comma_semantic_b1_crt_scope_admitted
          (comma_semantic_b1_source_slot_scope
            (comma_decisive_sector_period
              (comma_source_continuation_base source)) slot) \<and>
       fst (comma_semantic_b1_source_slot_scope
          (comma_decisive_sector_period
            (comma_source_continuation_base source)) slot)\<in>
          comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_slot_scope_certified
      [OF admitted slot_bound])
  have source_scope_facts:
      "comma_semantic_b1_crt_scope_admitted
          (comma_semantic_b1_source_slot_scope
            (comma_decisive_sector_period source) slot) \<and>
       fst (comma_semantic_b1_source_slot_scope
          (comma_decisive_sector_period source) slot)\<in>
          comma_semantic_b1_crt_source_periods"
    using scope_facts by (simp only: base_eq)
  show ?thesis using source_scope_facts
    by (simp add: comma_semantic_b1_crt_source_scope_certified_def)
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_generated_source_period_six
    comma_semantic_b1_generated_slot_scope_certified
    comma_semantic_b1_crt_source_slot_scope_certified
    comma_crt_source_axis_column_admitted comma_crt_source_axis_column_set
    comma_crt_source_axis_pair_set
    comma_crt_source_scope_column_admitted comma_crt_source_scope_column_set};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "direct CRT source-slot scopes" checked;
\<close>

end
