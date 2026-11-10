theory Comma_Semantic_Phase_Class
  imports Comma_Phase_Class_Rank
    Comma_Decade_Orbit.Comma_Endpoint_Orbit_Interface
    Comma_Decade_Helix.Comma_Decade_Helix
begin

text \<open>
The orbit index is a source-bound control class. It is not a portable image
authority or a claim of Moore minimality. The receiving phase remains a
separate coordinate; exact physical weights belong to the application.
\<close>

definition comma_semantic_phase_class_valid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_phase_class_valid phase class \<longleftrightarrow>
    phase<924 \<and> class<46"

definition comma_semantic_phase_class_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action" where
  "comma_semantic_phase_class_step phase class =
    (if comma_semantic_phase_class_valid phase class then
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control
          (Comma_Decade phase (comma_offset_representatives!class)))
     else Comma_Phase_Class_Invalid)"

lemma comma_semantic_phase_class_source_valid:
  assumes "comma_decade_admitted (Comma_Decade phase offset)"
  shows "comma_semantic_phase_class_valid phase (comma_offset_orbit offset)"
  using assms comma_offset_orbit_bound
  by (simp add: comma_semantic_phase_class_valid_def)

lemma comma_semantic_phase_class_source_control:
  assumes admitted: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "comma_semantic_phase_class_step phase (comma_offset_orbit offset) =
    comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase offset))"
proof -
  have offset: "offset\<le>90" using admitted by simp
  have control:
    "comma_decade_control (Comma_Decade phase offset) =
      comma_decade_control
        (Comma_Decade phase (comma_offset_representatives!
          comma_offset_orbit offset))"
    using comma_decade_control_orbit_representative[OF offset]
    by (simp only: comma_offset_representative_def)
  have class_valid:
    "comma_semantic_phase_class_valid phase (comma_offset_orbit offset)"
    by (rule comma_semantic_phase_class_source_valid[OF admitted])
  have exposed:
    "comma_semantic_phase_class_step phase (comma_offset_orbit offset) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control
          (Comma_Decade phase (comma_offset_representatives!
            comma_offset_orbit offset)))"
    using class_valid
    by (simp only: comma_semantic_phase_class_step_def if_True)
  show ?thesis using exposed
    by (simp only: control[symmetric])
qed

lemma comma_semantic_phase_class_representative:
  assumes valid: "comma_semantic_phase_class_valid phase class"
  shows "comma_decade_admitted
      (Comma_Decade phase (comma_offset_representatives!class))"
    "comma_offset_orbit (comma_offset_representatives!class)=class"
proof -
  have phase_bound: "phase<924" and class_bound: "class<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have representative: "comma_offset_representatives!class\<le>90 \<and>
      comma_offset_orbit (comma_offset_representatives!class)=class"
    using comma_offset_representatives_checked class_bound
    by (simp add: list_all_iff)
  show "comma_decade_admitted
      (Comma_Decade phase (comma_offset_representatives!class))"
    using phase_bound representative by simp
  show "comma_offset_orbit (comma_offset_representatives!class)=class"
    using representative by simp
qed

lemma comma_semantic_phase_class_step_not_invalid:
  assumes valid: "comma_semantic_phase_class_valid phase class"
  shows "comma_semantic_phase_class_step phase class \<noteq>
    Comma_Phase_Class_Invalid"
proof -
  have admitted: "comma_decade_admitted
      (Comma_Decade phase (comma_offset_representatives!class))"
    by (rule comma_semantic_phase_class_representative(1)[OF valid])
  have actual: "comma_decade_control
      (Comma_Decade phase (comma_offset_representatives!class)) \<noteq>
      Comma_Decade_Invalid"
    by (rule comma_decade_control_closed(1)[OF admitted refl])
  have exposed:
    "comma_semantic_phase_class_step phase class =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control
          (Comma_Decade phase (comma_offset_representatives!class)))"
    using valid
    by (simp only: comma_semantic_phase_class_step_def if_True)
  have classified_not_invalid:
    "comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control
        (Comma_Decade phase (comma_offset_representatives!class))) \<noteq>
      Comma_Phase_Class_Invalid"
    using actual
    by (simp only: comma_phase_classify_invalid_iff not_False_eq_True)
  show ?thesis by (subst exposed; rule classified_not_invalid)
qed

lemma comma_semantic_phase_class_continue_closed:
  assumes valid: "comma_semantic_phase_class_valid phase class"
    and continued: "comma_semantic_phase_class_step phase class =
      Comma_Phase_Class_Continue next_phase next_class"
  shows "next_phase=(phase+1) mod 924"
    "comma_semantic_phase_class_valid next_phase next_class"
proof -
  let ?offset = "comma_offset_representatives!class"
  have admitted: "comma_decade_admitted (Comma_Decade phase ?offset)"
    by (rule comma_semantic_phase_class_representative(1)[OF valid])
  have exposed:
    "comma_semantic_phase_class_step phase class =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase ?offset))"
    using valid
    by (simp only: comma_semantic_phase_class_step_def if_True)
  have classified:
    "comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase ?offset)) =
      Comma_Phase_Class_Continue next_phase next_class"
    using exposed[symmetric] continued by (rule trans)
  obtain next_offset where actual:
      "comma_decade_control (Comma_Decade phase ?offset) =
        Comma_Decade_Continue (Comma_Decade next_phase next_offset)"
    and next_class_eq: "next_class=comma_offset_orbit next_offset"
    using classified
    by (simp only: comma_phase_classify_continue_iff; blast)
  have phase: "next_phase=(phase+1) mod 924"
    by (rule comma_decade_continue_helix(1)[OF admitted actual])
  have next_admitted:
    "comma_decade_admitted (Comma_Decade next_phase next_offset)"
    by (rule comma_decade_control_closed(2)[OF admitted actual refl])
  show "next_phase=(phase+1) mod 924" by (rule phase)
  show "comma_semantic_phase_class_valid next_phase next_class"
    using comma_semantic_phase_class_source_valid[OF next_admitted] next_class_eq by simp
qed

theorem comma_semantic_phase_class_future_right_congruent:
  assumes "phase<924" "left\<le>90" "right\<le>90"
    "comma_offset_orbit left=comma_offset_orbit right"
  shows "comma_decade_block_power k (Comma_Decade phase left) =
    comma_decade_block_power k (Comma_Decade phase right)"
  by (rule comma_decade_power_orbit_congruent[OF assms])

ML \<open>
  val phase_class_rules =
    @{thms comma_semantic_phase_class_source_valid
      comma_semantic_phase_class_source_control
      comma_semantic_phase_class_continue_closed
      comma_semantic_phase_class_future_right_congruent};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma Semantic Phase Class" phase_class_rules;
\<close>

end
