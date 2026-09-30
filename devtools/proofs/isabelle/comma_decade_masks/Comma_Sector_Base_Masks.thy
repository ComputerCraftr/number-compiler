theory Comma_Sector_Base_Masks
  imports Comma_Sector_Mask_Constructor Comma_Orbit_Words
begin

text \<open>Base masks are filtered from already checked sparse response rows.
The complete response is retained until its crossing admission and exact
exponent delta have been checked. No 924-phase predicate is evaluated here.\<close>

fun comma_sector_base_admitted :: "comma_round_result \<Rightarrow> bool" where
  "comma_sector_base_admitted (Comma_Round_Cross (Comma_Entry f d x)) =
    (f=1 \<and> d=1 \<and> x\<le>90)"
| "comma_sector_base_admitted (Comma_Round_Cross (Comma_Near f d h)) = False"
| "comma_sector_base_admitted (Comma_Round_Fork a d) = (d=0)"
| "comma_sector_base_admitted (Comma_Round_Landmine d) = (d=0)"
| "comma_sector_base_admitted Comma_Round_Invalid = False"

fun comma_sector_base_project :: "comma_round_result \<Rightarrow> comma_word_result" where
  "comma_sector_base_project (Comma_Round_Cross (Comma_Entry f d x)) =
    (if f=1 \<and> d=1 \<and> x\<le>90 then Comma_Word_Live (comma_offset_orbit x)
     else Comma_Word_Invalid)"
| "comma_sector_base_project (Comma_Round_Cross (Comma_Near f d h)) = Comma_Word_Invalid"
| "comma_sector_base_project (Comma_Round_Fork a d) =
    (if d=0 then Comma_Word_Stop 0 (Comma_Terminal_Fork a) else Comma_Word_Invalid)"
| "comma_sector_base_project (Comma_Round_Landmine d) =
    (if d=0 then Comma_Word_Stop 0 Comma_Terminal_Landmine else Comma_Word_Invalid)"
| "comma_sector_base_project Comma_Round_Invalid = Comma_Word_Invalid"

definition comma_sector_output_mask ::
  "(comma_round_result \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> comma_sector_rows \<Rightarrow> nat" where
  "comma_sector_output_mask project desired rows =
    comma_mask_union (map snd (filter (\<lambda>(out,bits). project out=desired) rows))"

lemma comma_sector_output_mask_member:
  "comma_phase_member (comma_sector_output_mask project desired rows) r =
    (\<exists>out bits. (out,bits)\<in>set rows \<and> project out=desired \<and> comma_phase_member bits r)"
  unfolding comma_sector_output_mask_def
  by (induction rows)
    (auto simp: comma_phase_member_or split: prod.splits)

lemma comma_sector_rows_exact_output:
  assumes rows: "comma_sector_rows_refine F (mask 924) rows"
    and phase: "r<924"
  shows "comma_phase_member (comma_sector_output_mask project desired rows) r =
    (project (F r)=desired)"
proof -
  have coverage: "\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
    using rows phase by (auto simp: comma_sector_rows_refine_def comma_phase_full_mask)
  have exact: "\<And>out bits. (out,bits)\<in>set rows \<Longrightarrow> comma_phase_member bits r \<Longrightarrow> F r=out"
    using rows unfolding comma_sector_rows_refine_def by blast
  show ?thesis using coverage exact
    by (auto simp only: comma_sector_output_mask_member; blast)
qed

lemma comma_sector_base_project_refines:
  assumes source: "r<924" "x\<le>90"
    and exact: "comma_sector_mask_value 1 x r=out"
    and admitted: "comma_sector_base_admitted out"
  shows "comma_sector_base_project out =
    comma_word_project comma_offset_orbit (comma_decade_block_atom (Comma_Decade r x))"
proof -
  have control: "comma_fast_decade_control (Comma_Decade r x)=comma_decade_decode r out"
    using exact by (simp add: comma_sector_mask_value_def comma_fast_decade_control.simps)
  have valid: "comma_decade_admitted (Comma_Decade r x)" using source by simp
  show ?thesis
    apply (simp only: comma_decade_block_atom_def valid if_True control)
    using admitted
    apply (cases out; auto)
    subgoal for target by (cases target) auto
    done
qed

lemma comma_sector_base_rows_refine:
  assumes index: "i<46" and phase: "r<924"
    and rows: "comma_sector_rows_refine
      (comma_sector_mask_value 1 (comma_offset_representatives!i)) (mask 924) rows"
    and admitted: "\<And>out bits. (out,bits)\<in>set rows \<Longrightarrow>
      comma_phase_member bits r \<Longrightarrow> comma_sector_base_admitted out"
  shows "comma_phase_member (comma_sector_output_mask comma_sector_base_project desired rows) r =
    (comma_orbit_word 0 r i=desired)"
proof -
  let ?x = "comma_offset_representatives!i"
  obtain out bits where member: "(out,bits)\<in>set rows" "comma_phase_member bits r"
    using rows phase by (auto simp: comma_sector_rows_refine_def comma_phase_full_mask)
  have exact: "comma_sector_mask_value 1 ?x r=out"
    using rows member unfolding comma_sector_rows_refine_def by blast
  have bound: "?x\<le>90" by (rule comma_orbit_representative_index(1)[OF index])
  have projected: "comma_sector_base_project out=
    comma_word_project comma_offset_orbit (comma_decade_block_atom (Comma_Decade r ?x))"
    by (rule comma_sector_base_project_refines[OF phase bound exact admitted[OF member]])
  have word: "comma_orbit_word 0 r i=comma_sector_base_project out"
    using projected phase index
    by (simp only: comma_orbit_word_def comma_decade_block_power.simps; simp)
  show ?thesis
    using comma_sector_rows_exact_output[OF rows phase,
      where project=comma_sector_base_project and desired=desired]
    by (simp only: exact word)
qed

definition comma_sector_base_live :: "(nat \<Rightarrow> comma_sector_rows) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_sector_base_live rows i j = (if i<46 then
    comma_sector_output_mask comma_sector_base_project (Comma_Word_Live j) (rows i) else 0)"

definition comma_sector_base_stop ::
  "(nat \<Rightarrow> comma_sector_rows) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat" where
  "comma_sector_base_stop rows i h terminal = (if i<46 then
    comma_sector_output_mask comma_sector_base_project (Comma_Word_Stop h terminal) (rows i) else 0)"

theorem comma_sector_base_masks_correct:
  assumes rows: "\<And>i. i<46 \<Longrightarrow> comma_sector_rows_refine
    (comma_sector_mask_value 1 (comma_offset_representatives!i)) (mask 924) (rows i)"
    and admitted: "\<And>i out bits r. i<46 \<Longrightarrow> (out,bits)\<in>set (rows i) \<Longrightarrow>
      comma_phase_member bits r \<Longrightarrow> comma_sector_base_admitted out"
  shows "comma_word_masks_correct (comma_orbit_word 0)
    (comma_sector_base_live rows) (comma_sector_base_stop rows)"
proof -
  have exact: "\<And>i r desired. i<46 \<Longrightarrow> r<924 \<Longrightarrow>
    comma_phase_member (comma_sector_output_mask comma_sector_base_project desired (rows i)) r =
      (comma_orbit_word 0 r i=desired)"
    by (rule comma_sector_base_rows_refine) (use rows admitted in auto)
  show ?thesis unfolding comma_word_masks_correct_def
    by (auto simp: comma_sector_base_live_def comma_sector_base_stop_def exact
      comma_orbit_word_def split: if_splits)
qed

text \<open>The theorem requires 46 constructor certificates and admitted
nonempty response rows. It supplies neither those concrete instances nor the
later all-stop cover or winning-cycle certificate.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_rows_exact_output comma_sector_base_project_refines
      comma_sector_base_rows_refine comma_sector_base_masks_correct})
    then () else error "Sector base masks depend on an oracle";
\<close>
end
