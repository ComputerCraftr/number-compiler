theory Comma_Run_Moore
  imports Comma_Future_Structural_Check.Comma_Future_Descent_Lift
    Comma_Run_Cycle_Data.Comma_Run_Cycle_Data
begin



text \<open>
The source-20 survivor itinerary is represented at its maximal homogeneous-run
boundary.  The auxiliary source schedule records one one-bit entry prefix,
139 complete cyclic runs, and a one-bit suffix that splits the final zero run
across the physical source boundary.  The release checker proves that entry
and all 140 runs of the anchored cycle; absolute exponent gain remains
occurrence payload.
\<close>

definition comma_nine_run_schedule :: "comma_branch_run list" where
  "comma_nine_run_schedule =
    (False,1) # take 139 comma_nine_run_cycle @ [(False,1)]"


text \<open>
For a deterministic cyclic Moore machine, a merge of two states is exactly a
non-zero cyclic shift preserving every future run output.  This finite check
therefore certifies the Moore fixed point without constructing all pairwise
state comparisons.
\<close>

definition comma_run_shift_equivalent :: "comma_branch_run list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_run_shift_equivalent runs d =
    (\<forall>k<length runs. runs ! k = runs ! ((k+d) mod length runs))"

definition comma_run_moore_fixed :: "comma_branch_run list \<Rightarrow> bool" where
  "comma_run_moore_fixed runs =
    list_all (\<lambda>d. list_ex (\<lambda>k.
      runs ! k \<noteq> runs ! ((k+d) mod length runs)) [0..<length runs])
      [1..<length runs]"


definition comma_run_moore_certificate ::
  "comma_branch_run list \<Rightarrow> nat list \<Rightarrow> bool" where
  "comma_run_moore_certificate runs witnesses =
    (length witnesses = length runs - 1 \<and>
     (\<forall>d\<in>set [1..<length runs].
       (let k=witnesses ! (d-1) in
          k<length runs \<and> runs ! k \<noteq> runs ! ((k+d) mod length runs))))"

definition comma_nine_run_moore_witnesses :: "nat list" where
  "comma_nine_run_moore_witnesses = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]"

lemma comma_run_moore_certificate_sound:
  assumes "comma_run_moore_certificate runs witnesses"
  shows "comma_run_moore_fixed runs"
  using assms
  by (auto simp: comma_run_moore_certificate_def comma_run_moore_fixed_def
    list_all_iff list_ex_iff Let_def)

lemma comma_run_moore_fixed_no_shift:
  assumes fixed: "comma_run_moore_fixed runs"
    and positive: "0 < d" and below: "d < length runs"
  shows "\<not> comma_run_shift_equivalent runs d"
proof -
  have member: "d \<in> set [1..<length runs]"
    using positive below by simp
  have all:
      "\<forall>d\<in>set [1..<length runs].
        list_ex (\<lambda>k. runs ! k \<noteq> runs ! ((k+d) mod length runs))
          [0..<length runs]"
    using fixed by (simp add: comma_run_moore_fixed_def list_all_iff)
  have row:
      "list_ex (\<lambda>k. runs ! k \<noteq> runs ! ((k+d) mod length runs))
        [0..<length runs]"
    by (rule bspec[OF all member])
  have witness: "\<exists>k<length runs.
      runs ! k \<noteq> runs ! ((k+d) mod length runs)"
    using row by (auto simp: list_ex_iff atLeastLessThan_iff)
  then show ?thesis
    by (auto simp: comma_run_shift_equivalent_def)
qed

lemma comma_nine_run_cycle_length [simp]:
  "length comma_nine_run_cycle = 140"
  unfolding comma_nine_run_cycle_def by code_simp

lemma comma_nine_run_cycle_weight [simp]:
  "sum_list (map snd comma_nine_run_cycle) = 314"
  unfolding comma_nine_run_cycle_def by code_simp

lemma comma_nine_run_schedule_length [simp]:
  "length comma_nine_run_schedule = 141"
  unfolding comma_nine_run_schedule_def comma_nine_run_cycle_def by code_simp

lemma comma_nine_run_schedule_weight [simp]:
  "sum_list (map snd comma_nine_run_schedule) = 314"
  unfolding comma_nine_run_schedule_def comma_nine_run_cycle_def by code_simp

lemma comma_nine_run_cycle_moore_certificate:
  "comma_run_moore_certificate comma_nine_run_cycle comma_nine_run_moore_witnesses"
  unfolding comma_run_moore_certificate_def comma_nine_run_cycle_def
    comma_nine_run_moore_witnesses_def
  by code_simp


theorem comma_nine_run_cycle_moore_fixed:
  "comma_run_moore_fixed comma_nine_run_cycle"
  by (rule comma_run_moore_certificate_sound
    [OF comma_nine_run_cycle_moore_certificate])

theorem comma_nine_run_cycle_moore_minimal:
  assumes "0 < d" "d < 140"
  shows "\<not> comma_run_shift_equivalent comma_nine_run_cycle d"
  by (rule comma_run_moore_fixed_no_shift[OF
      comma_nine_run_cycle_moore_fixed]) (use assms in simp_all)

text \<open>
The checked run step follows the unique unranked child and simultaneously
checks that the other child is ranked.  Thus rejected-sibling safety is part of
the same finite transition check; no losing subtree is reconstructed.
\<close>

definition comma_summary_survivor_step ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   bool \<Rightarrow> comma_boundary_state \<Rightarrow>
   (comma_boundary_state \<times> nat) option" where
  "comma_summary_survivor_step height terminal rank choice q =
    (case comma_fast_total_boundary height terminal q of
       None \<Rightarrow> None
     | Some (Comma_Landmine_At d) \<Rightarrow> None
     | Some (Comma_Fork_At a d) \<Rightarrow>
         (let phase=(snd (snd q)+d) mod 924;
              left=(Comma_N,a,phase); right=(Comma_Z,a,phase);
              selected=(if choice then right else left);
              other=(if choice then left else right)
          in if rank q=None \<and> rank selected=None \<and> rank other\<noteq>None
             then Some (selected,d) else None))"

fun comma_summary_survivor_run ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   bool \<Rightarrow> nat \<Rightarrow> comma_boundary_state \<Rightarrow>
   (comma_boundary_state \<times> nat) option" where
  "comma_summary_survivor_run height terminal rank choice 0 q =
    (if comma_boundary_valid q \<and> rank q=None then Some (q,0) else None)"
| "comma_summary_survivor_run height terminal rank choice (Suc k) q =
    (case comma_summary_survivor_step height terminal rank choice q of
       None \<Rightarrow> None
     | Some (target,d) \<Rightarrow>
         map_option (\<lambda>(final_state,rest). (final_state,d+rest))
           (comma_summary_survivor_run height terminal rank choice k target))"

definition comma_safe_choice_edge ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_safe_choice_edge rank choice q target d =
    (comma_boundary_valid q \<and> comma_macro_defined q \<and> rank q=None \<and>
     (\<exists>a. comma_total_macro q=Comma_Fork_At a d \<and>
       (let phase=(snd (snd q)+d) mod 924;
            left=(Comma_N,a,phase); right=(Comma_Z,a,phase);
            selected=(if choice then right else left);
            other=(if choice then left else right)
        in target=selected \<and> rank target=None \<and> rank other\<noteq>None)))"

inductive comma_safe_choice_path ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool"
  for rank where
  empty: "comma_boundary_valid q \<Longrightarrow> rank q=None \<Longrightarrow>
    comma_safe_choice_path rank [] 0 q q 0"
| step: "comma_safe_choice_edge rank choice q target d \<Longrightarrow>
    comma_safe_choice_path rank choices n target final_state rest \<Longrightarrow>
    comma_safe_choice_path rank (choice#choices) (Suc n) q final_state (d+rest)"

lemma comma_safe_choice_edge_member:
  assumes edge: "comma_safe_choice_edge rank choice q target d"
  shows "target \<in> set (comma_total_children q)"
  using edge
  by (auto simp: comma_safe_choice_edge_def comma_total_children_def Let_def
    split: if_splits)

lemma comma_safe_choice_edge_target_live:
  assumes "comma_safe_choice_edge rank choice q target d"
  shows "rank target=None"
  using assms by (auto simp: comma_safe_choice_edge_def Let_def split: if_splits)

lemma comma_safe_choice_path_append:
  assumes first: "comma_safe_choice_path rank choices n q middle delta"
    and second: "comma_safe_choice_path rank choices' m middle final_state delta'"
  shows "comma_safe_choice_path rank (choices@choices') (n+m) q final_state
    (delta+delta')"
  using first second
  by (induction rule: comma_safe_choice_path.induct)
    (auto intro: comma_safe_choice_path.intros simp: add.assoc)


lemma comma_safe_choice_path_is_surviving_delta_path:
  assumes "comma_safe_choice_path rank choices n q final_state delta"
  shows "comma_surviving_delta_path rank n q final_state delta"
  using assms
proof (induction rule: comma_safe_choice_path.induct)
  case (empty q)
  show ?case by (rule comma_surviving_delta_path.empty)
next
  case (step choice q target d choices n final_state rest)
  obtain a where macro: "comma_total_macro q=Comma_Fork_At a d"
    and defined: "comma_macro_defined q"
    using step.hyps(1)
    by (auto simp: comma_safe_choice_edge_def Let_def)
  have member: "target \<in> set (comma_total_children q)"
    by (rule comma_safe_choice_edge_member[OF step.hyps(1)])
  have live: "rank target=None"
    by (rule comma_safe_choice_edge_target_live[OF step.hyps(1)])
  show ?case
    by (rule comma_surviving_delta_path.step
      [OF defined macro member live step.IH])
qed


lemma comma_summary_survivor_step_sound:
  assumes summary: "comma_decade_summary_checked height terminal"
    and computed: "comma_summary_survivor_step height terminal rank choice q =
      Some (target,d)"
  shows "comma_safe_choice_edge rank choice q target d"
proof -
  obtain a e where fast_result:
      "comma_fast_total_boundary height terminal q=Some (Comma_Fork_At a e)"
    using computed
    by (cases "comma_fast_total_boundary height terminal q";
      auto simp: comma_summary_survivor_step_def
        split: comma_finite_outcome.splits if_splits)
  let ?phase="(snd (snd q)+e) mod 924"
  let ?selected="if choice then (Comma_Z,a,?phase) else (Comma_N,a,?phase)"
  let ?other="if choice then (Comma_N,a,?phase) else (Comma_Z,a,?phase)"
  have branch:
      "(if rank q=None \<and> rank ?selected=None \<and> rank ?other\<noteq>None
        then Some (?selected,e) else None)=Some (target,d)"
    using computed
    by (simp only: comma_summary_survivor_step_def fast_result
      option.case comma_finite_outcome.case Let_def)
  have guard: "rank q=None \<and> rank ?selected=None \<and> rank ?other\<noteq>None"
    and binding: "?selected=target" "e=d"
    using branch by (auto split: if_splits)
  have fast: "comma_fast_total_boundary height terminal q=Some (Comma_Fork_At a d)"
    using fast_result binding(2) by simp
  have current_live: "rank q=None" and target_live: "rank target=None"
    using guard binding(1) by auto
  have selected: "target=(if choice then
        (Comma_Z,a,(snd (snd q)+d) mod 924)
      else (Comma_N,a,(snd (snd q)+d) mod 924))"
    using binding by (cases choice) auto
  have other_losing: "rank (if choice then
        (Comma_N,a,(snd (snd q)+d) mod 924)
      else (Comma_Z,a,(snd (snd q)+d) mod 924)) \<noteq> None"
    using guard binding(2) by (cases choice) auto
  have valid: "comma_boundary_valid q"
    using fast by (auto simp: comma_fast_total_boundary_def split: if_splits)
  obtain fuel result where refined:
      "comma_fast_total_boundary height terminal q=Some result"
      "comma_finite_macro fuel q=Some result"
    using comma_fast_total_boundary_refines[OF summary valid] by blast
  have defined: "comma_macro_defined q"
    using refined(2) by (auto simp: comma_macro_defined_def)
  have total: "comma_total_macro q=Comma_Fork_At a d"
    using comma_fast_total_boundary_correct[OF summary valid] fast by simp
  show ?thesis
    using valid defined current_live target_live selected other_losing total
    by (auto simp: comma_safe_choice_edge_def Let_def split: if_splits)
qed


lemma comma_summary_survivor_run_sound:
  assumes summary: "comma_decade_summary_checked height terminal"
    and computed: "comma_summary_survivor_run height terminal rank choice k q =
      Some (target,delta)"
  shows "comma_safe_choice_path rank (replicate k choice) k q target delta"
  using computed
proof (induction k arbitrary: q target delta)
  case 0
  then show ?case
    by (auto intro: comma_safe_choice_path.empty split: if_splits)
next
  case (Suc k)
  obtain middle d rest where edge:
      "comma_summary_survivor_step height terminal rank choice q=Some (middle,d)"
    and tail:
      "comma_summary_survivor_run height terminal rank choice k middle=
        Some (target,rest)"
    and delta: "delta=d+rest"
    using Suc.prems by (auto split: option.splits prod.splits)
  have safe_edge: "comma_safe_choice_edge rank choice q middle d"
    by (rule comma_summary_survivor_step_sound[OF summary edge])
  have safe_tail:
      "comma_safe_choice_path rank (replicate k choice) k middle target rest"
    by (rule Suc.IH[OF tail])
  have joined:
      "comma_safe_choice_path rank (choice#replicate k choice) (Suc k)
        q target (d+rest)"
    by (rule comma_safe_choice_path.step[OF safe_edge safe_tail])
  show ?case using joined delta by simp
qed



text \<open>
The release proof is built in maximal homogeneous runs.  A run certificate is
one already-proved homogeneous safe-choice action, so the concrete source-20
cycle constructs 140 proof steps rather than 314 edge proofs.  The run relation
retains the run word as an observable: run length is part of the temporal
output, not occurrence syntax that may be discarded.
\<close>

inductive comma_safe_run_path ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> comma_branch_run list \<Rightarrow> nat \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool"
  for rank where
  empty: "comma_boundary_valid q \<Longrightarrow> rank q=None \<Longrightarrow>
    comma_safe_run_path rank [] 0 q q 0"
| step: "0<k \<Longrightarrow>
    comma_safe_choice_path rank (replicate k choice) k q middle delta \<Longrightarrow>
    comma_safe_run_path rank runs n middle final_state rest \<Longrightarrow>
    comma_safe_run_path rank ((choice,k)#runs) (k+n) q final_state (delta+rest)"

lemma comma_safe_run_path_is_surviving_delta_path:
  assumes "comma_safe_run_path rank runs n q final_state delta"
  shows "comma_surviving_delta_path rank n q final_state delta"
  using assms
proof (induction rule: comma_safe_run_path.induct)
  case (empty q)
  show ?case by (rule comma_surviving_delta_path.empty)
next
  case (step k choice q middle delta runs n final_state rest)
  have first: "comma_surviving_delta_path rank k q middle delta"
    by (rule comma_safe_choice_path_is_surviving_delta_path[OF step.hyps(2)])
  have joined: "comma_surviving_delta_path rank (k+n) q final_state (delta+rest)"
    by (rule comma_surviving_delta_path_append[OF first step.IH])
  then show ?case .
qed


lemma comma_safe_choice_edge_other_ranked:
  assumes edge: "comma_safe_choice_edge rank choice q target d"
  obtains a other where
    "comma_total_macro q=Comma_Fork_At a d"
    "other=(if choice then (Comma_N,a,(snd (snd q)+d) mod 924)
      else (Comma_Z,a,(snd (snd q)+d) mod 924))"
    "rank other \<noteq> None"
  using edge
  by (auto simp: comma_safe_choice_edge_def Let_def split: if_splits)

text \<open>
Here “cyclic Moore observer” means the finite observer whose positions are
offsets into the run list, whose transition advances one position modulo the
list length, and whose output is the complete run action (choice, length).
For this observer, equal future output streams imply an output-preserving
rotation of the list.  The theorem below rules out every nonzero rotation, so
its 140 positions have distinct future outputs in this explicit cyclic model.
It does not construct or minimize a production automaton or a quotient that
projects away the run length.
\<close>

definition comma_cyclic_run_moore_minimal :: "comma_branch_run list \<Rightarrow> bool" where
  "comma_cyclic_run_moore_minimal runs =
    (runs \<noteq> [] \<and> (\<forall>d\<in>set [1..<length runs].
      \<not> comma_run_shift_equivalent runs d))"

lemma comma_run_moore_fixed_iff_cyclic_minimal:
  assumes "runs \<noteq> []"
  shows "comma_run_moore_fixed runs = comma_cyclic_run_moore_minimal runs"
  using assms
  by (auto simp: comma_run_moore_fixed_def comma_cyclic_run_moore_minimal_def
    comma_run_shift_equivalent_def list_all_iff list_ex_iff
    Ball_def Bex_def atLeastLessThan_iff)

theorem comma_nine_run_cycle_cyclic_moore_minimal:
  "comma_cyclic_run_moore_minimal comma_nine_run_cycle"
proof -
  have nonempty: "comma_nine_run_cycle \<noteq> []"
    by (simp add: comma_nine_run_cycle_def)
  have equivalent:
      "comma_run_moore_fixed comma_nine_run_cycle =
       comma_cyclic_run_moore_minimal comma_nine_run_cycle"
    by (rule comma_run_moore_fixed_iff_cyclic_minimal[OF nonempty])
  show ?thesis using equivalent comma_nine_run_cycle_moore_fixed by blast
qed

theorem comma_nine_run_cycle_has_140_moore_states:
  "length comma_nine_run_cycle = 140 \<and>
   comma_cyclic_run_moore_minimal comma_nine_run_cycle"
  using comma_nine_run_cycle_cyclic_moore_minimal by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_nine_run_cycle_moore_certificate
      comma_nine_run_cycle_moore_fixed
      comma_nine_run_cycle_moore_minimal
      comma_nine_run_cycle_cyclic_moore_minimal
      comma_nine_run_cycle_has_140_moore_states
      comma_summary_survivor_step_sound comma_summary_survivor_run_sound
      comma_safe_choice_path_is_surviving_delta_path
      comma_safe_run_path_is_surviving_delta_path
      comma_safe_choice_edge_other_ranked})
    then () else error "Comma run-Moore layer depends on an oracle";
\<close>

end
