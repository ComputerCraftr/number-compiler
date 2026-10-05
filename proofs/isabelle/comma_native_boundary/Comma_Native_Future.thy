theory Comma_Native_Future
  imports Comma_Native_Boundary.Comma_Native_Boundary
begin

text \<open>A concrete infinite witness is built from complete native boundary
actions. A selected edge is admitted only when the native action is a fork,
the selected child is unranked, and the sibling has a positive rank measure.
This keeps the finite measure as a checked witness and the B32 action as the
only source of child semantics.\<close>

definition comma_native_survivor_step ::
  "(comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool \<Rightarrow>
   comma_boundary_state \<Rightarrow> (comma_boundary_state \<times> nat) option" where
  "comma_native_survivor_step step rank choice q =
    (case step q of
       Some (Comma_Fork_At a d) \<Rightarrow>
         (let phase=(snd (snd q)+d) mod 924;
              left=(Comma_N,a,phase); right=(Comma_Z,a,phase);
              selected=(if choice then right else left);
              other=(if choice then left else right)
          in if comma_boundary_valid q \<and> rank q=None \<and>
                rank selected=None \<and> rank other\<noteq>None
             then Some (selected,d) else None)
     | _ \<Rightarrow> None)"

definition comma_native_survivor_edge ::
  "(comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_native_survivor_edge step rank choice q target d =
    (case step q of
       Some (Comma_Fork_At a e) \<Rightarrow>
         (let phase=(snd (snd q)+e) mod 924;
              left=(Comma_N,a,phase); right=(Comma_Z,a,phase);
              selected=(if choice then right else left);
              other=(if choice then left else right)
          in comma_boundary_valid q \<and> rank q=None \<and> e=d \<and>
              target=selected \<and> rank selected=None \<and> rank other\<noteq>None)
     | _ \<Rightarrow> False)"

lemma comma_native_survivor_step_sound:
  assumes result: "comma_native_survivor_step step rank choice q=Some (target,d)"
  shows "comma_native_survivor_edge step rank choice q target d"
  using result by (auto simp: comma_native_survivor_step_def
    comma_native_survivor_edge_def Let_def split: option.splits comma_finite_outcome.splits
      if_splits)

lemma comma_native_survivor_edge_member:
  assumes edge: "comma_native_survivor_edge step rank choice q target d"
    and result: "step q=Some (Comma_Fork_At a d)"
  shows "target\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
proof -
  obtain kind source_phase phase where q:
    "q=(kind,source_phase,phase)" by (cases q) auto
  show ?thesis
    using edge result q
    by (auto simp: comma_native_survivor_edge_def
        comma_native_boundary_children_def Let_def
        split: option.splits comma_finite_outcome.splits if_splits)
qed

fun comma_native_safe_run_execute ::
  "(comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow>
   comma_boundary_state \<Rightarrow> (comma_boundary_state \<times> nat) option" where
  "comma_native_safe_run_execute step rank choice 0 q =
    (if comma_boundary_valid q \<and> rank q=None then Some (q,0) else None)"
| "comma_native_safe_run_execute step rank choice (Suc n) q =
    (case comma_native_survivor_step step rank choice q of
       None \<Rightarrow> None
     | Some (target,d) \<Rightarrow>
         map_option (\<lambda>(final_state,rest). (final_state,d+rest))
           (comma_native_safe_run_execute step rank choice n target))"

fun comma_native_safe_runs_execute ::
  "(comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   (bool \<times> nat) list \<Rightarrow> comma_boundary_state \<Rightarrow>
   (comma_boundary_state \<times> nat) option" where
  "comma_native_safe_runs_execute step rank [] q =
    (if comma_boundary_valid q \<and> rank q=None then Some (q,0) else None)"
| "comma_native_safe_runs_execute step rank ((choice,run_length)#runs) q =
    (case comma_native_safe_run_execute step rank choice run_length q of
       None \<Rightarrow> None
     | Some (middle,d) \<Rightarrow>
         map_option (\<lambda>(final_state,rest). (final_state,d+rest))
           (comma_native_safe_runs_execute step rank runs middle))"

ML \<open>Comma_Native_Boundary_Profile.checkpoint "native-safe-run-execution"\<close>

lemma comma_native_survivor_step_literal:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and edge: "comma_native_survivor_step (comma_native_boundary_step rows)
      rank choice q=Some (target,d)"
  shows "\<exists>weight. comma_literal_path (Suc weight)
      (comma_boundary_value q p) (comma_boundary_value target (p+d)) \<and>
    comma_boundary_valid target \<and> (p+d) mod 924=snd (snd target)"
proof -
  have selected:
    "comma_native_survivor_edge (comma_native_boundary_step rows) rank
      choice q target d"
    by (rule comma_native_survivor_step_sound[OF edge])
  obtain a where action:
    "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
    using edge by (auto simp: comma_native_survivor_step_def
      Let_def split: option.splits comma_finite_outcome.splits if_splits)
  have member:
    "target\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
    by (rule comma_native_survivor_edge_member[OF selected action])
  obtain outcome where step_result:
      "comma_native_boundary_step rows q=Some outcome"
    and valid_children:
      "\<forall>child\<in>set (comma_native_boundary_children q outcome).
        comma_boundary_valid child \<and>
        (p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    using comma_native_boundary_step_children_valid_phase
      [OF powers stops valid exponent phase] .
  have same: "outcome=Comma_Fork_At a d"
    using action step_result by simp
  have child_valid:
    "comma_boundary_valid target \<and> (p+d) mod 924=snd (snd target)"
    using valid_children member same by (simp add: comma_native_outcome_delta_def)
  obtain found_outcome endpoint weight where found_step:
      "comma_native_boundary_step rows q=Some found_outcome"
    and found_children:
      "comma_native_boundary_children q found_outcome =
        (case found_outcome of Comma_Landmine_At d \<Rightarrow> []
         | Comma_Fork_At a d \<Rightarrow>
            [(Comma_N,a,(snd (snd q)+d) mod 924),
             (Comma_Z,a,(snd (snd q)+d) mod 924)])"
    and unique_found:
      "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    and child_relation_found: "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q found_outcome).
        v=comma_boundary_value child
          (p+comma_native_outcome_delta found_outcome))"
  proof (rule comma_sparse_boundary_ordered_occurrence_step
      [OF powers stops valid exponent phase])
    fix actual_outcome actual_endpoint actual_weight
    assume actual_step:
        "comma_native_boundary_step rows q=Some actual_outcome"
      and actual_children:
        "comma_native_boundary_children q actual_outcome =
          (case actual_outcome of Comma_Landmine_At d \<Rightarrow> []
           | Comma_Fork_At a d \<Rightarrow>
              [(Comma_N,a,(snd (snd q)+d) mod 924),
               (Comma_Z,a,(snd (snd q)+d) mod 924)])"
      and actual_unique:
        "comma_unique_literal_path actual_weight
          (comma_boundary_value q p) actual_endpoint"
      and actual_relation: "\<And>v. comma_child actual_endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (comma_native_boundary_children q actual_outcome).
          v=comma_boundary_value child
            (p+comma_native_outcome_delta actual_outcome))"
    show thesis by (rule that[OF actual_step actual_children actual_unique
      actual_relation])
  qed
  have found_same: "found_outcome=outcome"
    using found_step step_result by simp
  have occurrence: "comma_native_boundary_step rows q=Some outcome"
    by fact
  have unique: "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    using unique_found .
  have child_relation: "\<And>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (comma_native_boundary_children q outcome).
        v=comma_boundary_value child (p+comma_native_outcome_delta outcome))"
    using child_relation_found found_same by simp
  have literal:
    "comma_literal_path weight (comma_boundary_value q p) endpoint"
    by (rule comma_unique_literal_path_literal[OF unique])
  have child_value:
    "comma_boundary_value target (p+d)=
      comma_boundary_value target (p+comma_native_outcome_delta outcome)"
    using same by (simp add: comma_native_outcome_delta_def)
  have child_edge: "comma_child endpoint (comma_boundary_value target (p+d))"
  proof -
    have member_outcome:
      "target\<in>set (comma_native_boundary_children q outcome)"
      using member same by simp
    have child_witness:
      "\<exists>child\<in>set (comma_native_boundary_children q outcome).
        comma_boundary_value target (p+d)=
          comma_boundary_value child (p+comma_native_outcome_delta outcome)"
      using member_outcome child_value by blast
    show ?thesis
      using child_relation[of "comma_boundary_value target (p+d)"] child_witness
      by blast
  qed
  have path:
    "comma_literal_path (Suc weight) (comma_boundary_value q p)
      (comma_boundary_value target (p+d))"
    by (rule comma_literal_path_snoc[OF literal child_edge])
  show ?thesis using path child_valid by blast
qed

lemma comma_native_safe_run_execute_literal:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and result: "comma_native_safe_run_execute (comma_native_boundary_step rows)
      rank choice run_length q=Some (target,delta)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "\<exists>weight. comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value target (p+delta)) \<and>
    comma_boundary_valid target \<and> (p+delta) mod 924=snd (snd target)"
  using powers stops result valid exponent phase
  proof (induction run_length arbitrary: q target delta p
      rule: nat.induct[case_names zero successor])
  case zero
  have result_shape: "target=q \<and> delta=0"
    using zero.prems(3) by (simp add: comma_native_safe_run_execute.simps split: if_splits)
  show ?case using result_shape zero.prems(4,6)
    by (auto intro!: exI[of _ 0] intro: comma_literal_path.zero)
next
  case (successor run_length)
  obtain middle d rest where edge:
      "comma_native_survivor_step (comma_native_boundary_step rows) rank choice q=
        Some (middle,d)"
    and tail:
      "comma_native_safe_run_execute (comma_native_boundary_step rows)
        rank choice run_length middle=Some (target,rest)"
    and delta: "delta=d+rest"
    using successor.prems(3) by (auto simp: comma_native_safe_run_execute.simps
      split: option.splits prod.splits)
  have head:
    "\<exists>weight. comma_literal_path (Suc weight) (comma_boundary_value q p)
        (comma_boundary_value middle (p+d)) \<and>
      comma_boundary_valid middle \<and> (p+d) mod 924=snd (snd middle)"
    by (rule comma_native_survivor_step_literal
      [OF successor.prems(1,2,4,5,6) edge])
  then obtain head_weight where prefix:
      "comma_literal_path (Suc head_weight) (comma_boundary_value q p)
        (comma_boundary_value middle (p+d))"
    and middle_valid: "comma_boundary_valid middle"
    and middle_phase: "(p+d) mod 924=snd (snd middle)"
    by blast
  have next_exponent: "5\<le>p+d" using successor.prems(5) by simp
  have suffix:
    "\<exists>tail_weight. comma_literal_path tail_weight
        (comma_boundary_value middle (p+d))
        (comma_boundary_value target (p+d+rest)) \<and>
      comma_boundary_valid target \<and>
      (p+d+rest) mod 924=snd (snd target)"
    by (rule successor.IH[OF successor.prems(1,2) tail middle_valid
      next_exponent middle_phase])
  then obtain tail_weight where tail_path:
      "comma_literal_path tail_weight (comma_boundary_value middle (p+d))
        (comma_boundary_value target (p+d+rest))"
    and target_valid: "comma_boundary_valid target"
    and target_phase: "(p+d+rest) mod 924=snd (snd target)"
    by blast
  have joined:
    "comma_literal_path (Suc head_weight+tail_weight) (comma_boundary_value q p)
      (comma_boundary_value target (p+(d+rest)))"
    using comma_literal_path_append[OF prefix tail_path] by (simp add: add.assoc)
  show ?case
  proof (intro exI[of _ "Suc head_weight+tail_weight"] conjI)
    show "comma_literal_path (Suc head_weight+tail_weight)
        (comma_boundary_value q p) (comma_boundary_value target (p+delta))"
      using joined delta by simp
    show "comma_boundary_valid target" by fact
    show "(p+delta) mod 924=snd (snd target)"
      using target_phase delta by (simp add: add.assoc)
  qed
qed

lemma comma_native_safe_runs_execute_literal:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and result: "comma_native_safe_runs_execute (comma_native_boundary_step rows)
      rank runs q=Some (target,delta)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "\<exists>weight. comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value target (p+delta)) \<and>
    comma_boundary_valid target \<and> (p+delta) mod 924=snd (snd target)"
  using powers stops result valid exponent phase
proof (induction runs arbitrary: q target delta p)
  case Nil
  have result_shape: "target=q \<and> delta=0"
    using Nil.prems(3) by (simp add: comma_native_safe_runs_execute.simps split: if_splits)
  show ?case using result_shape Nil.prems(4,6)
    by (auto intro!: exI[of _ 0] intro: comma_literal_path.zero)
next
  case (Cons item runs)
  obtain choice run_length where item: "item=(choice,run_length)" by (cases item) auto
  obtain middle d rest where head:
      "comma_native_safe_run_execute (comma_native_boundary_step rows)
        rank choice run_length q=Some (middle,d)"
    and tail:
      "comma_native_safe_runs_execute (comma_native_boundary_step rows)
        rank runs middle=Some (target,rest)"
    and delta: "delta=d+rest"
    using Cons.prems(3) item by (auto simp: comma_native_safe_runs_execute.simps
      split: option.splits prod.splits)
  have prefix:
    "\<exists>head_weight. comma_literal_path head_weight (comma_boundary_value q p)
        (comma_boundary_value middle (p+d)) \<and>
      comma_boundary_valid middle \<and> (p+d) mod 924=snd (snd middle)"
    by (rule comma_native_safe_run_execute_literal
      [OF Cons.prems(1,2) head Cons.prems(4,5,6)])
  then obtain head_weight where head_path:
      "comma_literal_path head_weight (comma_boundary_value q p)
        (comma_boundary_value middle (p+d))"
    and middle_valid: "comma_boundary_valid middle"
    and middle_phase: "(p+d) mod 924=snd (snd middle)"
    by blast
  have next_exponent: "5\<le>p+d" using Cons.prems(5) by simp
  have suffix:
    "\<exists>tail_weight. comma_literal_path tail_weight
        (comma_boundary_value middle (p+d))
        (comma_boundary_value target (p+d+rest)) \<and>
      comma_boundary_valid target \<and>
      (p+d+rest) mod 924=snd (snd target)"
    by (rule Cons.IH[OF Cons.prems(1,2) tail middle_valid
      next_exponent middle_phase])
  then obtain tail_weight where tail_path:
      "comma_literal_path tail_weight (comma_boundary_value middle (p+d))
        (comma_boundary_value target (p+d+rest))"
    and target_valid: "comma_boundary_valid target"
    and target_phase: "(p+d+rest) mod 924=snd (snd target)"
    by blast
  have joined:
    "comma_literal_path (head_weight+tail_weight) (comma_boundary_value q p)
      (comma_boundary_value target (p+(d+rest)))"
    using comma_literal_path_append[OF head_path tail_path] by (simp add: add.assoc)
  show ?case
  proof (intro exI[of _ "head_weight+tail_weight"] conjI)
    show "comma_literal_path (head_weight+tail_weight)
        (comma_boundary_value q p) (comma_boundary_value target (p+delta))"
      using joined delta by simp
    show "comma_boundary_valid target" by fact
    show "(p+delta) mod 924=snd (snd target)"
      using target_phase delta by (simp add: add.assoc)
  qed
qed

text \<open>A strict natural-valued descent certificate is consumed only after
the native action has produced its complete ordered child set. The proof
projects an arbitrary infinite literal path to that same selected child,
transports its exponent/phase, and applies well-founded induction to the
actual successor state; a finite rank table is not itself an execution rule.\<close>

text \<open>The following executable predicate is a concrete checker interface,
not a rank authority: its provider is the completed native boundary action,
and the rank argument is only a candidate well-founded measure. A checked
instance must evaluate this predicate over the complete valid state space.\<close>

definition comma_native_rank_row_checked ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> bool" where
  "comma_native_rank_row_checked rank step q =
    (case step q of
       None \<Rightarrow> False
     | Some (Comma_Landmine_At d) \<Rightarrow> rank q \<noteq> None
     | Some (Comma_Fork_At a d) \<Rightarrow>
         (case rank q of
            None \<Rightarrow> length (filter (\<lambda>child. rank child=None)
              (comma_native_boundary_children q (Comma_Fork_At a d)))=1
          | Some k \<Rightarrow> list_all (\<lambda>child. \<exists>j<k. rank child=Some j)
              (comma_native_boundary_children q (Comma_Fork_At a d))))"

definition comma_native_rank_check ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> comma_finite_outcome option) \<Rightarrow> bool" where
  "comma_native_rank_check rank step =
    list_all (comma_native_rank_row_checked rank step) comma_boundary_states"

lemma comma_native_rank_check_row:
  assumes checked: "comma_native_rank_check rank step"
    and valid: "comma_boundary_valid q"
  shows "comma_native_rank_row_checked rank step q"
proof -
  have member: "q \<in> set comma_boundary_states"
    using valid by (simp add: comma_boundary_states_set)
  show ?thesis
    using checked member by (simp add: comma_native_rank_check_def list_all_iff)
qed

lemma comma_native_rank_check_fork_decreases:
  assumes checked: "comma_native_rank_check rank step"
    and valid: "comma_boundary_valid q"
    and ranked: "rank q=Some k"
    and fork: "step q=Some (Comma_Fork_At a d)"
  shows "\<forall>child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
    \<exists>j<k. rank child=Some j"
  using comma_native_rank_check_row[OF checked valid] ranked fork
  by (auto simp: comma_native_rank_row_checked_def list_all_iff
      split: option.splits comma_finite_outcome.splits)

lemma comma_native_rank_check_unranked_fork_unique:
  assumes checked: "comma_native_rank_check rank step"
    and valid: "comma_boundary_valid q"
    and unranked: "rank q=None"
    and fork: "step q=Some (Comma_Fork_At a d)"
  shows "\<exists>!child. child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))
    \<and> rank child=None"
proof -
  obtain kind a0 r where q: "q=(kind,a0,r)" by (cases q) auto
  let ?left = "(Comma_N,a,(r+d) mod 924)"
  let ?right = "(Comma_Z,a,(r+d) mod 924)"
  have count: "length (filter (\<lambda>child. rank child=None) [?left,?right])=1"
    using comma_native_rank_check_row[OF checked valid] unranked fork
    by (simp add: comma_native_rank_row_checked_def comma_native_boundary_children_def q)
  have distinct: "?left \<noteq> ?right" by simp
  have different: "(rank ?left=None) \<noteq> (rank ?right=None)"
    using count by (cases "rank ?left=None"; cases "rank ?right=None") simp_all
  show ?thesis using different distinct
    by (auto simp: comma_native_boundary_children_def q)
qed

lemma comma_native_rank_check_unranked_landmine_false:
  assumes checked: "comma_native_rank_check rank step"
    and valid: "comma_boundary_valid q"
    and unranked: "rank q=None"
  shows "step q \<noteq> Some (Comma_Landmine_At d)"
  using comma_native_rank_check_row[OF checked valid] unranked
  by (auto simp: comma_native_rank_row_checked_def
      split: option.splits comma_finite_outcome.splits)

lemma comma_native_ranked_path_has_smaller_child:
  fixes rank :: "comma_boundary_state \<Rightarrow> nat option"
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and descend: "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd source) \<Longrightarrow>
      rank source=Some k \<Longrightarrow>
      comma_native_boundary_step rows source=Some (Comma_Fork_At a d) \<Longrightarrow>
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow>
      (\<exists>j<k. rank child=Some j)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and ranked: "rank q=Some k"
    and path: "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  obtains child j p' tail where
    "j<k"
    "rank child=Some j"
    "comma_boundary_valid child"
    "5\<le>p'"
    "p' mod 924=snd (snd child)"
    "comma_native_infinite_literal_path (comma_boundary_value child p') tail"
proof -
  obtain outcome endpoint w child where step:
    "comma_native_boundary_step rows q=Some outcome"
    and member: "child\<in>set (comma_native_boundary_children q outcome)"
    and tail: "comma_native_infinite_literal_path
      (comma_boundary_value child (p+comma_native_outcome_delta outcome))
      (\<lambda>j. stream (w+Suc j))"
    and child_valid: "comma_boundary_valid child"
    and child_phase:
      "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    using comma_native_infinite_path_projects_admitted_child
      [OF powers stops valid exponent phase path] by blast
  show thesis
  proof (cases outcome)
    case (Comma_Landmine_At d)
    then show thesis using member
      by (simp add: comma_native_boundary_children_def)
  next
    case (Comma_Fork_At a d)
    have fork_step:
      "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
      using step Comma_Fork_At by simp
    obtain j where j_less: "j<k" and child_rank: "rank child=Some j"
      using descend[OF valid exponent phase ranked fork_step] member Comma_Fork_At
      by blast
    have next_exponent: "5\<le>p+comma_native_outcome_delta outcome"
      using exponent by (cases outcome) simp_all
    show thesis
      by (rule that[OF j_less child_rank child_valid next_exponent child_phase tail])
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "ranked-path-has-smaller-child"\<close>

definition comma_native_rank_decrease_relation ::
  "('a \<Rightarrow> nat option) \<Rightarrow> ('a \<times> 'a) set" where
  "comma_native_rank_decrease_relation rank =
    {(child,source). \<exists>j k. rank child=Some j \<and>
      rank source=Some k \<and> j<k}"

lemma comma_native_rank_decrease_relation_wf:
  "wf (comma_native_rank_decrease_relation rank)"
proof -
  let ?rank_value = "\<lambda>q. case rank q of None \<Rightarrow> 0 | Some n \<Rightarrow> n"
  have measure_wf:
    "wf (inv_image {(m,n::nat). m<n} ?rank_value)"
    by (rule wf_inv_image[OF wf_less])
  have relation_subset:
    "comma_native_rank_decrease_relation rank \<subseteq>
      inv_image {(m,n::nat). m<n} ?rank_value"
    unfolding comma_native_rank_decrease_relation_def inv_image_def
    by auto
  show ?thesis by (rule wf_subset[OF measure_wf relation_subset])
qed

theorem comma_native_ranked_state_no_infinite_path:
  fixes rank :: "comma_boundary_state \<Rightarrow> nat option"
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and descend: "\<And>source exponent k a d child.
      comma_boundary_valid source \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd source) \<Longrightarrow>
      rank source=Some k \<Longrightarrow>
      comma_native_boundary_step rows source=Some (Comma_Fork_At a d) \<Longrightarrow>
      child\<in>set (comma_native_boundary_children source (Comma_Fork_At a d)) \<Longrightarrow>
      (\<exists>j<k. rank child=Some j)"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and ranked: "rank q=Some k"
shows "\<not>comma_native_infinite_literal_path (comma_boundary_value q p) stream"
proof
  assume infinite:
    "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  let ?Q = "{source. \<exists>e trace k. comma_boundary_valid source \<and>
    5\<le>e \<and> e mod 924=snd (snd source) \<and> rank source=Some k \<and>
    comma_native_infinite_literal_path (comma_boundary_value source e) trace}"
  have q_in_Q: "q\<in>?Q"
    using valid exponent phase ranked infinite by blast
  have Q_closed_predecessor:
    "?Q \<subseteq> comma_native_rank_decrease_relation rank `` ?Q"
  proof
    fix source
    assume source_in_Q: "source\<in>?Q"
    then obtain e trace k where source_valid: "comma_boundary_valid source"
      and e_bound: "5\<le>e"
      and phase_e: "e mod 924=snd (snd source)"
      and source_rank: "rank source=Some k"
      and infinite:
        "comma_native_infinite_literal_path (comma_boundary_value source e) trace"
      by blast
    obtain child j child_exponent tail where j_less: "j<k"
      and child_rank: "rank child=Some j"
      and child_valid: "comma_boundary_valid child"
      and child_bound: "5\<le>child_exponent"
      and child_phase: "child_exponent mod 924=snd (snd child)"
      and tail: "comma_native_infinite_literal_path
        (comma_boundary_value child child_exponent) tail"
      by (rule comma_native_ranked_path_has_smaller_child
        [where rows=rows and rank=rank and q=source and p=e and k=k and stream=trace,
          OF powers stops _ source_valid e_bound phase_e source_rank infinite])
        (blast intro: descend, assumption)
    have child_in_Q: "child\<in>?Q"
      using child_valid child_bound child_phase child_rank tail by blast
    have lower_state:
      "(child,source)\<in>comma_native_rank_decrease_relation rank"
      using child_rank source_rank j_less
      by (auto simp: comma_native_rank_decrease_relation_def)
    show "source\<in>comma_native_rank_decrease_relation rank `` ?Q"
      using child_in_Q lower_state by blast
  qed
  have Q_empty: "?Q = {}"
    by (rule wfE_pf[OF comma_native_rank_decrease_relation_wf
      Q_closed_predecessor])
  have empty_member: "q\<in>({}::comma_boundary_state set)"
    using Q_empty q_in_Q by blast
  then show False by simp
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint "ranked-state-no-infinite-path"\<close>

text \<open>Every fork on an arbitrary infinite native path follows the unique
unranked child certified by the checked boundary relation. The result binds
the actual occurrence selected by the literal path, transports its exponent
and phase, and proves every alternative child ranked. This is the future-step
bridge used to iterate safety; a finite run witness alone would not establish
it.\<close>

theorem comma_native_infinite_path_forces_unique_unranked_child:
  assumes powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (rows i)"
    and stops: "\<forall>i<46. \<forall>out bits. (out,bits)\<in>set (rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    and checked: "comma_native_rank_check rank (comma_native_boundary_step rows)"
    and ranked_no_path: "\<And>state exponent k trace.
      comma_boundary_valid state \<Longrightarrow>
      5\<le>exponent \<Longrightarrow>
      exponent mod 924=snd (snd state) \<Longrightarrow>
      rank state=Some k \<Longrightarrow>
      \<not>comma_native_infinite_literal_path
        (comma_boundary_value state exponent) trace"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "comma_native_infinite_literal_path (comma_boundary_value q p) stream"
  obtains a d endpoint weight child tail where
    "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
    "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
    "stream (Suc weight)=comma_boundary_value child (p+d)"
    "comma_boundary_valid child"
    "5\<le>p+d"
    "(p+d) mod 924=snd (snd child)"
    "comma_native_infinite_literal_path (comma_boundary_value child (p+d)) tail"
    "rank q=None"
    "rank child=None"
    "\<forall>other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      other\<noteq>child \<longrightarrow> rank other\<noteq>None"
proof -
  have q_unranked: "rank q=None"
  proof (cases "rank q")
    case None
    then show ?thesis .
  next
    case (Some k)
    have no_path: "\<not>comma_native_infinite_literal_path
        (comma_boundary_value q p) stream"
      by (rule ranked_no_path[OF valid exponent phase Some])
    show ?thesis using no_path path by contradiction
  qed
  obtain outcome endpoint weight child where step:
      "comma_native_boundary_step rows q=Some outcome"
    and occurrence:
      "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    and member: "child\<in>set (comma_native_boundary_children q outcome)"
    and next_value:
      "stream (Suc weight)=comma_boundary_value child
        (p+comma_native_outcome_delta outcome)"
    and tail:
      "comma_native_infinite_literal_path
        (comma_boundary_value child (p+comma_native_outcome_delta outcome))
        (\<lambda>j. stream (weight+Suc j))"
    and child_valid: "comma_boundary_valid child"
    and child_phase:
      "(p+comma_native_outcome_delta outcome) mod 924=snd (snd child)"
    using comma_native_infinite_path_projects_admitted_child
      [OF powers stops valid exponent phase path] .
  show thesis
  proof (cases outcome)
    case (Comma_Landmine_At d)
    then show ?thesis using member
      by (simp add: comma_native_boundary_children_def)
  next
    case (Comma_Fork_At a d)
    have fork_step:
      "comma_native_boundary_step rows q=Some (Comma_Fork_At a d)"
      using step Comma_Fork_At by simp
    have p_bound: "5\<le>p+d" using exponent by simp
    have p_phase: "(p+d) mod 924=snd (snd child)"
      using child_phase Comma_Fork_At
      by (simp add: comma_native_outcome_delta_def)
    have child_unranked: "rank child=None"
    proof (cases "rank child")
      case None
      then show ?thesis .
    next
      case (Some k)
      have no_tail: "\<not>comma_native_infinite_literal_path
          (comma_boundary_value child (p+d))
          (\<lambda>j. stream (weight+Suc j))"
        by (rule ranked_no_path[OF child_valid p_bound p_phase Some])
      have tail_at_child:
        "comma_native_infinite_literal_path
          (comma_boundary_value child (p+d))
          (\<lambda>j. stream (weight+Suc j))"
        using tail Comma_Fork_At
        by (simp add: comma_native_outcome_delta_def)
      show ?thesis using no_tail tail_at_child by contradiction
    qed
    obtain only where only_member:
        "only\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
      and only_unranked: "rank only=None"
      and unique: "\<And>other. other\<in>set
          (comma_native_boundary_children q (Comma_Fork_At a d)) \<Longrightarrow>
          rank other=None \<Longrightarrow> other=only"
      using comma_native_rank_check_unranked_fork_unique
        [OF checked valid q_unranked fork_step] by blast
    have child_fork_member:
      "child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
      using member Comma_Fork_At by simp
    have child_eq_only: "child=only"
      by (rule unique[OF child_fork_member child_unranked])
    have other_ranked:
      "\<forall>other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
        other\<noteq>child \<longrightarrow> rank other\<noteq>None"
    proof (intro ballI impI)
      fix other
      assume other_member:
        "other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
        and different: "other\<noteq>child"
      show "rank other\<noteq>None"
      proof
        assume other_unranked: "rank other=None"
        have same: "other=only" by (rule unique[OF other_member other_unranked])
        show False using same child_eq_only different by simp
      qed
    qed
    have tail_expanded:
      "comma_native_infinite_literal_path (comma_boundary_value child (p+d))
        (\<lambda>j. stream (weight+Suc j))"
      using tail Comma_Fork_At
      by (simp add: comma_native_outcome_delta_def)
    have next_value_fork: "stream (Suc weight)=comma_boundary_value child (p+d)"
      using next_value Comma_Fork_At
      by (simp add: comma_native_outcome_delta_def)
    show ?thesis
      by (rule that[OF fork_step occurrence child_fork_member next_value_fork
        child_valid p_bound p_phase tail_expanded q_unranked child_unranked
        other_ranked])
  qed
qed

ML \<open>Comma_Native_Boundary_Profile.checkpoint
  "infinite-path-unique-unranked-child"\<close>

ML \<open>
  val checked = @{thms comma_native_survivor_step_sound
    comma_native_survivor_edge_member comma_native_safe_run_execute.simps
    comma_native_safe_runs_execute.simps comma_native_survivor_step_literal
    comma_native_safe_run_execute_literal comma_native_safe_runs_execute_literal
    comma_native_rank_check_row comma_native_rank_check_fork_decreases
    comma_native_rank_check_unranked_fork_unique
    comma_native_rank_check_unranked_landmine_false
    comma_native_ranked_path_has_smaller_child
    comma_native_rank_decrease_relation_wf
    comma_native_ranked_state_no_infinite_path
    comma_native_infinite_path_forces_unique_unranked_child}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native future projection and rank logic depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Native future projection and rank logic" checked
\<close>

end
