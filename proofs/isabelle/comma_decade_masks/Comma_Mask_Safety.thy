theory Comma_Mask_Safety
  imports Comma_Decade_Masks
    Comma_Cylinder.Comma_Future_Safety
    Comma_Total_Macro.Comma_Total_Macro
begin

unbundle bit_operations_syntax

type_synonym comma_boundary_schema = "comma_boundary_kind \<times> nat"
type_synonym comma_safety_masks = "comma_boundary_schema \<Rightarrow> nat"

datatype comma_fork_mask = Comma_Fork_Mask nat nat nat

definition comma_schema_valid :: "comma_boundary_schema \<Rightarrow> bool" where
  "comma_schema_valid s = (2\<le>snd s \<and> snd s\<le>9)"

definition comma_schema_state :: "comma_boundary_schema \<Rightarrow> nat \<Rightarrow> comma_boundary_state" where
  "comma_schema_state s r = (fst s,snd s,r)"

lemma comma_schema_state_valid:
  "comma_boundary_valid (comma_schema_state s r) = (comma_schema_valid s \<and> r<924)"
  by (simp add: comma_schema_state_def comma_schema_valid_def comma_boundary_valid_def)

text \<open>Each fork record retains the exact exponent gain. Only the phase
pullback reduces it modulo 924. These masks are not candidate ranks: their
refinement premise must be established from the executable macro constructor.
The successful-domain clause prevents definite-description values outside the
constructor's domain from becoming admission evidence.\<close>

definition comma_safety_masks_refine ::
  "comma_safety_masks \<Rightarrow> (comma_boundary_schema \<Rightarrow> comma_fork_mask list) \<Rightarrow> bool" where
  "comma_safety_masks_refine mines forks =
    ((\<forall>s r. comma_schema_valid s \<longrightarrow> comma_phase_member (mines s) r \<longrightarrow>
      comma_macro_defined (comma_schema_state s r) \<and>
      (\<exists>d. comma_total_macro (comma_schema_state s r)=Comma_Landmine_At d)) \<and>
    (\<forall>s r a d bits. comma_schema_valid s \<longrightarrow>
      Comma_Fork_Mask a d bits \<in> set (forks s) \<longrightarrow>
      comma_phase_member bits r \<longrightarrow>
      2\<le>a \<and> a\<le>9 \<and> comma_macro_defined (comma_schema_state s r) \<and>
      comma_total_macro (comma_schema_state s r)=Comma_Fork_At a d))"

fun comma_fork_losing_mask :: "comma_safety_masks \<Rightarrow> comma_fork_mask \<Rightarrow> nat" where
  "comma_fork_losing_mask old (Comma_Fork_Mask a d bits) =
    bits AND comma_rotate_phase d (old (Comma_N,a) AND old (Comma_Z,a))"

definition comma_safety_seed :: "comma_safety_masks \<Rightarrow> comma_safety_masks" where
  "comma_safety_seed mines s = (if comma_schema_valid s then take_bit 924 (mines s) else 0)"

definition comma_safety_update ::
  "comma_safety_masks \<Rightarrow> (comma_boundary_schema \<Rightarrow> comma_fork_mask list) \<Rightarrow>
    comma_safety_masks \<Rightarrow> comma_safety_masks" where
  "comma_safety_update mines forks old s =
    (if comma_schema_valid s then take_bit 924
      (old s OR mines s OR comma_mask_union (map (comma_fork_losing_mask old) (forks s))) else 0)"

primrec comma_safety_iteration ::
  "comma_safety_masks \<Rightarrow> (comma_boundary_schema \<Rightarrow> comma_fork_mask list) \<Rightarrow>
    nat \<Rightarrow> comma_safety_masks" where
  "comma_safety_iteration mines forks 0 = comma_safety_seed mines"
| "comma_safety_iteration mines forks (Suc n) =
    comma_safety_update mines forks (comma_safety_iteration mines forks n)"

lemma comma_phase_member_trim:
  "comma_phase_member (take_bit 924 bits) r=comma_phase_member bits r"
  by (auto simp: comma_phase_member_def bit_simps)

lemma comma_fork_losing_mask_member:
  assumes "r<924"
  shows "comma_phase_member (comma_fork_losing_mask old (Comma_Fork_Mask a d bits)) r =
    (comma_phase_member bits r \<and>
     comma_phase_member (old (Comma_N,a)) ((r+d) mod 924) \<and>
     comma_phase_member (old (Comma_Z,a)) ((r+d) mod 924))"
  using assms by (simp add: comma_phase_member_and comma_rotate_phase_member)

lemma comma_fork_losing_mask_record_member:
  assumes "r<924"
  shows "comma_phase_member (comma_fork_losing_mask old item) r =
    (\<exists>a d bits. item=Comma_Fork_Mask a d bits \<and>
      comma_phase_member bits r \<and>
      comma_phase_member (old (Comma_N,a)) ((r+d) mod 924) \<and>
      comma_phase_member (old (Comma_Z,a)) ((r+d) mod 924))"
  using assms by (cases item) (simp only: comma_fork_losing_mask_member; auto)

lemma comma_safety_seed_member:
  "comma_phase_member (comma_safety_seed mines s) r =
    (comma_schema_valid s \<and> comma_phase_member (mines s) r)"
  by (simp add: comma_safety_seed_def comma_phase_member_trim)

lemma comma_safety_update_member:
  assumes "r<924"
  shows "comma_phase_member (comma_safety_update mines forks old s) r =
    (comma_schema_valid s \<and>
      (comma_phase_member (old s) r \<or> comma_phase_member (mines s) r \<or>
       (\<exists>a d bits. Comma_Fork_Mask a d bits \<in> set (forks s) \<and>
        comma_phase_member bits r \<and>
        comma_phase_member (old (Comma_N,a)) ((r+d) mod 924) \<and>
        comma_phase_member (old (Comma_Z,a)) ((r+d) mod 924))))"
  using assms
  by (auto simp: comma_safety_update_def comma_phase_member_trim
      comma_phase_member_or comma_mask_union_member comma_fork_losing_mask_record_member)

text \<open>The update is simultaneous: both children are tested in the old
mask family. The following induction bounds its semantic losing rank by the
iteration number and uses the canonical total-macro child relation. It does
not assert that any particular iteration is a fixed point.\<close>

theorem comma_safety_iteration_losing:
  assumes refined: "comma_safety_masks_refine mines forks"
    and member: "comma_phase_member (comma_safety_iteration mines forks n s) r"
  shows "comma_schema_state s r \<in>
    comma_losing_levels comma_total_children {q. comma_boundary_valid q} n"
  using member
proof (induction n arbitrary: s r)
  case 0
  have valid: "comma_schema_valid s" and mine: "comma_phase_member (mines s) r"
    using "0.prems" by (auto simp only: comma_safety_iteration.simps comma_safety_seed_member)
  have phase: "r<924" using mine by (simp add: comma_phase_member_def)
  obtain d where outcome: "comma_total_macro (comma_schema_state s r)=Comma_Landmine_At d"
    using refined valid mine unfolding comma_safety_masks_refine_def by blast
  show ?case using valid phase outcome
    by (simp add: comma_schema_state_valid comma_total_children_def)
next
  case (Suc n)
  have phase: "r<924" using Suc.prems by (simp add: comma_phase_member_def)
  have row: "comma_schema_valid s \<and>
      (comma_phase_member (comma_safety_iteration mines forks n s) r \<or>
       comma_phase_member (mines s) r \<or>
       (\<exists>a d bits. Comma_Fork_Mask a d bits \<in> set (forks s) \<and>
        comma_phase_member bits r \<and>
        comma_phase_member (comma_safety_iteration mines forks n (Comma_N,a)) ((r+d) mod 924) \<and>
        comma_phase_member (comma_safety_iteration mines forks n (Comma_Z,a)) ((r+d) mod 924)))"
    using Suc.prems comma_safety_update_member[OF phase]
    by (simp only: comma_safety_iteration.simps)
  have valid: "comma_schema_valid s" using row by blast
  have state: "comma_boundary_valid (comma_schema_state s r)"
    using valid phase by (simp only: comma_schema_state_valid)
  consider (old) "comma_phase_member (comma_safety_iteration mines forks n s) r"
    | (mine) "comma_phase_member (mines s) r"
    | (fork) a d bits where "Comma_Fork_Mask a d bits \<in> set (forks s)"
      "comma_phase_member bits r"
      "comma_phase_member (comma_safety_iteration mines forks n (Comma_N,a)) ((r+d) mod 924)"
      "comma_phase_member (comma_safety_iteration mines forks n (Comma_Z,a)) ((r+d) mod 924)"
    using row by blast
  then show ?case
  proof cases
    case old
    show ?thesis using Suc.IH[OF old] by simp
  next
    case mine
    obtain d where outcome: "comma_total_macro (comma_schema_state s r)=Comma_Landmine_At d"
      using refined valid mine unfolding comma_safety_masks_refine_def by blast
    have base: "comma_schema_state s r \<in>
      comma_losing_levels comma_total_children {q. comma_boundary_valid q} 0"
      using state outcome by (simp add: comma_total_children_def)
    show ?thesis
      by (rule subsetD[OF comma_losing_levels_zero_subset
          [where children=comma_total_children and states="{q. comma_boundary_valid q}"
            and n="Suc n"] base])
  next
    case (fork a d bits)
    have outcome: "comma_total_macro (comma_schema_state s r)=Comma_Fork_At a d"
      using refined valid fork(1,2) unfolding comma_safety_masks_refine_def by blast
    have left: "comma_schema_state (Comma_N,a) ((r+d) mod 924) \<in>
      comma_losing_levels comma_total_children {q. comma_boundary_valid q} n"
      by (rule Suc.IH[OF fork(3)])
    have right: "comma_schema_state (Comma_Z,a) ((r+d) mod 924) \<in>
      comma_losing_levels comma_total_children {q. comma_boundary_valid q} n"
      by (rule Suc.IH[OF fork(4)])
    have children: "comma_total_children (comma_schema_state s r) =
      [comma_schema_state (Comma_N,a) ((r+d) mod 924),
       comma_schema_state (Comma_Z,a) ((r+d) mod 924)]"
      by (simp only: comma_total_children_def outcome;
          simp add: comma_schema_state_def)
    have nonempty: "comma_total_children (comma_schema_state s r) \<noteq> []"
      by (simp only: children list.distinct; simp)
    have below: "set (comma_total_children (comma_schema_state s r)) \<subseteq>
      comma_losing_levels comma_total_children {q. comma_boundary_valid q} n"
      using left right by (simp only: children; auto)
    show ?thesis using state nonempty below
      by (simp only: comma_losing_levels.simps; auto)
  qed
qed

corollary comma_safety_iteration_terminates:
  assumes "comma_safety_masks_refine mines forks"
    "comma_phase_member (comma_safety_iteration mines forks n s) r"
  shows "comma_all_branches_terminate comma_total_children (comma_schema_state s r)"
  by (rule comma_losing_levels_terminate[OF comma_safety_iteration_losing[OF assms]])

corollary comma_safety_iteration_no_infinite_path:
  assumes "comma_safety_masks_refine mines forks"
    "comma_phase_member (comma_safety_iteration mines forks n s) r"
  shows "\<not> (\<exists>path :: nat \<Rightarrow> comma_boundary_state.
    path 0=comma_schema_state s r \<and>
    (\<forall>j. path (Suc j) \<in> set (comma_total_children (path j))))"
  by (rule comma_termination_excludes_infinite_path[OF comma_safety_iteration_terminates[OF assms]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fork_losing_mask_member comma_safety_iteration_losing
      comma_safety_iteration_terminates comma_safety_iteration_no_infinite_path})
    then () else error "Comma mask safety depends on an oracle";
\<close>
end
