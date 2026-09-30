theory Comma_Future_Cycle_Check
  imports Comma_Fast_Future_Check
begin

text \<open>A phase return alone loses multiples of 924. These computations
 retain every actual terminal macro delta, and sum them along the selected
 path. A successful check is still a quotient path theorem; positive literal
 weights and their validity at every shifted exponent need a separate bridge.\<close>

definition comma_fast_surviving_step ::
  "nat \<Rightarrow> (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
    comma_boundary_state \<Rightarrow> (comma_boundary_state \<times> nat) option" where
  "comma_fast_surviving_step rounds rank q =
    (case comma_fast_boundary_macro rounds q of
       Some (Comma_Fork_At a d) \<Rightarrow>
         (let phase=(snd (snd q)+d) mod 924;
              left=(Comma_N,a,phase); right=(Comma_Z,a,phase)
          in if rank left = None then
               if rank right = None then None else Some (left,d)
             else if rank right = None then Some (right,d) else None)
     | _ \<Rightarrow> None)"

lemma comma_fast_surviving_step_sound:
  assumes computed: "comma_fast_surviving_step rounds rank q = Some (target,d)"
  shows "comma_macro_defined q"
    and "rank target = None"
    and "target \<in> set (comma_total_children q)"
    and "\<exists>a. comma_total_macro q = Comma_Fork_At a d"
  using computed comma_fast_boundary_macro_total[of rounds q]
  by (auto simp: comma_fast_surviving_step_def Let_def comma_total_children_def
    split: option.splits comma_finite_outcome.splits if_splits)

fun comma_fast_surviving_walk ::
  "nat \<Rightarrow> nat \<Rightarrow> (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
    comma_boundary_state \<Rightarrow> (comma_boundary_state \<times> nat) option" where
  "comma_fast_surviving_walk 0 rounds rank q = Some (q,0)"
| "comma_fast_surviving_walk (Suc steps) rounds rank q =
    (case comma_fast_surviving_step rounds rank q of None \<Rightarrow> None
     | Some (target,d) \<Rightarrow>
         map_option (\<lambda>(final_state,rest). (final_state,d+rest))
           (comma_fast_surviving_walk steps rounds rank target))"

fun comma_fast_surviving_sources ::
  "nat \<Rightarrow> nat \<Rightarrow> (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_boundary_state list option" where
  "comma_fast_surviving_sources 0 rounds rank q = Some []"
| "comma_fast_surviving_sources (Suc steps) rounds rank q =
    (case comma_fast_surviving_step rounds rank q of None \<Rightarrow> None
     | Some (target,d) \<Rightarrow>
         map_option (Cons q) (comma_fast_surviving_sources steps rounds rank target))"

lemma comma_fast_surviving_sources_length:
  assumes "comma_fast_surviving_sources steps rounds rank q = Some sources"
  shows "length sources = steps"
  using assms by (induction steps arbitrary: q sources)
    (auto split: option.splits prod.splits)

inductive comma_surviving_delta_path ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow>
    comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool"
  for rank where
  empty: "comma_surviving_delta_path rank 0 q q 0"
| step: "comma_macro_defined q \<Longrightarrow>
    comma_total_macro q = Comma_Fork_At a d \<Longrightarrow>
    target \<in> set (comma_total_children q) \<Longrightarrow> rank target = None \<Longrightarrow>
    comma_surviving_delta_path rank steps target final_state rest \<Longrightarrow>
    comma_surviving_delta_path rank (Suc steps) q final_state (d+rest)"

theorem comma_fast_surviving_walk_sound:
  assumes "comma_fast_surviving_walk steps rounds rank q = Some (final_state,delta)"
  shows "comma_surviving_delta_path rank steps q final_state delta"
  using assms
proof (induction steps arbitrary: q final_state delta)
  case 0
  then show ?case by (auto intro: comma_surviving_delta_path.empty)
next
  case (Suc steps)
  obtain target d rest where edge:
      "comma_fast_surviving_step rounds rank q = Some (target,d)"
    and tail: "comma_fast_surviving_walk steps rounds rank target = Some (final_state,rest)"
    and delta: "delta = d+rest"
    using Suc.prems by (auto split: option.splits prod.splits)
  obtain a where macro: "comma_total_macro q = Comma_Fork_At a d"
    using comma_fast_surviving_step_sound(4)[OF edge] by blast
  have path: "comma_surviving_delta_path rank steps target final_state rest"
    by (rule Suc.IH[OF tail])
  show ?case unfolding delta
    by (rule comma_surviving_delta_path.step[OF
      comma_fast_surviving_step_sound(1)[OF edge] macro
      comma_fast_surviving_step_sound(3)[OF edge]
      comma_fast_surviving_step_sound(2)[OF edge] path])
qed

lemma comma_fast_surviving_sources_sound:
  assumes computed: "comma_fast_surviving_sources steps rounds rank q = Some sources"
    and index: "i<steps"
  shows "\<exists>delta. comma_surviving_delta_path rank i q (sources ! i) delta"
  using computed index
proof (induction steps arbitrary: q sources i)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  obtain target d rest where edge:
      "comma_fast_surviving_step rounds rank q = Some (target,d)"
    and tail: "comma_fast_surviving_sources steps rounds rank target = Some rest"
    and sources: "sources = q # rest"
    using Suc.prems(1) by (auto split: option.splits prod.splits)
  note step_ih = Suc.IH
  note step_index = Suc.prems(2)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis using sources
      by (auto intro: comma_surviving_delta_path.empty)
  next
    case (Suc j)
    have below: "j<steps" using step_index Suc by simp
    obtain delta where path: "comma_surviving_delta_path rank j target (rest ! j) delta"
      using step_ih[OF tail below] by blast
    obtain a where macro: "comma_total_macro q = Comma_Fork_At a d"
      using comma_fast_surviving_step_sound(4)[OF edge] by blast
    have "comma_surviving_delta_path rank (Suc j) q (rest ! j) (d+delta)"
      by (rule comma_surviving_delta_path.step[OF
        comma_fast_surviving_step_sound(1)[OF edge] macro
        comma_fast_surviving_step_sound(3)[OF edge]
        comma_fast_surviving_step_sound(2)[OF edge] path])
    then show ?thesis using Suc sources by auto
  qed
qed

lemma comma_surviving_delta_path_append:
  assumes first: "comma_surviving_delta_path rank n q middle a"
    and second: "comma_surviving_delta_path rank m middle final_state b"
  shows "comma_surviving_delta_path rank (n+m) q final_state (a+b)"
  using first second
  by (induction rule: comma_surviving_delta_path.induct)
    (auto intro: comma_surviving_delta_path.intros simp: add.assoc)

corollary comma_surviving_cycle_repeats:
  assumes cycle: "comma_surviving_delta_path rank 314 q q 924"
  shows "comma_surviving_delta_path rank (k*314) q q (k*924)"
proof (induction k)
  case 0
  then show ?case by (simp add: comma_surviving_delta_path.empty)
next
  case (Suc k)
  have "comma_surviving_delta_path rank (k*314+314) q q (k*924+924)"
    by (rule comma_surviving_delta_path_append[OF Suc.IH cycle])
  then show ?case by (simp add: algebra_simps)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_surviving_step_sound comma_fast_surviving_walk_sound
      comma_fast_surviving_sources_length comma_fast_surviving_sources_sound
      comma_surviving_delta_path_append comma_surviving_cycle_repeats})
    then () else error "Comma cycle checker depends on an oracle";
\<close>
end
