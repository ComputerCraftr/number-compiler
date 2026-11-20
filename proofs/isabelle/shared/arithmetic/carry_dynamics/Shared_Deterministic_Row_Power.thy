theory Shared_Deterministic_Row_Power
  imports Finite_Transfer_Power
begin

text \<open>Pointed execution of partial deterministic weighted rows. A row
with two different outcomes is outside this representation and must use the
general weighted relation. An empty row means no successor, not a zero-weight
self loop.\<close>

fun deterministic_weighted_run ::
  "('s \<Rightarrow> ('s \<times> 'w::comm_monoid_add) option) \<Rightarrow>
    nat \<Rightarrow> 's \<Rightarrow> ('s \<times> 'w) option" where
  "deterministic_weighted_run row 0 source = Some (source,0)"
| "deterministic_weighted_run row (Suc n) source =
    (case row source of None \<Rightarrow> None
     | Some (target,weight) \<Rightarrow>
       map_option (\<lambda>(endpoint,total). (endpoint,weight+total))
         (deterministic_weighted_run row n target))"

lemma deterministic_weighted_run_append:
  "deterministic_weighted_run row (m+n) source =
    (case deterministic_weighted_run row m source of None \<Rightarrow> None
     | Some (middle,first) \<Rightarrow>
       map_option (\<lambda>(endpoint,second). (endpoint,first+second))
         (deterministic_weighted_run row n middle))"
  by (induction m arbitrary: source)
    (auto simp: add.assoc map_option_case split: option.splits prod.splits)

lemma deterministic_weighted_run_then:
  "deterministic_weighted_run row (m+n) =
    partial_weighted_then (deterministic_weighted_run row m)
      (deterministic_weighted_run row n)"
  by (rule ext)
    (simp add: deterministic_weighted_run_append partial_weighted_then_def
      split: option.splits prod.splits)

lemma deterministic_weighted_run_relation_then:
  "partial_weighted_relation (deterministic_weighted_run row (m+n)) =
    weighted_relation_then
      (partial_weighted_relation (deterministic_weighted_run row m))
      (partial_weighted_relation (deterministic_weighted_run row n))"
  by (simp add: deterministic_weighted_run_then partial_weighted_relation_then_exact)

lemma deterministic_weighted_cycle_repeat:
  assumes cycle: "deterministic_weighted_run row period source = Some (source,weight)"
  shows "deterministic_weighted_run row (repetitions*period) source =
    Some (source,sum_list (replicate repetitions weight))"
  using cycle
  by (induction repetitions)
    (simp_all add: deterministic_weighted_run_append)

lemma deterministic_weighted_cycle_remainder:
  assumes cycle: "deterministic_weighted_run row period source = Some (source,weight)"
      and tail: "deterministic_weighted_run row remainder source = Some (target,tail_weight)"
  shows "deterministic_weighted_run row (repetitions*period+remainder) source =
    Some (target,sum_list (replicate repetitions weight)+tail_weight)"
  using deterministic_weighted_cycle_repeat[OF cycle, of repetitions] tail
  by (simp add: deterministic_weighted_run_append)

lemma deterministic_weighted_transient_cycle_remainder:
  assumes prefix:
      "deterministic_weighted_run row transient initial = Some (source,prefix_weight)"
      and cycle: "deterministic_weighted_run row period source = Some (source,weight)"
      and tail: "deterministic_weighted_run row remainder source = Some (target,tail_weight)"
  shows "deterministic_weighted_run row (transient+(repetitions*period+remainder)) initial =
    Some (target,prefix_weight+sum_list (replicate repetitions weight)+tail_weight)"
  using prefix deterministic_weighted_cycle_remainder[OF cycle tail, of repetitions]
  by (simp add: deterministic_weighted_run_append add.assoc)

lemma deterministic_integer_cycle_weight:
  "sum_list (replicate n (weight::int)) = int n * weight"
  by (induction n) (simp_all add: algebra_simps)

ML \<open>
  val checked = @{thms deterministic_weighted_run_append
    deterministic_weighted_run_then deterministic_weighted_run_relation_then
    deterministic_weighted_cycle_repeat deterministic_weighted_cycle_remainder
    deterministic_weighted_transient_cycle_remainder deterministic_integer_cycle_weight};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Deterministic row powering depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped deterministic row proof" else ();
\<close>

end
