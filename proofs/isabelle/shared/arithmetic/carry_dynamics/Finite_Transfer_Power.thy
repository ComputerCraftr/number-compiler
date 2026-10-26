theory Finite_Transfer_Power
  imports Main "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

text \<open>Chronological Boolean transfer composition. A relation describes
allowed successors under supplied boundary inputs. Powering it does not prove
that a physical source realizes repeated inputs.\<close>

definition transfer_rows :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<times> 'a) set" where
  "transfer_rows rows = {(x,y). y \<in> rows x}"

definition transfer_rows_then ::
  "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "transfer_rows_then first after x = (\<Union>y\<in>first x. after y)"

lemma transfer_rows_then_exact:
  "transfer_rows (transfer_rows_then first after) =
    transfer_rows first O transfer_rows after"
  by (auto simp: transfer_rows_def transfer_rows_then_def)

fun transfer_binary_value :: "bool list \<Rightarrow> nat" where
  "transfer_binary_value [] = 0"
| "transfer_binary_value (chosen # bits) =
    (if chosen then 1 else 0) + 2 * transfer_binary_value bits"

fun transfer_binary_power ::
  "('a \<times> 'a) set \<Rightarrow> bool list \<Rightarrow> ('a \<times> 'a) set" where
  "transfer_binary_power R [] = Id"
| "transfer_binary_power R (chosen # bits) =
    (if chosen then R else Id) O transfer_binary_power (R O R) bits"

lemma transfer_square_power:
  "(R O R) ^^ n = R ^^ (2*n)"
  by (induction n) (simp_all add: relpow_add O_assoc)

theorem transfer_binary_power_exact:
  "transfer_binary_power R bits = R ^^ transfer_binary_value bits"
proof (induction bits arbitrary: R)
  case Nil
  then show ?case by simp
next
  case (Cons chosen bits)
  then show ?case
    by (cases chosen) (simp_all add: transfer_square_power relpow_add relpow_commute)
qed

text \<open>A state for the integer-driven binary loop used by the Python
\<open>binary_power\<close> owner.  The accumulator and current block are relations;
the third field is the unprocessed integer exponent.  Squaring is omitted
after the final shift, matching the runtime loop's \<open>if n\<close> guard.\<close>

type_synonym 'a transfer_binary_state =
  "(('a \<times> 'a) set) \<times> (('a \<times> 'a) set) \<times> nat"

definition transfer_binary_next_accumulator ::
  "(('a \<times> 'a) set) \<Rightarrow>
    (('a \<times> 'a) set) \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) set)" where
  "transfer_binary_next_accumulator accumulator current remaining =
    (if odd remaining then accumulator O current else accumulator)"

definition transfer_binary_next_block ::
  "(('a \<times> 'a) set) \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) set)" where
  "transfer_binary_next_block current remaining =
    (if remaining div 2 > 0 then current O current else current)"

definition transfer_binary_state_step ::
  "'a transfer_binary_state \<Rightarrow> 'a transfer_binary_state" where
  "transfer_binary_state_step state =
    (case state of (accumulator,(current,remaining)) \<Rightarrow>
      (transfer_binary_next_accumulator accumulator current remaining,
       transfer_binary_next_block current remaining,
       remaining div 2))"

lemma transfer_binary_next_block_power:
  "transfer_binary_next_block current remaining ^^ (remaining div 2) =
    current ^^ (2 * (remaining div 2))"
proof (cases "remaining div 2")
  case 0
  then show ?thesis
    by (simp add: transfer_binary_next_block_def)
next
  case (Suc quotient)
  then show ?thesis
    by (simp add: transfer_binary_next_block_def transfer_square_power)
qed

lemma transfer_binary_state_step_preserves:
  assumes invariant:
    "accumulator O current ^^ remaining = base ^^ duration"
  shows
    "transfer_binary_next_accumulator accumulator current remaining O
       (transfer_binary_next_block current remaining ^^ (remaining div 2)) =
     base ^^ duration"
proof -
  let ?quotient = "remaining div 2"
  have division:
    "remaining = 2 * ?quotient + remaining mod 2"
    by presburger
  have remainder: "remaining mod 2 < 2" by simp
  show ?thesis
  proof (cases "remaining mod 2 = 0")
    case True
    have exponent: "remaining = 2 * ?quotient"
      using division True by simp
    have next_accumulator:
      "transfer_binary_next_accumulator accumulator current remaining =
        accumulator"
      using True by (simp add: transfer_binary_next_accumulator_def
          even_iff_mod_2_eq_zero)
    have next_power:
      "transfer_binary_next_block current remaining ^^ ?quotient =
        current ^^ (2 * ?quotient)"
      using transfer_binary_next_block_power .
    have step_value:
      "transfer_binary_next_accumulator accumulator current remaining O
          (transfer_binary_next_block current remaining ^^ ?quotient) =
        accumulator O current ^^ (2 * ?quotient)"
      using next_accumulator next_power
      by (simp only: next_accumulator next_power)
    have invariant_value:
      "accumulator O current ^^ (2 * ?quotient) = base ^^ duration"
      using invariant exponent by simp
    show ?thesis
      using step_value invariant_value by (rule trans)
  next
    case False
    have remainder_one: "remaining mod 2 = 1"
      using remainder False by presburger
    have exponent: "remaining = 2 * ?quotient + 1"
      using division remainder_one by simp
    have next_accumulator:
      "transfer_binary_next_accumulator accumulator current remaining =
        accumulator O current"
      using remainder_one by (simp add: transfer_binary_next_accumulator_def
          odd_iff_mod_2_eq_one)
    have next_power: "transfer_binary_next_block current remaining ^^ ?quotient =
        current ^^ (2 * ?quotient)"
      by (rule transfer_binary_next_block_power)
    have concatenate:
      "(accumulator O current) O current ^^ (2 * ?quotient) =
        accumulator O current ^^ (2 * ?quotient + 1)"
    proof -
      have order: "2 * ?quotient + 1 = 1 + 2 * ?quotient"
        by presburger
      have first:
        "(accumulator O current) O current ^^ (2 * ?quotient) =
          accumulator O (current O current ^^ (2 * ?quotient))"
        by (simp add: O_assoc)
      have second:
        "accumulator O (current O current ^^ (2 * ?quotient)) =
          accumulator O (current ^^ 1 O current ^^ (2 * ?quotient))"
        by simp
      have third:
        "accumulator O (current ^^ 1 O current ^^ (2 * ?quotient)) =
          accumulator O current ^^ (1 + 2 * ?quotient)"
        by (simp only: relpow_add)
      have joined:
        "(accumulator O current) O current ^^ (2 * ?quotient) =
          accumulator O current ^^ (1 + 2 * ?quotient)"
      proof -
        have "(accumulator O current) O current ^^ (2 * ?quotient) =
            accumulator O (current O current ^^ (2 * ?quotient))"
          by (rule first)
        also have "... =
            accumulator O (current ^^ 1 O current ^^ (2 * ?quotient))"
          by (rule second)
        also have "... = accumulator O current ^^ (1 + 2 * ?quotient)"
          by (rule third)
        finally show ?thesis .
      qed
      have order_reversed: "1 + 2 * ?quotient = 2 * ?quotient + 1"
        using order by presburger
      have reorder:
        "accumulator O current ^^ (1 + 2 * ?quotient) =
          accumulator O current ^^ (2 * ?quotient + 1)"
        using arg_cong[where f="\<lambda>n. accumulator O current ^^ n"]
          order_reversed .
      show ?thesis by (rule trans[OF joined reorder])
    qed
    have step_value:
      "transfer_binary_next_accumulator accumulator current remaining O
          (transfer_binary_next_block current remaining ^^ ?quotient) =
        accumulator O current ^^ (2 * ?quotient + 1)"
      using next_accumulator next_power concatenate
      by (simp only: next_accumulator next_power concatenate)
    have invariant_value:
      "accumulator O current ^^ (2 * ?quotient + 1) = base ^^ duration"
      using invariant exponent by simp
    show ?thesis
      using step_value invariant_value by (rule trans)
  qed
qed

inductive transfer_binary_loop_reaches ::
  "'a transfer_binary_state \<Rightarrow> 'a transfer_binary_state \<Rightarrow> bool" where
  transfer_binary_loop_refl: "transfer_binary_loop_reaches state state"
| transfer_binary_loop_step:
    "remaining > 0 \<Longrightarrow>
      transfer_binary_loop_reaches
        (transfer_binary_state_step (accumulator,current,remaining)) final \<Longrightarrow>
      transfer_binary_loop_reaches (accumulator,current,remaining) final"

definition transfer_binary_state_invariant ::
  "(('a \<times> 'a) set) \<Rightarrow> nat \<Rightarrow>
    'a transfer_binary_state \<Rightarrow> bool" where
  "transfer_binary_state_invariant base duration state \<longleftrightarrow>
    (case state of (accumulator,(current,remaining)) \<Rightarrow>
      accumulator O current ^^ remaining = base ^^ duration)"

lemma transfer_binary_loop_state_invariant:
  assumes reached: "transfer_binary_loop_reaches start final"
  shows "transfer_binary_state_invariant R duration start \<longrightarrow>
    transfer_binary_state_invariant R duration final"
  using reached
proof (induction rule: transfer_binary_loop_reaches.induct)
  case (transfer_binary_loop_refl state)
  then show ?case by simp
next
  case (transfer_binary_loop_step remaining accumulator current final)
  let ?start = "(accumulator,current,remaining)"
  let ?next = "transfer_binary_state_step ?start"
  have preserved:
      "transfer_binary_state_invariant R duration ?start \<longrightarrow>
      transfer_binary_state_invariant R duration ?next"
  proof
    assume start_invariant:
      "transfer_binary_state_invariant R duration ?start"
    have step_equation:
      "transfer_binary_next_accumulator accumulator current remaining O
          (transfer_binary_next_block current remaining ^^ (remaining div 2)) =
        R ^^ duration"
      using transfer_binary_state_step_preserves[
          where accumulator=accumulator and current=current
            and remaining=remaining and base=R and duration=duration]
        start_invariant
      by (simp add: transfer_binary_state_invariant_def)
    show "transfer_binary_state_invariant R duration ?next"
      using step_equation
      by (simp add: transfer_binary_state_invariant_def
          transfer_binary_state_step_def)
  qed
  show ?case
    using transfer_binary_loop_step.IH preserved by blast
qed

lemma transfer_binary_loop_reaches_terminal:
  "\<exists>final_acc final_block.
    transfer_binary_loop_reaches (accumulator,current,remaining)
      (final_acc,final_block,0)"
proof (induction remaining arbitrary: accumulator current rule: less_induct)
  case (less remaining)
  show ?case
  proof (cases remaining)
    case 0
    then show ?thesis
      by (intro exI) (auto intro: transfer_binary_loop_reaches.intros)
  next
    case (Suc predecessor)
    let ?next = "transfer_binary_state_step (accumulator,current,remaining)"
    obtain next_acc next_block next_remaining where shape:
      "?next = (next_acc,next_block,next_remaining)"
      by (cases ?next) (auto split: prod.splits)
    have next_value: "next_remaining = remaining div 2"
      using shape by (simp add: transfer_binary_state_step_def split: prod.splits)
    have smaller: "next_remaining < remaining"
      using Suc next_value by simp
    obtain final_acc final_block where tail:
      "transfer_binary_loop_reaches (next_acc,next_block,next_remaining)
        (final_acc,final_block,0)"
      using less.IH[OF smaller, of next_acc next_block] by blast
    have positive: "remaining > 0" using Suc by simp
    have next_reaches:
      "transfer_binary_loop_reaches
        (transfer_binary_state_step (accumulator,current,remaining))
        (final_acc,final_block,0)"
      using tail shape by simp
    have start_reaches:
      "transfer_binary_loop_reaches (accumulator,current,remaining)
        (final_acc,final_block,0)"
      by (rule transfer_binary_loop_step[OF positive next_reaches])
    show ?thesis using start_reaches by blast
  qed
qed

theorem transfer_binary_loop_accumulator_exact:
  assumes reached:
    "transfer_binary_loop_reaches (Id,R,duration) (accumulator,current,0)"
  shows "accumulator = R ^^ duration"
proof -
  have invariant:
    "transfer_binary_state_invariant R duration (Id,R,duration)"
    by (simp add: transfer_binary_state_invariant_def)
  have final:
    "transfer_binary_state_invariant R duration (accumulator,current,0)"
    using transfer_binary_loop_state_invariant[OF reached] invariant by blast
  show ?thesis
    using final by (simp add: transfer_binary_state_invariant_def)
qed

corollary transfer_binary_loop_terminates_exactly:
  "\<exists>accumulator current.
    transfer_binary_loop_reaches (Id,R,duration)
      (accumulator,current,0) \<and> accumulator = R ^^ duration"
  using transfer_binary_loop_reaches_terminal[
      where accumulator=Id and current=R and remaining=duration]
      transfer_binary_loop_accumulator_exact[where R=R and duration=duration]
  by blast

lemma transfer_source_join:
  assumes "(source, middle) \<in> first" "(middle, target) \<in> after"
  shows "(source, target) \<in> first O after"
  using assms by auto

text \<open>Weighted row products use the same relational semantics whether
a row has zero/one successor or several. The partial-row representation is
the deterministic fast path: it is valid only when the row has at most one
distinct target/weight pair. Weights compose chronologically in their
additive coordinates.\<close>

type_synonym ('state,'weight) weighted_relation =
  "('state \<times> ('state \<times> 'weight)) set"

definition weighted_relation_then ::
  "('state,'weight::comm_monoid_add) weighted_relation \<Rightarrow>
    ('state,'weight) weighted_relation \<Rightarrow>
    ('state,'weight) weighted_relation" where
  "weighted_relation_then before after =
    {(source,(target,left_weight+right_weight)) |
      source middle target left_weight right_weight.
        (source,(middle,left_weight)) \<in> before \<and>
        (middle,(target,right_weight)) \<in> after}"

definition partial_weighted_relation ::
  "('state \<Rightarrow> ('state \<times> 'weight) option) \<Rightarrow>
    ('state,'weight) weighted_relation" where
  "partial_weighted_relation row =
    {(source,(target,weight)) | source target weight.
        row source = Some (target,weight)}"

lemma partial_weighted_relation_member:
  "(source,(target,weight)) \<in> partial_weighted_relation row \<longleftrightarrow>
    row source = Some (target,weight)"
  by (simp add: partial_weighted_relation_def)

definition partial_weighted_then ::
  "('state \<Rightarrow> ('state \<times> 'weight::comm_monoid_add) option) \<Rightarrow>
    ('state \<Rightarrow> ('state \<times> 'weight) option) \<Rightarrow>
    ('state \<Rightarrow> ('state \<times> 'weight) option)" where
  "partial_weighted_then before after source =
    (case before source of None \<Rightarrow> None
     | Some (middle,left_weight) \<Rightarrow>
       (case after middle of None \<Rightarrow> None
        | Some (target,right_weight) \<Rightarrow>
          Some (target,left_weight+right_weight)))"

lemma partial_weighted_relation_then_exact:
  fixes before after :: "'state \<Rightarrow> ('state \<times> 'weight::comm_monoid_add) option"
  shows
  "partial_weighted_relation (partial_weighted_then before after) =
    weighted_relation_then (partial_weighted_relation before)
      (partial_weighted_relation after)"
proof (rule set_eqI)
  fix edge :: "'state \<times> ('state \<times> 'weight)"
  obtain source payload where edge_pair: "edge = (source,payload)"
    by (cases edge) auto
  obtain target weight where payload_shape: "payload = (target,weight)"
    by (cases payload) auto
  have edge_form: "edge = (source,(target,weight))"
    using edge_pair payload_shape by simp
  have partial_member:
    "(edge \<in> partial_weighted_relation
        (partial_weighted_then before after)) =
      (partial_weighted_then before after source = Some (target,weight))"
    using edge_form by (simp add: partial_weighted_relation_member)
  have composed_member:
    "(edge \<in> weighted_relation_then
        (partial_weighted_relation before) (partial_weighted_relation after)) =
      (\<exists>middle left_weight right_weight.
        before source = Some (middle,left_weight) \<and>
        after middle = Some (target,right_weight) \<and>
        weight = left_weight + right_weight)"
    using edge_form
    by (auto simp: weighted_relation_then_def
        partial_weighted_relation_member)
  show "edge \<in> partial_weighted_relation
        (partial_weighted_then before after) \<longleftrightarrow>
      edge \<in> weighted_relation_then
        (partial_weighted_relation before) (partial_weighted_relation after)"
    using partial_member composed_member
  proof (cases "before source")
    case None
    then show ?thesis
      using partial_member composed_member
      by (simp add: partial_weighted_then_def)
  next
    case (Some first_result)
    obtain middle left_weight where first_pair:
      "first_result = (middle,left_weight)"
      by (cases first_result)
    have before_source:
      "before source = Some (middle,left_weight)"
      using Some first_pair by simp
    show ?thesis
    proof (cases "after middle")
      case None
      then show ?thesis
        using before_source partial_member composed_member
        by (simp add: partial_weighted_then_def)
    next
      case (Some second_result)
      obtain target' right_weight where second_pair:
        "second_result = (target',right_weight)"
        by (cases second_result)
      have after_middle:
        "after middle = Some (target',right_weight)"
        using Some second_pair by simp
      show ?thesis
        using before_source after_middle partial_member composed_member
        by (auto simp: partial_weighted_then_def)
    qed
  qed
qed

text \<open>The middle state is essential. Equal projected centers do not
supply the full source equality required by this composition premise.\<close>

text \<open>The Python owner stores each row as an integer bitset. The next
definitions give that representation its exact finite-relation meaning. The
owner number models the runtime state-space identity; the ordered state list
maps row indices to the owner's states.\<close>

definition bitset_image :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> nat" where
  "bitset_image width rows sources =
    List.fold (\<lambda>middle accumulated.
      if bit sources middle
      then accumulated OR rows middle
      else accumulated) [0..<width] 0"

definition bitset_then :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "bitset_then width first after source =
    bitset_image width after (first source)"

definition typed_bitset_relation :: "nat \<Rightarrow> 'state list \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow>
    ((nat \<times> 'state) \<times> (nat \<times> 'state)) set"
    where
  "typed_bitset_relation owner states rows =
    {((owner,states ! source),(owner,states ! target)) | source target.
      source < length states \<and> target < length states \<and>
      bit (rows source) target}"

lemma bit_fold_mask:
  "bit (List.fold (\<lambda>middle accumulated.
      if bit sources middle
      then accumulated OR rows middle
      else accumulated) indices initial) target =
    (bit initial target \<or>
      (\<exists>middle\<in>set indices. bit sources middle \<and>
        bit (rows middle) target))"
  by (induction indices arbitrary: initial) (auto simp: bit_simps)

lemma bitset_image_exact:
  "bit (bitset_image width rows sources) target =
    (\<exists>middle<width. bit sources middle \<and> bit (rows middle) target)"
  by (auto simp: bitset_image_def bit_fold_mask atLeast0LessThan
      Bex_def lessThan_def)

lemma distinct_state_nth_index_eq:
  assumes distinct: "distinct states"
      and left: "i < length states"
      and right: "j < length states"
      and equal: "states ! i = states ! j"
  shows "i = j"
  using distinct left right equal by (metis nth_eq_iff_index_eq)

lemma typed_bitset_then_exact:
  assumes "distinct states"
  shows
  "typed_bitset_relation owner states (bitset_then (length states) first after) =
    typed_bitset_relation owner states first O
      typed_bitset_relation owner states after"
  using assms unfolding typed_bitset_relation_def bitset_then_def
  by (auto simp: bitset_image_exact
      dest: distinct_state_nth_index_eq)

text \<open>Sparse Boolean rows omit zero rows. This recursion models the
finite union performed by a sparse join: each retained later row contributes
its target bitset exactly when its source is selected by the incoming row.
It preserves all branches and treats a missing later row as the empty set.\<close>

fun sparse_bitset_row_join :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat" where
  "sparse_bitset_row_join incoming [] = 0"
| "sparse_bitset_row_join incoming ((middle,targets) # later) =
    (if bit incoming middle then targets else 0) OR
      sparse_bitset_row_join incoming later"

lemma bit_sparse_bitset_row_join_exact:
  "bit (sparse_bitset_row_join incoming rows) target =
    (\<exists>middle targets. (middle,targets) \<in> set rows \<and>
      bit incoming middle \<and> bit targets target)"
proof (induction rows)
  case Nil
  then show ?case by simp
next
  case (Cons entry later)
  obtain middle targets where entry:
    "entry = (middle,targets)"
    by (cases entry)
  have step:
    "bit (sparse_bitset_row_join incoming (entry # later)) target =
      ((bit incoming middle \<and> bit targets target) \<or>
        bit (sparse_bitset_row_join incoming later) target)"
    using entry by (cases "bit incoming middle") (simp_all add: bit_simps)
  show ?case
    using step entry Cons.IH by auto
qed

lemma sparse_bitset_row_join_matches_dense:
  assumes distinct: "distinct (map fst rows)"
      and in_bounds: "\<And>middle targets. (middle,targets) \<in> set rows
        \<Longrightarrow> middle < width"
      and representation: "\<And>middle. middle < width \<Longrightarrow>
        map_of rows middle = (if dense middle = 0 then None
          else Some (dense middle))"
  shows
    "bit (sparse_bitset_row_join incoming rows) target =
      bit (bitset_image width dense incoming) target"
proof -
  have sparse_fold:
    "bit (sparse_bitset_row_join incoming rows) target =
      (\<exists>middle targets. (middle,targets) \<in> set rows \<and>
        bit incoming middle \<and> bit targets target)"
    by (rule bit_sparse_bitset_row_join_exact)
  have dense_image:
    "bit (bitset_image width dense incoming) target =
      (\<exists>middle<width. bit incoming middle \<and>
        bit (dense middle) target)"
    by (rule bitset_image_exact)
  have witnesses:
    "(\<exists>middle targets. (middle,targets) \<in> set rows \<and>
        bit incoming middle \<and> bit targets target) \<longleftrightarrow>
      (\<exists>middle<width. bit incoming middle \<and>
        bit (dense middle) target)"
  proof
    assume sparse_witness:
      "\<exists>middle targets. (middle,targets) \<in> set rows \<and>
        bit incoming middle \<and> bit targets target"
    then obtain middle targets where row:
      "(middle,targets) \<in> set rows"
      and selected: "bit incoming middle"
      and target: "bit targets target"
      by blast
    have middle_bound: "middle < width"
      using in_bounds row by blast
    have lookup: "map_of rows middle = Some targets"
      using distinct row by (simp add: map_of_eq_Some_iff)
    have "map_of rows middle =
        (if dense middle = 0 then None else Some (dense middle))"
      by (rule representation[OF middle_bound])
    with lookup have row_value: "targets = dense middle"
      by (cases "dense middle = 0") auto
    show "\<exists>middle<width. bit incoming middle \<and>
        bit (dense middle) target"
      using middle_bound selected target row_value by blast
  next
    assume dense_witness:
      "\<exists>middle<width. bit incoming middle \<and>
        bit (dense middle) target"
    then obtain middle where middle_bound: "middle < width"
      and selected: "bit incoming middle"
      and target: "bit (dense middle) target"
      by blast
    have nonzero: "dense middle \<noteq> 0"
    proof (rule notI)
      assume zero: "dense middle = 0"
      with target show False by simp
    qed
    have lookup: "map_of rows middle = Some (dense middle)"
      using representation[OF middle_bound] nonzero by simp
    have row: "(middle,dense middle) \<in> set rows"
      using distinct lookup by (simp add: map_of_eq_Some_iff)
    show "\<exists>middle targets. (middle,targets) \<in> set rows \<and>
        bit incoming middle \<and> bit targets target"
      using row selected target by blast
  qed
  show ?thesis
    using sparse_fold dense_image witnesses by blast
qed

lemma typed_bitset_foreign_seam_empty:
  assumes "first_owner \<noteq> after_owner"
  shows "typed_bitset_relation first_owner first_states first O
      typed_bitset_relation after_owner after_states after = {}"
  using assms unfolding typed_bitset_relation_def by auto

ML \<open>
  val checked = @{thms transfer_rows_then_exact transfer_square_power
    transfer_binary_power_exact transfer_source_join
    transfer_binary_state_step_preserves transfer_binary_loop_state_invariant
    transfer_binary_loop_reaches_terminal
    transfer_binary_loop_accumulator_exact transfer_binary_loop_terminates_exactly
    partial_weighted_relation_then_exact bit_fold_mask
    bitset_image_exact typed_bitset_then_exact
    bit_sparse_bitset_row_join_exact
    sparse_bitset_row_join_matches_dense
    typed_bitset_foreign_seam_empty};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Finite transfer algebra depends on an oracle";
  val _ = if not (Thm_Deps.has_skip_proof checked) then ()
    else error "Finite transfer algebra contains a skipped proof";
\<close>

end
