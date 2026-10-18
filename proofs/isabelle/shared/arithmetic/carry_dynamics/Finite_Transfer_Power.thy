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

lemma transfer_source_join:
  assumes "(source, middle) \<in> first" "(middle, target) \<in> after"
  shows "(source, target) \<in> first O after"
  using assms by auto

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

lemma typed_bitset_foreign_seam_empty:
  assumes "first_owner \<noteq> after_owner"
  shows "typed_bitset_relation first_owner first_states first O
      typed_bitset_relation after_owner after_states after = {}"
  using assms unfolding typed_bitset_relation_def by auto

ML \<open>
  val checked = @{thms transfer_rows_then_exact transfer_square_power
    transfer_binary_power_exact transfer_source_join bit_fold_mask
    bitset_image_exact typed_bitset_then_exact
    typed_bitset_foreign_seam_empty};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Finite transfer algebra depends on an oracle";
\<close>

end
