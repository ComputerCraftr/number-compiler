theory Comma_Quotient_Totality
  imports Comma_Cylinder.Comma_Finite_Transition
begin

text \<open>Only the canonical finite control is evaluated by the checker.
Successful control is transported to the weighted constructor by erasure;
no representative literal weight is computed during the finite check.\<close>

definition comma_totality_slice ::
  "comma_boundary_kind \<Rightarrow> nat \<Rightarrow> comma_boundary_state list" where
  "comma_totality_slice kind a = map (\<lambda>r. (kind,a,r)) [0..<924]"

definition comma_totality_slice_keys ::
  "(comma_boundary_kind \<times> nat) list" where
  "comma_totality_slice_keys =
    [(Comma_N,2),(Comma_N,3),(Comma_N,4),(Comma_N,5),
     (Comma_N,6),(Comma_N,7),(Comma_N,8),(Comma_N,9),
     (Comma_Z,2),(Comma_Z,3),(Comma_Z,4),(Comma_Z,5),
     (Comma_Z,6),(Comma_Z,7),(Comma_Z,8),(Comma_Z,9)]"

definition comma_totality_slice_check ::
  "nat \<Rightarrow> comma_boundary_kind \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_totality_slice_check B kind a =
    list_all (\<lambda>q. comma_finite_macro B q \<noteq> None)
      (comma_totality_slice kind a)"

definition comma_totality_all_slices_check :: "nat \<Rightarrow> bool" where
  "comma_totality_all_slices_check B =
    list_all (\<lambda>ka.
      comma_totality_slice_check B (fst ka) (snd ka))
      comma_totality_slice_keys"

lemma comma_totality_slice_keys_length:
  "length comma_totality_slice_keys = 16"
  by (simp add: comma_totality_slice_keys_def)

lemma comma_totality_slice_length:
  "length (comma_totality_slice kind a) = 924"
  by (simp add: comma_totality_slice_def)

lemma comma_totality_slice_coverage:
  assumes valid: "comma_boundary_valid q"
  shows "\<exists>ka\<in>set comma_totality_slice_keys.
    q \<in> set (comma_totality_slice (fst ka) (snd ka))"
proof -
  obtain kind a r where q: "q = (kind,a,r)"
    by (cases q) auto
  have a: "2 \<le> a" "a \<le> 9" and r: "r < 924"
    using valid by (auto simp: q comma_boundary_valid_def)
  have key: "(kind,a) \<in> set comma_totality_slice_keys"
    using a by (cases kind)
      (auto simp: comma_totality_slice_keys_def)
  have member: "q \<in> set (comma_totality_slice kind a)"
    using r by (simp add: q comma_totality_slice_def)
  show ?thesis
  proof (rule bexI[where x="(kind,a)"])
    show "q \<in> set (comma_totality_slice (fst (kind,a)) (snd (kind,a)))"
      using member by simp
    show "(kind,a) \<in> set comma_totality_slice_keys"
      by (rule key)
  qed
qed

lemma comma_totality_slice_check_sound:
  assumes checked: "comma_totality_slice_check B kind a"
    and member: "q \<in> set (comma_totality_slice kind a)"
  shows "\<exists>outcome. comma_finite_macro B q = Some outcome"
  using checked member
  by (auto simp: comma_totality_slice_check_def list_all_iff
    split: option.splits)

lemma comma_totality_all_slices_check_sound:
  assumes checked: "comma_totality_all_slices_check B"
    and valid: "comma_boundary_valid q"
  shows "\<exists>outcome. comma_finite_macro B q = Some outcome"
proof -
  obtain ka where key: "ka \<in> set comma_totality_slice_keys"
    and member: "q \<in> set
      (comma_totality_slice (fst ka) (snd ka))"
    using comma_totality_slice_coverage[OF valid] by blast
  have slice: "comma_totality_slice_check B (fst ka) (snd ka)"
    using checked key
    by (simp add: comma_totality_all_slices_check_def list_all_iff)
  show ?thesis
    using comma_totality_slice_check_sound[OF slice member] .
qed

lemma comma_totality_checked_weighted:
  assumes checked: "comma_totality_all_slices_check B"
    and valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>result. comma_finite_weighted_macro B p q = Some result"
proof -
  obtain outcome where control:
      "comma_finite_macro B q = Some outcome"
    using comma_totality_all_slices_check_sound[OF checked valid]
    by blast
  have erasure: "map_option fst (comma_finite_weighted_macro B p q) =
      Some outcome"
    using comma_finite_weighted_macro_erasure[OF exponent phase]
      control by simp
  show ?thesis
    using erasure by (cases "comma_finite_weighted_macro B p q") auto
qed

text \<open>Witnesses are untrusted control-position lists.  Only a checked
local edge at every position licenses a macro.  This theory proves the
conditional totality and bound calculation; no concrete all-state witness
bundle is asserted here.\<close>

type_synonym comma_control_witness =
  "comma_boundary_state \<times> comma_finite_position list \<times>
    comma_finite_outcome"

definition comma_control_witness_source ::
  "comma_control_witness \<Rightarrow> comma_boundary_state" where
  "comma_control_witness_source witness =
    (case witness of (q,positions,outcome) \<Rightarrow> q)"

definition comma_control_witness_depth ::
  "comma_control_witness \<Rightarrow> nat" where
  "comma_control_witness_depth witness =
    (case witness of (q,positions,outcome) \<Rightarrow> length positions)"

definition comma_control_witness_check ::
  "comma_control_witness \<Rightarrow> bool" where
  "comma_control_witness_check witness =
    (case witness of (q,positions,outcome) \<Rightarrow>
      comma_boundary_valid q \<and>
      positions \<noteq> [] \<and>
      hd positions = comma_finite_initial q \<and>
      comma_finite_trace_ok (snd (snd q)) positions outcome)"

lemma comma_control_witness_sound:
  assumes checked: "comma_control_witness_check witness"
  shows "\<exists>q positions outcome.
    witness = (q,positions,outcome) \<and>
    comma_boundary_valid q \<and>
    comma_finite_macro (length positions) q = Some outcome"
proof -
  obtain q positions outcome where witness: "witness = (q,positions,outcome)"
    by (cases witness) auto
  have valid: "comma_boundary_valid q"
    and start: "hd positions = comma_finite_initial q"
    and trace: "comma_finite_trace_ok (snd (snd q)) positions outcome"
    using checked by (auto simp: witness comma_control_witness_check_def)
  have run: "comma_finite_run (length positions) (snd (snd q))
      (comma_finite_initial q) = Some outcome"
    using comma_finite_trace_ok_sound[OF trace] start by simp
  have macro: "comma_finite_macro (length positions) q = Some outcome"
    using run valid by (cases q) (simp add: comma_finite_macro_def)
  show ?thesis using witness valid macro by blast
qed

lemma comma_finite_macro_more:
  assumes source: "comma_finite_macro fuel q = Some outcome"
  shows "comma_finite_macro (fuel + extra) q = Some outcome"
proof -
  have valid: "comma_boundary_valid q"
    using source by (cases q)
      (auto simp: comma_finite_macro_def split: if_splits)
  have run: "comma_finite_run fuel (snd (snd q))
      (comma_finite_initial q) = Some outcome"
    using source valid by (cases q) (simp add: comma_finite_macro_def)
  have longer: "comma_finite_run (fuel + extra) (snd (snd q))
      (comma_finite_initial q) = Some outcome"
    using comma_finite_run_more[OF run] .
  show ?thesis using longer valid
    by (cases q) (simp add: comma_finite_macro_def)
qed

definition comma_control_witness_bound ::
  "comma_control_witness list \<Rightarrow> nat" where
  "comma_control_witness_bound witnesses =
    Max (insert 0 (set (map comma_control_witness_depth witnesses)))"

lemma comma_control_witness_depth_le_bound:
  assumes member: "witness \<in> set witnesses"
  shows "comma_control_witness_depth witness \<le>
    comma_control_witness_bound witnesses"
proof -
  have inside: "comma_control_witness_depth witness \<in>
      insert 0 (set (map comma_control_witness_depth witnesses))"
    using member by auto
  have finite: "finite
      (insert 0 (set (map comma_control_witness_depth witnesses)))"
    by simp
  show ?thesis
    unfolding comma_control_witness_bound_def
    using Max_ge[OF finite inside] .
qed

definition comma_control_witness_bundle_check ::
  "comma_control_witness list \<Rightarrow> bool" where
  "comma_control_witness_bundle_check witnesses =
    (list_all comma_control_witness_check witnesses \<and>
      set (map comma_control_witness_source witnesses) =
        set comma_boundary_states)"

lemma comma_control_witness_bundle_sound:
  assumes checked: "comma_control_witness_bundle_check witnesses"
    and valid: "comma_boundary_valid q"
  shows "\<exists>outcome.
    comma_finite_macro (comma_control_witness_bound witnesses) q =
      Some outcome"
proof -
  have source_member:
      "q \<in> set (map comma_control_witness_source witnesses)"
    using checked valid comma_boundary_states_set
    by (simp add: comma_control_witness_bundle_check_def)
  obtain witness where member: "witness \<in> set witnesses"
    and source: "comma_control_witness_source witness = q"
    using source_member by auto
  have witness_checked: "comma_control_witness_check witness"
    using checked member
    by (simp add: comma_control_witness_bundle_check_def list_all_iff)
  obtain q' positions outcome where decomposition:
      "witness = (q',positions,outcome)"
    and base_valid: "comma_boundary_valid q'"
    and base: "comma_finite_macro (length positions) q' = Some outcome"
    using comma_control_witness_sound[OF witness_checked] by blast
  have equal: "q' = q"
    using source decomposition
    by (simp add: comma_control_witness_source_def)
  have depth: "comma_control_witness_depth witness = length positions"
    by (simp add: decomposition comma_control_witness_depth_def)
  have le: "length positions \<le>
      comma_control_witness_bound witnesses"
    using comma_control_witness_depth_le_bound[OF member] depth by simp
  have arithmetic: "length positions +
      (comma_control_witness_bound witnesses - length positions) =
      comma_control_witness_bound witnesses"
    using le by arith
  have longer: "comma_finite_macro
      (length positions +
        (comma_control_witness_bound witnesses - length positions)) q =
      Some outcome"
    using comma_finite_macro_more[OF base, of
      "comma_control_witness_bound witnesses - length positions"]
      equal by simp
  show ?thesis using longer arithmetic by auto
qed

lemma comma_control_witness_bundle_weighted:
  assumes checked: "comma_control_witness_bundle_check witnesses"
    and valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>result.
    comma_finite_weighted_macro
      (comma_control_witness_bound witnesses) p q = Some result"
proof -
  obtain outcome where control: "comma_finite_macro
      (comma_control_witness_bound witnesses) q = Some outcome"
    using comma_control_witness_bundle_sound[OF checked valid] by blast
  have erasure: "map_option fst (comma_finite_weighted_macro
      (comma_control_witness_bound witnesses) p q) = Some outcome"
    using comma_finite_weighted_macro_erasure[OF exponent phase]
      control by simp
  show ?thesis
    using erasure
    by (cases "comma_finite_weighted_macro
      (comma_control_witness_bound witnesses) p q") auto
qed

text \<open>A small untrusted trace probes the local-edge checker without
recursively evaluating a macro.  It establishes no all-state totality.\<close>

definition comma_tiny_Z7_5_positions :: "comma_finite_position list" where
  "comma_tiny_Z7_5_positions = [
    Comma_Entry 7 0 0, Comma_Near 7 0 160,
    Comma_Near 7 0 153, Comma_Near 7 0 76,
    Comma_Near 7 0 29, Comma_Near 7 0 12,
    Comma_Entry 8 0 76, Comma_Near 8 0 84,
    Comma_Near 8 0 16, Comma_Entry 9 0 33,
    Comma_Near 9 0 67, Comma_Near 9 0 28]"

lemma comma_tiny_Z7_5_shape:
  "length comma_tiny_Z7_5_positions = 12"
  "hd comma_tiny_Z7_5_positions = comma_finite_initial (Comma_Z,7,5)"
  by (simp_all add: comma_tiny_Z7_5_positions_def
    comma_finite_initial_def)

lemma comma_tiny_Z7_5_trace:
  "comma_finite_trace_ok 5 comma_tiny_Z7_5_positions
    (Comma_Landmine_At 0)"
  unfolding comma_tiny_Z7_5_positions_def
  apply (simp only: comma_finite_trace_ok.simps)
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_tiny_Z7_5_checked:
  "comma_control_witness_check
    ((Comma_Z,7,5),comma_tiny_Z7_5_positions,Comma_Landmine_At 0)"
proof -
  have nonempty: "comma_tiny_Z7_5_positions \<noteq> []"
    using comma_tiny_Z7_5_shape(1) by auto
  show ?thesis
    using nonempty comma_tiny_Z7_5_trace comma_tiny_Z7_5_shape(2)
    by (simp add: comma_control_witness_check_def
      comma_boundary_valid_def)
qed

lemma comma_tiny_Z7_5_macro:
  "comma_finite_macro 12 (Comma_Z,7,5) = Some (Comma_Landmine_At 0)"
  using comma_control_witness_sound[OF comma_tiny_Z7_5_checked]
    comma_tiny_Z7_5_shape
  by (auto simp: comma_control_witness_depth_def
    comma_control_witness_source_def)

lemma comma_tiny_Z7_5_wrong_start_rejected:
  "\<not> comma_control_witness_check
    ((Comma_Z,7,5),tl comma_tiny_Z7_5_positions,Comma_Landmine_At 0)"
  by (simp add: comma_control_witness_check_def
    comma_tiny_Z7_5_positions_def comma_finite_initial_def)

lemma comma_tiny_Z7_5_truncated_rejected:
  "\<not> comma_finite_trace_ok 5
    (take 11 comma_tiny_Z7_5_positions) (Comma_Landmine_At 0)"
  using comma_tiny_Z7_5_trace
  by (simp add: comma_tiny_Z7_5_positions_def
    comma_finite_trace_ok.simps comma_finite_step_def Let_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_totality_slice_keys_length comma_totality_slice_length
      comma_totality_slice_coverage comma_totality_slice_check_sound
      comma_totality_all_slices_check_sound
      comma_totality_checked_weighted
      comma_control_witness_sound comma_finite_macro_more
      comma_control_witness_depth_le_bound
      comma_control_witness_bundle_sound
      comma_control_witness_bundle_weighted
      comma_tiny_Z7_5_shape comma_tiny_Z7_5_trace
      comma_tiny_Z7_5_checked comma_tiny_Z7_5_macro
      comma_tiny_Z7_5_wrong_start_rejected
      comma_tiny_Z7_5_truncated_rejected})
    then () else error "Comma totality checker depends on an oracle";
\<close>

end
