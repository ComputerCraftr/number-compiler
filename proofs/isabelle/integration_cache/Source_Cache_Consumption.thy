theory Source_Cache_Consumption
  imports Collatz_Parity_Shift_Germ
    "Shared_S_Arithmetic.Dyadic_Balanced_Worklist"
begin

text \<open>The arithmetic record below matches CollatzDyadicOccurrence:
width, low source residue, odd-symbol count, target origin and multiplier.
Admission is a publication invariant, not a claim that checking a multiplier
alone authenticates an arbitrary supplied record.  The Python cache is an
internal store of constructor-issued records.  These results refine its
application and physical-fit test; they do not certify the entire Python
constructor or a logarithmic cold-discovery bound.\<close>

record collatz_cached_occurrence =
  cached_width :: nat
  cached_residue :: nat
  cached_odd :: nat
  cached_origin :: nat
  cached_gain :: nat

definition cached_occurrence_admitted :: "collatz_cached_occurrence \<Rightarrow> bool" where
  "cached_occurrence_admitted E \<longleftrightarrow>
    cached_residue E < 2 ^ cached_width E \<and>
    cached_odd E = length (filter id
      (collatz_qprefix (cached_width E) (cached_residue E))) \<and>
    cached_origin E = dyadic_source_orbit collatz_normalized_step
      (cached_residue E) (cached_width E) \<and>
    cached_gain E = 3 ^ cached_odd E"

definition cached_occurrence_apply :: "collatz_cached_occurrence \<Rightarrow> nat \<Rightarrow> nat" where
  "cached_occurrence_apply E source =
    cached_origin E + cached_gain E * (source div 2 ^ cached_width E)"

theorem cached_occurrence_source_transport:
  assumes admitted: "cached_occurrence_admitted E"
    and bound: "source mod 2 ^ cached_width E = cached_residue E"
  shows "cached_occurrence_apply E source =
    dyadic_source_orbit collatz_normalized_step source (cached_width E)"
proof -
  have split: "cached_residue E + 2 ^ cached_width E *
      (source div 2 ^ cached_width E) = source"
    using mod_mult_div_eq[of source "2 ^ cached_width E"]
    by (simp only: bound mult.commute)
  show ?thesis
    using collatz_target_centered_source_lift
      [of "cached_residue E" "cached_width E"
        "source div 2 ^ cached_width E"] admitted
    by (simp add: split cached_occurrence_admitted_def cached_occurrence_apply_def)
qed

definition normalized_physical_ticks :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "normalized_physical_ticks width source =
    width + length (filter id (collatz_qprefix width source))"

lemma normalized_physical_ticks_zero [simp]:
  "normalized_physical_ticks 0 source = 0"
  by (simp add: normalized_physical_ticks_def collatz_qprefix_def)

lemma normalized_physical_ticks_suc:
  "normalized_physical_ticks (Suc n) source =
    (if odd source then 2 else 1) +
      normalized_physical_ticks n (collatz_normalized_step source)"
  by (simp add: normalized_physical_ticks_def collatz_qprefix_def)

lemma normalized_one_physical_block:
  "(physical_collatz ^^ (if odd source then 2 else 1)) source =
    collatz_normalized_step source"
  by (cases "even source")
    (simp_all add: numeral_2_eq_2 physical_collatz_normalized_even
      physical_collatz_pending_division)

theorem normalized_physical_prefix_exact:
  "(physical_collatz ^^ normalized_physical_ticks n source) source =
    dyadic_source_orbit collatz_normalized_step source n"
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have steps: "normalized_physical_ticks (Suc n) source =
      normalized_physical_ticks n (collatz_normalized_step source) +
        (if odd source then 2 else 1)"
    by (simp add: normalized_physical_ticks_suc add.commute)
  show ?case
    by (simp add: steps funpow_add normalized_one_physical_block Suc.IH)
qed

theorem cached_occurrence_physical_consumer:
  assumes "cached_occurrence_admitted E"
    "source mod 2 ^ cached_width E = cached_residue E"
  shows "(physical_collatz ^^ (cached_width E + cached_odd E)) source =
    cached_occurrence_apply E source"
proof -
  have prefix: "collatz_qprefix (cached_width E) source =
      collatz_qprefix (cached_width E) (cached_residue E)"
    using collatz_qprefix_low[of "cached_width E" source] assms(2) by simp
  have ticks: "normalized_physical_ticks (cached_width E) source =
      cached_width E + cached_odd E"
    using assms(1) prefix
    by (simp add: normalized_physical_ticks_def cached_occurrence_admitted_def)
  show ?thesis
    using normalized_physical_prefix_exact[of "cached_width E" source]
      cached_occurrence_source_transport[OF assms]
    by (simp add: ticks)
qed

lemma cached_occurrence_fit_preserves_remaining:
  assumes "cached_width E + cached_odd E \<le> remaining"
  shows "remaining - (cached_width E + cached_odd E) +
    (cached_width E + cached_odd E) = remaining"
  using assms by simp

text \<open>A parent hit is checked before leaf construction or child
transport in the shared executable worklist.  Both equations below refer
to machine_step itself.  They do not turn cache-key lookup, admission or
integer arithmetic into zero work.\<close>

context dyadic_balanced_worklist
begin

theorem admitted_parent_lookup_returns_without_descent:
  assumes "memo_valid memo" "map_of memo (n,r) = Some outcome"
  shows "machine_step (Machine (Descend n r) frames memo) =
    Machine (Return (balanced_spec n r)) frames memo"
  using memo_lookup_valid[OF assms] assms(2) by (simp add: numeral_2_eq_2)

theorem admitted_root_hit_completes_in_two_control_steps:
  assumes "memo_valid memo" "map_of memo (n,r) = Some outcome"
  shows "machine_run 2 (Machine (Descend n r) [] memo) =
    Machine (Complete (balanced_spec n r)) [] memo"
  using memo_lookup_valid[OF assms] assms(2) by (simp add: numeral_2_eq_2)

end

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms cached_occurrence_source_transport
      normalized_physical_prefix_exact cached_occurrence_physical_consumer
      cached_occurrence_fit_preserves_remaining
      dyadic_balanced_worklist.admitted_parent_lookup_returns_without_descent
      dyadic_balanced_worklist.admitted_root_hit_completes_in_two_control_steps})
    then () else error "Source cache consumption depends on an oracle";
\<close>

end
