theory Reverse_Centered_Future_Grammar
  imports Cylinder_Residue_Carry_SLP
begin

text \<open>
  Polynomial semantics for the carry-SLP bridge used by the bounded centered
  future constructor.  Concatenation is a monomial chart and repetition is
  repeated concatenation.  These laws justify the SLP-to-innovation rewrite;
  they do not prove temporal pumping or a construction bound across events.
\<close>

fun reverse_word_poly :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "reverse_word_poly [] z = 0"
| "reverse_word_poly (a#as) z = a + z * reverse_word_poly as z"

lemma reverse_word_poly_append:
  "reverse_word_poly (xs@ys) z =
    reverse_word_poly xs z + z^(length xs) * reverse_word_poly ys z"
  by (induction xs) (simp_all add: algebra_simps power_Suc)

lemma reverse_word_poly_map_int_append:
  "reverse_word_poly (map int (xs@ys)) z =
    reverse_word_poly (map int xs) z +
      z^(length xs) * reverse_word_poly (map int ys) z"
  by (simp add: reverse_word_poly_append)

lemma length_residue_repeat_word [simp]:
  "length (residue_repeat_word xs n) = n * length xs"
  by (induction n) (simp_all add: algebra_simps)

theorem reverse_word_poly_repeat_step:
  "reverse_word_poly
      (map int (residue_repeat_word xs (Suc n))) z =
    reverse_word_poly (map int (residue_repeat_word xs n)) z +
      z^(n * length xs) * reverse_word_poly (map int xs) z"
  by (simp add: reverse_word_poly_append)

theorem reverse_word_poly_repeat_add:
  "reverse_word_poly
      (map int (residue_repeat_word xs (m+n))) z =
    reverse_word_poly (map int (residue_repeat_word xs m)) z +
      z^(m * length xs) *
        reverse_word_poly (map int (residue_repeat_word xs n)) z"
  by (simp add: residue_repeat_word_add reverse_word_poly_append)

corollary reverse_word_poly_repeat_double:
  "reverse_word_poly
      (map int (residue_repeat_word xs (2*n))) z =
    reverse_word_poly (map int (residue_repeat_word xs n)) z +
      z^(n * length xs) *
        reverse_word_poly (map int (residue_repeat_word xs n)) z"
proof -
  have twice: "2*n = n+n" by arith
  show ?thesis unfolding twice by (rule reverse_word_poly_repeat_add)
qed

definition residue_outgoing_poly ::
    "nat list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "residue_outgoing_poly pairs incoming z =
    reverse_word_poly
      (map int (residue_outgoing (residue_carry_scan pairs incoming))) z"

theorem residue_outgoing_poly_append:
  assumes bit: "incoming = 0 \<or> incoming = 1"
  shows "residue_outgoing_poly (before@after) incoming z =
    residue_outgoing_poly before incoming z +
      z^(length before) *
        residue_outgoing_poly after
          (residue_final_carry (residue_carry_scan before incoming)) z"
proof -
  have scan: "residue_carry_scan (before@after) incoming =
      residue_outcome_compose (residue_carry_scan before incoming)
        (residue_summary after)"
    by (rule residue_scan_append[OF bit])
  have next_bit:
      "residue_final_carry (residue_carry_scan before incoming) = 0 \<or>
       residue_final_carry (residue_carry_scan before incoming) = 1"
    by (rule residue_scan_final_bit[OF bit])
  show ?thesis
    using scan next_bit residue_scan_lengths[of before incoming]
    by (simp add: residue_outgoing_poly_def residue_outcome_compose_def
        residue_summary_at_scan reverse_word_poly_append Let_def)
qed

theorem residue_outgoing_poly_repeat_is_powered_summary:
  "residue_summary (residue_repeat_word pairs n) =
    residue_summary_power (residue_summary pairs) n"
  by (rule residue_summary_repeat)

text \<open>
  A constant pair-symbol interval has only one physical carry event.  The
  decimal threshold is centered at pair value 9: a symbol below 9 resets the
  carry to zero, 9 preserves it, and a symbol above 9 resets it to one.  The
  following lemmas concern one spatial LSD-to-MSD scan.  They neither identify
  different source occurrences nor provide temporal compression.
\<close>

lemma forcing_carry_step_centered_domain:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "forcing_carry_step pair incoming =
    (if pair < 9 then 0 else if pair = 9 then incoming else 1)"
  using incoming
  by (auto simp: forcing_carry_step_def split: if_splits)

lemma forcing_carry_step_centered_idempotent:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "forcing_carry_step pair (forcing_carry_step pair incoming) =
    forcing_carry_step pair incoming"
proof -
  consider (below) "pair < 9" | (neutral) "pair = 9" | (above) "9 < pair"
    by arith
  then show ?thesis
    using incoming
    by cases (simp_all add: forcing_carry_step_centered_domain)
qed

theorem residue_constant_run_outgoing:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "residue_outgoing (residue_carry_scan (replicate n pair) incoming) =
    replicate n (forcing_carry_step pair incoming)"
  using incoming
proof (induction n arbitrary: incoming)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "forcing_carry_step pair incoming"
  have next_bit: "?next = 0 \<or> ?next = 1"
    by (rule forcing_carry_step_bit)
  have stable: "forcing_carry_step pair ?next = ?next"
    by (rule forcing_carry_step_centered_idempotent[OF Suc.prems])
  show ?case
    using Suc.IH[OF next_bit] stable by (simp add: Let_def)
qed

theorem residue_constant_run_final:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "residue_final_carry
      (residue_carry_scan (replicate (Suc n) pair) incoming) =
    forcing_carry_step pair incoming"
  using incoming
proof (induction n arbitrary: incoming)
  case 0
  then show ?case by (simp add: Let_def)
next
  case (Suc n)
  let ?next = "forcing_carry_step pair incoming"
  have next_bit: "?next = 0 \<or> ?next = 1"
    by (rule forcing_carry_step_bit)
  have stable: "forcing_carry_step pair ?next = ?next"
    by (rule forcing_carry_step_centered_idempotent[OF Suc.prems])
  show ?case
    using Suc.IH[OF next_bit] stable by (simp add: Let_def)
qed

theorem residue_constant_run_first_reset:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "residue_jumps
      (residue_carry_scan (replicate (Suc n) pair) incoming) =
    (int (forcing_carry_step pair incoming) - int incoming) # replicate n 0"
  using incoming
proof (induction n arbitrary: incoming)
  case 0
  then show ?case by (simp add: Let_def)
next
  case (Suc n)
  let ?next = "forcing_carry_step pair incoming"
  have next_bit: "?next = 0 \<or> ?next = 1"
    by (rule forcing_carry_step_bit)
  have stable: "forcing_carry_step pair ?next = ?next"
    by (rule forcing_carry_step_centered_idempotent[OF Suc.prems])
  have tail:
      "residue_jumps (residue_carry_scan (replicate (Suc n) pair) ?next) =
       0 # replicate n 0"
    using Suc.IH[OF next_bit] stable by simp
  show ?case using tail stable by (simp add: Let_def)
qed

corollary residue_concatenated_resets_telescope:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "sum_list (residue_jumps
      (residue_carry_scan (before @ after) incoming)) =
    int (residue_final_carry
      (residue_carry_scan after
        (residue_final_carry (residue_carry_scan before incoming)))) -
      int incoming"
proof -
  have before_bit:
      "residue_final_carry (residue_carry_scan before incoming) = 0 \<or>
       residue_final_carry (residue_carry_scan before incoming) = 1"
    by (rule residue_scan_final_bit[OF incoming])
  have scan:
      "residue_final_carry (residue_carry_scan (before @ after) incoming) =
       residue_final_carry
         (residue_carry_scan after
           (residue_final_carry (residue_carry_scan before incoming)))"
    using residue_scan_append[OF incoming, of before after]
      residue_summary_at_scan[OF before_bit, of after]
    by (simp add: residue_outcome_compose_def Let_def)
  show ?thesis
    using residue_interior_jumps_telescope[of "before @ after" incoming] scan
    by simp
qed

fun residue_interval_poly :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "residue_interval_poly 0 z = 0"
| "residue_interval_poly (Suc n) z = 1 + z * residue_interval_poly n z"

lemma reverse_word_poly_replicate:
  "reverse_word_poly (replicate n a) z = a * residue_interval_poly n z"
  by (induction n) (simp_all add: algebra_simps)

theorem residue_constant_run_carry_interval:
  assumes incoming: "incoming = 0 \<or> incoming = 1"
  shows "residue_outgoing_poly (replicate n pair) incoming z =
    int (forcing_carry_step pair incoming) * residue_interval_poly n z"
  using residue_constant_run_outgoing[OF incoming, of n pair]
  by (simp add: residue_outgoing_poly_def reverse_word_poly_replicate)

corollary residue_two_disjoint_carry_intervals:
  fixes first second middle :: nat
  assumes incoming: "incoming = 0 \<or> incoming = 1"
      and nonempty: "0 < m"
  defines "middle \<equiv> forcing_carry_step first incoming"
  shows "residue_outgoing_poly
      (replicate m first @ replicate n second) incoming z =
    int middle * residue_interval_poly m z +
      z^m * int (forcing_carry_step second middle) *
        residue_interval_poly n z"
proof -
  have middle_bit: "middle = 0 \<or> middle = 1"
    unfolding middle_def by (rule forcing_carry_step_bit)
  have final_first:
      "residue_final_carry (residue_carry_scan (replicate m first) incoming) =
       middle"
    using nonempty residue_constant_run_final[OF incoming, of "m - 1" first]
    unfolding middle_def by (cases m) simp_all
  show ?thesis
    using residue_outgoing_poly_append[OF incoming,
        of "replicate m first" "replicate n second" z]
      residue_constant_run_carry_interval[OF incoming, of m first z]
      residue_constant_run_carry_interval[OF middle_bit, of n second z]
      final_first
    by (simp add: middle_def)
qed

fun residue_normalized_digits :: "nat list \<Rightarrow> nat \<Rightarrow> int list" where
  "residue_normalized_digits [] incoming = []"
| "residue_normalized_digits (pair#pairs) incoming =
    (let following = forcing_carry_step pair incoming
     in (int pair + int incoming - 10 * int following) #
       residue_normalized_digits pairs following)"

theorem residue_coboundary_polynomial:
  "reverse_word_poly (residue_normalized_digits pairs incoming) z +
      int (residue_final_carry (residue_carry_scan pairs incoming)) *
        z^(length pairs) =
    reverse_word_poly (map int pairs) z + int incoming +
      (z - 10) * residue_outgoing_poly pairs incoming z"
proof (induction pairs arbitrary: incoming)
  case Nil
  then show ?case by (simp add: residue_outgoing_poly_def)
next
  case (Cons pair pairs)
  let ?following = "forcing_carry_step pair incoming"
  note tail = Cons.IH[of ?following]
  have scaled:
          "z * (reverse_word_poly
              (residue_normalized_digits pairs ?following) z +
            int (residue_final_carry
              (residue_carry_scan pairs ?following)) * z ^ length pairs) =
           z * (reverse_word_poly (map int pairs) z + int ?following +
            (z - 10) * residue_outgoing_poly pairs ?following z)"
    using tail by (rule arg_cong)
  show ?case
    using scaled
    by (simp add: residue_outgoing_poly_def Let_def power_Suc algebra_simps)
qed

corollary residue_initial_carry_zero_correction:
  "reverse_word_poly (residue_normalized_digits pairs 0) z +
      int (residue_final_carry (residue_carry_scan pairs 0)) *
        z^(length pairs) =
    reverse_word_poly (map int pairs) z +
      (z - 10) * residue_outgoing_poly pairs 0 z"
  using residue_coboundary_polynomial[of pairs 0 z] by simp

corollary residue_terminal_carry_is_bit:
  "residue_final_carry (residue_carry_scan pairs 0) = 0 \<or>
   residue_final_carry (residue_carry_scan pairs 0) = 1"
  by (rule residue_scan_final_bit) simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms reverse_word_poly_append reverse_word_poly_map_int_append
        reverse_word_poly_repeat_step reverse_word_poly_repeat_add
        reverse_word_poly_repeat_double residue_outgoing_poly_append
        residue_outgoing_poly_repeat_is_powered_summary
        forcing_carry_step_centered_domain
        forcing_carry_step_centered_idempotent
        residue_constant_run_outgoing residue_constant_run_final
        residue_constant_run_first_reset
        residue_concatenated_resets_telescope
        reverse_word_poly_replicate residue_constant_run_carry_interval
        residue_two_disjoint_carry_intervals
        residue_coboundary_polynomial
        residue_initial_carry_zero_correction
        residue_terminal_carry_is_bit})
    then () else error "Reverse centered future grammar laws depend on an oracle";
\<close>

end
