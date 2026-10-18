theory Collatz_Guarded_Word_Progression
  imports Collatz_Skew_Cylinder_Temporal_Squaring
    "Shared_S_Arithmetic.Integer_Cylinder_Transport"
begin

text \<open>Bounded image and full-stride refinement for an already admitted
normalized parity word. This consumer theorem is separate from the core
skew-cylinder squaring algebra.\<close>

theorem collatz_guarded_word_endpoint_progression:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
      and "target \<equiv> collatz_guarded_normalized_word_endpoint bits source"
  shows "(\<lambda>q. int (collatz_guarded_normalized_word_endpoint
      bits (source + 2^length bits*q))) ` {..<count} =
    integer_progression (int target)
      (int (joint_dyadic_gain action)) count"
proof -
  let ?span = "(2::int)^length bits"
  let ?gain = "int (joint_dyadic_gain action)"
  let ?offset = "int (joint_dyadic_offset action)"
  let ?target = "int target"
  have steps: "joint_dyadic_steps action = length bits"
    by (simp add: action_def collatz_joint_dyadic_word_steps)
  have base_nat:
    "joint_dyadic_gain action * source +
        joint_dyadic_offset action =
      2^(joint_dyadic_steps action) * target"
    using collatz_guarded_word_affine_endpoint[OF admitted]
    by (simp add: action_def target_def)
  have base:
    "?gain * int source + ?offset = ?span * ?target"
    using collatz_nat_affine_cast[OF base_nat] steps by simp
  have denominator: "0 < ?span" by simp
  have stride: "?gain * ?span = ?span * ?gain"
    by (simp add: mult.commute)
  have affine_image:
    "(\<lambda>x. (?gain*x+?offset) div ?span) `
        integer_progression (int source) ?span count =
      integer_progression ?target ?gain count"
    by (rule integer_progression_affine_image[OF denominator base stride])
  have source_progression:
    "integer_progression (int source) ?span count =
      (\<lambda>q. int (source + 2^length bits*q)) ` {..<count}"
    unfolding integer_progression_def
    by (simp add: algebra_simps)
  have affine_parameterized:
    "(\<lambda>q. (?gain * int (source + 2^length bits*q) + ?offset)
        div ?span) ` {..<count} = integer_progression ?target ?gain count"
    using affine_image source_progression
    by (simp only: source_progression image_image)
  have lifted_residue:
    "(source + 2^length bits*q) mod 2^(length bits) =
      source mod 2^(length bits)"
    for q :: nat
    by simp
  have lifted_admitted:
    "collatz_guarded_normalized_word_admitted bits
      (source + 2^length bits*q)"
    for q :: nat
    using collatz_guarded_word_same_residue_cylinder[
        OF lifted_residue[of q]] admitted by blast
  have lifted_endpoint:
    "collatz_guarded_normalized_word_endpoint bits
        (source + 2^length bits*q) =
      target + joint_dyadic_gain action*q"
    for q :: nat
  proof -
    have lifted_affine:
      "joint_dyadic_gain action * (source + 2^length bits*q) +
          joint_dyadic_offset action =
        2^(joint_dyadic_steps action) *
          collatz_guarded_normalized_word_endpoint
            bits (source + 2^length bits*q)"
      using collatz_guarded_word_affine_endpoint[
          OF lifted_admitted[of q]]
      by (simp add: action_def)
    have equal_products:
      "2^(length bits) *
          collatz_guarded_normalized_word_endpoint
            bits (source + 2^length bits*q) =
        2^(length bits) * (target + joint_dyadic_gain action*q)"
    proof -
      have initial:
        "2^(length bits) *
            collatz_guarded_normalized_word_endpoint
              bits (source + 2^length bits*q) =
          joint_dyadic_gain action * (source + 2^length bits*q) +
            joint_dyadic_offset action"
        using lifted_affine steps by simp
      also have "... =
          (joint_dyadic_gain action * source +
            joint_dyadic_offset action) +
            2^(length bits) * (joint_dyadic_gain action*q)"
        by (simp add: algebra_simps)
      also have "... =
          2^(length bits) * (target + joint_dyadic_gain action*q)"
        using base_nat steps by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have nonzero: "(2::nat)^(length bits) \<noteq> 0" by simp
    show ?thesis
      using equal_products nonzero by (metis mult_left_cancel)
  qed
  have affine_index:
    "(?gain * (int source + int q * ?span) + ?offset) div ?span =
      ?target + int q * ?gain"
    for q :: nat
    using integer_progression_affine_point[OF denominator base stride]
    by simp
  have actual_is_affine:
    "(\<lambda>q. int (collatz_guarded_normalized_word_endpoint
        bits (source + 2^length bits*q))) ` {..<count} =
      (\<lambda>q. (?gain * int (source + 2^length bits*q) + ?offset)
        div ?span) ` {..<count}"
  proof (rule image_cong)
    show "{..<count} = {..<count}" by simp
    fix q
    assume q_in: "q \<in> {..<count}"
    show "int (collatz_guarded_normalized_word_endpoint
        bits (source + 2^length bits*q)) =
      (?gain * int (source + 2^length bits*q) + ?offset) div ?span"
      using q_in lifted_endpoint[of q] affine_index[of q]
      by (simp add: algebra_simps)
  qed
  show ?thesis
    using actual_is_affine affine_parameterized by simp
qed

text \<open>A guarded word is composable at its actual midpoint, not at an
unrelated source with the same coarse clock.  The two block clocks add
independently: true symbols are odd events, list length is normalized
division count, and their sum is physical duration.  The endpoint clause
connects this word-level composition to the runtime's source-rooted blocks;
it does not assert a selector for future words.\<close>

theorem collatz_guarded_word_midpoint_composition:
  fixes first second :: "bool list" and source :: nat
  defines "midpoint \<equiv>
      collatz_guarded_normalized_word_endpoint first source"
  shows
    "collatz_guarded_normalized_word_admitted (first @ second) source \<longleftrightarrow>
      collatz_guarded_normalized_word_admitted first source \<and>
      collatz_guarded_normalized_word_admitted second midpoint"
    "collatz_guarded_normalized_word_endpoint (first @ second) source =
      collatz_guarded_normalized_word_endpoint second midpoint"
    "collatz_normalized_clock (first @ second) =
      (fst (collatz_normalized_clock first) +
         fst (collatz_normalized_clock second),
       snd (collatz_normalized_clock first) +
         snd (collatz_normalized_clock second))"
    "collatz_physical_ticks (first @ second) =
      collatz_physical_ticks first + collatz_physical_ticks second"
    "collatz_physical_ticks (first @ second) =
      fst (collatz_normalized_clock (first @ second)) +
      snd (collatz_normalized_clock (first @ second))"
    "collatz_guarded_normalized_word_admitted first source \<Longrightarrow>
      collatz_guarded_normalized_word_admitted second midpoint \<Longrightarrow>
      collatz_guarded_normalized_word_endpoint (first @ second) source =
        (physical_collatz ^^ collatz_physical_ticks second)
          ((physical_collatz ^^ collatz_physical_ticks first) source)"
proof -
  show "collatz_guarded_normalized_word_admitted (first @ second) source \<longleftrightarrow>
      collatz_guarded_normalized_word_admitted first source \<and>
      collatz_guarded_normalized_word_admitted second midpoint"
    by (simp add: midpoint_def collatz_guarded_normalized_word_admitted_append)
  show "collatz_guarded_normalized_word_endpoint (first @ second) source =
      collatz_guarded_normalized_word_endpoint second midpoint"
    by (simp add: midpoint_def collatz_guarded_normalized_word_endpoint_append)
  show "collatz_normalized_clock (first @ second) =
      (fst (collatz_normalized_clock first) +
         fst (collatz_normalized_clock second),
       snd (collatz_normalized_clock first) +
         snd (collatz_normalized_clock second))"
    by (simp add: collatz_normalized_clock_def count_list_append)
  show "collatz_physical_ticks (first @ second) =
      collatz_physical_ticks first + collatz_physical_ticks second"
    by (simp add: collatz_physical_ticks_def count_list_append algebra_simps)
  show "collatz_physical_ticks (first @ second) =
      fst (collatz_normalized_clock (first @ second)) +
      snd (collatz_normalized_clock (first @ second))"
    by (simp add: collatz_physical_ticks_def collatz_normalized_clock_def)
  assume first_admitted:
    "collatz_guarded_normalized_word_admitted first source"
  assume second_admitted:
    "collatz_guarded_normalized_word_admitted second midpoint"
  have midpoint_physical:
    "midpoint = (physical_collatz ^^ collatz_physical_ticks first) source"
    using collatz_guarded_normalized_word_refines_physical[OF first_admitted]
    by (simp add: midpoint_def collatz_physical_ticks_def)
  have second_physical:
    "collatz_guarded_normalized_word_endpoint second midpoint =
      (physical_collatz ^^ collatz_physical_ticks second) midpoint"
    using collatz_guarded_normalized_word_refines_physical[OF second_admitted]
    by (simp add: collatz_physical_ticks_def)
  show "collatz_guarded_normalized_word_endpoint (first @ second) source =
      (physical_collatz ^^ collatz_physical_ticks second)
        ((physical_collatz ^^ collatz_physical_ticks first) source)"
    using midpoint_physical second_physical
    by (simp add: midpoint_def collatz_guarded_normalized_word_endpoint_append)
qed

text \<open>The runtime's finite changing-tail path is not one repeated word.
Its exact selected word is the concatenation of the individually admitted
6305 returns. This induction records both normalized clocks and the summed
physical duration, then refines the complete path through the actual physical
recurrence. The selector remains responsible for proving each source guard;
the theorem only consumes the resulting exact admitted word.\<close>

definition collatz_6305_mixed_return_word :: "nat list \<Rightarrow> bool list" where
  "collatz_6305_mixed_return_word tails =
    concat (map collatz_6305_return_word tails)"

lemma collatz_6305_mixed_return_clocks:
  "collatz_normalized_clock (collatz_6305_mixed_return_word tails) =
      (2 * length tails, sum_list (map (\<lambda>j. j+2) tails))"
  "collatz_physical_ticks (collatz_6305_mixed_return_word tails) =
      sum_list (map (\<lambda>j. j+4) tails)"
proof -
  show "collatz_normalized_clock (collatz_6305_mixed_return_word tails) =
      (2 * length tails, sum_list (map (\<lambda>j. j+2) tails))"
    by (induction tails)
      (simp_all add: collatz_6305_mixed_return_word_def
        collatz_6305_return_word_def collatz_normalized_clock_def
        count_list_append algebra_simps)
  show "collatz_physical_ticks (collatz_6305_mixed_return_word tails) =
      sum_list (map (\<lambda>j. j+4) tails)"
    by (induction tails)
      (simp_all add: collatz_physical_ticks_def
        collatz_6305_mixed_return_word_def collatz_6305_return_word_def
        count_list_append algebra_simps)
qed

theorem collatz_6305_mixed_returns_refine_physical:
  assumes admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_6305_mixed_return_word tails) source"
  shows "collatz_guarded_normalized_word_endpoint
      (collatz_6305_mixed_return_word tails) source =
    (physical_collatz ^^ sum_list (map (\<lambda>j. j+4) tails)) source"
proof -
  let ?word = "collatz_6305_mixed_return_word tails"
  have word_refines:
    "collatz_guarded_normalized_word_endpoint ?word source =
      (physical_collatz ^^ (length ?word + count_list ?word True)) source"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  have duration:
    "length ?word + count_list ?word True =
      sum_list (map (\<lambda>j. j+4) tails)"
    using collatz_6305_mixed_return_clocks(2)[of tails]
    by (simp add: collatz_physical_ticks_def)
  have refinement:
    "collatz_guarded_normalized_word_endpoint
        (collatz_6305_mixed_return_word tails) source =
      (physical_collatz ^^ sum_list (map (\<lambda>j. j+4) tails)) source"
    using word_refines duration by simp
  show ?thesis
    using refinement .
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_guarded_word_endpoint_progression
      collatz_guarded_word_midpoint_composition
      collatz_6305_mixed_return_clocks
      collatz_6305_mixed_returns_refine_physical}) then ()
    else error "Guarded Collatz word progression depends on an oracle";
\<close>

end
