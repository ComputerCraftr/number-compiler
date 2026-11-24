theory Collatz_Guarded_Word_Progression
  imports Collatz_Skew_Cylinder_Temporal_Squaring
    "Shared_S_Arithmetic.Integer_Cylinder_Transport"
    "Shared_Carry_Dynamics.Ordered_Matrix_Program_Algebra"
begin

text \<open>Bounded image and full-stride refinement for an already admitted
normalized parity word. This consumer theorem is separate from the core
skew-cylinder squaring algebra.\<close>

theorem collatz_cyclic_source_consumer:
  assumes source_word:
    "bits = dyadic_source_word collatz_temporal_source_step odd source (length bits)"
    and defect:
      "(2::int)^(repetitions * length bits) dvd
        collatz_temporal_word_defect bits source"
  defines "word \<equiv> concat (replicate repetitions bits)"
  shows "collatz_guarded_normalized_word_admitted word source"
    "collatz_guarded_normalized_word_endpoint word source =
      (physical_collatz ^^ (repetitions * collatz_physical_ticks bits)) source"
    "collatz_normalized_clock word =
      (repetitions * count_list bits True, repetitions * length bits)"
proof -
  have initial: "collatz_guarded_normalized_word_admitted bits source"
    using source_word collatz_guarded_word_admitted_iff_temporal_word by blast
  have repeated: "collatz_guarded_normalized_word_admitted word source"
    using collatz_guarded_word_repetition_dyadic_cylinder[OF initial]
      defect by (simp add: word_def)
  show "collatz_guarded_normalized_word_admitted word source"
    by (rule repeated)
  have physical:
    "collatz_guarded_normalized_word_endpoint word source =
      (physical_collatz ^^ collatz_physical_ticks word) source"
    using collatz_guarded_normalized_word_refines_physical[OF repeated]
    by (simp add: collatz_physical_ticks_def)
  show "collatz_guarded_normalized_word_endpoint word source =
      (physical_collatz ^^ (repetitions * collatz_physical_ticks bits)) source"
    using physical collatz_repeated_word_clock(2)[of repetitions bits]
    by (simp add: word_def)
  show "collatz_normalized_clock word =
      (repetitions * count_list bits True, repetitions * length bits)"
    using collatz_repeated_word_clock(1)[of repetitions bits]
    by (simp add: word_def)
qed

theorem collatz_canonical_rotation_source_consumer:
  fixes bits received word :: "bool list" and rotation phase repetitions source :: nat
  assumes nonempty: "bits \<noteq> []"
    and source_word:
      "bits = dyadic_source_word collatz_temporal_source_step odd source (length bits)"
    and defect:
      "(2::int)^(repetitions * length bits) dvd
        collatz_temporal_word_defect bits source"
  defines "phase \<equiv> (length bits - rotation mod length bits) mod length bits"
    and "received \<equiv> rotate phase (rotate rotation bits)"
    and "word \<equiv> concat (replicate repetitions received)"
  shows "collatz_guarded_normalized_word_admitted word source"
    "collatz_guarded_normalized_word_endpoint word source =
      (physical_collatz ^^ (repetitions * collatz_physical_ticks bits)) source"
    "collatz_normalized_clock word =
      (repetitions * count_list bits True, repetitions * length bits)"
proof -
  have receiving: "received = bits"
    using ordered_rotation_entry_phase[where word=bits and rotation=rotation, OF nonempty]
    by (simp only: received_def phase_def)
  show "collatz_guarded_normalized_word_admitted word source"
    using collatz_cyclic_source_consumer(1)[OF source_word defect] receiving
    by (simp add: word_def)
  show "collatz_guarded_normalized_word_endpoint word source =
      (physical_collatz ^^ (repetitions * collatz_physical_ticks bits)) source"
    using collatz_cyclic_source_consumer(2)[OF source_word defect] receiving
    by (simp add: word_def)
  show "collatz_normalized_clock word =
      (repetitions * count_list bits True, repetitions * length bits)"
    using collatz_cyclic_source_consumer(3)[OF source_word defect] receiving
    by (simp add: word_def)
qed

theorem collatz_cyclic_rotated_defect_source_step:
  fixes source :: nat and delta offset next_offset :: int
  assumes offset_transport:
    "2 * next_offset =
      (if odd source then 3 else 1) * offset -
        delta * (if odd source then 1 else 0)"
  shows "2 * (delta * int (collatz_temporal_source_step source) + next_offset) =
    (if odd source then 3 else 1) * (delta * int source + offset)"
proof (cases "odd source")
  case True
  then obtain q where source: "source = 2*q+1" by (rule oddE)
  have step: "collatz_temporal_source_step source = 3*q+2"
    using source by (simp add: collatz_temporal_source_step_def)
  have transport: "2 * next_offset = 3 * offset - delta"
    using True offset_transport by simp
  have source_eq: "2 * int (collatz_temporal_source_step source) = 3 * int source + 1"
    using source step by simp
  have scaled:
    "2 * (delta * int (collatz_temporal_source_step source)) =
      delta * (3 * int source + 1)"
    using source_eq by (simp only: mult.left_commute)
  have branch: "(if odd source then (3::int) else 1) = 3" using True by simp
  have "2 * (delta * int (collatz_temporal_source_step source) + next_offset) =
      (2 * (delta * int (collatz_temporal_source_step source))) + 2 * next_offset"
    by (rule distrib_left)
  also have "... = delta * (3 * int source + 1) + (3 * offset - delta)"
    by (simp only: scaled transport)
  also have "... = 3 * (delta * int source + offset)"
    by (simp add: algebra_simps)
  finally show ?thesis by (simp only: branch)
next
  case False
  then have "even source" by simp
  then obtain q where source: "source = 2*q" by (rule evenE)
  have step: "collatz_temporal_source_step source = q"
    using source by (simp add: collatz_temporal_source_step_def)
  have transport: "2 * next_offset = offset"
    using False offset_transport by simp
  have source_eq: "2 * int (collatz_temporal_source_step source) = int source"
    using source step by simp
  have scaled:
    "2 * (delta * int (collatz_temporal_source_step source)) = delta * int source"
    using source_eq by (simp only: mult.left_commute)
  have branch: "(if odd source then (3::int) else 1) = 1" using False by simp
  have "2 * (delta * int (collatz_temporal_source_step source) + next_offset) =
      (2 * (delta * int (collatz_temporal_source_step source))) + 2 * next_offset"
    by (rule distrib_left)
  also have "... = delta * int source + offset" by (simp only: scaled transport)
  finally show ?thesis by (simp only: branch mult_1)
qed

theorem collatz_guarded_moving_cut_numerator:
  fixes bits :: "bool list"
  defines "action \<equiv> collatz_joint_dyadic_word bits"
  shows "(joint_dyadic_gain action * (high * 2^cut + low) +
      joint_dyadic_offset action) div 2^cut =
    joint_dyadic_gain action * high +
      (joint_dyadic_gain action * low + joint_dyadic_offset action) div 2^cut"
proof -
  have reordered:
    "joint_dyadic_gain action * (high * 2^cut + low) +
      joint_dyadic_offset action =
    (joint_dyadic_gain action * low + joint_dyadic_offset action) +
      (joint_dyadic_gain action * high) * 2^cut"
    by (simp add: algebra_simps)
  show ?thesis by (simp add: reordered)
qed

text \<open>A repeated admitted motif has an increasing affine endpoint.
Each physical phase, including the odd intermediate value, is increasing in
the motif inlet. Its width therefore attains its bounds at the first and
last complete copy. The tail remains an independently admitted prefix.\<close>

theorem collatz_cyclic_phase_extrema:
  fixes action observe :: "nat \<Rightarrow> nat"
  assumes action_mono: "mono action"
    and observe_mono: "mono observe"
    and index: "i \<le> n"
  shows "min (observe source) (observe ((action ^^ n) source))
      \<le> observe ((action ^^ i) source) \<and>
      observe ((action ^^ i) source)
      \<le> max (observe source) (observe ((action ^^ n) source))"
proof (cases "source \<le> action source")
  case True
  have low: "source \<le> (action ^^ i) source"
    using funpow_mono2[OF action_mono, of 0 i source source] True by simp
  have high: "(action ^^ i) source \<le> (action ^^ n) source"
    by (rule funpow_mono2[OF action_mono index order_refl True])
  have observed_low: "observe source \<le> observe ((action ^^ i) source)"
    by (rule monoD[OF observe_mono low])
  have observed_high: "observe ((action ^^ i) source) \<le> observe ((action ^^ n) source)"
    by (rule monoD[OF observe_mono high])
  show ?thesis using observed_low observed_high by auto
next
  case False
  have first: "action source \<le> source" using False by simp
  have step: "(action ^^ Suc k) source \<le> (action ^^ k) source" for k
    using funpow_mono[OF action_mono first, of k]
    by (simp only: funpow_Suc_right comp_apply)
  have downward: "(action ^^ n) source \<le> (action ^^ i) source"
    if "i \<le> n" for i n
    using that
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    show ?case
    proof (cases "i = Suc n")
      case True
      then show ?thesis by simp
    next
      case False
      have bound: "i \<le> n" using Suc.prems False by simp
      have descent: "(action ^^ n) source \<le> (action ^^ i) source"
        by (rule Suc.IH[OF bound])
      show ?thesis by (rule order_trans[OF step[of n] descent])
    qed
  qed
  have low: "(action ^^ n) source \<le> (action ^^ i) source"
    using downward[OF index] .
  have high: "(action ^^ i) source \<le> source"
    using downward[of 0 i] by simp
  have observed_low: "observe ((action ^^ n) source) \<le> observe ((action ^^ i) source)"
    by (rule monoD[OF observe_mono low])
  have observed_high: "observe ((action ^^ i) source) \<le> observe source"
    by (rule monoD[OF observe_mono high])
  show ?thesis using observed_low observed_high by auto
qed

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

theorem collatz_witness_then_cyclic_source_consumer:
  assumes witness: "seam = (physical_collatz ^^ prefix_ticks) seed"
    and source_word:
      "bits = dyadic_source_word collatz_temporal_source_step odd seam (length bits)"
    and defect:
      "(2::int)^(repetitions * length bits) dvd
        collatz_temporal_word_defect bits seam"
  shows "collatz_guarded_normalized_word_endpoint
      (concat (replicate repetitions bits)) seam =
    (physical_collatz ^^ (prefix_ticks +
      repetitions * collatz_physical_ticks bits)) seed"
    "collatz_normalized_clock (concat (replicate repetitions bits)) =
      (repetitions * count_list bits True, repetitions * length bits)"
proof -
  let ?duration = "repetitions * collatz_physical_ticks bits"
  have transport:
    "(physical_collatz ^^ ?duration) ((physical_collatz ^^ prefix_ticks) seed) =
      (physical_collatz ^^ (prefix_ticks + ?duration)) seed"
  proof -
    have "(physical_collatz ^^ ?duration) ((physical_collatz ^^ prefix_ticks) seed) =
        (physical_collatz ^^ (?duration + prefix_ticks)) seed"
      by (simp only: funpow_add comp_apply)
    then show ?thesis by (simp only: add.commute)
  qed
  show "collatz_guarded_normalized_word_endpoint
      (concat (replicate repetitions bits)) seam =
    (physical_collatz ^^ (prefix_ticks + ?duration)) seed"
    using collatz_cyclic_source_consumer(2)[OF source_word defect] witness transport
    by simp
  show "collatz_normalized_clock (concat (replicate repetitions bits)) =
      (repetitions * count_list bits True, repetitions * length bits)"
    by (rule collatz_cyclic_source_consumer(3)[OF source_word defect])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_cyclic_phase_extrema collatz_cyclic_rotated_defect_source_step
      collatz_guarded_moving_cut_numerator
      collatz_guarded_word_endpoint_progression
      collatz_cyclic_source_consumer collatz_canonical_rotation_source_consumer
      collatz_witness_then_cyclic_source_consumer
      collatz_guarded_word_midpoint_composition
      collatz_6305_mixed_return_clocks
      collatz_6305_mixed_returns_refine_physical}) then ()
    else error "Guarded Collatz word progression depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof
    @{thms collatz_witness_then_cyclic_source_consumer}
    then error "Skipped Collatz witness continuation proof" else ();
\<close>

end
