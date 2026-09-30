theory Prime_Prefix_Image_Projection_Refinement
  imports Prime_Python_Count_Transition_Refinement
begin

text \<open>This theory connects the checked deterministic Phi evaluator to the
zero-phase, single-forbidden-residue prefix image observed by
\<open>PrimeSuccessorActionArena.rank_before\<close>.  The semantic list is used only
for the proof: production constructs \<open>prefix(width)\<close> by binary action
composition and does not materialize these marks.\<close>

definition zero_phase_prefix_word ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "zero_phase_prefix_word parent q W =
    fresh_block_word (wheel_sift (rev parent) {1..W}) q {0} 0 W"

lemma zero_phase_prefix_word_length [simp]:
  "length (zero_phase_prefix_word parent q W) = W"
  by (simp add: zero_phase_prefix_word_def fresh_block_word_def)

theorem zero_phase_prefix_rank_exact:
  assumes stop: "stop \<le> W"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "mark_rank_before (zero_phase_prefix_word parent q W) stop =
    numerical_Phi (parent @ [q]) (Suc (length parent)) stop"
proof -
  let ?indices =
    "filter (\<lambda>i. fresh_mark (wheel_sift (rev parent) {1..W})
      q {0} 0 (Suc i)) [0..<stop]"
  have rank_indices:
      "mark_rank_before (zero_phase_prefix_word parent q W) stop =
        length ?indices"
  proof -
    have take_indices: "take stop [0..<W] = [0..<stop]"
      using stop by simp
    show ?thesis
      by (simp only: mark_rank_before_def zero_phase_prefix_word_def
          fresh_block_word_def take_map take_indices filter_map length_map
          o_def id_def)
  qed
  have distinct_indices: "distinct ?indices" by simp
  have list_card: "length ?indices = card (set ?indices)"
    using distinct_card[OF distinct_indices] by simp
  have image_card: "card (Suc ` set ?indices) = card (set ?indices)"
    by (rule card_image) simp
  have rank_card:
      "mark_rank_before (zero_phase_prefix_word parent q W) stop =
        card (Suc ` set ?indices)"
    using rank_indices list_card image_card by simp
  have q_prime: "prime q" using primes by simp
  have q_positive: "0 < q"
    using prime_gt_1_nat[OF q_prime] by simp
  have marked_set:
      "Suc ` set ?indices = wheel_sift (q # rev parent) {1..stop}"
  proof (rule Set.set_eqI)
    fix n
    show "n \<in> Suc ` set ?indices \<longleftrightarrow>
        n \<in> wheel_sift (q # rev parent) {1..stop}"
    proof (cases n)
      case 0
      then show ?thesis
        by (simp add: wheel_sift_membership)
    next
      case (Suc i)
      then show ?thesis
        using stop q_positive
        by (auto simp: fresh_mark_def wheel_sift_membership
            mod_eq_0_iff_dvd)
    qed
  qed
  have semantic:
      "numerical_Phi (parent @ [q]) (Suc (length parent)) stop =
        card (wheel_sift (q # rev parent) {1..stop})"
    by (rule fresh_successor_partial_count_semantics[OF distinct primes])
  show ?thesis using rank_card marked_set semantic by simp
qed

corollary zero_phase_prefix_rank_extension:
  assumes first: "stop \<le> W" and extension: "W \<le> W'"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "mark_rank_before (zero_phase_prefix_word parent q W) stop =
    mark_rank_before (zero_phase_prefix_word parent q W') stop"
proof -
  have later: "stop \<le> W'" using first extension by simp
  show ?thesis
    using zero_phase_prefix_rank_exact[OF first distinct primes]
      zero_phase_prefix_rank_exact[OF later distinct primes]
    by simp
qed

lemma zero_phase_prefix_rank_interval:
  assumes lower: "1 \<le> lo" and order: "lo \<le> hi"
    and cached: "hi - 1 \<le> W"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows
    "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
       mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
     card (wheel_half_open (q # rev parent) lo hi)"
proof -
  let ?full = "parent @ [q]"
  let ?high = "wheel_sift (q # rev parent) {1..hi - 1}"
  let ?low = "wheel_sift (q # rev parent) {1..lo - 1}"
  have low_cached: "lo - 1 \<le> W" using order cached by arith
  have high_rank:
      "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) =
        card ?high"
    using zero_phase_prefix_rank_exact[OF cached distinct primes]
      fresh_successor_partial_count_semantics[OF distinct primes,
        of "hi - 1"]
    by simp
  have low_rank:
      "mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
        card ?low"
    using zero_phase_prefix_rank_exact[OF low_cached distinct primes]
      fresh_successor_partial_count_semantics[OF distinct primes,
        of "lo - 1"]
    by simp
  have finite_low: "finite ?low" by (rule finite_wheel_sift) simp
  have subset: "?low \<subseteq> ?high" using order
    by (auto simp: wheel_sift_membership)
  have difference:
      "?high - ?low = wheel_half_open (q # rev parent) lo hi"
    using lower order
    by (auto simp: wheel_half_open_def wheel_sift_membership)
  show ?thesis
    using high_rank low_rank card_Diff_subset[OF finite_low subset] difference
    by simp
qed

theorem complete_prefix_cached_image_interval_exact:
  assumes prefix: "complete_prime_prefix (parent @ [q]) H"
    and lower: "2 \<le> lo"
    and order: "lo \<le> hi"
    and upper: "hi \<le> Suc H"
    and cached: "hi - 1 \<le> W"
  shows
    "card {p \<in> set (parent @ [q]). lo \<le> p \<and> p < hi} +
       (mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
        mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1)) =
     card {p. prime p \<and> lo \<le> p \<and> p < hi}"
proof -
  have nonempty: "parent @ [q] \<noteq> []" by simp
  have distinct: "distinct (parent @ [q])"
    using complete_prime_prefix_distinct_sorted[OF prefix] by simp
  have primes: "\<forall>p \<in> set (parent @ [q]). prime p"
    using complete_prime_prefix_set[OF prefix] by auto
  have rank_interval:
      "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
         mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
       card (wheel_half_open (q # rev parent) lo hi)"
    by (rule zero_phase_prefix_rank_interval)
      (use lower order cached distinct primes in auto)
  have exact:
      "card {p \<in> set (parent @ [q]). lo \<le> p \<and> p < hi} +
         card (wheel_half_open (rev (parent @ [q])) lo hi) =
       card {p. prime p \<and> lo \<le> p \<and> p < hi}"
    by (rule complete_prefix_half_open_prime_count[OF prefix nonempty lower
          order upper])
  show ?thesis using rank_interval exact by simp
qed

text \<open>The first theorem is the arithmetic observation used by
\<open>successor_action.py:496-507\<close>.  The extension corollary justifies
projecting an earlier stop from the larger image retained at
\<open>partial_successor_image.py:141-160\<close>, and the final theorem is the
two-rank-plus-known-prefix result returned at lines 163-166 when the caller
uses the whole admitted factor prefix, as \<open>select.py:267\<close> does.

The theory does not identify Python arena handles with this word, prove that
binary \<open>prefix\<close> construction preserves width, authenticate scheduler
images, or refine \<open>PrimeSuccessorActionArena.select\<close>.  It also leaves
the routine representation lemma equating Python's sorted-list
\<open>bisect_right\<close> difference with the finite descriptor cardinality to
a future source-language refinement.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms zero_phase_prefix_rank_exact zero_phase_prefix_rank_extension
      zero_phase_prefix_rank_interval
      complete_prefix_cached_image_interval_exact}) then ()
    else error "Prime prefix image projection refinement depends on an oracle";
\<close>

end
