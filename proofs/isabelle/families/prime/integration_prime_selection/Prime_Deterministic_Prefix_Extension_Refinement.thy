theory Prime_Deterministic_Prefix_Extension_Refinement
  imports Prime_Retained_Prefix_Count_Refinement
    "HOL-Library.While_Combinator"
begin

text \<open>This theory models the inner binary search at
\<open>select.py:241-250\<close>.  Its executable transition asks the same
numerical-Phi question as \<open>CoprimeRankDAG.count(mid) > 1\<close>.  The
proof derives the threshold from a retained consecutive descriptor; it does
not assume that the selected integer is prime.\<close>

record prefix_search_state =
  prefix_search_lo :: nat
  prefix_search_hi :: nat

definition prefix_search_guard :: "prefix_search_state \<Rightarrow> bool" where
  "prefix_search_guard state \<longleftrightarrow>
    prefix_search_lo state < prefix_search_hi state"

definition prefix_search_mid :: "prefix_search_state \<Rightarrow> nat" where
  "prefix_search_mid state =
    prefix_search_lo state +
      (prefix_search_hi state - prefix_search_lo state) div 2"

definition prefix_search_step ::
    "nat list \<Rightarrow> prefix_search_state \<Rightarrow> prefix_search_state" where
  "prefix_search_step ps state =
    (let mid = prefix_search_mid state
     in if 1 < numerical_Phi ps (length ps) mid
        then state\<lparr>prefix_search_hi := mid\<rparr>
        else state\<lparr>prefix_search_lo := Suc mid\<rparr>)"

definition prefix_search_loop ::
    "nat list \<Rightarrow> prefix_search_state \<Rightarrow>
      prefix_search_state option" where
  "prefix_search_loop ps state =
    while_option prefix_search_guard (prefix_search_step ps) state"

lemma prefix_search_mid_python:
  fixes lo hi :: nat
  assumes order: "lo \<le> hi"
  shows "lo + (hi - lo) div 2 = (lo + hi) div 2"
  using order by presburger

lemma consecutive_descriptor_set:
  assumes "consecutive_prime_descriptor ps"
  shows "set ps = {p. prime p \<and> p \<le> last ps}"
proof -
  from assms have retained: "ps = primes_upto (last ps)"
    by (simp add: consecutive_prime_descriptor_def)
  have "set ps = set (primes_upto (last ps))" using retained by metis
  then show ?thesis by (auto simp: set_primes_upto)
qed

lemma consecutive_descriptor_distinct:
  assumes "consecutive_prime_descriptor ps"
  shows "distinct ps"
proof -
  from assms have retained: "ps = primes_upto (last ps)"
    by (simp add: consecutive_prime_descriptor_def)
  have "distinct (primes_upto (last ps))" by simp
  with retained show ?thesis by metis
qed

lemma consecutive_descriptor_one_in_sift:
  assumes descriptor: "consecutive_prime_descriptor ps"
    and bound: "last ps \<le> x"
  shows "1 \<in> wheel_sift (rev ps) {1..x}"
proof -
  from descriptor have nonempty: "ps \<noteq> []"
    by (simp add: consecutive_prime_descriptor_def)
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty]
    by (auto simp only: prefix_set mem_Collect_eq)
  have xpos: "1 \<le> x"
    using prime_gt_1_nat[OF last_prime] bound by arith
  have avoids: "\<forall>p\<in>set ps. \<not> p dvd 1"
  proof (intro ballI)
    fix p
    assume "p \<in> set ps"
    then have "prime p" by (simp only: prefix_set mem_Collect_eq)
    then have "1 < p" by (rule prime_gt_1_nat)
    then show "\<not> p dvd 1" by auto
  qed
  show ?thesis using xpos avoids by (simp add: wheel_sift_membership)
qed

lemma consecutive_descriptor_sift_through_next:
  assumes descriptor: "consecutive_prime_descriptor ps"
  defines "q \<equiv> next_prime_after (last ps)"
  shows "wheel_sift (rev ps) {1..q} = {1, q}"
proof (rule Set.set_eqI)
  from descriptor have nonempty: "ps \<noteq> []"
    and retained: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have primes: "\<forall>p\<in>set ps. prime p"
    by (auto simp only: prefix_set mem_Collect_eq)
  have qprime: "prime q" unfolding q_def by (rule next_prime_after_prime)
  have qlast: "last ps < q" unfolding q_def by (rule next_prime_after_gt)
  have qavoids: "\<forall>p\<in>set ps. \<not> p dvd q"
  proof (intro ballI notI)
    fix p
    assume pin: "p \<in> set ps" and pdvd: "p dvd q"
    have pprime: "prime p" using primes pin by blast
    have ple: "p \<le> last ps"
      using pin by (auto simp only: prefix_set mem_Collect_eq)
    have "p = q" using pprime qprime pdvd by (metis primes_dvd_imp_eq)
    with ple qlast show False by arith
  qed
  fix n
  show "n \<in> wheel_sift (rev ps) {1..q} \<longleftrightarrow> n \<in> {1, q}"
  proof
    assume member: "n \<in> wheel_sift (rev ps) {1..q}"
    then have npos: "1 \<le> n" and nq: "n \<le> q"
      and avoids: "\<forall>p\<in>set ps. \<not> p dvd n"
      by (auto simp: wheel_sift_membership)
    show "n \<in> {1, q}"
    proof (cases "n = 1")
      case True
      then show ?thesis by simp
    next
      case False
      from prime_factor_nat[OF False] obtain p where
        pprime: "prime p" and pdvd: "p dvd n" by blast
      have npositive: "0 < n" using npos by arith
      have pn: "p \<le> n" by (rule dvd_imp_le[OF pdvd npositive])
      have last_p: "last ps < p"
      proof (rule ccontr)
        assume "\<not> last ps < p"
        then have ple: "p \<le> last ps" by arith
        have "p \<in> set ps"
          using pprime ple by (auto simp only: prefix_set mem_Collect_eq)
        with avoids pdvd show False by blast
      qed
      have "q \<le> p" unfolding q_def
        by (rule next_prime_after_least[OF pprime last_p])
      with pn nq have "n = q" by arith
      then show ?thesis by simp
    qed
  next
    assume member: "n \<in> {1, q}"
    have one_member: "1 \<in> wheel_sift (rev ps) {1..q}"
      by (rule consecutive_descriptor_one_in_sift[OF descriptor])
        (use qlast in arith)
    then show "n \<in> wheel_sift (rev ps) {1..q}"
      using member qlast qavoids
      by (auto simp: wheel_sift_membership)
  qed
qed

lemma consecutive_descriptor_phi_threshold:
  assumes descriptor: "consecutive_prime_descriptor ps"
    and above: "last ps \<le> x"
  shows "1 < numerical_Phi ps (length ps) x \<longleftrightarrow>
    next_prime_after (last ps) \<le> x"
proof -
  from descriptor have retained: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have distinct: "distinct ps"
    by (rule consecutive_descriptor_distinct[OF descriptor])
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have primes: "\<forall>p\<in>set ps. prime p"
    by (auto simp only: prefix_set mem_Collect_eq)
  have semantic:
      "numerical_Phi ps (length ps) x =
        card (wheel_sift (rev ps) {1..x})"
  proof -
    have raw:
        "numerical_Phi ps (length ps) x =
          card (wheel_sift (rev (take (length ps) ps)) {1..x})"
      by (rule numerical_Phi_is_sift_card)
        (use distinct primes in auto)
    then show ?thesis by simp
  qed
  let ?q = "next_prime_after (last ps)"
  have qlast: "last ps < ?q" by (rule next_prime_after_gt)
  have through_q: "wheel_sift (rev ps) {1..?q} = {1, ?q}"
    by (rule consecutive_descriptor_sift_through_next[OF descriptor])
  show ?thesis
  proof (cases "?q \<le> x")
    case True
    have subset:
        "wheel_sift (rev ps) {1..?q} \<subseteq> wheel_sift (rev ps) {1..x}"
      using True by (auto simp: wheel_sift_membership)
    have finite: "finite (wheel_sift (rev ps) {1..x})"
      by (rule finite_wheel_sift) simp
    have qnotone: "?q \<noteq> 1"
      using prime_gt_1_nat[OF next_prime_after_prime[of "last ps"]] by arith
    have "2 \<le> card (wheel_sift (rev ps) {1..x})"
      using card_mono[OF finite subset] through_q qnotone by simp
    with semantic True show ?thesis by arith
  next
    case False
    then have xq: "x < ?q" by simp
    have current: "wheel_sift (rev ps) {1..x} = {1}"
    proof (rule Set.set_eqI)
      fix n
      have inclusion:
          "n \<in> wheel_sift (rev ps) {1..x} \<Longrightarrow>
            n \<in> wheel_sift (rev ps) {1..?q}"
        using xq by (auto simp: wheel_sift_membership)
      show "n \<in> wheel_sift (rev ps) {1..x} \<longleftrightarrow> n \<in> {1}"
      proof
        assume member: "n \<in> wheel_sift (rev ps) {1..x}"
        have alternatives: "n = 1 \<or> n = ?q"
          using inclusion[OF member] through_q by auto
        have upper: "n \<le> x"
          using member by (auto simp: wheel_sift_membership)
        from alternatives upper xq show "n \<in> {1}" by auto
      next
        assume "n \<in> {1}"
        have one_member: "1 \<in> wheel_sift (rev ps) {1..x}"
          by (rule consecutive_descriptor_one_in_sift[OF descriptor above])
        with \<open>n \<in> {1}\<close> show
            "n \<in> wheel_sift (rev ps) {1..x}" by simp
      qed
    qed
    with semantic False show ?thesis by simp
  qed
qed

lemma consecutive_descriptor_next_prime_counts:
  assumes descriptor: "consecutive_prime_descriptor ps"
  defines "q \<equiv> next_prime_after (last ps)"
  shows "numerical_Phi ps (length ps) (q - 1) = 1"
    "numerical_Phi ps (length ps) q = 2"
proof -
  from descriptor have retained: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have distinct: "distinct ps"
    by (rule consecutive_descriptor_distinct[OF descriptor])
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have primes: "\<forall>p\<in>set ps. prime p"
    by (auto simp only: prefix_set mem_Collect_eq)
  have qlast: "last ps < q" unfolding q_def by (rule next_prime_after_gt)
  have qnotone: "q \<noteq> 1"
    unfolding q_def
    using prime_gt_1_nat[OF next_prime_after_prime[of "last ps"]] by arith
  have upto_q: "wheel_sift (rev ps) {1..q} = {1, q}"
    unfolding q_def
    by (rule consecutive_descriptor_sift_through_next[OF descriptor])
  have truncate:
      "wheel_sift (rev ps) {1..q - 1} =
        wheel_sift (rev ps) {1..q} - {q}"
    by (auto simp: wheel_sift_membership)
  have before_q: "wheel_sift (rev ps) {1..q - 1} = {1}"
  proof -
    have deletion: "{1, q} - {q} = {1}" using qnotone by auto
    show ?thesis using truncate upto_q deletion by metis
  qed
  show "numerical_Phi ps (length ps) (q - 1) = 1"
  proof -
    have raw:
        "numerical_Phi ps (length ps) (q - 1) =
          card (wheel_sift (rev (take (length ps) ps)) {1..q - 1})"
      by (rule numerical_Phi_is_sift_card)
        (use distinct primes in auto)
    then show ?thesis using before_q by simp
  qed
  show "numerical_Phi ps (length ps) q = 2"
  proof -
    have raw:
        "numerical_Phi ps (length ps) q =
          card (wheel_sift (rev (take (length ps) ps)) {1..q})"
      by (rule numerical_Phi_is_sift_card)
        (use distinct primes in auto)
    then show ?thesis using upto_q qnotone by simp
  qed
qed

definition prefix_search_invariant ::
    "nat list \<Rightarrow> nat \<Rightarrow> prefix_search_state \<Rightarrow> bool" where
  "prefix_search_invariant ps q state \<longleftrightarrow>
    consecutive_prime_descriptor ps \<and>
    q = next_prime_after (last ps) \<and>
    last ps < prefix_search_lo state \<and>
    prefix_search_lo state \<le> q \<and> q \<le> prefix_search_hi state"

lemma prefix_search_mid_bounds:
  assumes guard: "prefix_search_guard state"
  shows "prefix_search_lo state \<le> prefix_search_mid state"
    "prefix_search_mid state < prefix_search_hi state"
proof -
  let ?lo = "prefix_search_lo state"
  let ?hi = "prefix_search_hi state"
  have positive: "0 < ?hi - ?lo" using guard
    by (simp add: prefix_search_guard_def)
  show "?lo \<le> prefix_search_mid state"
    by (simp add: prefix_search_mid_def)
  have "(?hi - ?lo) div 2 < ?hi - ?lo" using positive by simp
  then show "prefix_search_mid state < ?hi"
    unfolding prefix_search_mid_def using guard
    by (simp add: prefix_search_guard_def; arith)
qed

theorem prefix_search_step_preserves_invariant:
  assumes invariant: "prefix_search_invariant ps q state"
    and guard: "prefix_search_guard state"
  shows "prefix_search_invariant ps q (prefix_search_step ps state)"
    "prefix_search_hi (prefix_search_step ps state) -
       prefix_search_lo (prefix_search_step ps state) <
     prefix_search_hi state - prefix_search_lo state"
proof -
  let ?mid = "prefix_search_mid state"
  from invariant have descriptor: "consecutive_prime_descriptor ps"
    and q: "q = next_prime_after (last ps)"
    and last_lo: "last ps < prefix_search_lo state"
    and lo_q: "prefix_search_lo state \<le> q"
    and q_hi: "q \<le> prefix_search_hi state"
    by (auto simp: prefix_search_invariant_def)
  note bounds = prefix_search_mid_bounds[OF guard]
  have last_mid: "last ps < ?mid" using last_lo bounds(1) by arith
  have last_mid_le: "last ps \<le> ?mid" by (rule less_imp_le[OF last_mid])
  have threshold:
      "1 < numerical_Phi ps (length ps) ?mid \<longleftrightarrow> q \<le> ?mid"
    using consecutive_descriptor_phi_threshold[OF descriptor last_mid_le] q by simp
  show "prefix_search_invariant ps q (prefix_search_step ps state)"
    using descriptor q last_lo lo_q q_hi bounds threshold
    by (auto simp: prefix_search_invariant_def prefix_search_step_def Let_def)
  show "prefix_search_hi (prefix_search_step ps state) -
       prefix_search_lo (prefix_search_step ps state) <
     prefix_search_hi state - prefix_search_lo state"
    using bounds guard
    by (auto simp: prefix_search_step_def Let_def prefix_search_guard_def)
qed

theorem prefix_search_loop_terminates:
  assumes invariant: "prefix_search_invariant ps q initial"
  shows "\<exists>final. prefix_search_loop ps initial = Some final"
  unfolding prefix_search_loop_def
  by (rule measure_while_option_Some[
        where P="prefix_search_invariant ps q"
          and f="\<lambda>state. prefix_search_hi state - prefix_search_lo state"])
    (use prefix_search_step_preserves_invariant invariant in blast)+

theorem prefix_search_loop_returns_next_prime:
  assumes invariant: "prefix_search_invariant ps q initial"
    and result: "prefix_search_loop ps initial = Some final"
  shows "prefix_search_lo final = q" "prefix_search_hi final = q"
proof -
  have loop:
      "while_option prefix_search_guard (prefix_search_step ps) initial =
        Some final"
    using result unfolding prefix_search_loop_def .
  have preserved: "prefix_search_invariant ps q final"
    by (rule while_option_rule[
          where P="prefix_search_invariant ps q"
            and b=prefix_search_guard and c="prefix_search_step ps"
            and s=initial and t=final,
          OF _ loop invariant])
      (use prefix_search_step_preserves_invariant in blast)
  have stopped: "\<not> prefix_search_guard final"
    by (rule while_option_stop[OF loop])
  from preserved have "prefix_search_lo final \<le> q"
    "q \<le> prefix_search_hi final"
    by (auto simp: prefix_search_invariant_def)
  moreover from stopped have
      "prefix_search_hi final \<le> prefix_search_lo final"
    by (simp add: prefix_search_guard_def)
  ultimately show "prefix_search_lo final = q" "prefix_search_hi final = q"
    by arith+
qed

theorem deterministic_prefix_extension_step:
  fixes root :: nat
  assumes descriptor: "consecutive_prime_descriptor ps"
    and root_count: "numerical_Phi ps (length ps) root \<noteq> 1"
    and root_above: "last ps < root"
  defines "q \<equiv> next_prime_after (last ps)"
    and "initial \<equiv>
      \<lparr>prefix_search_lo = Suc (last ps), prefix_search_hi = root\<rparr>"
  shows "\<exists>final.
      prefix_search_loop ps initial = Some final \<and>
      prefix_search_lo final = q \<and>
      prefix_search_hi final = q \<and>
      ps @ [q] = primes_upto q \<and>
      numerical_Phi ps (length ps) (q - 1) = 1 \<and>
      numerical_Phi ps (length ps) q = 2"
proof -
  have root_positive: "1 \<le> numerical_Phi ps (length ps) root"
  proof -
    from descriptor have retained: "ps = primes_upto (last ps)"
      by (auto simp: consecutive_prime_descriptor_def)
    have distinct: "distinct ps"
      by (rule consecutive_descriptor_distinct[OF descriptor])
    have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
      by (rule consecutive_descriptor_set[OF descriptor])
    have primes: "\<forall>p\<in>set ps. prime p"
      by (auto simp only: prefix_set mem_Collect_eq)
    have semantic:
        "numerical_Phi ps (length ps) root =
          card (wheel_sift (rev ps) {1..root})"
    proof -
      have raw:
          "numerical_Phi ps (length ps) root =
            card (wheel_sift (rev (take (length ps) ps)) {1..root})"
        by (rule numerical_Phi_is_sift_card)
          (use distinct primes in auto)
      then show ?thesis by simp
    qed
    have one_member: "1 \<in> wheel_sift (rev ps) {1..root}"
      by (rule consecutive_descriptor_one_in_sift[OF descriptor])
        (use root_above in arith)
    have finite: "finite (wheel_sift (rev ps) {1..root})"
      by (rule finite_wheel_sift) simp
    have nonempty: "wheel_sift (rev ps) {1..root} \<noteq> {}"
      using one_member by auto
    have card_positive: "0 < card (wheel_sift (rev ps) {1..root})"
      using finite nonempty by (simp add: card_gt_0_iff)
    show ?thesis using semantic card_positive by arith
  qed
  have root_more: "1 < numerical_Phi ps (length ps) root"
    using root_count root_positive by arith
  have root_above_le: "last ps \<le> root"
    by (rule less_imp_le[OF root_above])
  have q_root: "q \<le> root"
    using consecutive_descriptor_phi_threshold[OF descriptor root_above_le]
      root_more unfolding q_def by simp
  have last_q: "last ps < q"
    unfolding q_def by (rule next_prime_after_gt[of "last ps"])
  have initial_invariant: "prefix_search_invariant ps q initial"
    using descriptor q_root last_q
    unfolding prefix_search_invariant_def initial_def q_def by simp
  from prefix_search_loop_terminates[OF initial_invariant]
  obtain final where loop: "prefix_search_loop ps initial = Some final" by blast
  note selected = prefix_search_loop_returns_next_prime[OF initial_invariant loop]
  have appended: "ps @ [q] = primes_upto q"
    by (rule append_next_prime_preserves_consecutive_descriptor[OF descriptor,
          folded q_def])
  note counts = consecutive_descriptor_next_prime_counts[OF descriptor,
      folded q_def]
  show ?thesis using loop selected appended counts by blast
qed

theorem deterministic_prefix_discovery_stop:
  fixes root :: nat
  assumes descriptor: "consecutive_prime_descriptor ps"
    and covered: "last ps \<le> root"
    and stopped: "numerical_Phi ps (length ps) root = 1"
  shows "ps = primes_upto root"
proof -
  from descriptor have nonempty: "ps \<noteq> []"
    and retained: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have sorted: "sorted ps"
  proof -
    have "sorted (primes_upto (last ps))" by simp
    with retained show ?thesis by metis
  qed
  have distinct: "distinct ps"
    by (rule consecutive_descriptor_distinct[OF descriptor])
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have primes: "\<forall>p\<in>set ps. prime p"
    by (auto simp only: prefix_set mem_Collect_eq)
  have root_positive: "0 < root"
  proof -
    have last_prime: "prime (last ps)"
      using last_in_set[OF nonempty] primes by blast
    have "1 < last ps" by (rule prime_gt_1_nat[OF last_prime])
    with covered show ?thesis by arith
  qed
  have bounded: "\<forall>p\<in>set ps. p \<le> root"
    using prefix_set covered by auto
  have sound: "sound_prime_descriptor ps root"
    using sorted distinct primes bounded
    by (auto simp: sound_prime_descriptor_def)
  have semantic:
      "numerical_Phi ps (length ps) root =
        card (wheel_sift ps {1..root})"
  proof -
    have rev_same:
        "wheel_sift (rev ps) {1..root} = wheel_sift ps {1..root}"
      by (auto simp: wheel_sift_membership)
    show ?thesis
      by (subst numerical_Phi_is_sift_card)
        (use distinct primes rev_same in auto)
  qed
  have admission: "discovery_stopped ps root"
    using sound root_positive stopped semantic
    by (simp add: discovery_stopped_def)
  show ?thesis by (rule discovery_stop_constructs_complete_prefix[OF admission])
qed

text \<open>The bounded phase-lane selector inspects odd candidates after the
last authenticated factor and tests only old prime lanes whose square does
not exceed the candidate.  This is sound up to the square of the current
prefix endpoint: any composite candidate has a prime divisor no larger than
its square root, hence inside the authenticated consecutive prefix.  The
square bound is a guard for this shortcut, not a bound on prime gaps or a
claim that every requested root is covered by it.\<close>

theorem consecutive_descriptor_phase_lane_candidate_prime:
  assumes descriptor: "consecutive_prime_descriptor ps"
      and above: "last ps < candidate"
      and square_bound: "candidate \<le> (last ps)^2"
      and lanes: "\<forall>p\<in>set ps. p^2 \<le> candidate \<longrightarrow>
        \<not> p dvd candidate"
  shows "prime candidate"
proof -
  have prefix_set:
    "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have nonempty: "ps \<noteq> []"
    using descriptor by (simp add: consecutive_prime_descriptor_def)
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty] prefix_set by auto
  have last_lower: "2 \<le> last ps"
    using prime_gt_1_nat[OF last_prime] by arith
  have candidate_nontrivial: "candidate \<noteq> 0" "candidate \<noteq> 1"
    using above last_lower by arith+
  have no_small_prime_divisor:
    "\<nexists>p. prime p \<and> p dvd candidate \<and> p^2 \<le> candidate"
  proof
    assume "\<exists>p. prime p \<and> p dvd candidate \<and> p^2 \<le> candidate"
    then obtain p where p_prime: "prime p"
      and p_divides: "p dvd candidate"
      and p_small: "p^2 \<le> candidate" by blast
    have p_square_bound: "p^2 \<le> (last ps)^2"
      by (rule order_trans[OF p_small square_bound])
    have p_le_last: "p \<le> last ps"
      using power_le_imp_le_base[of p 1 "last ps"] p_square_bound by simp
    have p_member: "p \<in> set ps"
      using p_prime p_le_last prefix_set by blast
    show False using lanes[rule_format, OF p_member] p_small p_divides by blast
  qed
  have candidate_criterion:
    "prime candidate \<longleftrightarrow>
      candidate \<noteq> 0 \<and> candidate \<noteq> 1 \<and>
      (\<not> (\<exists>p. prime p \<and> p dvd candidate \<and> p^2 \<le> candidate))"
    by (rule prime_prime_factor_sqrt)
  show ?thesis
    using candidate_criterion candidate_nontrivial no_small_prime_divisor
    by blast
qed

lemma consecutive_descriptor_bounded_lane_rejection_iff:
  assumes descriptor: "consecutive_prime_descriptor ps"
      and above: "last ps < n"
      and square_bound: "n \<le> (last ps)^2"
  shows "n \<notin> wheel_sift (rev ps) {1..n} \<longleftrightarrow>
    (\<exists>p. p \<in> set ps \<and> p^2 \<le> n \<and> p dvd n)"
proof -
  have prefix_set:
    "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have nonempty: "ps \<noteq> []"
    using descriptor by (simp add: consecutive_prime_descriptor_def)
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty] prefix_set by auto
  have last_lower: "2 \<le> last ps"
    using prime_gt_1_nat[OF last_prime] by arith
  have n_gt_one: "1 < n" using above last_lower by arith
  show ?thesis
  proof
    assume rejected: "n \<notin> wheel_sift (rev ps) {1..n}"
    have some_lane:
      "\<exists>p. p \<in> set ps \<and> p dvd n"
      using rejected n_gt_one
      by (auto simp: wheel_sift_membership)
    then obtain p where p_member: "p \<in> set ps" and p_divides: "p dvd n"
      by blast
    have p_prime: "prime p" and p_le_last: "p \<le> last ps"
      using prefix_set p_member by auto
    have p_below_n: "p < n" using p_le_last above by arith
    have n_not_prime: "\<not> prime n"
    proof
      assume n_prime: "prime n"
      have p_eq_n: "p = n"
        by (rule primes_dvd_imp_eq[OF p_prime n_prime p_divides])
      with p_below_n show False by arith
    qed
    have n_criterion:
      "prime n \<longleftrightarrow>
        n \<noteq> 0 \<and> n \<noteq> 1 \<and>
        (\<not> (\<exists>q. prime q \<and> q dvd n \<and> q^2 \<le> n))"
      by (rule prime_prime_factor_sqrt)
    have n_nontrivial: "n \<noteq> 0" "n \<noteq> 1"
      using n_gt_one by arith+
    have small_lane:
      "\<exists>q. prime q \<and> q dvd n \<and> q^2 \<le> n"
      using n_criterion n_nontrivial n_not_prime by blast
    then obtain q where q_prime: "prime q" and q_divides: "q dvd n"
      and q_small: "q^2 \<le> n" by blast
    have q_square_bound: "q^2 \<le> (last ps)^2"
      by (rule order_trans[OF q_small square_bound])
    have q_le_last: "q \<le> last ps"
      using power_le_imp_le_base[of q 1 "last ps"] q_square_bound by simp
    have q_member: "q \<in> set ps"
      using prefix_set q_prime q_le_last by blast
    show "\<exists>p. p \<in> set ps \<and> p^2 \<le> n \<and> p dvd n"
      using q_member q_small q_divides by blast
  next
    assume "\<exists>p. p \<in> set ps \<and> p^2 \<le> n \<and> p dvd n"
    then obtain p where "p \<in> set ps" and "p dvd n" by blast
    then show "n \<notin> wheel_sift (rev ps) {1..n}"
      using n_gt_one by (auto simp: wheel_sift_membership)
  qed
qed

theorem consecutive_descriptor_first_odd_lane_candidate_is_next_prime:
  assumes descriptor: "consecutive_prime_descriptor ps"
      and above: "last ps < candidate"
      and square_bound: "candidate \<le> (last ps)^2"
      and lanes: "\<forall>p\<in>set ps. p^2 \<le> candidate \<longrightarrow>
        \<not> p dvd candidate"
      and intervening_rejected: "\<forall>n. last ps < n \<and> n < candidate \<and>
        odd n \<longrightarrow> n \<notin> wheel_sift (rev ps) {1..n}"
  shows "candidate = next_prime_after (last ps)"
proof -
  have candidate_prime:
    "prime candidate"
    by (rule consecutive_descriptor_phase_lane_candidate_prime
      [OF descriptor above square_bound lanes])
  have next_prime: "prime (next_prime_after (last ps))"
    by (rule next_prime_after_prime)
  have next_after_last: "last ps < next_prime_after (last ps)"
    by (rule next_prime_after_gt)
  have next_le_candidate: "next_prime_after (last ps) \<le> candidate"
    by (rule next_prime_after_least[OF candidate_prime above])
  have nonempty: "ps \<noteq> []"
    using descriptor by (simp add: consecutive_prime_descriptor_def)
  have prefix_set:
    "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty] prefix_set by auto
  have last_lower: "2 \<le> last ps"
    using prime_gt_1_nat[OF last_prime] by arith
  have next_odd: "odd (next_prime_after (last ps))"
    by (rule prime_odd_nat[OF next_prime])
      (use next_after_last last_lower in arith)
  have candidate_le_next:
    "candidate \<le> next_prime_after (last ps)"
  proof (rule ccontr)
    assume "\<not> candidate \<le> next_prime_after (last ps)"
    then have next_before: "next_prime_after (last ps) < candidate" by simp
    have next_rejected:
      "next_prime_after (last ps) \<notin>
        wheel_sift (rev ps) {1..next_prime_after (last ps)}"
      using intervening_rejected[rule_format, of "next_prime_after (last ps)"]
        next_after_last next_before next_odd by blast
    have next_survives:
      "next_prime_after (last ps) \<in>
        wheel_sift (rev ps) {1..next_prime_after (last ps)}"
    proof -
      have next_sift:
        "wheel_sift (rev ps) {1..next_prime_after (last ps)} =
          {1, next_prime_after (last ps)}"
        by (rule consecutive_descriptor_sift_through_next[OF descriptor])
      have next_not_one: "next_prime_after (last ps) \<noteq> 1"
        using prime_gt_1_nat[OF next_prime] by arith
      show ?thesis using next_sift next_not_one by simp
    qed
    from next_rejected next_survives show False by contradiction
  qed
  show ?thesis using candidate_le_next next_le_candidate by simp
qed

theorem consecutive_descriptor_phase_lane_exhaustion_is_exact:
  fixes root :: nat
  assumes descriptor: "consecutive_prime_descriptor ps"
      and root_above: "last ps < root"
      and square_bound: "root \<le> (last ps)^2"
      and rejected: "\<forall>candidate. last ps < candidate \<and>
        candidate \<le> root \<and> odd candidate \<longrightarrow>
        candidate \<notin> wheel_sift (rev ps) {1..candidate}"
  shows "root < next_prime_after (last ps)"
proof -
  have next_prime: "prime (next_prime_after (last ps))"
    by (rule next_prime_after_prime)
  have next_after_last: "last ps < next_prime_after (last ps)"
    by (rule next_prime_after_gt)
  have nonempty: "ps \<noteq> []"
    using descriptor by (simp add: consecutive_prime_descriptor_def)
  have prefix_set:
    "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty] prefix_set by auto
  have last_lower: "2 \<le> last ps"
    using prime_gt_1_nat[OF last_prime] by arith
  have next_odd: "odd (next_prime_after (last ps))"
    by (rule prime_odd_nat[OF next_prime])
      (use next_after_last last_lower in arith)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> root < next_prime_after (last ps)"
    then have next_le_root: "next_prime_after (last ps) \<le> root" by simp
    have next_le_square:
      "next_prime_after (last ps) \<le> (last ps)^2"
      by (rule order_trans[OF next_le_root square_bound])
    have next_rejected:
      "next_prime_after (last ps) \<notin>
        wheel_sift (rev ps) {1..next_prime_after (last ps)}"
      using rejected[rule_format, of "next_prime_after (last ps)"]
        next_after_last next_le_root next_odd by blast
    have next_survives:
      "next_prime_after (last ps) \<in>
        wheel_sift (rev ps) {1..next_prime_after (last ps)}"
    proof -
      have next_sift:
        "wheel_sift (rev ps) {1..next_prime_after (last ps)} =
          {1, next_prime_after (last ps)}"
        by (rule consecutive_descriptor_sift_through_next[OF descriptor])
      have next_not_one: "next_prime_after (last ps) \<noteq> 1"
        using prime_gt_1_nat[OF next_prime] by arith
      show ?thesis using next_sift next_not_one by simp
    qed
    from next_rejected next_survives show False by contradiction
  qed
qed

text \<open>The exported theorem maps the exact Python branch entered after
\<open>count(root) != 1\<close>: initial bounds are \<open>last_factor + 1\<close>
and \<open>root\<close>, midpoint selection uses the same floor average, and the
predicate is the actual numerical-Phi count.  It proves finite termination at
the mathematical next prime, preservation of the consecutive descriptor after
\<open>append_consecutive_factor\<close>, and the two count equalities checked by
\<open>validate_fresh_successor\<close>.  The stopping theorem maps the other
outer-loop branch: count one at the covered root yields exactly
\<open>primes_upto root\<close>, rather than assuming coverage as its result.

The theorem assumes the entering Python factor arena already denotes a
consecutive descriptor and that each \<open>count\<close> call returns
\<open>numerical_Phi\<close>.  Existing downstream theories prove the pure
cache-pruned count transition, but this file does not identify Python object
authority, exceptions, work charges or shared-cache reads with the formal
state.  The downstream \<open>Prime_Deterministic_Cover_Loop_Refinement\<close>
composes these checked steps through the repeated outer loop.  Committed
\<open>covered_root\<close> publication remains a separate executable trace
obligation.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms prefix_search_mid_python consecutive_descriptor_set
      consecutive_descriptor_distinct consecutive_descriptor_one_in_sift
      consecutive_descriptor_phi_threshold
      consecutive_descriptor_next_prime_counts
      prefix_search_step_preserves_invariant prefix_search_loop_terminates
      prefix_search_loop_returns_next_prime
      consecutive_descriptor_phase_lane_candidate_prime
      consecutive_descriptor_bounded_lane_rejection_iff
      consecutive_descriptor_first_odd_lane_candidate_is_next_prime
      consecutive_descriptor_phase_lane_exhaustion_is_exact
      deterministic_prefix_extension_step
      deterministic_prefix_discovery_stop}) then ()
    else error "Deterministic prime prefix extension depends on an oracle";
\<close>

end
