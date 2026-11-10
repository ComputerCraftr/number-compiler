theory Prime_Birth_Innovation_Refinement
  imports Prime_Deterministic_Phi_Refinement Prime_Prefix_Image_Projection_Refinement
begin

text \<open>A fixed-boundary suffix of admitted primes removes only the primes
themselves once the square-root prefix has removed every composite. The
boundary remains a parameter: this does not identify ranks at different
boundaries or authenticate an arbitrary factor descriptor.\<close>

lemma complete_prefix_positive_survivor:
  assumes prefix: "complete_prime_prefix core x"
    and member: "n \<in> wheel_sift core {1..x}"
  shows "n=1 \<or> prime n"
proof (rule ccontr)
  assume neither: "\<not> (n=1 \<or> prime n)"
  have bounds: "1<n" "n\<le>x"
    using member neither by (auto simp: wheel_sift_membership)
  have divisor: "\<exists>p\<in>set core. p dvd n"
    by (rule complete_prefix_prime_divisor[OF prefix bounds]) (use neither in auto)
  show False using member divisor by (auto simp: wheel_sift_membership)
qed

lemma prime_birth_suffix_sift:
  assumes prefix: "complete_prime_prefix core x"
    and primes: "\<forall>p\<in>set suffix. prime p"
  shows "wheel_sift (core@suffix) {1..x} =
    wheel_sift core {1..x} - {p\<in>set suffix. p\<le>x}"
proof (rule set_eqI)
  fix n
  show "n\<in>wheel_sift (core@suffix) {1..x} \<longleftrightarrow>
      n\<in>wheel_sift core {1..x} - {p\<in>set suffix. p\<le>x}"
  proof
    assume "n\<in>wheel_sift (core@suffix) {1..x}"
    then show "n\<in>wheel_sift core {1..x} - {p\<in>set suffix. p\<le>x}"
      by (auto simp: wheel_sift_membership; blast intro: dvd_refl)
  next
    assume remaining:
      "n\<in>wheel_sift core {1..x} - {p\<in>set suffix. p\<le>x}"
    have member: "n\<in>wheel_sift core {1..x}" using remaining by simp
    have kind: "n=1 \<or> prime n"
      by (rule complete_prefix_positive_survivor[OF prefix member])
    have avoids: "\<forall>p\<in>set suffix. \<not> p dvd n"
    proof (intro ballI notI)
      fix p
      assume pin: "p\<in>set suffix" and divides: "p dvd n"
      have pp: "prime p" using primes pin by simp
      have "p=n"
      proof (cases "n=1")
        case True
        have "p=1" using divides True by simp
        then show ?thesis using prime_gt_1_nat[OF pp] by simp
      next
        case False
        have pn: "prime n" using kind False by simp
        show ?thesis by (rule primes_dvd_imp_eq[OF pp pn divides])
      qed
      then show False using remaining pin member
        by (auto simp: wheel_sift_membership)
    qed
    show "n\<in>wheel_sift (core@suffix) {1..x}"
      using member avoids by (auto simp: wheel_sift_membership)
  qed
qed

lemma prime_birth_suffix_survives_core:
  assumes prefix: "complete_prime_prefix core x"
    and primes: "\<forall>p\<in>set suffix. prime p"
    and disjoint: "set core \<inter> set suffix = {}"
  shows "{p\<in>set suffix. p\<le>x} \<subseteq> wheel_sift core {1..x}"
proof
  fix p
  assume member: "p\<in>{p\<in>set suffix. p\<le>x}"
  have pp: "prime p" using primes member by simp
  have lower: "1\<le>p" using prime_gt_1_nat[OF pp] by simp
  have avoids: "\<forall>q\<in>set core. \<not> q dvd p"
  proof (intro ballI notI)
    fix q
    assume qin: "q\<in>set core" and divides: "q dvd p"
    have qp: "prime q"
      using complete_prime_prefix_set[OF prefix] qin by blast
    have "q=p" by (rule primes_dvd_imp_eq[OF qp pp divides])
    then show False using disjoint qin member by blast
  qed
  show "p\<in>wheel_sift core {1..x}"
    using member lower avoids by (auto simp: wheel_sift_membership)
qed

theorem prime_birth_suffix_card:
  assumes prefix: "complete_prime_prefix core x"
    and primes: "\<forall>p\<in>set suffix. prime p"
    and separate: "distinct (core@suffix)"
  shows "card (wheel_sift (core@suffix) {1..x}) =
    card (wheel_sift core {1..x}) - length (filter (\<lambda>p. p\<le>x) suffix)"
proof -
  have disjoint: "set core \<inter> set suffix = {}"
    using separate by simp
  have subset: "{p\<in>set suffix. p\<le>x} \<subseteq> wheel_sift core {1..x}"
    by (rule prime_birth_suffix_survives_core[OF prefix primes disjoint])
  have finite_suffix: "finite {p\<in>set suffix. p\<le>x}"
    by simp
  have count: "card {p\<in>set suffix. p\<le>x} =
      length (filter (\<lambda>p. p\<le>x) suffix)"
    using separate distinct_card[of "filter (\<lambda>p. p\<le>x) suffix"] by simp
  show ?thesis
    using card_Diff_subset[OF finite_suffix subset] count
      prime_birth_suffix_sift[OF prefix primes] by simp
qed

theorem numerical_Phi_prime_birth_innovation:
  assumes cut: "j\<le>d" and depth: "d\<le>length ps"
    and distinct: "distinct ps"
    and primes: "\<forall>p\<in>set ps. prime p"
    and prefix: "complete_prime_prefix (take j ps) x"
  shows "numerical_Phi ps d x = numerical_Phi ps j x -
    length (filter (\<lambda>p. p\<le>x) (drop j (take d ps)))"
proof -
  let ?core = "take j ps"
  let ?suffix = "drop j (take d ps)"
  have jd: "j\<le>length ps" using cut depth by arith
  have take_core: "take j (take d ps) = ?core"
    using cut by (simp add: take_take min.absorb1)
  have split: "?core@?suffix=take d ps"
    using append_take_drop_id[of j "take d ps"] take_core by simp
  have suffix_subset: "set ?suffix \<subseteq> set (take d ps)"
    by (rule set_drop_subset)
  have prefix_subset: "set (take d ps) \<subseteq> set ps"
    by (rule set_take_subset)
  have suffix_primes: "\<forall>p\<in>set ?suffix. prime p"
    using primes suffix_subset prefix_subset by blast
  have separate: "distinct (?core@?suffix)"
    using distinct split by simp
  have count:
    "card (wheel_sift (take d ps) {1..x}) =
      card (wheel_sift ?core {1..x}) -
        length (filter (\<lambda>p. p\<le>x) ?suffix)"
    using prime_birth_suffix_card[OF prefix suffix_primes separate] split by simp
  have left: "numerical_Phi ps d x = card (wheel_sift (take d ps) {1..x})"
    using numerical_Phi_is_sift_card[OF depth distinct primes, of x]
    by (simp add: wheel_sift_membership)
  have right: "numerical_Phi ps j x = card (wheel_sift ?core {1..x})"
    using numerical_Phi_is_sift_card[OF jd distinct primes, of x]
    by (simp add: wheel_sift_membership)
  show ?thesis using count left right by simp
qed

text \<open>The runtime cutoff is the number of admitted factors satisfying the
integer square guard \<open>q*q \<le> x\<close>.  The next lemma records why that
guard selects an initial segment of a sorted prime prefix; it does not use a
Python-state equivalence or assume the resulting segment is already complete.
Completeness follows from the admitted prefix descriptor and its square
horizon below.\<close>

definition prime_birth_square_cut :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "prime_birth_square_cut ps x = length (takeWhile (\<lambda>q. q*q \<le> x) ps)"

lemma sorted_square_guard_takeWhile_filter:
  fixes ps :: "nat list" and x :: nat
  assumes sorted: "sorted ps"
  shows "takeWhile (\<lambda>q. q*q \<le> x) ps =
    filter (\<lambda>q. q*q \<le> x) ps"
  using sorted
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  have tail_sorted: "sorted qs" using Cons.prems by simp
  have q_le_tail: "\<And>r. r \<in> set qs \<Longrightarrow> q \<le> r"
    using Cons.prems by simp
  show ?case
  proof (cases "q*q \<le> x")
    case True
    have tail:
      "takeWhile (\<lambda>r. r*r \<le> x) qs =
        filter (\<lambda>r. r*r \<le> x) qs"
      by (rule Cons.IH[OF tail_sorted])
    show ?thesis using True tail by simp
  next
    case False
    have no_later_predicate: "\<forall>r \<in> set qs. \<not> r*r \<le> x"
    proof
      fix r
      assume member: "r \<in> set qs"
      have order: "q \<le> r" using q_le_tail[OF member] .
      have square: "q*q \<le> r*r"
        by (rule mult_le_mono[OF order order])
      show "\<not> r*r \<le> x"
      proof
        assume r_square: "r*r \<le> x"
        have "q*q \<le> x" by (rule le_trans[OF square r_square])
        with False show False by contradiction
      qed
    qed
    have no_later: "filter (\<lambda>r. r*r \<le> x) qs = []"
      using no_later_predicate by (induction qs) auto
    show ?thesis using False no_later by simp
  qed
qed

lemma consecutive_square_cut_is_complete:
  assumes descriptor: "consecutive_prime_descriptor ps"
    and short: "prime_birth_square_cut ps x < length ps"
  shows "prime_birth_square_cut ps x \<le> length ps"
    and "prime_birth_square_cut ps x =
      length (filter (\<lambda>q. q*q \<le> x) ps)"
    and "take (prime_birth_square_cut ps x) ps = trim_prime_prefix ps x"
    and "complete_prime_prefix (take (prime_birth_square_cut ps x) ps) x"
proof -
  let ?j = "prime_birth_square_cut ps x"
  have nonempty: "ps \<noteq> []"
    and prefix: "ps = primes_upto (last ps)"
    using descriptor by (auto simp: consecutive_prime_descriptor_def)
  have sorted_rhs: "sorted (primes_upto (last ps))" by simp
  have distinct_rhs: "distinct (primes_upto (last ps))" by simp
  have sorted: "sorted ps" using prefix sorted_rhs by metis
  have distinct: "distinct ps" using prefix distinct_rhs by metis
  have square_filter:
    "filter (\<lambda>q. q*q \<le> x) ps = trim_prime_prefix ps x"
  proof -
    have same:
      "filter (\<lambda>q. q*q \<le> x) ps =
        filter (\<lambda>q. q \<le> floor_sqrt x) ps"
      by (rule filter_cong)
        (auto simp: le_floor_sqrt_iff power2_eq_square)
    show ?thesis using same by (simp add: trim_prime_prefix_def)
  qed
  have take_while:
    "takeWhile (\<lambda>q. q*q \<le> x) ps = trim_prime_prefix ps x"
    using sorted_square_guard_takeWhile_filter[OF sorted] square_filter by simp
  have len_cut: "?j = length (takeWhile (\<lambda>q. q*q \<le> x) ps)"
    by (simp add: prime_birth_square_cut_def)
  have cut_bound: "?j \<le> length ps"
    using len_cut length_takeWhile_le[of "\<lambda>q. q*q \<le> x" ps] by simp
  have cut_count:
    "?j = length (filter (\<lambda>q. q*q \<le> x) ps)"
    using len_cut sorted_square_guard_takeWhile_filter[OF sorted] by simp
  have exact_cut: "take ?j ps = trim_prime_prefix ps x"
  proof -
    have "take ?j ps = take (length (takeWhile (\<lambda>q. q*q \<le> x) ps)) ps"
      using len_cut by simp
    also have "... = takeWhile (\<lambda>q. q*q \<le> x) ps"
      by (rule takeWhile_eq_take[symmetric])
    also have "... = trim_prime_prefix ps x" by (rule take_while)
    finally show ?thesis .
  qed
  have last_not_guard: "\<not> (last ps * last ps \<le> x)"
  proof
    assume last_guard: "last ps * last ps \<le> x"
    have all_guard: "\<forall>q \<in> set ps. q*q \<le> x"
    proof
      fix q
      assume member: "q \<in> set ps"
      have q_le: "q \<le> last ps"
        by (rule sorted_member_le_last[OF sorted nonempty member])
      have square_le: "q*q \<le> last ps * last ps"
        by (rule mult_le_mono[OF q_le q_le])
      show "q*q \<le> x" using square_le last_guard by arith
    qed
    have filter_full: "filter (\<lambda>q. q*q \<le> x) ps = ps"
      using all_guard by (induction ps) auto
    have "?j = length ps"
      unfolding prime_birth_square_cut_def
      using sorted_square_guard_takeWhile_filter[OF sorted]
      by (simp add: filter_full)
    with short show False by simp
  qed
  have horizon: "x < (last ps)^2"
    using last_not_guard by (simp add: power2_eq_square)
  have last_prime: "prime (last ps)"
  proof -
    have member: "last ps \<in> set ps" by (rule last_in_set[OF nonempty])
    have member_rhs: "last ps \<in> set (primes_upto (last ps))"
      using prefix member by metis
    show ?thesis using member_rhs by (auto simp: set_primes_upto)
  qed
  have floor_sqrt_last_square: "floor_sqrt (last ps * last ps) = last ps"
  proof (rule antisym)
    show "floor_sqrt (last ps * last ps) \<le> last ps"
    proof (rule ccontr)
      assume "\<not> floor_sqrt (last ps * last ps) \<le> last ps"
      then have next_le: "Suc (last ps) \<le> floor_sqrt (last ps * last ps)"
        by simp
      have "(Suc (last ps))^2 \<le> last ps * last ps"
        using le_floor_sqrt_iff[of "Suc (last ps)" "last ps * last ps"] next_le
        by (simp add: power2_eq_square)
      then have next_square_le:
        "Suc (last ps) * Suc (last ps) \<le> last ps * last ps"
        by (simp add: power2_eq_square)
      have square_strict:
        "last ps * last ps < Suc (last ps) * Suc (last ps)"
        by (simp add: mult_Suc mult_Suc_right; arith)
      show False using next_square_le square_strict by arith
    qed
    show "last ps \<le> floor_sqrt (last ps * last ps)"
      using le_floor_sqrt_iff[of "last ps" "last ps * last ps"]
      by (simp add: power2_eq_square)
  qed
  have complete_horizon: "complete_prime_prefix ps (last ps * last ps)"
    using prefix floor_sqrt_last_square
    by (simp add: complete_prime_prefix_def)
  have horizon_le: "x \<le> last ps * last ps"
    using horizon by (simp add: power2_eq_square; arith)
  have complete:
    "complete_prime_prefix (trim_prime_prefix ps x) x"
    by (rule complete_prefix_smaller_horizon[OF complete_horizon horizon_le])
  show "prime_birth_square_cut ps x \<le> length ps" using cut_bound .
  show "prime_birth_square_cut ps x =
      length (filter (\<lambda>q. q*q \<le> x) ps)" using cut_count .
  show "take (prime_birth_square_cut ps x) ps = trim_prime_prefix ps x"
    using exact_cut .
  show "complete_prime_prefix (take (prime_birth_square_cut ps x) ps) x"
    using complete exact_cut by simp
qed

lemma numerical_Phi_prefix_sift_card:
  assumes depth: "d \<le> length ps"
    and distinct: "distinct (take d ps)"
    and primes: "\<forall>p \<in> set (take d ps). prime p"
  shows "numerical_Phi ps d x =
    card (wheel_sift (take d ps) {1..x})"
proof -
  have prefix_depth: "d \<le> length (take d ps)"
    using depth by simp
  have prefix_count:
    "numerical_Phi (take d ps) d x =
      card (wheel_sift (rev (take d (take d ps))) {1..x})"
    by (rule numerical_Phi_is_sift_card[OF prefix_depth distinct primes])
  have append_phi:
    "numerical_Phi (take d ps @ drop d ps) d x =
      numerical_Phi (take d ps) d x"
    by (rule numerical_Phi_append_prefix) (use depth in simp)
  have same_phi: "numerical_Phi ps d x = numerical_Phi (take d ps) d x"
    using append_phi by (simp add: append_take_drop_id)
  show ?thesis using prefix_count same_phi
    by (simp add: wheel_sift_membership)
qed

theorem numerical_Phi_prime_birth_square_cut:
  assumes depth: "d \<le> length ps"
    and admitted: "consecutive_prime_descriptor (take d ps)"
    and short: "prime_birth_square_cut (take d ps) x < d"
  defines "j \<equiv> prime_birth_square_cut (take d ps) x"
  shows cut_bound: "j \<le> d"
    and cut_count:
      "j = length (filter (\<lambda>q. q*q \<le> x) (take d ps))"
    and complete: "complete_prime_prefix (take j ps) x"
    and quotient:
      "numerical_Phi ps d x = numerical_Phi ps j x -
        length (filter (\<lambda>p. p \<le> x) (drop j (take d ps)))"
proof -
  let ?core = "take d ps"
  let ?j = "prime_birth_square_cut ?core x"
  have j_eq: "j = ?j" using j_def by simp
  have core_short: "?j < length ?core"
    using short depth by simp
  have cut_depth: "?j \<le> length ?core"
    using consecutive_square_cut_is_complete(1)[OF admitted core_short] .
  have cut_count_core:
    "?j = length (filter (\<lambda>q. q*q \<le> x) ?core)"
    using consecutive_square_cut_is_complete(2)[OF admitted core_short] .
  have cut_trim: "take ?j ?core = trim_prime_prefix ?core x"
    using consecutive_square_cut_is_complete(3)[OF admitted core_short] .
  have cut_complete_core: "complete_prime_prefix (take ?j ?core) x"
    using consecutive_square_cut_is_complete(4)[OF admitted core_short] .
  have core_length: "length ?core = d" using depth by simp
  have j_bound: "j \<le> d" using cut_depth core_length j_eq by simp
  have take_same: "take j ?core = take j ps"
    using j_bound depth by (simp add: min_def)
  have counted_cut:
    "j = length (filter (\<lambda>q. q*q \<le> x) ?core)"
    using cut_count_core j_eq by simp
  have complete_cut: "complete_prime_prefix (take j ps) x"
    using cut_complete_core take_same j_eq by simp
  have core_prefix: "?core = primes_upto (last ?core)"
    using admitted by (auto simp: consecutive_prime_descriptor_def)
  have core_distinct_rhs: "distinct (primes_upto (last ?core))" by simp
  have core_distinct: "distinct ?core"
    using core_prefix core_distinct_rhs by metis
  have core_primes_rhs:
    "\<forall>p \<in> set (primes_upto (last ?core)). prime p"
    by (auto simp: set_primes_upto)
  have core_primes: "\<forall>p \<in> set ?core. prime p"
    using core_prefix core_primes_rhs by metis
  have cut_distinct: "distinct (take j ps)"
    using core_distinct take_same by (metis distinct_take)
  have cut_primes: "\<forall>p \<in> set (take j ps). prime p"
  proof -
    have members:
      "set (take j ps) = {p. prime p \<and> p \<le> floor_sqrt x}"
      by (rule complete_prime_prefix_set[OF complete_cut])
    show ?thesis using members by auto
  qed
  have left:
    "numerical_Phi ps d x = card (wheel_sift ?core {1..x})"
    by (rule numerical_Phi_prefix_sift_card[OF depth core_distinct core_primes])
  have right_depth: "j \<le> length ps"
    using j_bound depth by simp
  have right:
    "numerical_Phi ps j x = card (wheel_sift (take j ps) {1..x})"
    by (rule numerical_Phi_prefix_sift_card[OF right_depth cut_distinct cut_primes])
  have suffix_primes: "\<forall>p \<in> set (drop j ?core). prime p"
    using core_primes set_drop_subset[of j ?core] by blast
  have separate: "distinct (take j ps @ drop j ?core)"
    using core_distinct take_same by (metis append_take_drop_id)
  have split: "take j ps @ drop j ?core = ?core"
    using take_same by (metis append_take_drop_id)
  have count:
    "card (wheel_sift ?core {1..x}) =
      card (wheel_sift (take j ps) {1..x}) -
        length (filter (\<lambda>p. p \<le> x) (drop j ?core))"
    using prime_birth_suffix_card[OF complete_cut suffix_primes separate]
      split by simp
  have quotient_identity: "numerical_Phi ps d x = numerical_Phi ps j x -
      length (filter (\<lambda>p. p \<le> x) (drop j ?core))"
    using left right count by simp
  show cut_bound: "j \<le> d" using j_bound .
  show "j = length (filter (\<lambda>q. q*q \<le> x) (take d ps))"
    using counted_cut j_def by simp
  show complete: "complete_prime_prefix (take j ps) x" using complete_cut .
  show quotient:
    "numerical_Phi ps d x = numerical_Phi ps j x -
      length (filter (\<lambda>p. p \<le> x) (drop j (take d ps)))"
    using quotient_identity by (simp add: j_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms prime_birth_suffix_sift prime_birth_suffix_card
      numerical_Phi_prime_birth_innovation
      consecutive_square_cut_is_complete
      numerical_Phi_prime_birth_square_cut}) then ()
    else error "Prime birth innovation contains an oracle";
\<close>

end
