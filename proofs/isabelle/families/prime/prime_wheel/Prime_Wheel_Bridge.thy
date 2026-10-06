theory Prime_Wheel_Bridge
  imports
    "HOL-Number_Theory.Eratosthenes"
    "HOL-Number_Theory.Pocklington"
    "HOL-Library.Discrete_Functions"
begin

text \<open>
  This theory describes the mathematical prime-wheel carrier.  The descriptor
  is the complete consecutive list of primes through the square-root boundary;
  it is not a caller-supplied partial factor list.  The executable Python wheel
  and its resource accounting require a separate refinement theorem.
\<close>

definition complete_prime_prefix :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "complete_prime_prefix ps H \<longleftrightarrow> ps = primes_upto (floor_sqrt H)"

fun wheel_sift :: "nat list \<Rightarrow> nat set \<Rightarrow> nat set" where
  "wheel_sift [] A = A"
| "wheel_sift (p # ps) A = {n \<in> wheel_sift ps A. \<not> p dvd n}"

definition wheel_interval :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "wheel_interval L H = {Suc L..H}"

definition wheel_survivors :: "nat list \<Rightarrow> nat \<Rightarrow> nat set" where
  "wheel_survivors ps H = wheel_sift ps (wheel_interval (last ps) H)"

lemma wheel_sift_membership:
  "wheel_sift ps A = {n \<in> A. \<forall>p \<in> set ps. \<not> p dvd n}"
  by (induction ps) auto

definition sound_prime_descriptor :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_prime_descriptor ps B \<longleftrightarrow>
    distinct ps \<and> sorted ps \<and>
    (\<forall>p \<in> set ps. prime p \<and> p \<le> B)"

definition discovery_stopped :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "discovery_stopped ps B \<longleftrightarrow>
    sound_prime_descriptor ps B \<and> 0 < B \<and>
    card (wheel_sift ps {1..B}) = 1"

lemma sound_descriptor_one_survives:
  assumes sound: "sound_prime_descriptor ps B" and positive: "0 < B"
  shows "1 \<in> wheel_sift ps {1..B}"
proof -
  have avoids: "\<forall>p \<in> set ps. \<not> p dvd 1"
  proof (intro ballI)
    fix p
    assume "p \<in> set ps"
    then have "prime p" using sound
      by (auto simp: sound_prime_descriptor_def)
    then show "\<not> p dvd 1" using prime_gt_1_nat by auto
  qed
  show ?thesis using positive avoids by (auto simp: wheel_sift_membership)
qed

lemma discovery_count_one_is_singleton:
  assumes stopped: "discovery_stopped ps B"
  shows "wheel_sift ps {1..B} = {1}"
proof -
  from stopped have sound: "sound_prime_descriptor ps B" and positive: "0 < B"
    and count: "card (wheel_sift ps {1..B}) = 1"
    by (auto simp: discovery_stopped_def)
  from count obtain x where singleton: "wheel_sift ps {1..B} = {x}"
    by (auto simp: card_1_singleton_iff)
  have "1 \<in> wheel_sift ps {1..B}"
    by (rule sound_descriptor_one_survives[OF sound positive])
  with singleton have "x = 1" by simp
  with singleton show ?thesis by simp
qed

theorem discovery_stop_covers_all_primes:
  assumes stopped: "discovery_stopped ps B"
  shows "set ps = {p. prime p \<and> p \<le> B}"
proof (rule Set.set_eqI)
  fix p
  from stopped have sound: "sound_prime_descriptor ps B"
    by (simp add: discovery_stopped_def)
  show "p \<in> set ps \<longleftrightarrow> p \<in> {p. prime p \<and> p \<le> B}"
  proof
    assume "p \<in> set ps"
    with sound show "p \<in> {p. prime p \<and> p \<le> B}"
      by (auto simp: sound_prime_descriptor_def)
  next
    assume member: "p \<in> {p. prime p \<and> p \<le> B}"
    then have pprime: "prime p" and pbound: "p \<le> B" by auto
    show "p \<in> set ps"
    proof (rule ccontr)
      assume absent: "p \<notin> set ps"
      have avoids: "\<forall>q \<in> set ps. \<not> q dvd p"
      proof (intro ballI notI)
        fix q
        assume qin: "q \<in> set ps" and qdvd: "q dvd p"
        have qprime: "prime q" using sound qin
          by (auto simp: sound_prime_descriptor_def)
        have "q = p" using qprime pprime qdvd by (metis primes_dvd_imp_eq)
        with qin absent show False by simp
      qed
      have pone: "1 \<le> p" using prime_gt_1_nat[OF pprime] by arith
      have "p \<in> wheel_sift ps {1..B}"
        using pone pbound avoids by (auto simp: wheel_sift_membership)
      then have "p = 1" using discovery_count_one_is_singleton[OF stopped] by simp
      with pprime show False by simp
    qed
  qed
qed

theorem discovery_stop_constructs_complete_prefix:
  assumes stopped: "discovery_stopped ps B"
  shows "ps = primes_upto B"
proof -
  from stopped have sound: "sound_prime_descriptor ps B"
    by (simp add: discovery_stopped_def)
  have seteq: "set ps = set (primes_upto B)"
    using discovery_stop_covers_all_primes[OF stopped]
    by (auto simp: set_primes_upto)
  show ?thesis
    by (rule sorted_distinct_set_unique)
      (use sound seteq in \<open>auto simp: sound_prime_descriptor_def\<close>)
qed

lemma finite_wheel_sift:
  assumes "finite A"
  shows "finite (wheel_sift ps A)"
  using assms by (induction ps) auto

lemma legendre_finite_prefix_recurrence:
  assumes "finite A"
  shows "card (wheel_sift (p # ps) A) =
    card (wheel_sift ps A) - card {n \<in> wheel_sift ps A. p dvd n}"
proof -
  have finite: "finite (wheel_sift ps A)"
    by (rule finite_wheel_sift[OF assms])
  have subset: "{n \<in> wheel_sift ps A. p dvd n} \<subseteq> wheel_sift ps A"
    by auto
  have finite_bad: "finite {n \<in> wheel_sift ps A. p dvd n}"
    using finite by auto
  have seteq: "{n \<in> wheel_sift ps A. \<not> p dvd n} =
      wheel_sift ps A - {n \<in> wheel_sift ps A. p dvd n}"
    by auto
  show ?thesis
    using card_Diff_subset[OF finite_bad subset]
    by (simp only: wheel_sift.simps seteq)
qed

text \<open>
  The production evaluator indexes a consecutive factor word by a depth and
  evaluates the numerical Legendre recurrence in postorder.  The following
  function has exactly that indexing convention: at depth @{term "Suc d"},
  the newly admitted factor is @{term "ps ! d"}.
\<close>

fun numerical_Phi :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "numerical_Phi ps 0 x = x"
| "numerical_Phi ps (Suc d) x =
    numerical_Phi ps d x - numerical_Phi ps d (x div (ps ! d))"

lemma prime_multiples_in_sift:
  assumes pprime: "prime p"
    and psprime: "\<forall>q \<in> set ps. prime q"
    and fresh: "p \<notin> set ps"
  shows "{n \<in> wheel_sift ps {1..x}. p dvd n} =
    (\<lambda>q. p * q) ` wheel_sift ps {1..x div p}"
proof (rule Set.set_eqI)
  fix n
  have ppos: "0 < p" using prime_gt_1_nat[OF pprime] by arith
  show "n \<in> {n \<in> wheel_sift ps {1..x}. p dvd n} \<longleftrightarrow>
      n \<in> (\<lambda>q. p * q) ` wheel_sift ps {1..x div p}"
  proof
    assume member: "n \<in> {n \<in> wheel_sift ps {1..x}. p dvd n}"
    then obtain q where nq: "n = p * q" by (auto elim: dvdE)
    from member have npos: "0 < n" and nle: "n \<le> x"
      and avoids: "\<forall>r \<in> set ps. \<not> r dvd n"
      by (auto simp: wheel_sift_membership)
    have qpos: "0 < q" using npos nq by auto
    have qle: "q \<le> x div p"
      using nle ppos nq
      by (simp add: less_eq_div_iff_mult_less_eq ac_simps)
    have qavoids: "\<forall>r \<in> set ps. \<not> r dvd q"
      using avoids nq by auto
    have "q \<in> wheel_sift ps {1..x div p}"
      using qpos qle qavoids by (auto simp: wheel_sift_membership)
    with nq show "n \<in> (\<lambda>q. p * q) ` wheel_sift ps {1..x div p}"
      by blast
  next
    assume member: "n \<in> (\<lambda>q. p * q) ` wheel_sift ps {1..x div p}"
    then obtain q where qmember: "q \<in> wheel_sift ps {1..x div p}"
      and nq: "n = p * q" by blast
    from qmember have qpos: "0 < q" and qle: "q \<le> x div p"
      and qavoids: "\<forall>r \<in> set ps. \<not> r dvd q"
      by (auto simp: wheel_sift_membership)
    have npos: "0 < n" using ppos qpos nq by simp
    have nle: "n \<le> x"
      using qle ppos nq
      by (simp add: less_eq_div_iff_mult_less_eq ac_simps)
    have navoids: "\<forall>r \<in> set ps. \<not> r dvd n"
    proof (intro ballI notI)
      fix r
      assume rin: "r \<in> set ps" and rdvd: "r dvd n"
      have rprime: "prime r" using psprime rin by blast
      have rne: "r \<noteq> p" using fresh rin by auto
      from rdvd nq rprime have "r dvd p \<or> r dvd q"
        by (simp add: prime_dvd_mult_iff)
      then show False
      proof
        assume "r dvd p"
        then have "r = p" using rprime pprime by (metis primes_dvd_imp_eq)
        with rne show False by simp
      next
        assume "r dvd q"
        with qavoids rin show False by blast
      qed
    qed
    show "n \<in> {n \<in> wheel_sift ps {1..x}. p dvd n}"
      using npos nle navoids nq by (auto simp: wheel_sift_membership)
  qed
qed

lemma card_prime_multiples_in_sift:
  assumes pprime: "prime p"
    and psprime: "\<forall>q \<in> set ps. prime q"
    and fresh: "p \<notin> set ps"
  shows "card {n \<in> wheel_sift ps {1..x}. p dvd n} =
    card (wheel_sift ps {1..x div p})"
proof -
  have ppos: "0 < p" using prime_gt_1_nat[OF pprime] by arith
  have inj: "inj_on (\<lambda>q. p * q) (wheel_sift ps {1..x div p})"
    using ppos by (auto intro!: inj_onI)
  show ?thesis
    unfolding prime_multiples_in_sift[OF assms]
    by (rule card_image[OF inj])
qed

theorem numerical_Phi_is_sift_card:
  assumes depth: "d \<le> length ps"
    and distinct: "distinct ps"
    and primes: "\<forall>p \<in> set ps. prime p"
  shows "numerical_Phi ps d x =
    card (wheel_sift (rev (take d ps)) {1..x})"
  using depth
proof (induction d arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc d)
  let ?qs = "rev (take d ps)"
  let ?p = "ps ! d"
  have dlt: "d < length ps" using Suc.prems by simp
  have take_suc: "rev (take (Suc d) ps) = ?p # ?qs"
    using dlt by (simp add: take_Suc_conv_app_nth)
  have pprime: "prime ?p" using primes dlt by simp
  have qsprime: "\<forall>q \<in> set ?qs. prime q"
  proof (intro ballI)
    fix q
    assume member: "q \<in> set ?qs"
    have in_take: "q \<in> set (take d ps)" using member by simp
    have "set (take d ps) \<subseteq> set ps" by (rule set_take_subset)
    then have "q \<in> set ps" using in_take by blast
    then show "prime q" using primes by blast
  qed
  have fresh: "?p \<notin> set ?qs"
  proof
    assume member: "?p \<in> set ?qs"
    then have in_take: "?p \<in> set (take d ps)" by simp
    then obtain i where ilen: "i < length (take d ps)"
      and equal: "take d ps ! i = ?p"
      by (auto simp: in_set_conv_nth)
    have id: "i < d" using ilen by simp
    have ilt: "i < length ps" using id dlt by arith
    have nth_equal: "ps ! i = ps ! d" using equal id by simp
    have "ps ! i \<noteq> ps ! d"
      using distinct ilt dlt id by (auto simp: distinct_conv_nth)
    with nth_equal show False by simp
  qed
  have finite: "finite {1..x}" by simp
  have recurrence: "card (wheel_sift (?p # ?qs) {1..x}) =
      card (wheel_sift ?qs {1..x}) -
      card (wheel_sift ?qs {1..x div ?p})"
    using legendre_finite_prefix_recurrence[OF finite, of ?p ?qs]
      card_prime_multiples_in_sift[OF pprime qsprime fresh, of x]
    by simp
  have left: "numerical_Phi ps d x = card (wheel_sift ?qs {1..x})"
    by (rule Suc.IH) (use Suc.prems in simp)
  have right: "numerical_Phi ps d (x div ?p) =
      card (wheel_sift ?qs {1..x div ?p})"
    by (rule Suc.IH) (use Suc.prems in simp)
  show ?case using recurrence left right take_suc by simp
qed

corollary numerical_Phi_recurrence_correct:
  assumes "Suc d \<le> length ps" "distinct ps" "\<forall>p \<in> set ps. prime p"
  shows "card (wheel_sift (rev (take (Suc d) ps)) {1..x}) =
    card (wheel_sift (rev (take d ps)) {1..x}) -
    card (wheel_sift (rev (take d ps)) {1..x div (ps ! d)})"
  using numerical_Phi_is_sift_card[OF assms(1) assms(2) assms(3), of x]
    numerical_Phi_is_sift_card[of d ps x]
    numerical_Phi_is_sift_card[of d ps "x div (ps ! d)"] assms
  by simp

type_synonym phi_key = "nat \<times> nat"
type_synonym phi_store = "phi_key \<Rightarrow> nat option"

definition phi_key_value :: "nat list \<Rightarrow> phi_key \<Rightarrow> nat" where
  "phi_key_value ps key = numerical_Phi ps (fst key) (snd key)"

definition valid_phi_store :: "nat list \<Rightarrow> phi_store \<Rightarrow> bool" where
  "valid_phi_store ps M \<longleftrightarrow>
    (\<forall>d x v. M (d,x) = Some v \<longrightarrow>
      d \<le> length ps \<and> v = numerical_Phi ps d x)"

lemma empty_phi_store_valid: "valid_phi_store ps (\<lambda>_. None)"
  by (simp add: valid_phi_store_def)

lemma valid_phi_store_lookup:
  assumes "valid_phi_store ps M" "M (d,x) = Some v"
  shows "d \<le> length ps" "v = numerical_Phi ps d x"
  using assms by (auto simp: valid_phi_store_def)

lemma valid_phi_store_update:
  assumes valid: "valid_phi_store ps M"
    and depth: "d \<le> length ps"
    and exact: "v = numerical_Phi ps d x"
  shows "valid_phi_store ps (M((d,x) \<mapsto> v))"
  using assms by (auto simp: valid_phi_store_def)

lemma postorder_children_compute_parent:
  assumes depth: "Suc d \<le> length ps"
    and left: "M (d,x) = Some l"
    and right: "M (d,x div (ps ! d)) = Some r"
    and valid: "valid_phi_store ps M"
  shows "l - r = numerical_Phi ps (Suc d) x"
proof -
  have "l = numerical_Phi ps d x" and
    "r = numerical_Phi ps d (x div (ps ! d))"
    using valid_phi_store_lookup[OF valid left]
      valid_phi_store_lookup[OF valid right] by auto
  then show ?thesis by simp
qed

lemma postorder_parent_update_valid:
  assumes depth: "Suc d \<le> length ps"
    and left: "M (d,x) = Some l"
    and right: "M (d,x div (ps ! d)) = Some r"
    and valid: "valid_phi_store ps M"
  shows "valid_phi_store ps (M(((Suc d,x)) \<mapsto> (l-r)))"
  by (rule valid_phi_store_update[OF valid depth])
    (rule postorder_children_compute_parent[OF depth left right valid])

lemma complete_prime_prefix_set:
  assumes "complete_prime_prefix ps H"
  shows "set ps = {p. prime p \<and> p \<le> floor_sqrt H}"
  using assms by (auto simp: complete_prime_prefix_def set_primes_upto)

lemma complete_prime_prefix_distinct_sorted:
  assumes "complete_prime_prefix ps H"
  shows "distinct ps \<and> sorted ps"
  using assms by (simp add: complete_prime_prefix_def)

definition trim_prime_prefix :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "trim_prime_prefix ps H = filter (\<lambda>p. p \<le> floor_sqrt H) ps"

theorem complete_prefix_smaller_horizon:
  assumes prefix: "complete_prime_prefix ps H" and smaller: "h \<le> H"
  shows "complete_prime_prefix (trim_prime_prefix ps h) h"
proof -
  have root_le: "floor_sqrt h \<le> floor_sqrt H"
    by (rule mono_floor_sqrt'[OF smaller])
  have sorted: "sorted ps" and distinct: "distinct ps"
    using complete_prime_prefix_distinct_sorted[OF prefix] by auto
  have seteq: "set (trim_prime_prefix ps h) = set (primes_upto (floor_sqrt h))"
  proof (rule Set.set_eqI)
    fix p
    have in_ps: "p \<in> set ps \<longleftrightarrow>
        prime p \<and> p \<le> floor_sqrt H"
      using complete_prime_prefix_set[OF prefix] by blast
    show "p \<in> set (trim_prime_prefix ps h) \<longleftrightarrow>
        p \<in> set (primes_upto (floor_sqrt h))"
      unfolding trim_prime_prefix_def
      using in_ps root_le
      by (simp only: set_filter mem_Collect_eq set_primes_upto) auto
  qed
  have sorted_trim: "sorted (trim_prime_prefix ps h)"
  proof -
    have "sorted (map id (filter (\<lambda>p. p \<le> floor_sqrt h) ps))"
      by (rule sorted_filter) (use sorted in simp)
    then show ?thesis by (simp add: trim_prime_prefix_def)
  qed
  have distinct_trim: "distinct (trim_prime_prefix ps h)"
    using distinct by (simp add: trim_prime_prefix_def)
  have "trim_prime_prefix ps h = primes_upto (floor_sqrt h)"
    by (rule sorted_distinct_set_unique)
      (use sorted_trim distinct_trim seteq in auto)
  then show ?thesis by (simp add: complete_prime_prefix_def)
qed

lemma sorted_member_le_last:
  assumes "sorted xs" "xs \<noteq> []" "x \<in> set xs"
  shows "x \<le> last xs"
  using assms
  by (induction xs) (auto split: list.split)

lemma complete_prefix_prime_divisor:
  assumes prefix: "complete_prime_prefix ps H"
    and n: "1 < n" "n \<le> H" "\<not> prime n"
  shows "\<exists>p \<in> set ps. p dvd n"
proof -
  from n have n01: "n \<noteq> 0" "n \<noteq> 1" by arith+
  from n n01 prime_prime_factor_sqrt
  obtain p where p: "prime p" "p dvd n" "p^2 \<le> n"
    by blast
  have "p \<le> floor_sqrt H"
    using p(3) n(2) by (simp add: le_floor_sqrt_iff)
  with p prefix show ?thesis
    by (auto simp: complete_prime_prefix_def set_primes_upto)
qed

theorem complete_prefix_survivors_are_exact_primes:
  assumes prefix: "complete_prime_prefix ps H" and nonempty: "ps \<noteq> []"
  shows "wheel_survivors ps H =
    {n. last ps < n \<and> n \<le> H \<and> prime n}"
proof (rule Set.set_eqI)
  fix n
  have sorted: "sorted ps"
    using complete_prime_prefix_distinct_sorted[OF prefix] by blast
  show "n \<in> wheel_survivors ps H \<longleftrightarrow>
      n \<in> {n. last ps < n \<and> n \<le> H \<and> prime n}"
  proof
    assume member: "n \<in> wheel_survivors ps H"
    then have bounds: "last ps < n" "n \<le> H"
      and avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
      by (auto simp: wheel_survivors_def wheel_interval_def wheel_sift_membership)
    have one: "1 < n"
    proof -
      have "prime (last ps)"
        using last_in_set[OF nonempty] complete_prime_prefix_set[OF prefix] by blast
      then have "1 < last ps" by (rule prime_gt_1_nat)
      with bounds show ?thesis by arith
    qed
    have "prime n"
    proof (rule ccontr)
      assume "\<not> prime n"
      from complete_prefix_prime_divisor[OF prefix one bounds(2) this]
      show False using avoids by blast
    qed
    with bounds show "n \<in> {n. last ps < n \<and> n \<le> H \<and> prime n}"
      by simp
  next
    assume member: "n \<in> {n. last ps < n \<and> n \<le> H \<and> prime n}"
    then have bounds: "last ps < n" "n \<le> H" and prime: "prime n"
      by auto
    have avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
    proof (intro ballI notI)
      fix p
      assume pin: "p \<in> set ps" and pdvd: "p dvd n"
      have pprime: "prime p"
        using pin complete_prime_prefix_set[OF prefix] by blast
      have ple: "p \<le> last ps"
        by (rule sorted_member_le_last[OF sorted nonempty pin])
      from pprime prime pdvd have "p = n"
        by (metis primes_dvd_imp_eq)
      with ple bounds show False by arith
    qed
    show "n \<in> wheel_survivors ps H"
      using bounds avoids
      by (auto simp: wheel_survivors_def wheel_interval_def wheel_sift_membership)
  qed
qed

definition next_prime_after :: "nat \<Rightarrow> nat" where
  "next_prime_after p = smallest_prime_beyond (Suc p)"

lemma next_prime_after_prime: "prime (next_prime_after p)"
  by (simp add: next_prime_after_def)

lemma next_prime_after_gt: "p < next_prime_after p"
proof -
  have "Suc p \<le> smallest_prime_beyond (Suc p)"
    by (rule smallest_prime_beyond_le)
  then show ?thesis unfolding next_prime_after_def by arith
qed

lemma next_prime_after_least:
  assumes "prime q" "p < q"
  shows "next_prime_after p \<le> q"
  using assms smallest_prime_beyond_smallest[of q "Suc p"]
  by (simp add: next_prime_after_def)

definition consecutive_prime_descriptor :: "nat list \<Rightarrow> bool" where
  "consecutive_prime_descriptor ps \<longleftrightarrow>
    ps \<noteq> [] \<and> ps = primes_upto (last ps)"

theorem append_next_prime_preserves_consecutive_descriptor:
  assumes descriptor: "consecutive_prime_descriptor ps"
  defines "q \<equiv> next_prime_after (last ps)"
  shows "ps @ [q] = primes_upto q"
proof -
  from descriptor have nonempty: "ps \<noteq> []" and prefix: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have sorted_rhs: "sorted (primes_upto (last ps))" by simp
  have distinct_rhs: "distinct (primes_upto (last ps))" by simp
  have sorted: "sorted ps" using prefix sorted_rhs by metis
  have distinct: "distinct ps" using prefix distinct_rhs by metis
  have prefix_set_list: "set ps = set (primes_upto (last ps))"
    using prefix by metis
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    using prefix_set_list by (auto simp: set_primes_upto)
  have all_less: "\<forall>p \<in> set ps. p < q"
  proof
    fix p
    assume pin: "p \<in> set ps"
    have "p \<le> last ps" by (rule sorted_member_le_last[OF sorted nonempty pin])
    also have "last ps < q" unfolding q_def by (rule next_prime_after_gt)
    finally show "p < q" .
  qed
  have seteq: "set (ps @ [q]) = set (primes_upto q)"
  proof (rule Set.set_eqI)
    fix p
    show "p \<in> set (ps @ [q]) \<longleftrightarrow> p \<in> set (primes_upto q)"
    proof
      assume member: "p \<in> set (ps @ [q])"
      have alternatives: "p \<in> set ps \<or> p = q" using member by auto
      then show "p \<in> set (primes_upto q)"
      proof
        assume pin: "p \<in> set ps"
        from pin have pprime: "prime p" and ple: "p \<le> last ps"
          using prefix_set by auto
        have lq: "last ps < q" unfolding q_def by (rule next_prime_after_gt)
        have pq: "p \<le> q" using ple lq by arith
        show ?thesis using pprime pq by (simp add: set_primes_upto)
      next
        assume peq: "p = q"
        have qprime: "prime q" unfolding q_def by (rule next_prime_after_prime)
        show ?thesis using peq qprime by (simp add: set_primes_upto)
      qed
    next
      assume member: "p \<in> set (primes_upto q)"
      then have pprime: "prime p" and ple: "p \<le> q"
        by (auto simp: set_primes_upto)
      show "p \<in> set (ps @ [q])"
      proof (cases "p \<le> last ps")
        case True
        then have "p \<in> set ps" using prefix_set pprime by auto
        then show ?thesis by simp
      next
        case False
        then have lp: "last ps < p" by arith
        have "q \<le> p" unfolding q_def
          by (rule next_prime_after_least[OF pprime lp])
        with ple have "p = q" by arith
        then show ?thesis by simp
      qed
    qed
  qed
  have all_le: "\<forall>p \<in> set ps. p \<le> q" using all_less by auto
  have sorted_append: "sorted (ps @ [q])"
    using sorted all_le by (simp add: sorted_append)
  have distinct_append: "distinct (ps @ [q])"
    using distinct all_less by auto
  show ?thesis
    by (rule sorted_distinct_set_unique)
      (use sorted_append distinct_append seteq in auto)
qed

theorem consecutive_descriptor_least_survivor_is_next_prime:
  assumes descriptor: "consecutive_prime_descriptor ps"
    and horizon: "next_prime_after (last ps) \<le> H"
  shows "Min (wheel_survivors ps H) = next_prime_after (last ps)"
proof -
  from descriptor have nonempty: "ps \<noteq> []" and prefix: "ps = primes_upto (last ps)"
    by (auto simp: consecutive_prime_descriptor_def)
  have sorted_rhs: "sorted (primes_upto (last ps))" by simp
  have sorted: "sorted ps" using prefix sorted_rhs by metis
  have prefix_set_list: "set ps = set (primes_upto (last ps))"
    using prefix by metis
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    using prefix_set_list by (auto simp: set_primes_upto)
  have last_prime: "prime (last ps)"
    using last_in_set[OF nonempty] prefix_set by auto
  let ?q = "next_prime_after (last ps)"
  have lq: "last ps < ?q" by (rule next_prime_after_gt)
  have qavoids: "\<forall>p \<in> set ps. \<not> p dvd ?q"
  proof (intro ballI notI)
    fix p
    assume pin: "p \<in> set ps" and pdvd: "p dvd ?q"
    have pprime: "prime p" using pin prefix_set by auto
    have ple: "p \<le> last ps"
      by (rule sorted_member_le_last[OF sorted nonempty pin])
    have "p = ?q" using pprime next_prime_after_prime pdvd
      by (metis primes_dvd_imp_eq)
    with ple lq show False by arith
  qed
  have qmember: "?q \<in> wheel_survivors ps H"
    using lq horizon qavoids
    by (auto simp: wheel_survivors_def wheel_interval_def wheel_sift_membership)
  have least: "\<And>n. n \<in> wheel_survivors ps H \<Longrightarrow> ?q \<le> n"
  proof -
    fix n
    assume member: "n \<in> wheel_survivors ps H"
    then have bounds: "last ps < n" "n \<le> H"
      and avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
      by (auto simp: wheel_survivors_def wheel_interval_def wheel_sift_membership)
    show "?q \<le> n"
    proof (cases "prime n")
      case True
      then show ?thesis using bounds(1) by (rule next_prime_after_least)
    next
      case False
      have none: "n \<noteq> 1"
        using prime_gt_1_nat[OF last_prime] bounds(1) by arith
      from prime_factor_nat[OF none] obtain p where pprime: "prime p" and pdvd: "p dvd n"
        by blast
      have npos: "0 < n" using bounds(1) by arith
      have ple_n: "p \<le> n" by (rule dvd_imp_le[OF pdvd npos])
      have pne: "p \<noteq> n" using pprime False by auto
      have plt_n: "p < n" using ple_n pne by arith
      have lp: "last ps < p"
      proof (rule ccontr)
        assume "\<not> last ps < p"
        then have "p \<le> last ps" by arith
        then have "p \<in> set ps" using pprime prefix_set by auto
        with avoids pdvd show False by blast
      qed
      have "?q \<le> p" by (rule next_prime_after_least[OF pprime lp])
      also have "p \<le> n" by fact
      finally show ?thesis .
    qed
  qed
  have finite: "finite (wheel_survivors ps H)"
    unfolding wheel_survivors_def wheel_interval_def
    by (rule finite_wheel_sift) simp
  show ?thesis by (rule Min_eqI[OF finite least qmember])
qed

definition complete_wheel_admission :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "complete_wheel_admission ps H \<longleftrightarrow>
    complete_prime_prefix ps H \<and> ps \<noteq> [] \<and>
    next_prime_after (last ps) \<le> H"

theorem least_survivor_is_next_prime:
  assumes admission: "complete_wheel_admission ps H"
  shows "Min (wheel_survivors ps H) = next_prime_after (last ps)"
proof -
  from admission have prefix: "complete_prime_prefix ps H" and nonempty: "ps \<noteq> []"
    and bound: "next_prime_after (last ps) \<le> H"
    by (auto simp: complete_wheel_admission_def)
  let ?q = "next_prime_after (last ps)"
  have qmember: "?q \<in> wheel_survivors ps H"
    using complete_prefix_survivors_are_exact_primes[OF prefix nonempty]
      next_prime_after_gt next_prime_after_prime bound
    by auto
  have least: "\<And>n. n \<in> wheel_survivors ps H \<Longrightarrow> ?q \<le> n"
  proof -
    fix n
    assume "n \<in> wheel_survivors ps H"
    then have "prime n" "last ps < n"
      using complete_prefix_survivors_are_exact_primes[OF prefix nonempty] by auto
    then show "?q \<le> n" by (rule next_prime_after_least)
  qed
  have finite: "finite (wheel_survivors ps H)"
    unfolding wheel_survivors_def wheel_interval_def
    by (rule finite_wheel_sift) simp
  show ?thesis
    by (rule Min_eqI[OF finite least qmember])
qed

theorem complete_prefix_count_is_prime_count:
  assumes prefix: "complete_prime_prefix ps H" and nonempty: "ps \<noteq> []"
  shows "card {n. prime n \<and> n \<le> H} =
    length ps + card (wheel_survivors ps H)"
proof -
  have sorted: "sorted ps" and distinct: "distinct ps"
    using complete_prime_prefix_distinct_sorted[OF prefix] by auto
  have split: "{n. prime n \<and> n \<le> H} =
      set ps \<union> wheel_survivors ps H"
  proof (rule Set.set_eqI)
    fix n
    show "n \<in> {n. prime n \<and> n \<le> H} \<longleftrightarrow>
        n \<in> set ps \<union> wheel_survivors ps H"
    proof
      assume member: "n \<in> {n. prime n \<and> n \<le> H}"
      then have prime: "prime n" and bound: "n \<le> H" by auto
      show "n \<in> set ps \<union> wheel_survivors ps H"
      proof (cases "n \<le> last ps")
        case True
        have last_bound: "last ps \<le> floor_sqrt H"
          using last_in_set[OF nonempty] complete_prime_prefix_set[OF prefix] by auto
        with True prime have "n \<in> set ps"
          using complete_prime_prefix_set[OF prefix] by auto
        then show ?thesis by simp
      next
        case False
        then have "last ps < n" by arith
        with prime bound have "n \<in> wheel_survivors ps H"
          using complete_prefix_survivors_are_exact_primes[OF prefix nonempty] by auto
        then show ?thesis by simp
      qed
    next
      assume member: "n \<in> set ps \<union> wheel_survivors ps H"
      show "n \<in> {n. prime n \<and> n \<le> H}"
      proof (cases "n \<in> set ps")
        case True
        then have "prime n" "n \<le> floor_sqrt H"
          using complete_prime_prefix_set[OF prefix] by auto
        then show ?thesis using floor_sqrt_le[of H] by auto
      next
        case False
        with member have "n \<in> wheel_survivors ps H" by auto
        then show ?thesis
          using complete_prefix_survivors_are_exact_primes[OF prefix nonempty] by auto
      qed
    qed
  qed
  have finite_survivors: "finite (wheel_survivors ps H)"
    unfolding wheel_survivors_def wheel_interval_def
    by (rule finite_wheel_sift) simp
  have disjoint: "set ps \<inter> wheel_survivors ps H = {}"
  proof (rule equals0I)
    fix n
    assume member: "n \<in> set ps \<inter> wheel_survivors ps H"
    then have "n \<le> last ps"
      using sorted_member_le_last[OF sorted nonempty] by auto
    moreover from member have "last ps < n"
      using complete_prefix_survivors_are_exact_primes[OF prefix nonempty] by auto
    ultimately show False by arith
  qed
  have "card {n. prime n \<and> n \<le> H} =
      card (set ps) + card (wheel_survivors ps H)"
    unfolding split
    by (rule card_Un_disjoint[OF finite_set finite_survivors disjoint])
  moreover have "card (set ps) = length ps"
    by (rule distinct_card[OF distinct])
  ultimately show ?thesis by simp
qed

theorem cached_prefix_smaller_horizon_count:
  assumes prefix: "complete_prime_prefix ps H" and smaller: "h \<le> H"
    and nonempty: "trim_prime_prefix ps h \<noteq> []"
  shows "card {n. prime n \<and> n \<le> h} =
    length (trim_prime_prefix ps h) +
    card (wheel_survivors (trim_prime_prefix ps h) h)"
  by (rule complete_prefix_count_is_prime_count)
    (use complete_prefix_smaller_horizon[OF prefix smaller] nonempty in auto)

definition prime_rank :: "nat \<Rightarrow> nat" where
  "prime_rank H = card {p. prime p \<and> p \<le> H}"

definition prime_block_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prime_block_count L H = prime_rank H - prime_rank (L - 1)"

lemma finite_prime_rank_set: "finite {p. prime p \<and> p \<le> (H::nat)}"
  by (rule finite_subset[of _ "{..H}"]) auto

lemma prime_rank_mono:
  assumes "h \<le> H"
  shows "prime_rank h \<le> prime_rank H"
  unfolding prime_rank_def
  by (rule card_mono[OF finite_prime_rank_set]) (use assms in auto)

theorem prime_block_count_exact:
  assumes "L \<le> H"
  shows "prime_block_count L H = card {p. prime p \<and> L \<le> p \<and> p \<le> H}"
proof -
  let ?A = "{p. prime p \<and> p \<le> H}"
  let ?B = "{p. prime p \<and> p \<le> L - 1}"
  have finiteB: "finite ?B" by (rule finite_prime_rank_set)
  have subset: "?B \<subseteq> ?A" using assms by auto
  have diff: "?A - ?B = {p. prime p \<and> L \<le> p \<and> p \<le> H}"
    by (auto dest: prime_gt_1_nat)
  have "card ?A - card ?B = card (?A - ?B)"
    using card_Diff_subset[OF finiteB subset] by simp
  also have "card (?A - ?B) =
      card {p. prime p \<and> L \<le> p \<and> p \<le> H}"
    using diff by simp
  finally show ?thesis
    by (simp only: prime_block_count_def prime_rank_def)
qed

theorem prime_block_bisection:
  assumes "L \<le> M" "M < H"
  shows "prime_block_count L H =
    prime_block_count L M + prime_block_count (Suc M) H"
proof -
  have left_exact: "prime_block_count L M =
      card {p. prime p \<and> L \<le> p \<and> p \<le> M}"
    by (rule prime_block_count_exact[OF assms(1)])
  have right_exact: "prime_block_count (Suc M) H =
      card {p. prime p \<and> Suc M \<le> p \<and> p \<le> H}"
    by (rule prime_block_count_exact) (use assms in simp)
  have whole_exact: "prime_block_count L H =
      card {p. prime p \<and> L \<le> p \<and> p \<le> H}"
    by (rule prime_block_count_exact) (use assms in arith)
  let ?A = "{p. prime p \<and> L \<le> p \<and> p \<le> M}"
  let ?B = "{p. prime p \<and> Suc M \<le> p \<and> p \<le> H}"
  have finiteA: "finite ?A" by (rule finite_subset[of _ "{..M}"]) auto
  have finiteB: "finite ?B" by (rule finite_subset[of _ "{..H}"]) auto
  have disjoint: "?A \<inter> ?B = {}" by auto
  have union: "?A \<union> ?B = {p. prime p \<and> L \<le> p \<and> p \<le> H}"
    using assms by auto
  show ?thesis
    using card_Un_disjoint[OF finiteA finiteB disjoint]
      left_exact right_exact whole_exact union by simp
qed

theorem binary_prime_branch_preserves_target:
  assumes split: "prime_block_count L H =
      prime_block_count L M + prime_block_count (Suc M) H"
    and target: "k < prime_block_count L H"
  shows "(k < prime_block_count L M) \<or>
    (k - prime_block_count L M < prime_block_count (Suc M) H)"
  using assms by arith

theorem singleton_prime_block:
  "prime_block_count n n = (if prime n then 1 else 0)"
proof -
  have exact: "prime_block_count n n =
      card {p. prime p \<and> n \<le> p \<and> p \<le> n}"
    by (rule prime_block_count_exact) simp
  have seteq: "{p. prime p \<and> n \<le> p \<and> p \<le> n} =
      (if prime n then {n} else {})"
    by auto
  show ?thesis using exact seteq by simp
qed

text \<open>
  The numerical recurrence, its postorder store invariant, smaller-horizon
  descriptor transport, and the rank-count branch law above match the values
  consumed by the Python implementation.  This theory does not model Python's
  resource ledger, process-cache authority, exception cleanup, or the concrete
  while-loop stack as generated code.  Those implementation obligations remain
  separate from the arithmetic refinement established here.
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms legendre_finite_prefix_recurrence numerical_Phi_is_sift_card
      numerical_Phi_recurrence_correct valid_phi_store_lookup
      postorder_parent_update_valid complete_prefix_smaller_horizon
      cached_prefix_smaller_horizon_count prime_block_bisection
      binary_prime_branch_preserves_target singleton_prime_block
      discovery_stop_covers_all_primes discovery_stop_constructs_complete_prefix
      append_next_prime_preserves_consecutive_descriptor
      consecutive_descriptor_least_survivor_is_next_prime
      complete_prefix_survivors_are_exact_primes least_survivor_is_next_prime
      complete_prefix_count_is_prime_count}) then ()
    else error "Prime wheel bridge depends on an oracle";
\<close>

end
