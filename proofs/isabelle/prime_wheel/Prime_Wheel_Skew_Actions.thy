theory Prime_Wheel_Skew_Actions
  imports
    Prime_Wheel_Executor
begin

text \<open>
  The production successor descriptor counts old-wheel survivors subject to a
  congruence restriction.  This theory uses the same inclusive prefix and
  depth convention as @{const numerical_Phi}.  Public half-open intervals are
  obtained by subtracting two prefix counts.
\<close>

definition progression_wheel ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "progression_wheel ps x m r =
    {n \<in> wheel_sift ps {1..x}. n mod m = r mod m}"

definition positive_progression_count ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "positive_progression_count x m r = card {n \<in> {1..x}. n mod m = r mod m}"

definition nat_modular_inverse :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_modular_inverse m p = (SOME u. [p * u = 1] (mod m))"

lemma nat_modular_inverse_cong:
  assumes "coprime p m"
  shows "[p * nat_modular_inverse m p = 1] (mod m)"
proof -
  obtain u where inverse: "[p * u = Suc 0] (mod m)"
    using cong_solve_coprime_nat[OF assms] by blast
  have inverse1: "[p * u = 1] (mod m)" using inverse by simp
  have chosen: "[p * (SOME u. [p * u = 1] (mod m)) = 1] (mod m)"
    by (rule someI[of "\<lambda>u. [p * u = 1] (mod m)" u, OF inverse1])
  show ?thesis unfolding nat_modular_inverse_def by (fact chosen)
qed

fun numerical_Psi ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "numerical_Psi ps 0 x m r = positive_progression_count x m r"
| "numerical_Psi ps (Suc d) x m r =
    numerical_Psi ps d x m r -
    numerical_Psi ps d (x div (ps ! d)) m
      ((r * nat_modular_inverse m (ps ! d)) mod m)"

definition progression_interval_count ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "progression_interval_count ps d lo hi m r =
    numerical_Psi ps d (hi - 1) m r - numerical_Psi ps d (lo - 1) m r"

lemma progression_wheel_base:
  "card (progression_wheel [] x m r) = positive_progression_count x m r"
  by (simp add: progression_wheel_def positive_progression_count_def)

lemma finite_progression_wheel [simp]:
  "finite (progression_wheel ps x m r)"
proof -
  have finite_wheel: "finite (wheel_sift ps {1..x})"
    by (rule finite_wheel_sift) simp
  have subset: "progression_wheel ps x m r \<subseteq> wheel_sift ps {1..x}"
    by (auto simp: progression_wheel_def)
  show ?thesis by (rule finite_subset[OF subset finite_wheel])
qed

lemma residue_transport_by_inverse:
  assumes coprime: "coprime p m"
  shows "(p * k) mod m = r mod m \<longleftrightarrow>
    k mod m = (r * nat_modular_inverse m p) mod m"
proof -
  have inverse: "[p * nat_modular_inverse m p = 1] (mod m)"
    by (rule nat_modular_inverse_cong[OF coprime])
  have inverse_commuted: "[nat_modular_inverse m p * p = 1] (mod m)"
    using inverse by (simp add: mult.commute)
  show ?thesis
  proof
    assume eq: "(p * k) mod m = r mod m"
    then have cong: "[p * k = r] (mod m)"
      by (simp add: Cong.cong_def)
    have multiplied:
      "[nat_modular_inverse m p * (p * k) = nat_modular_inverse m p * r] (mod m)"
      by (rule cong_mult) (rule cong_refl, fact cong)
    have reduce_left: "[nat_modular_inverse m p * (p * k) = k] (mod m)"
    proof -
      have "[(nat_modular_inverse m p * p) * k = 1 * k] (mod m)"
        by (rule cong_mult) (fact inverse_commuted, rule cong_refl)
      then show ?thesis by (simp add: mult.assoc)
    qed
    have "[k = nat_modular_inverse m p * r] (mod m)"
      by (rule cong_trans[OF cong_sym[OF reduce_left] multiplied])
    then have "[k = r * nat_modular_inverse m p] (mod m)"
      by (simp add: mult.commute)
    then show "k mod m = (r * nat_modular_inverse m p) mod m"
      by (simp add: Cong.cong_def)
  next
    assume eq: "k mod m = (r * nat_modular_inverse m p) mod m"
    then have cong: "[k = r * nat_modular_inverse m p] (mod m)"
      by (simp add: Cong.cong_def)
    have multiplied: "[p * k = p * (r * nat_modular_inverse m p)] (mod m)"
      by (rule cong_mult) (rule cong_refl, fact cong)
    have reduce_right: "[p * (r * nat_modular_inverse m p) = r] (mod m)"
    proof -
      have "[(p * nat_modular_inverse m p) * r = 1 * r] (mod m)"
        by (rule cong_mult) (fact inverse, rule cong_refl)
      then show ?thesis by (simp add: mult_ac)
    qed
    have "[p * k = r] (mod m)"
      by (rule cong_trans[OF multiplied reduce_right])
    then show "(p * k) mod m = r mod m"
      by (simp add: Cong.cong_def)
  qed
qed

lemma prime_multiples_in_progression_wheel:
  assumes pprime: "prime p"
    and psprime: "\<forall>q \<in> set ps. prime q"
    and fresh: "p \<notin> set ps"
    and coprime: "coprime p m"
  shows "{n \<in> progression_wheel ps x m r. p dvd n} =
    (\<lambda>k. p * k) ` progression_wheel ps (x div p) m
      ((r * nat_modular_inverse m p) mod m)"
proof (rule Set.set_eqI)
  fix n
  have ppos: "0 < p" using prime_gt_1_nat[OF pprime] by arith
  show "n \<in> {n \<in> progression_wheel ps x m r. p dvd n} \<longleftrightarrow>
    n \<in> (\<lambda>k. p * k) ` progression_wheel ps (x div p) m
      ((r * nat_modular_inverse m p) mod m)"
  proof
    assume member: "n \<in> {n \<in> progression_wheel ps x m r. p dvd n}"
    then obtain k where nk: "n = p * k" by (auto elim: dvdE)
    from member have base: "n \<in> wheel_sift ps {1..x}"
      and residue: "n mod m = r mod m"
      by (auto simp: progression_wheel_def)
    from base have npos: "0 < n" and nle: "n \<le> x"
      and avoids: "\<forall>s \<in> set ps. \<not> s dvd n"
      by (auto simp: wheel_sift_membership)
    have kpos: "0 < k" using npos nk by auto
    have kle: "k \<le> x div p"
      using nle ppos nk by (simp add: less_eq_div_iff_mult_less_eq ac_simps)
    have kavoids: "\<forall>s \<in> set ps. \<not> s dvd k"
      using avoids nk by auto
    have kmember: "k \<in> wheel_sift ps {1..x div p}"
      using kpos kle kavoids by (auto simp: wheel_sift_membership)
    have kresidue: "k mod m =
        ((r * nat_modular_inverse m p) mod m) mod m"
      using residue nk residue_transport_by_inverse[OF coprime, of k r] by simp
    have "k \<in> progression_wheel ps (x div p) m
        ((r * nat_modular_inverse m p) mod m)"
      using kmember kresidue by (simp add: progression_wheel_def)
    with nk show "n \<in> (\<lambda>k. p * k) `
        progression_wheel ps (x div p) m
          ((r * nat_modular_inverse m p) mod m)"
      by blast
  next
    assume member: "n \<in> (\<lambda>k. p * k) ` progression_wheel ps (x div p) m
      ((r * nat_modular_inverse m p) mod m)"
    then obtain k where kmember:
      "k \<in> progression_wheel ps (x div p) m
        ((r * nat_modular_inverse m p) mod m)"
      and nk: "n = p * k" by blast
    from kmember have kbase: "k \<in> wheel_sift ps {1..x div p}"
      and kresidue: "k mod m =
        ((r * nat_modular_inverse m p) mod m) mod m"
      by (auto simp: progression_wheel_def)
    have nbase: "n \<in> wheel_sift ps {1..x}"
      using prime_multiples_in_sift[OF pprime psprime fresh, of x] kbase nk by auto
    have nresidue: "n mod m = r mod m"
      using kresidue nk residue_transport_by_inverse[OF coprime, of k r] by simp
    show "n \<in> {n \<in> progression_wheel ps x m r. p dvd n}"
      using nbase nresidue nk by (auto simp: progression_wheel_def)
  qed
qed

lemma card_prime_multiples_in_progression_wheel:
  assumes "prime p" "\<forall>q \<in> set ps. prime q" "p \<notin> set ps" "coprime p m"
  shows "card {n \<in> progression_wheel ps x m r. p dvd n} =
    card (progression_wheel ps (x div p) m
      ((r * nat_modular_inverse m p) mod m))"
proof -
  have "inj_on (\<lambda>k. p * k)
      (progression_wheel ps (x div p) m ((r * nat_modular_inverse m p) mod m))"
    using prime_gt_1_nat[OF assms(1)] by (auto intro!: inj_onI)
  then show ?thesis
    unfolding prime_multiples_in_progression_wheel[OF assms]
    by (rule card_image)
qed

theorem numerical_Psi_is_progression_card:
  assumes depth: "d \<le> length ps"
    and distinct: "distinct ps"
    and primes: "\<forall>p \<in> set ps. prime p"
    and modulus: "m > 0"
    and factor_coprime: "\<forall>p \<in> set ps. coprime p m"
  shows "numerical_Psi ps d x m r =
    card (progression_wheel (rev (take d ps)) x m r)"
  using depth
proof (induction d arbitrary: x r)
  case 0
  then show ?case by (simp add: progression_wheel_base)
next
  case (Suc d)
  let ?p = "ps ! d"
  let ?qs = "rev (take d ps)"
  have pprime: "prime ?p" using Suc.prems primes by auto
  have qsprime: "\<forall>q \<in> set ?qs. prime q"
    using primes set_take_subset[of d ps] by auto
  have take_step: "take (Suc d) ps = take d ps @ [?p]"
    using Suc.prems by (simp add: take_Suc_conv_app_nth)
  have distinct_step: "distinct (take (Suc d) ps)"
    using distinct by simp
  have fresh: "?p \<notin> set ?qs"
    using distinct_step take_step by simp
  have pcoprime: "coprime ?p m" using Suc.prems factor_coprime by auto
  have finite: "finite (progression_wheel ?qs x m r)" by simp
  have recurrence:
    "card (progression_wheel (?p # ?qs) x m r) =
      card (progression_wheel ?qs x m r) -
      card (progression_wheel ?qs (x div ?p) m
        ((r * nat_modular_inverse m ?p) mod m))"
  proof -
    have seteq: "progression_wheel (?p # ?qs) x m r =
        progression_wheel ?qs x m r -
          {n \<in> progression_wheel ?qs x m r. ?p dvd n}"
      by (auto simp: progression_wheel_def)
    have subset: "{n \<in> progression_wheel ?qs x m r. ?p dvd n}
        \<subseteq> progression_wheel ?qs x m r" by auto
    show ?thesis
      using card_Diff_subset[OF _ subset] finite
        card_prime_multiples_in_progression_wheel[OF pprime qsprime fresh pcoprime,
          of x r]
      by (simp add: seteq)
  qed
  have left: "numerical_Psi ps d x m r = card (progression_wheel ?qs x m r)"
    by (rule Suc.IH) (use Suc.prems in simp_all)
  have right: "numerical_Psi ps d (x div ?p) m
      ((r * nat_modular_inverse m ?p) mod m) =
      card (progression_wheel ?qs (x div ?p) m
        ((r * nat_modular_inverse m ?p) mod m))"
    by (rule Suc.IH) (use Suc.prems in simp_all)
  have take_suc: "rev (take (Suc d) ps) = ?p # ?qs"
    using Suc.prems by (simp add: take_Suc_conv_app_nth)
  show ?case using recurrence left right take_suc by simp
qed

corollary numerical_Psi_modulus_one_is_Phi:
  assumes "d \<le> length ps" "distinct ps" "\<forall>p \<in> set ps. prime p"
  shows "numerical_Psi ps d x 1 0 = numerical_Phi ps d x"
proof -
  have psi: "numerical_Psi ps d x 1 0 =
      card (progression_wheel (rev (take d ps)) x 1 0)"
    by (rule numerical_Psi_is_progression_card) (use assms in auto)
  have phi: "numerical_Phi ps d x =
      card (wheel_sift (rev (take d ps)) {1..x})"
    by (rule numerical_Phi_is_sift_card[OF assms])
  show ?thesis using psi phi by (simp add: progression_wheel_def)
qed

theorem fresh_successor_partial_count_equation:
  "numerical_Phi (parent @ [q]) (Suc (length parent)) x =
    numerical_Phi (parent @ [q]) (length parent) x -
    numerical_Phi (parent @ [q]) (length parent) (x div q)"
  by simp

theorem fresh_successor_partial_count_semantics:
  assumes distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "numerical_Phi (parent @ [q]) (Suc (length parent)) x =
    card (wheel_sift (q # rev parent) {1..x})"
proof -
  have exact:
    "numerical_Phi (parent @ [q]) (Suc (length parent)) x =
      card (wheel_sift
        (rev (take (Suc (length parent)) (parent @ [q]))) {1..x})"
    by (rule numerical_Phi_is_sift_card)
      (use distinct primes in simp_all)
  show ?thesis using exact by simp
qed

definition wheel_half_open :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "wheel_half_open ps lo hi = wheel_sift ps {lo..<hi}"

theorem fresh_successor_half_open_count_semantics:
  assumes lower: "1 \<le> lo" and order: "lo \<le> hi"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows
    "(numerical_Phi (parent @ [q]) (length parent) (hi - 1) -
       numerical_Phi (parent @ [q]) (length parent) (lo - 1)) -
     (numerical_Phi (parent @ [q]) (length parent) ((hi - 1) div q) -
       numerical_Phi (parent @ [q]) (length parent) ((lo - 1) div q)) =
     card (wheel_half_open (q # rev parent) lo hi)"
proof -
  let ?full = "parent @ [q]"
  let ?old = "rev parent"
  let ?OH = "wheel_sift ?old {1..hi - 1}"
  let ?OL = "wheel_sift ?old {1..lo - 1}"
  let ?DH = "{n \<in> ?OH. q dvd n}"
  let ?DL = "{n \<in> ?OL. q dvd n}"
  let ?A = "wheel_half_open ?old lo hi"
  let ?D = "{n \<in> ?A. q dvd n}"

  have qprime: "prime q" using primes by simp
  have old_primes: "\<forall>p \<in> set ?old. prime p"
    using primes by auto
  have fresh: "q \<notin> set ?old" using distinct by simp
  have old_take: "rev (take (length parent) ?full) = ?old" by simp

  have phi_hi:
    "numerical_Phi ?full (length parent) (hi - 1) = card ?OH"
    using numerical_Phi_is_sift_card[of "length parent" ?full "hi - 1"]
      distinct primes old_take by simp
  have phi_lo:
    "numerical_Phi ?full (length parent) (lo - 1) = card ?OL"
    using numerical_Phi_is_sift_card[of "length parent" ?full "lo - 1"]
      distinct primes old_take by simp
  have phi_dhi:
    "numerical_Phi ?full (length parent) ((hi - 1) div q) =
      card (wheel_sift ?old {1..(hi - 1) div q})"
    using numerical_Phi_is_sift_card[
      of "length parent" ?full "(hi - 1) div q"] distinct primes old_take
    by simp
  have phi_dlo:
    "numerical_Phi ?full (length parent) ((lo - 1) div q) =
      card (wheel_sift ?old {1..(lo - 1) div q})"
    using numerical_Phi_is_sift_card[
      of "length parent" ?full "(lo - 1) div q"] distinct primes old_take
    by simp

  have finite_OH: "finite ?OH" by (rule finite_wheel_sift) simp
  have finite_OL: "finite ?OL" by (rule finite_wheel_sift) simp
  have OL_subset: "?OL \<subseteq> ?OH" using order
    by (auto simp: wheel_sift_membership)
  have A_diff: "?A = ?OH - ?OL" using lower order
    by (auto simp: wheel_half_open_def wheel_sift_membership)
  have card_A: "card ?A = card ?OH - card ?OL"
    using A_diff card_Diff_subset[OF finite_OL OL_subset] by simp

  have finite_DL: "finite ?DL" using finite_OL by auto
  have DL_subset: "?DL \<subseteq> ?DH" using OL_subset by auto
  have D_diff: "?D = ?DH - ?DL" using A_diff by auto
  have card_D: "card ?D = card ?DH - card ?DL"
    using D_diff card_Diff_subset[OF finite_DL DL_subset] by simp
  have card_DH:
    "card ?DH = card (wheel_sift ?old {1..(hi - 1) div q})"
    by (rule card_prime_multiples_in_sift[OF qprime old_primes fresh])
  have card_DL:
    "card ?DL = card (wheel_sift ?old {1..(lo - 1) div q})"
    by (rule card_prime_multiples_in_sift[OF qprime old_primes fresh])

  have finite_D: "finite ?D" using finite_OH A_diff by auto
  have D_subset: "?D \<subseteq> ?A" by auto
  have filtered: "wheel_half_open (q # ?old) lo hi = ?A - ?D"
    by (auto simp: wheel_half_open_def wheel_sift_membership)
  have card_filtered:
    "card (wheel_half_open (q # ?old) lo hi) = card ?A - card ?D"
    using filtered card_Diff_subset[OF finite_D D_subset] by simp

  show ?thesis
    using phi_hi phi_lo phi_dhi phi_dlo card_A card_D card_DH card_DL
      card_filtered
    by simp
qed

theorem complete_prefix_half_open_prime_count:
  assumes prefix: "complete_prime_prefix ps H"
    and nonempty: "ps \<noteq> []"
    and lower: "2 \<le> lo"
    and order: "lo \<le> hi"
    and upper: "hi \<le> Suc H"
  shows
    "card {p \<in> set ps. lo \<le> p \<and> p < hi} +
       card (wheel_half_open (rev ps) lo hi) =
     card {p. prime p \<and> lo \<le> p \<and> p < hi}"
proof -
  let ?K = "{p \<in> set ps. lo \<le> p \<and> p < hi}"
  let ?B = "wheel_half_open (rev ps) lo hi"
  let ?Q = "{p. prime p \<and> lo \<le> p \<and> p < hi}"
  have descriptor_primes: "\<forall>p \<in> set ps. prime p"
    using complete_prime_prefix_set[OF prefix] by auto
  have split: "?Q = ?K \<union> ?B"
  proof (rule Set.set_eqI)
    fix n
    show "n \<in> ?Q \<longleftrightarrow> n \<in> ?K \<union> ?B"
    proof
      assume member: "n \<in> ?Q"
      then have nprime: "prime n" and bounds: "lo \<le> n" "n < hi" by auto
      show "n \<in> ?K \<union> ?B"
      proof (cases "n \<in> set ps")
        case True
        with bounds show ?thesis by auto
      next
        case False
        have avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
        proof (intro ballI notI)
          fix p
          assume pin: "p \<in> set ps" and pdvd: "p dvd n"
          have pprime: "prime p" using descriptor_primes pin by blast
          have "p = n" using pprime nprime pdvd by (metis primes_dvd_imp_eq)
          with pin False show False by simp
        qed
        with bounds show ?thesis
          by (auto simp: wheel_half_open_def wheel_sift_membership)
      qed
    next
      assume member: "n \<in> ?K \<union> ?B"
      show "n \<in> ?Q"
      proof (cases "n \<in> ?K")
        case True
        with descriptor_primes show ?thesis by auto
      next
        case False
        with member have bmember: "n \<in> ?B" by auto
        then have bounds: "lo \<le> n" "n < hi"
          and avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
          by (auto simp: wheel_half_open_def wheel_sift_membership)
        have one: "1 < n" using lower bounds by arith
        have hbound: "n \<le> H" using upper bounds by arith
        have "prime n"
        proof (rule ccontr)
          assume "\<not> prime n"
          from complete_prefix_prime_divisor[OF prefix one hbound this]
          show False using avoids by blast
        qed
        with bounds show ?thesis by auto
      qed
    qed
  qed
  have finiteK: "finite ?K" by auto
  have finiteB: "finite ?B"
    by (auto simp: wheel_half_open_def intro: finite_wheel_sift)
  have disjoint: "?K \<inter> ?B = {}"
  proof (rule equals0I)
    fix n
    assume member: "n \<in> ?K \<inter> ?B"
    then have nin: "n \<in> set ps" and avoids: "\<forall>p \<in> set ps. \<not> p dvd n"
      by (auto simp: wheel_half_open_def wheel_sift_membership)
    show False using nin avoids by auto
  qed
  have "card ?Q = card ?K + card ?B"
    unfolding split by (rule card_Un_disjoint[OF finiteK finiteB disjoint])
  then show ?thesis by simp
qed

lemma progression_interval_count_exact:
  assumes "d \<le> length ps" "distinct ps" "\<forall>p \<in> set ps. prime p"
    "m > 0" "\<forall>p \<in> set ps. coprime p m" "lo \<le> hi"
  shows "progression_interval_count ps d lo hi m r =
    card {n \<in> progression_wheel (rev (take d ps)) (hi - 1) m r. lo \<le> n}"
proof -
  let ?qs = "rev (take d ps)"
  let ?A = "progression_wheel ?qs (hi - 1) m r"
  let ?B = "progression_wheel ?qs (lo - 1) m r"
  have finiteB: "finite ?B" by simp
  have subset: "?B \<subseteq> ?A" using assms
    by (auto simp: progression_wheel_def wheel_sift_membership)
  have diff: "?A - ?B = {n \<in> ?A. lo \<le> n}" using assms
    by (auto simp: progression_wheel_def wheel_sift_membership)
  have exact_hi: "numerical_Psi ps d (hi - 1) m r = card ?A"
    by (rule numerical_Psi_is_progression_card) (use assms in auto)
  have exact_lo: "numerical_Psi ps d (lo - 1) m r = card ?B"
    by (rule numerical_Psi_is_progression_card) (use assms in auto)
  show ?thesis
    unfolding progression_interval_count_def exact_hi exact_lo
    using card_Diff_subset[OF finiteB subset] diff by simp
qed

text \<open>
  A fresh-prime action has one port for every incoming residue.  Its semantic
  payload is kept as the complete mark word here; production may store a
  source-bound scan DAG, provided rank and select refine this word.
\<close>

definition fresh_mark ::
    "nat set \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "fresh_mark old q forbidden phase i \<longleftrightarrow>
    i \<in> old \<and> (phase + i) mod q \<notin> forbidden"

definition fresh_block_word ::
    "nat set \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "fresh_block_word old q forbidden phase W =
    map (\<lambda>i. fresh_mark old q forbidden phase (Suc i)) [0..<W]"

definition phase_after :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "phase_after (q::nat) (phase::nat) (phase_width::nat) =
    (phase + phase_width) mod q"

lemma phase_after_zero [simp]: "q > 0 \<Longrightarrow> phase_after q phase 0 = phase mod q"
  by (simp add: phase_after_def)

lemma phase_after_compose:
  "q > 0 \<Longrightarrow> phase_after q (phase_after q a m) n = phase_after q a (m+n)"
proof -
  have "phase_after q (phase_after q a m) n =
      (((a + m) mod q) + n) mod q"
    by (simp only: phase_after_def)
  also have "... = ((a + m) + n) mod q"
    by (rule mod_add_left_eq)
  also have "... = phase_after q a (m+n)"
    by (simp only: phase_after_def add.assoc)
  finally show ?thesis .
qed

lemma full_fresh_phase_cycle:
  assumes "q > 0"
  shows "phase_after q a (q * W) = a mod q"
  using assms by (simp add: phase_after_def mod_add_left_eq)

definition mark_rank_before :: "bool list \<Rightarrow> nat \<Rightarrow> nat" where
  "mark_rank_before xs k = length (filter id (take k xs))"

definition mark_select :: "bool list \<Rightarrow> nat \<Rightarrow> nat option" where
  "mark_select xs k = (if k < length (filter id xs)
    then Some (LEAST i. i < length xs \<and> xs ! i \<and> mark_rank_before xs i = k)
    else None)"

lemma mark_rank_before_append_left:
  "k \<le> length xs \<Longrightarrow> mark_rank_before (xs @ ys) k = mark_rank_before xs k"
  by (simp add: mark_rank_before_def take_append)

lemma mark_rank_before_append_right:
  "length xs \<le> k \<Longrightarrow> mark_rank_before (xs @ ys) k =
    mark_rank_before xs (length xs) + mark_rank_before ys (k - length xs)"
  by (simp add: mark_rank_before_def take_append filter_append)

text \<open>
  The seven-deletion argument is independent of every finite Goldbach audit.
  Its only arithmetic input is the cardinality of a residue class inside the
  open interval @{term "{x. q < x \<and> x < 5*q}"}.
\<close>

definition five_q_window :: "nat \<Rightarrow> nat set" where
  "five_q_window q = {x. q < x \<and> x < 5*q}"

definition residue_sites :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "residue_sites q r = {x \<in> five_q_window q. x mod q = r mod q}"

lemma quotient_in_four_slots:
  assumes "q > 0" "x \<in> five_q_window q"
  shows "x div q \<in> {1,2,3,4}"
proof -
  from assms have lower_value: "q \<le> x" and upper_value: "x < 5*q"
    by (auto simp: five_q_window_def)
  have lower: "1 \<le> x div q"
    using less_eq_div_iff_mult_less_eq[OF assms(1), of 1 x] lower_value by simp
  have upper: "x div q < 5"
    using div_less_iff_less_mult[OF assms(1), of x 5] upper_value
    by (simp add: mult.commute)
  have "x div q = 1 \<or> x div q = 2 \<or> x div q = 3 \<or> x div q = 4"
    using lower upper by arith
  then show ?thesis by auto
qed

lemma same_residue_and_quotient:
  fixes q x y :: nat
  assumes "q > 0" "x mod q = y mod q" "x div q = y div q"
  shows "x = y"
proof -
  have "x = (x div q) * q + x mod q" by simp
  also have "... = (y div q) * q + y mod q" using assms by simp
  also have "... = y" by simp
  finally show ?thesis .
qed

lemma residue_sites_at_most_four:
  assumes "q > 0"
  shows "card (residue_sites q r) \<le> 4"
proof -
  have finite: "finite (residue_sites q r)"
    by (rule finite_subset[of _ "{..5*q}"]) (auto simp: residue_sites_def five_q_window_def)
  have inj: "inj_on (\<lambda>x. x div q) (residue_sites q r)"
    using assms by (auto simp: inj_on_def residue_sites_def
      intro: same_residue_and_quotient)
  have image: "(\<lambda>x. x div q) ` residue_sites q r \<subseteq>
      ({1,2,3,4} :: nat set)"
    using quotient_in_four_slots[OF assms] by (auto simp: residue_sites_def)
  have "card (residue_sites q r) = card ((\<lambda>x. x div q) ` residue_sites q r)"
    by (rule card_image[symmetric, OF inj])
  also have "... \<le> card ({1,2,3,4} :: nat set)"
    by (rule card_mono) (use image in auto)
  finally show ?thesis by simp
qed

lemma zero_residue_sites:
  assumes "q > 0"
  shows "residue_sites q 0 = {2*q,3*q,4*q}"
proof (rule Set.set_eqI)
  fix x
  show "x \<in> residue_sites q 0 \<longleftrightarrow> x \<in> {2*q,3*q,4*q}"
  proof
    assume member: "x \<in> residue_sites q 0"
    then have window: "q < x" "x < 5*q" and dvd: "q dvd x"
      by (auto simp: residue_sites_def five_q_window_def dvd_eq_mod_eq_0)
    then obtain k where xk: "x = q*k" by (auto elim: dvdE)
    have lower_product: "q * 1 < q * k" using window xk by simp
    have upper_product: "q * k < q * 5"
      using window xk by (simp add: mult.commute)
    have "1 < k" using lower_product assms by simp
    moreover have "k < 5" using upper_product assms by simp
    ultimately have "1 < k" "k < 5" by simp_all
    then have "k = 2 \<or> k = 3 \<or> k = 4" by arith
    with xk show "x \<in> {2*q,3*q,4*q}" by auto
  next
    assume "x \<in> {2*q,3*q,4*q}"
    with assms show "x \<in> residue_sites q 0"
      by (auto simp: residue_sites_def five_q_window_def)
  qed
qed

lemma zero_residue_sites_card:
  assumes "q > 0"
  shows "card (residue_sites q 0) = 3"
  using assms zero_residue_sites[OF assms] by auto

definition fresh_deleted_sites :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "fresh_deleted_sites q target = residue_sites q 0 \<union> residue_sites q target"

theorem fresh_prime_deletes_at_most_seven:
  assumes "q > 0"
  shows "card (fresh_deleted_sites q target) \<le> 7"
proof -
  have finite0: "finite (residue_sites q 0)"
    by (rule finite_subset[of _ "{..5*q}"]) (auto simp: residue_sites_def five_q_window_def)
  have finiter: "finite (residue_sites q target)"
    by (rule finite_subset[of _ "{..5*q}"]) (auto simp: residue_sites_def five_q_window_def)
  have "card (fresh_deleted_sites q target) \<le>
      card (residue_sites q 0) + card (residue_sites q target)"
    unfolding fresh_deleted_sites_def by (rule card_Un_le)
  also have "... \<le> 3 + 4"
    using zero_residue_sites_card[OF assms] residue_sites_at_most_four[OF assms] by simp
  finally show ?thesis by simp
qed

theorem eight_prebirth_survivors_leave_one:
  assumes finite: "finite prebirth"
    and eight: "8 \<le> card prebirth"
    and deleted: "deleted \<subseteq> fresh_deleted_sites q target"
    and qpos: "q > 0"
  shows "prebirth - deleted \<noteq> {}"
proof
  assume empty: "prebirth - deleted = {}"
  then have subset: "prebirth \<subseteq> deleted" by auto
  have finite_fresh: "finite (fresh_deleted_sites q target)"
    unfolding fresh_deleted_sites_def
    by (rule finite_UnI;
        rule finite_subset[of _ "{..5*q}"];
        auto simp: residue_sites_def five_q_window_def)
  have finite_deleted: "finite deleted"
    by (rule finite_subset[OF deleted finite_fresh])
  have "card prebirth \<le> card deleted"
    by (rule card_mono[OF finite_deleted subset])
  also have "... \<le> card (fresh_deleted_sites q target)"
    by (rule card_mono[OF finite_fresh deleted])
  also have "... \<le> 7" by (rule fresh_prime_deletes_at_most_seven[OF qpos])
  finally show False using eight by arith
qed

text \<open>
  This theory proves the executable arithmetic recurrence and the universal
  seven-deletion implication.  It does not assert the observed stage-49--256
  eight-survivor lower bound for untested stages, nor any universal Goldbach
  theorem.  Full scan-DAG selection refinement and Python ledger/lease behavior
  remain separate executable obligations.
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms numerical_Psi_is_progression_card numerical_Psi_modulus_one_is_Phi
      fresh_successor_partial_count_equation fresh_successor_partial_count_semantics
      fresh_successor_half_open_count_semantics
      complete_prefix_half_open_prime_count
      progression_interval_count_exact phase_after_compose full_fresh_phase_cycle
      mark_rank_before_append_left mark_rank_before_append_right
      zero_residue_sites_card residue_sites_at_most_four
      fresh_prime_deletes_at_most_seven eight_prebirth_survivors_leave_one}) then ()
    else error "Prime skew action theory depends on an oracle";
\<close>

end
