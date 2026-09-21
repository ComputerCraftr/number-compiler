theory Cylinder_Radial_Event_Clock
  imports Main
begin

text \<open>
  Exact certificate algebra for scalar radial event packets. Expanding only
  the relative shift after t = 1+z does not expand the radial exponent.
  This theory does not yet prove the Wronskian valuation bound, the gap
  partition algorithm, source admission, or temporal packet-count closure.
\<close>

lemma radial_event_shift_basis:
  fixes z c :: int
  shows "c * z^d * (1+z)^r =
    (\<Sum>k\<le>d. (c * int (d choose k) * (-1)^(d-k)) * (1+z)^(r+k))"
proof -
  have expansion: "z^d =
    (\<Sum>k\<le>d. int (d choose k) * (1+z)^k * (-1)^(d-k))"
    using binomial_ring[of "1+z" "-1" d] by simp
  show ?thesis
    unfolding expansion
    by (simp add: sum_distrib_left sum_distrib_right power_add algebra_simps)
qed

definition radial_basis_value :: "(nat * int) list => int => int" where
  "radial_basis_value entries t = sum_list (map (\<lambda>(e,c). c*t^e) entries)"

definition radial_basis_coefficient :: "(nat * int) list => nat => int" where
  "radial_basis_coefficient entries e =
    sum_list (map (\<lambda>(k,c). if k=e then c else 0) entries)"

lemma radial_basis_value_cons:
  "radial_basis_value ((k,c)#entries) t = c*t^k + radial_basis_value entries t"
  by (simp add: radial_basis_value_def)

lemma radial_basis_coefficient_cons:
  "radial_basis_coefficient ((k,c)#entries) e =
    (if k=e then c else 0) + radial_basis_coefficient entries e"
  by (simp add: radial_basis_coefficient_def)

lemma radial_basis_grouping:
  assumes finite: "finite E" and support: "set (map fst entries) \<subseteq> E"
  shows "radial_basis_value entries t =
    (\<Sum>e\<in>E. radial_basis_coefficient entries e * t^e)"
  using support
proof (induction entries)
  case Nil
  then show ?case by (simp add: radial_basis_value_def radial_basis_coefficient_def)
next
  case (Cons entry entries)
  obtain k c where entry: "entry = (k,c)" by (cases entry) auto
  have member: "k \<in> E" and tail: "set (map fst entries) \<subseteq> E"
    using Cons.prems by (auto simp: entry)
  have previous: "radial_basis_value entries t =
    (\<Sum>e\<in>E. radial_basis_coefficient entries e * t^e)"
    using Cons.IH[OF tail] .
  have contribution:
    "radial_basis_coefficient ((k,c)#entries) e * t^e =
      (if e=k then c*t^k else 0) + radial_basis_coefficient entries e * t^e" for e
    by (auto simp: radial_basis_coefficient_cons algebra_simps)
  show ?case
    using previous finite member
    by (simp only: entry radial_basis_value_cons contribution sum.distrib;
        simp add: sum.delta)
qed

theorem radial_basis_zero_certificate:
  assumes certificate:
    "\<forall>e\<in>set (map fst entries). radial_basis_coefficient entries e = 0"
  shows "radial_basis_value entries t = 0"
  using radial_basis_grouping[of "set (map fst entries)" entries t] certificate
  by simp

text \<open>
  A zero certificate checks all sparse basis coefficients. A truncated zero
  jet is not its substitute. The shift-basis formula and grouping establish
  the arithmetic meaning of that certificate.
\<close>

record executable_radial_packet =
  radial_coefficient :: int
  radial_shift :: int
  radial_growth :: nat

definition radial_packet_basis_entries ::
    "int \<Rightarrow> executable_radial_packet \<Rightarrow> (nat * int) list" where
  "radial_packet_basis_entries origin packet =
    (let degree = nat (radial_shift packet - origin) in
      map (\<lambda>k. (radial_growth packet + k,
        radial_coefficient packet * int (degree choose k) * (-1)^(degree-k)))
        [0..<Suc degree])"

definition radial_packets_basis_entries ::
    "int \<Rightarrow> executable_radial_packet list \<Rightarrow> (nat * int) list" where
  "radial_packets_basis_entries origin packets =
    concat (map (radial_packet_basis_entries origin) packets)"

definition radial_sparse_zero_certificate ::
    "int \<Rightarrow> executable_radial_packet list \<Rightarrow> bool" where
  "radial_sparse_zero_certificate origin packets \<longleftrightarrow>
    (let entries = radial_packets_basis_entries origin packets in
      list_all (\<lambda>e. radial_basis_coefficient entries e = 0) (map fst entries))"

definition radial_weighted_basis_value ::
    "(nat * int) list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int" where
  "radial_weighted_basis_value entries weight =
    sum_list (map (\<lambda>(e,c). c * weight e) entries)"

lemma radial_weighted_basis_value_cons:
  "radial_weighted_basis_value ((k,c)#entries) weight =
    c * weight k + radial_weighted_basis_value entries weight"
  by (simp add: radial_weighted_basis_value_def)

lemma radial_weighted_basis_value_append:
  "radial_weighted_basis_value (left @ right) weight =
    radial_weighted_basis_value left weight +
      radial_weighted_basis_value right weight"
  by (simp add: radial_weighted_basis_value_def)

lemma radial_weighted_basis_grouping:
  assumes finite: "finite E" and support: "set (map fst entries) \<subseteq> E"
  shows "radial_weighted_basis_value entries weight =
    (\<Sum>e\<in>E. radial_basis_coefficient entries e * weight e)"
  using support
proof (induction entries)
  case Nil
  then show ?case
    by (simp add: radial_weighted_basis_value_def radial_basis_coefficient_def)
next
  case (Cons entry entries)
  obtain k c where entry: "entry = (k,c)" by (cases entry) auto
  have member: "k \<in> E" and tail: "set (map fst entries) \<subseteq> E"
    using Cons.prems by (auto simp: entry)
  have previous: "radial_weighted_basis_value entries weight =
      (\<Sum>e\<in>E. radial_basis_coefficient entries e * weight e)"
    using Cons.IH[OF tail] .
  have contribution:
    "radial_basis_coefficient ((k,c)#entries) e * weight e =
      (if e=k then c * weight k else 0) +
        radial_basis_coefficient entries e * weight e" for e
    by (auto simp: radial_basis_coefficient_cons algebra_simps)
  show ?case
    using previous finite member
    by (simp only: entry radial_weighted_basis_value_cons
        contribution sum.distrib; simp add: sum.delta)
qed

lemma radial_sparse_dictionary_zero:
  assumes certificate:
    "\<forall>e\<in>set (map fst entries). radial_basis_coefficient entries e = 0"
  shows "radial_weighted_basis_value entries weight = 0"
  using radial_weighted_basis_grouping[of "set (map fst entries)" entries weight]
    certificate by simp

definition radial_binomial_difference :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "radial_binomial_difference d r n =
    (\<Sum>k\<le>d. int (d choose k) * (-1)^(d-k) * int ((r+k) choose n))"

lemma radial_binomial_tail_reindex:
  fixes f :: "nat \<Rightarrow> int"
  shows "(-1)^(Suc d) * f 0 +
      (\<Sum>k\<le>d. int (d choose Suc k) * (-1)^(d-k) * f (Suc k)) =
    - (\<Sum>k\<le>d. int (d choose k) * (-1)^(d-k) * f k)"
proof (cases d)
  case 0
  then show ?thesis by simp
next
  case (Suc q)
  let ?g = "\<lambda>k. int (Suc q choose k) * (-1)^(Suc q-k) * f k"
  let ?h = "\<lambda>k. int (Suc q choose Suc k) *
    (-1)^(Suc q-k) * f (Suc k)"
  have old_split: "(\<Sum>k\<le>Suc q. ?g k) = ?g 0 + (\<Sum>k\<le>q. ?g (Suc k))"
    by (rule sum.atMost_Suc_shift)
  have tail_drop: "(\<Sum>k\<le>Suc q. ?h k) = (\<Sum>k\<le>q. ?h k)"
    by (subst sum.atMost_Suc) (simp add: binomial_eq_0)
  have head: "(-1)^(Suc (Suc q)) * f 0 = - ?g 0"
    by simp
  have tail_term: "?h k = - ?g (Suc k)" if "k \<le> q" for k
    using that by (simp add: Suc_diff_le algebra_simps)
  have tail: "(\<Sum>k\<le>q. ?h k) = - (\<Sum>k\<le>q. ?g (Suc k))"
  proof -
    have "(\<Sum>k\<le>q. ?h k) = (\<Sum>k\<le>q. - ?g (Suc k))"
    proof (rule sum.cong)
      show "{..q} = {..q}" by simp
      fix k
      assume "k \<in> {..q}"
      then show "?h k = - ?g (Suc k)"
        using tail_term[of k] by simp
    qed
    then show ?thesis by (simp add: sum_negf)
  qed
  show ?thesis
    unfolding Suc using old_split tail_drop head tail by simp
qed

lemma radial_binomial_difference_Suc:
  "radial_binomial_difference (Suc d) r n =
    radial_binomial_difference d (Suc r) n - radial_binomial_difference d r n"
proof -
  let ?f = "\<lambda>k. int ((r+k) choose n)"
  have split: "radial_binomial_difference (Suc d) r n =
      (-1)^(Suc d) * ?f 0 +
      (\<Sum>k\<le>d. (int (d choose k) + int (d choose Suc k)) *
        (-1)^(d-k) * ?f (Suc k))"
    unfolding radial_binomial_difference_def
    by (subst sum.atMost_Suc_shift) (simp add: algebra_simps)
  also have "... =
      (\<Sum>k\<le>d. int (d choose k) * (-1)^(d-k) * ?f (Suc k)) +
      ((-1)^(Suc d) * ?f 0 +
       (\<Sum>k\<le>d. int (d choose Suc k) * (-1)^(d-k) * ?f (Suc k)))"
    by (simp add: sum.distrib algebra_simps)
  also have "... =
      (\<Sum>k\<le>d. int (d choose k) * (-1)^(d-k) * ?f (Suc k)) -
      (\<Sum>k\<le>d. int (d choose k) * (-1)^(d-k) * ?f k)"
    using radial_binomial_tail_reindex[of d ?f] by simp
  also have "... = radial_binomial_difference d (Suc r) n -
      radial_binomial_difference d r n"
    unfolding radial_binomial_difference_def by simp
  finally show ?thesis .
qed

lemma radial_binomial_difference_closed:
  "radial_binomial_difference d r n =
    (if d \<le> n then int (r choose (n-d)) else 0)"
proof (induction d arbitrary: r n)
  case 0
  then show ?case by (simp add: radial_binomial_difference_def)
next
  case (Suc d)
  show ?case
  proof (cases "Suc d \<le> n")
    case True
    then obtain m where n: "n = Suc d + m" by (metis le_iff_add)
    show ?thesis
      unfolding radial_binomial_difference_Suc Suc.IH n
      by (cases m) simp_all
  next
    case False
    then have "n \<le> d" by linarith
    then show ?thesis
      unfolding radial_binomial_difference_Suc Suc.IH using False by simp
  qed
qed

definition radial_packet_at :: "executable_radial_packet \<Rightarrow> int \<Rightarrow> int" where
  "radial_packet_at packet position =
    (if radial_shift packet \<le> position then
       radial_coefficient packet *
         int (radial_growth packet choose nat (position - radial_shift packet))
     else 0)"

definition radial_packets_at :: "executable_radial_packet list \<Rightarrow> int \<Rightarrow> int" where
  "radial_packets_at packets position =
    sum_list (map (\<lambda>packet. radial_packet_at packet position) packets)"

fun radial_jet_search_from ::
    "executable_radial_packet list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int * int) option" where
  "radial_jet_search_from packets position 0 = None"
| "radial_jet_search_from packets position (Suc fuel) =
    (let value = radial_packets_at packets position in
      if value \<noteq> 0 then Some (position, value)
      else radial_jet_search_from packets (position + 1) fuel)"

definition radial_first_event ::
    "executable_radial_packet list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "radial_first_event packets position leading \<longleftrightarrow>
    leading = radial_packets_at packets position \<and>
    leading \<noteq> 0 \<and>
    (\<forall>earlier<position. radial_packets_at packets earlier = 0)"

lemma radial_packets_at_append:
  "radial_packets_at (left @ right) position =
    radial_packets_at left position + radial_packets_at right position"
  by (simp add: radial_packets_at_def)

lemma radial_packet_before_shift:
  assumes "position < radial_shift packet"
  shows "radial_packet_at packet position = 0"
  using assms by (simp add: radial_packet_at_def)

lemma radial_packets_before_lower_bound:
  assumes lower: "\<forall>packet\<in>set packets. lower_bound \<le> radial_shift packet"
      and position: "position < lower_bound"
  shows "radial_packets_at packets position = 0"
  using lower
proof (induction packets)
  case Nil
  then show ?case by (simp add: radial_packets_at_def)
next
  case (Cons packet packets)
  have packet: "radial_packet_at packet position = 0"
    using Cons.prems position by (auto intro: radial_packet_before_shift)
  have tail: "radial_packets_at packets position = 0"
    using Cons.IH Cons.prems by auto
  show ?case using packet tail by (simp add: radial_packets_at_def)
qed

lemma radial_sum_list_map_upt:
  "sum_list (map f [0..<m]) = (\<Sum>k<m. f k)"
  by (induction m) (simp_all add: atLeast0_lessThan_Suc)

lemma radial_packet_basis_coefficient:
  assumes origin: "origin \<le> radial_shift packet"
  shows "radial_weighted_basis_value (radial_packet_basis_entries origin packet)
      (\<lambda>e. int (e choose n)) =
    radial_packet_at packet (origin + int n)"
proof -
  let ?d = "nat (radial_shift packet - origin)"
  have shift: "radial_shift packet = origin + int ?d" using origin by simp
  have difference:
    "(\<Sum>k\<le>?d. int (?d choose k) * (-1)^(?d-k) *
      int ((radial_growth packet+k) choose n)) =
      (if ?d \<le> n then int (radial_growth packet choose (n-?d)) else 0)"
    using radial_binomial_difference_closed[of ?d "radial_growth packet" n]
    by (simp add: radial_binomial_difference_def)
  have entries:
    "radial_weighted_basis_value (radial_packet_basis_entries origin packet)
        (\<lambda>e. int (e choose n)) =
      radial_coefficient packet *
        (\<Sum>k\<le>?d. int (?d choose k) * (-1)^(?d-k) *
          int ((radial_growth packet+k) choose n))"
    unfolding radial_packet_basis_entries_def radial_weighted_basis_value_def
      Let_def
    by (simp add: radial_sum_list_map_upt sum.lessThan_Suc
        sum_distrib_left algebra_simps flip: lessThan_Suc_atMost)
  have starts:
    "(radial_shift packet \<le> origin + int n) = (?d \<le> n)"
    using shift by (simp only: nat_le_iff; linarith)
  show ?thesis
  proof (cases "?d \<le> n")
    case True
    have integer_index:
      "origin + int n - radial_shift packet = int (n - ?d)"
      using shift True by simp
    have index:
      "nat (origin + int n - radial_shift packet) = n - ?d"
      by (simp only: integer_index nat_int)
    show ?thesis
      unfolding radial_packet_at_def
      using entries difference starts True index by simp
  next
    case False
    show ?thesis
      unfolding radial_packet_at_def
      using entries difference starts False by simp
  qed
qed

lemma radial_packets_basis_coefficient:
  assumes origin: "\<forall>packet\<in>set packets. origin \<le> radial_shift packet"
  shows "radial_weighted_basis_value (radial_packets_basis_entries origin packets)
      (\<lambda>e. int (e choose n)) =
    radial_packets_at packets (origin + int n)"
  using origin
proof (induction packets)
  case Nil
  then show ?case
    by (simp add: radial_packets_basis_entries_def radial_weighted_basis_value_def
        radial_packets_at_def)
next
  case (Cons packet packets)
  have head: "radial_weighted_basis_value
      (radial_packet_basis_entries origin packet) (\<lambda>e. int (e choose n)) =
      radial_packet_at packet (origin + int n)"
    using radial_packet_basis_coefficient Cons.prems by auto
  have tail: "radial_weighted_basis_value
      (radial_packets_basis_entries origin packets) (\<lambda>e. int (e choose n)) =
      radial_packets_at packets (origin + int n)"
    using Cons.IH Cons.prems by auto
  show ?case
    using head tail
    by (simp add: radial_packets_basis_entries_def
        radial_weighted_basis_value_append radial_packets_at_def)
qed

theorem radial_sparse_zero_certificate_sound:
  assumes certificate: "radial_sparse_zero_certificate origin packets"
      and origin: "\<forall>packet\<in>set packets. origin \<le> radial_shift packet"
  shows "radial_packets_at packets position = 0"
proof (cases "position < origin")
  case True
  show ?thesis
    using radial_packets_before_lower_bound[OF origin True] .
next
  case False
  let ?entries = "radial_packets_basis_entries origin packets"
  let ?n = "nat (position - origin)"
  have position: "position = origin + int ?n" using False by simp
  have dictionary:
    "\<forall>e\<in>set (map fst ?entries). radial_basis_coefficient ?entries e = 0"
    using certificate
    by (simp add: radial_sparse_zero_certificate_def list_all_iff Let_def)
  have weighted: "radial_weighted_basis_value ?entries
      (\<lambda>e. int (e choose ?n)) = 0"
    using radial_sparse_dictionary_zero[OF dictionary] .
  show ?thesis
    using radial_packets_basis_coefficient[OF origin, of ?n] weighted position by simp
qed

lemma radial_jet_search_from_sound:
  assumes search:
    "radial_jet_search_from packets start fuel = Some (position, leading)"
  shows "leading = radial_packets_at packets position \<and>
    leading \<noteq> 0 \<and>
    start \<le> position \<and>
    position < start + int fuel \<and>
    (\<forall>earlier. start \<le> earlier \<and> earlier < position \<longrightarrow>
      radial_packets_at packets earlier = 0)"
  using search
proof (induction fuel arbitrary: start)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "radial_packets_at packets start = 0")
    case False
    then show ?thesis using Suc.prems by auto
  next
    case True
    have recurse:
      "radial_jet_search_from packets (start + 1) fuel =
        Some (position, leading)"
      using Suc.prems True by simp
    have IH: "leading = radial_packets_at packets position \<and>
        leading \<noteq> 0 \<and>
        start + 1 \<le> position \<and>
        position < start + 1 + int fuel \<and>
        (\<forall>earlier. start + 1 \<le> earlier \<and> earlier < position \<longrightarrow>
          radial_packets_at packets earlier = 0)"
      using Suc.IH[OF recurse] .
    have before: "radial_packets_at packets earlier = 0"
      if "start \<le> earlier" "earlier < position" for earlier
    proof (cases "earlier = start")
      case True
      then show ?thesis using `radial_packets_at packets start = 0` by simp
    next
      case False
      have "start + 1 \<le> earlier" using that False by linarith
      then show ?thesis using IH that by blast
    qed
    show ?thesis using IH before by simp
  qed
qed

text \<open>
  The next theorem is the executable worklist's successful branch.  Earlier
  blocks have already passed an exact zero certificate.  The current bounded
  jet is searched in increasing order.  A gap places every unvisited packet
  at or beyond the end of that search.  These facts suffice for a genuine
  first-event witness; no valuation theorem is used here.
\<close>

theorem radial_gap_worklist_witness_sound:
  assumes search:
    "radial_jet_search_from block start fuel = Some (position, leading)"
      and prior_zero: "\<forall>n. radial_packets_at prior n = 0"
      and block_lower: "\<forall>packet\<in>set block. start \<le> radial_shift packet"
      and later_lower:
        "\<forall>packet\<in>set later. start + int fuel \<le> radial_shift packet"
  shows "radial_first_event (prior @ block @ later) position leading"
proof -
  have leading: "leading = radial_packets_at block position"
    and nonzero: "leading \<noteq> 0"
    and position_bound: "position < start + int fuel"
    and searched_zero:
      "\<forall>earlier. start \<le> earlier \<and> earlier < position \<longrightarrow>
        radial_packets_at block earlier = 0"
    using radial_jet_search_from_sound[OF search] by blast+
  have later_position: "radial_packets_at later position = 0"
    using radial_packets_before_lower_bound[OF later_lower position_bound] .
  have before_block: "radial_packets_at block earlier = 0"
    if "earlier < start" for earlier
    using radial_packets_before_lower_bound[OF block_lower that] .
  have before_later: "radial_packets_at later earlier = 0"
    if "earlier < position" for earlier
  proof -
    have below_search_end: "earlier < start + int fuel"
      using that position_bound by linarith
    show ?thesis
      using radial_packets_before_lower_bound[OF later_lower below_search_end] .
  qed
  have all_before: "radial_packets_at (prior @ block @ later) earlier = 0"
    if "earlier < position" for earlier
  proof -
    have block_zero: "radial_packets_at block earlier = 0"
    proof (cases "earlier < start")
      case True
      then show ?thesis using before_block by blast
    next
      case False
      then show ?thesis using searched_zero that by auto
    qed
    show ?thesis
      using prior_zero before_later[OF that] block_zero
      by (simp add: radial_packets_at_append)
  qed
  show ?thesis
    using leading nonzero prior_zero later_position all_before
    by (simp add: radial_first_event_def radial_packets_at_append)
qed

corollary radial_gap_worklist_single_certified_witness_sound:
  assumes search:
    "radial_jet_search_from block start fuel = Some (position, leading)"
      and prior_certificate:
        "radial_sparse_zero_certificate prior_origin prior"
      and prior_lower:
        "\<forall>packet\<in>set prior. prior_origin \<le> radial_shift packet"
      and block_lower: "\<forall>packet\<in>set block. start \<le> radial_shift packet"
      and later_lower:
        "\<forall>packet\<in>set later. start + int fuel \<le> radial_shift packet"
  shows "radial_first_event (prior @ block @ later) position leading"
proof -
  have prior_zero: "\<forall>n. radial_packets_at prior n = 0"
    using radial_sparse_zero_certificate_sound[OF prior_certificate prior_lower]
    by blast
  show ?thesis
    using radial_gap_worklist_witness_sound[OF search prior_zero block_lower later_lower] .
qed

type_synonym radial_certified_block = "int * executable_radial_packet list"

definition radial_prior_packets ::
    "radial_certified_block list \<Rightarrow> executable_radial_packet list" where
  "radial_prior_packets blocks = concat (map snd blocks)"

definition radial_prior_blocks_certified ::
    "radial_certified_block list \<Rightarrow> bool" where
  "radial_prior_blocks_certified blocks \<longleftrightarrow>
    list_all (\<lambda>(origin,packets).
      radial_sparse_zero_certificate origin packets \<and>
      (\<forall>packet\<in>set packets. origin \<le> radial_shift packet)) blocks"

lemma radial_prior_blocks_certified_zero:
  assumes "radial_prior_blocks_certified blocks"
  shows "radial_packets_at (radial_prior_packets blocks) position = 0"
  using assms
proof (induction blocks)
  case Nil
  then show ?case
    by (simp add: radial_prior_blocks_certified_def radial_prior_packets_def
        radial_packets_at_def)
next
  case (Cons certified blocks)
  obtain origin packets where certified: "certified = (origin, packets)"
    by (cases certified)
  have head: "radial_packets_at packets position = 0"
    using Cons.prems radial_sparse_zero_certificate_sound
    by (auto simp: certified radial_prior_blocks_certified_def)
  have tail: "radial_packets_at (radial_prior_packets blocks) position = 0"
    using Cons.IH Cons.prems
    by (auto simp: certified radial_prior_blocks_certified_def)
  show ?case
    using head tail
    by (simp add: certified radial_prior_packets_def radial_packets_at_append)
qed

corollary radial_gap_worklist_certified_witness_sound:
  assumes search:
    "radial_jet_search_from block start fuel = Some (position, leading)"
      and prior_certificates: "radial_prior_blocks_certified prior_blocks"
      and block_lower: "\<forall>packet\<in>set block. start \<le> radial_shift packet"
      and later_lower:
        "\<forall>packet\<in>set later. start + int fuel \<le> radial_shift packet"
  shows "radial_first_event
    (radial_prior_packets prior_blocks @ block @ later) position leading"
proof -
  have prior_zero:
    "\<forall>n. radial_packets_at (radial_prior_packets prior_blocks) n = 0"
    using radial_prior_blocks_certified_zero[OF prior_certificates] by blast
  show ?thesis
    using radial_gap_worklist_witness_sound[OF search prior_zero block_lower later_lower] .
qed

text \<open>
  Soundness above is deliberately separate from completeness.  To justify the
  Python choice of fuel from its packet-count gap bound, one still needs the
  lacunary/Wronskian valuation theorem.  Source admission and closure of the
  packet count under later temporal actions are also outside this result.
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms radial_event_shift_basis radial_basis_grouping
        radial_basis_zero_certificate radial_jet_search_from_sound
        radial_sparse_zero_certificate_sound
        radial_gap_worklist_witness_sound
        radial_gap_worklist_single_certified_witness_sound
        radial_prior_blocks_certified_zero
        radial_gap_worklist_certified_witness_sound})
    then () else error "Radial event certificate depends on an oracle";
\<close>

end
