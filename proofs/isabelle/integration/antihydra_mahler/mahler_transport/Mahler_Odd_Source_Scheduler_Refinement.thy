theory Mahler_Odd_Source_Scheduler_Refinement
  imports Mahler_Source_Cylinder_Transport
    "Collatz_Cylinder_Refinement.Collatz_Cylinder_Constructor"
begin

text \<open>This integration theorem connects the scheduler's exact odd seam
to the existing source-selected Mahler cylinder.  Collatz's shared
two-adic split supplies the exponent from the current integer; it is not an
itinerary premise.  The logical odd-return clock is the sum of these
exponents.  Antihydra's physical TM roof remains a separate measured clock
and is not replaced by this normalized source-step count.\<close>

fun mahler_source_odd_exponents :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_source_odd_exponents D 0 = []"
| "mahler_source_odd_exponents D (Suc n) =
    collatz_source_valuation D #
      mahler_source_odd_exponents
        (mahler_orbit D (collatz_source_valuation D)) n"

lemma mahler_source_selected_odd_block:
  assumes odd_source: "odd D"
  defines "a \<equiv> collatz_source_valuation D"
      and "u \<equiv> collatz_accelerated_target D"
  shows "0 < a"
    and "3*D+1 = 2^a*u"
    and "odd u"
    and "mahler_orbit D a = 3^(a-1)*u"
    and "odd (mahler_orbit D a)"
    and "odd_events D a = 1"
    and "ledger_at D a = 3-int a"
proof -
  have positive: "0 < a"
    using odd_source odd_source_has_positive_valuation
    by (simp add: a_def)
  obtain k where a_suc: "a = Suc k"
    using positive by (cases a) auto
  have valuation: "collatz_source_valuation D = Suc k"
    using a_def a_suc by simp
  have target: "collatz_accelerated_target D = u"
    using u_def by simp
  have split: "3*D+1 = 2^(Suc k)*u"
    using collatz_source_split_exact[of D] valuation target by simp
  have odd_u: "odd u"
    using collatz_accelerated_target_odd[of D] by (simp add: u_def)
  have facts:
      "mahler_orbit D (Suc k) = 3^k*u"
      "odd (mahler_orbit D (Suc k))"
      "odd_events D (Suc k) = 1"
      "ledger_at D (Suc k) = 3-int (Suc k)"
    using mahler_odd_event_block_refines_endpoint_and_ledger[
        OF odd_source split odd_u]
    by blast+
  show "0 < a" by (rule positive)
  show "3*D+1 = 2^a*u" using split a_suc by simp
  show "odd u" by (rule odd_u)
  show "mahler_orbit D a = 3^(a-1)*u"
    using facts(1) a_suc by simp
  show "odd (mahler_orbit D a)" using facts(2) a_suc by simp
  show "odd_events D a = 1" using facts(3) a_suc by simp
  show "ledger_at D a = 3-int a" using facts(4) a_suc by simp
qed

theorem mahler_source_odd_exponents_admitted:
  assumes odd_source: "odd D"
  shows "mahler_odd_word_admitted D (mahler_source_odd_exponents D events)"
  using odd_source
proof (induction events arbitrary: D)
  case 0
  then show ?case by simp
next
  case (Suc events)
  let ?a = "collatz_source_valuation D"
  let ?u = "collatz_accelerated_target D"
  have selected:
      "0 < ?a"
      "3*D+1 = 2^?a*?u"
      "odd ?u"
      "mahler_orbit D ?a = 3^(?a-1)*?u"
      "odd (mahler_orbit D ?a)"
    using mahler_source_selected_odd_block[OF Suc.prems]
    by (simp add: collatz_source_valuation_def collatz_accelerated_target_def)+
  have tail:
    "mahler_odd_word_admitted (mahler_orbit D ?a)
       (mahler_source_odd_exponents (mahler_orbit D ?a) events)"
    using Suc.IH[OF selected(5)] .
  obtain k where exponent: "?a = Suc k"
    using selected(1) by (cases ?a) auto
  have split: "3*D+1 = 2^(Suc k)*?u"
    using selected(2) exponent by simp
  have endpoint: "mahler_orbit D (Suc k) = 3^k*?u"
    using selected(4) exponent by simp
  show ?case
    using split selected(3) tail endpoint exponent
    by (simp only: mahler_source_odd_exponents.simps
        mahler_odd_word_admitted.simps)
       (blast)
qed

text \<open>A fixed, already admitted temporal word is stable on its complete
source cylinder.  The extra endpoint bit is essential: it preserves the
odd terminal seam as well as the parity bits used by the word.\<close>

lemma mahler_odd_word_admitted_high_fiber:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "mahler_odd_word_admitted
      (D + k * 2^(Suc (mahler_odd_word_span as))) as"
using admitted
proof (induction as arbitrary: D k)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  obtain j u where a: "a = Suc j"
      and split: "3*D+1 = 2^(Suc j)*u"
      and odd_u: "odd u"
      and tail: "mahler_odd_word_admitted (3^j*u) as"
    using Cons.prems by auto
  let ?s = "mahler_odd_word_span as"
  let ?N = "Suc (mahler_odd_word_span (a#as))"
  let ?D = "D + k * 2^?N"
  let ?u = "u + 3 * 2^(Suc ?s) * k"
  have span: "mahler_odd_word_span (a#as) = a + ?s"
    by (simp add: mahler_odd_word_span_def)
  have N: "?N = Suc j + Suc ?s"
    using span a by simp
  have split_lift: "3*?D+1 = 2^(Suc j)*?u"
    using split N a by (simp add: power_add algebra_simps)
  have even_tail: "even (3 * 2^(Suc ?s) * k)" by simp
  have odd_lift: "odd ?u"
    using odd_u even_tail by simp
  have tail_lift:
    "mahler_odd_word_admitted
      (3^j*u + (k*3^(Suc j))*2^(Suc ?s)) as"
    using Cons.IH[of "3^j*u" "k*3^(Suc j)"] tail .
  have tail_source:
    "3^j*?u = 3^j*u + (k*3^(Suc j))*2^(Suc ?s)"
    by (simp add: algebra_simps power_Suc)
  have tail_lift_endpoint:
    "mahler_odd_word_admitted (3^j*?u) as"
    using tail_lift tail_source by simp
  have witnesses:
    "\<exists>k u. a = Suc k \<and> 3*?D+1 = 2^(Suc k)*u \<and> odd u \<and>
      mahler_odd_word_admitted (3^k*u) as"
  proof (rule exI[of _ j], rule exI[of _ ?u])
    show "a = Suc j \<and> 3*?D+1 = 2^(Suc j)*?u \<and> odd ?u \<and>
        mahler_odd_word_admitted (3^j*?u) as"
      using a split_lift odd_lift tail_lift_endpoint by blast
  qed
  show ?case
    using witnesses by (simp only: mahler_odd_word_admitted.simps)
qed

text \<open>Source-cylinder transport supports repeated applications of one
authenticated odd-event word.  The induction advances only between complete
word boundaries; the exact occurrence clock remains the word span.\<close>

lemma mahler_odd_word_repeated_source_admission:
  fixes D k m L :: nat and as :: "nat list"
  assumes extent: "L = mahler_odd_word_span as"
      and admitted: "mahler_odd_word_admitted D as"
      and shifted_endpoint:
        "mahler_orbit D L = D + k * 2^(m*L+1)"
  shows "\<forall>j\<le>m. mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
  using admitted shifted_endpoint
proof (induction m arbitrary: D k)
  case 0
  then show ?case by simp
next
  case (Suc m)
  define E where "E = mahler_orbit D L"
  have exponent_decomposition: "Suc m * L + 1 = m*L + Suc L"
    by (simp add: algebra_simps)
  have source_fiber:
    "E = D + (k * 2^(m*L)) * 2^(Suc L)"
    using Suc.prems(2) exponent_decomposition
    by (simp add: E_def power_add algebra_simps)
  have E_admitted: "mahler_odd_word_admitted E as"
    using mahler_odd_word_admitted_high_fiber[OF Suc.prems(1), of "k*2^(m*L)"]
      extent source_fiber by simp
  have source_height: "L \<le> Suc m * L + 1"
    by (simp add: algebra_simps)
  have transported:
    "mahler_orbit (D + k * 2^(Suc m * L + 1)) L =
      mahler_orbit D L + k * 2^(Suc m * L + 1 - L) * 3^L"
    by (rule moving_source_cylinder[OF source_height])
  have exponent_subtraction: "Suc m * L + 1 - L = m*L+1"
    by (simp add: algebra_simps)
  have E_shift:
    "mahler_orbit E L = E + (k*3^L) * 2^(m*L+1)"
  proof -
    have "mahler_orbit E L =
        mahler_orbit (D + k * 2^(Suc m * L + 1)) L"
      using E_def Suc.prems(2) by simp
    also have "... = mahler_orbit D L +
        k * 2^(Suc m * L + 1 - L) * 3^L"
      by (rule transported)
    also have "... = E + (k*3^L) * 2^(m*L+1)"
      using E_def exponent_subtraction by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have IH_E:
    "\<forall>j\<le>m. mahler_odd_word_admitted (mahler_orbit E (j*L)) as"
    using Suc.IH[OF E_admitted E_shift] .
  show ?case
  proof (intro allI impI)
    fix j
    assume j_bound: "j \<le> Suc m"
    show "mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
    proof (cases j)
      case 0
      then show ?thesis using Suc.prems(1) by simp
    next
      case (Suc r)
      have r_bound: "r \<le> m"
        using j_bound Suc by arith
      have translated:
        "mahler_orbit D (j*L) = mahler_orbit E (r*L)"
        using Suc by (simp add: E_def mahler_orbit_add algebra_simps)
      have "mahler_odd_word_admitted (mahler_orbit E (r*L)) as"
        using IH_E r_bound by blast
      then show ?thesis using translated by simp
    qed
  qed
qed

text \<open>The source-action capacity is a count of complete applications.
For every positive count below the exact valuation bound, all word-boundary
sources remain admitted; each boundary can therefore reuse the same exact
endpoint, event, ledger, and prefix-safety laws.\<close>

theorem mahler_odd_word_source_capacity_bridge:
  fixes D L v w copies :: nat and as :: "nat list"
  assumes admitted: "mahler_odd_word_admitted D as"
      and extent: "L = mahler_odd_word_span as"
      and positive_extent: "0 < L"
      and displacement: "mahler_orbit D L - D = (2::nat)^v * w"
      and exact_valuation: "odd w"
      and capacity: "copies \<le> (L + v - 1) div L"
      and positive_copies: "0 < copies"
  shows "\<forall>j<copies.
      mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
proof -
  let ?q = "(L + v - 1) div L"
  have scaled_capacity: "copies*L \<le> ?q*L"
    using mult_le_mono1[OF capacity, of L]
    by (simp add: mult.commute)
  have quotient_decomposition:
    "?q*L + (L+v-1) mod L = L+v-1"
    using div_mult_mod_eq[of "L+v-1" L]
    by (simp add: mult.commute)
  have quotient_bound: "?q*L \<le> L+v-1"
    using quotient_decomposition by arith
  have scaled_bound: "copies*L \<le> L+v-1"
    using scaled_capacity quotient_bound by arith
  obtain n where copies_eq: "copies = Suc n"
    using positive_copies by (cases copies) auto
  have block_bound: "n*L+L \<le> L+v-1"
    using scaled_bound copies_eq by (simp add: algebra_simps)
  have exponent_bound: "n*L+1 \<le> v"
    using block_bound positive_extent by arith
  have exponent_split: "v = (n*L+1) + (v-(n*L+1))"
    using exponent_bound by arith
  have power_argument:
    "(2::nat)^v = (2::nat)^(n*L+1+(v-(n*L+1)))"
    using exponent_split by simp
  have power_split:
    "(2::nat)^v = (2::nat)^(n*L+1)*(2::nat)^(v-(n*L+1))"
    using power_argument by (simp only: power_add)
  have displacement_factor:
    "mahler_orbit D L-D =
      2^(n*L+1) * (2^(v-(n*L+1))*w)"
    using displacement power_split
    by (simp only: displacement power_split; simp add: mult.assoc)
  have w_nonzero: "w \<noteq> 0"
    using exact_valuation by (cases w) auto
  have w_positive: "0 < w"
    using w_nonzero by simp
  have displacement_positive: "0 < mahler_orbit D L-D"
    using displacement w_positive by simp
  have source_order: "D < mahler_orbit D L"
    using displacement_positive by arith
  have cylinder_divides: "2^(n*L+1) dvd mahler_orbit D L-D"
    unfolding displacement_factor dvd_def
    by (rule exI[of _ "2^(v-(n*L+1))*w"]) (simp add: mult.commute)
  obtain k where displacement_multiple:
    "mahler_orbit D L-D = 2^(n*L+1)*k"
    using cylinder_divides unfolding dvd_def by blast
  have source_shift:
    "mahler_orbit D L = D + k*2^(n*L+1)"
  proof -
    have difference_add:
      "mahler_orbit D L-D + D = mahler_orbit D L"
      using source_order by simp
    show ?thesis
      using difference_add displacement_multiple
      by (simp add: mult.commute)
  qed
  have all_boundaries:
    "\<forall>j\<le>n. mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
    using mahler_odd_word_repeated_source_admission[OF extent admitted source_shift] .
  show ?thesis
  proof (intro allI impI)
    fix j
    assume j_bound: "j < copies"
    have j_bound_n: "j \<le> n"
      using j_bound copies_eq by arith
    show "mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
      using all_boundaries j_bound_n by blast
  qed
qed

theorem mahler_odd_word_two_copy_capacity_bridge:
  fixes D L v w :: nat and as :: "nat list"
  assumes admitted: "mahler_odd_word_admitted D as"
      and extent: "L = mahler_odd_word_span as"
      and positive_extent: "0 < L"
      and displacement: "mahler_orbit D L - D = (2::nat)^v*w"
      and exact_valuation: "odd w"
      and capacity: "2 \<le> (L+v-1) div L"
  shows "mahler_odd_word_admitted (mahler_orbit D L) as"
proof -
  have all:
    "\<forall>j<2. mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
    by (rule mahler_odd_word_source_capacity_bridge[OF admitted extent
      positive_extent displacement exact_valuation capacity]) simp
  have at_one:
    "mahler_odd_word_admitted (mahler_orbit D (1*L)) as"
    using all[rule_format, of 1] by simp
  show ?thesis using at_one by simp
qed

theorem mahler_odd_word_source_capacity_trace:
  fixes D L v w copies :: nat and as :: "nat list"
    and incoming_balance :: int and t :: real
  assumes admitted: "mahler_odd_word_admitted D as"
      and extent: "L = mahler_odd_word_span as"
      and positive_extent: "0 < L"
      and displacement: "mahler_orbit D L-D = (2::nat)^v*w"
      and exact_valuation: "odd w"
      and capacity: "copies \<le> (L+v-1) div L"
      and positive_copies: "0 < copies"
  shows "\<forall>j<copies.
    mahler_odd_word_admitted (mahler_orbit D (j*L)) as \<and>
    mahler_orbit (mahler_orbit D (j*L)) L =
      mahler_odd_word_endpoint as (mahler_orbit D (j*L)) \<and>
    odd_events (mahler_orbit D (j*L)) L = length as \<and>
    ledger_at (mahler_orbit D (j*L)) L = mahler_odd_word_delta as \<and>
    ((\<forall>q\<le>L. 0 \<le> incoming_balance +
        ledger_at (mahler_orbit D (j*L)) q) \<longleftrightarrow>
      0 \<le> incoming_balance + mahler_odd_word_minimum as) \<and>
    (cylinder_guard (mahler_orbit D (j*L)) L t \<longleftrightarrow>
      mahler_odd_word_guard (mahler_orbit D (j*L)) as t) \<and>
    antihydra_family_orbit (mahler_orbit D (j*L)+1) L =
      mahler_odd_word_endpoint as (mahler_orbit D (j*L)) + 1"
proof -
  have span_eq: "mahler_odd_word_span as = L"
    using extent by simp
  have all_admitted:
    "\<forall>j<copies.
      mahler_odd_word_admitted (mahler_orbit D (j*L)) as"
    by (rule mahler_odd_word_source_capacity_bridge[OF admitted extent
      positive_extent displacement exact_valuation capacity positive_copies])
  show ?thesis
  proof (intro allI impI)
    fix j
    assume j_bound: "j < copies"
    let ?E = "mahler_orbit D (j*L)"
    have admitted_j: "mahler_odd_word_admitted ?E as"
      using all_admitted j_bound by blast
    have endpoint_j: "mahler_orbit ?E L = mahler_odd_word_endpoint as ?E"
      using mahler_odd_word_refines_endpoint_events_and_ledger(1)[OF admitted_j]
        span_eq by simp
    have events_j: "odd_events ?E L = length as"
      using mahler_odd_word_refines_endpoint_events_and_ledger(2)[OF admitted_j]
        span_eq by simp
    have ledger_j: "ledger_at ?E L = mahler_odd_word_delta as"
      using mahler_odd_word_refines_endpoint_events_and_ledger(3)[OF admitted_j]
        span_eq by simp
    have safety_j:
      "((\<forall>q\<le>L. 0 \<le> incoming_balance + ledger_at ?E q) \<longleftrightarrow>
        0 \<le> incoming_balance + mahler_odd_word_minimum as)"
      using mahler_odd_word_prefix_safety_iff[OF admitted_j] span_eq by simp
    have guard_j:
      "cylinder_guard ?E L t \<longleftrightarrow> mahler_odd_word_guard ?E as t"
      using mahler_odd_word_fractional_guard_decomposition[of ?E as t]
        span_eq by simp
    have physical_j:
      "antihydra_family_orbit (?E+1) L =
        mahler_odd_word_endpoint as ?E + 1"
      using antihydra_family_centered_orbit[of ?E L] endpoint_j by simp
    show "mahler_odd_word_admitted ?E as \<and>
        mahler_orbit ?E L = mahler_odd_word_endpoint as ?E \<and>
        odd_events ?E L = length as \<and>
        ledger_at ?E L = mahler_odd_word_delta as \<and>
        ((\<forall>q\<le>L. 0 \<le> incoming_balance + ledger_at ?E q) \<longleftrightarrow>
          0 \<le> incoming_balance + mahler_odd_word_minimum as) \<and>
        (cylinder_guard ?E L t \<longleftrightarrow> mahler_odd_word_guard ?E as t) \<and>
        antihydra_family_orbit (?E+1) L =
          mahler_odd_word_endpoint as ?E + 1"
      using admitted_j endpoint_j events_j ledger_j safety_j guard_j physical_j
      by blast
  qed
qed

lemma mahler_D_step_strict_positive:
  fixes D :: nat
  assumes positive: "0 < D"
  shows "D < mahler_D_step D"
  using positive
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps; arith)

lemma mahler_orbit_lower_bound:
  assumes positive: "0 < D"
  shows "D \<le> mahler_orbit D n"
  using positive
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have current_positive: "0 < mahler_orbit D n"
    using Suc.prems Suc.IH by arith
  have step: "mahler_orbit D n < mahler_D_step (mahler_orbit D n)"
    by (rule mahler_D_step_strict_positive[OF current_positive])
  show ?case
    using Suc.IH step by (simp only: mahler_orbit.simps; arith)
qed

lemma mahler_orbit_strict_positive_span:
  assumes source_positive: "0 < D" and span_positive: "0 < L"
  shows "D < mahler_orbit D L"
proof -
  obtain n where L_eq: "L = Suc n"
    using span_positive by (cases L) auto
  have lower: "D \<le> mahler_orbit D n"
    by (rule mahler_orbit_lower_bound[OF source_positive])
  have current_positive: "0 < mahler_orbit D n"
    using source_positive lower by arith
  have step: "mahler_orbit D n < mahler_D_step (mahler_orbit D n)"
    by (rule mahler_D_step_strict_positive[OF current_positive])
  show ?thesis using L_eq lower step
    by (simp only: L_eq mahler_orbit.simps; arith)
qed

text \<open>This source-selected form obtains the exact two-adic split from the
positive orbit displacement itself.  It therefore does not take a caller-
supplied valuation or odd cofactor as an authority premise.  The logical
event clock, ledger prefix, fractional guard, and centered physical endpoint
are all inherited from the one admitted word at every copied boundary.\<close>

theorem mahler_odd_word_source_selected_capacity_trace:
  fixes D L copies :: nat and as :: "nat list"
    and incoming_balance :: int and t :: real
  assumes source_positive: "0 < D"
      and admitted: "mahler_odd_word_admitted D as"
      and extent: "L = mahler_odd_word_span as"
      and positive_extent: "0 < L"
      and capacity:
        "copies \<le> (L + fst (strip_twos (mahler_orbit D L-D)) - 1) div L"
      and positive_copies: "0 < copies"
  shows "\<forall>j<copies.
    mahler_odd_word_admitted (mahler_orbit D (j*L)) as \<and>
    mahler_orbit (mahler_orbit D (j*L)) L =
      mahler_odd_word_endpoint as (mahler_orbit D (j*L)) \<and>
    odd_events (mahler_orbit D (j*L)) L = length as \<and>
    ledger_at (mahler_orbit D (j*L)) L = mahler_odd_word_delta as \<and>
    ((\<forall>q\<le>L. 0 \<le> incoming_balance +
        ledger_at (mahler_orbit D (j*L)) q) \<longleftrightarrow>
      0 \<le> incoming_balance + mahler_odd_word_minimum as) \<and>
    (cylinder_guard (mahler_orbit D (j*L)) L t \<longleftrightarrow>
      mahler_odd_word_guard (mahler_orbit D (j*L)) as t) \<and>
    antihydra_family_orbit (mahler_orbit D (j*L)+1) L =
      mahler_odd_word_endpoint as (mahler_orbit D (j*L)) + 1"
proof -
  have endpoint_growth: "D < mahler_orbit D L"
    by (rule mahler_orbit_strict_positive_span[OF source_positive positive_extent])
  have displacement_positive: "0 < mahler_orbit D L-D"
    using endpoint_growth by simp
  have split:
    "mahler_orbit D L-D =
        2^(fst (strip_twos (mahler_orbit D L-D))) *
          snd (strip_twos (mahler_orbit D L-D))"
    and odd_cofactor:
      "odd (snd (strip_twos (mahler_orbit D L-D)))"
    using strip_twos_spec[OF displacement_positive] by blast+
  show ?thesis
    by (rule mahler_odd_word_source_capacity_trace[OF admitted extent
      positive_extent split odd_cofactor capacity positive_copies])
qed

lemma mahler_source_odd_exponents_length [simp]:
  "length (mahler_source_odd_exponents D events) = events"
  by (induct events arbitrary: D) simp_all

theorem mahler_source_odd_scheduler_trace:
  fixes events :: nat and incoming_balance :: int and t :: real
  assumes odd_source: "odd D"
  defines "as \<equiv> mahler_source_odd_exponents D events"
  shows "mahler_orbit D (mahler_odd_word_span as) =
      mahler_odd_word_endpoint as D"
    and "odd_events D (mahler_odd_word_span as) = events"
    and "ledger_at D (mahler_odd_word_span as) = mahler_odd_word_delta as"
    and "(\<forall>j\<le>mahler_odd_word_span as.
        0 \<le> incoming_balance + ledger_at D j) \<longleftrightarrow>
      0 \<le> incoming_balance + mahler_odd_word_minimum as"
    and "cylinder_guard D (mahler_odd_word_span as) t \<longleftrightarrow>
      mahler_odd_word_guard D as t"
    and "antihydra_family_orbit (D+1) (mahler_odd_word_span as) =
      mahler_odd_word_endpoint as D + 1"
proof -
  have admitted: "mahler_odd_word_admitted D as"
    using mahler_source_odd_exponents_admitted[OF odd_source, of events]
    by (simp add: as_def)
  have endpoint:
    "mahler_orbit D (mahler_odd_word_span as) =
      mahler_odd_word_endpoint as D"
    using mahler_odd_word_refines_endpoint_events_and_ledger(1)[OF admitted] .
  show "mahler_orbit D (mahler_odd_word_span as) =
      mahler_odd_word_endpoint as D" by (rule endpoint)
  show "odd_events D (mahler_odd_word_span as) = events"
    using mahler_odd_word_refines_endpoint_events_and_ledger(2)[OF admitted]
    by (simp add: as_def)
  show "ledger_at D (mahler_odd_word_span as) = mahler_odd_word_delta as"
    by (rule mahler_odd_word_refines_endpoint_events_and_ledger(3)[OF admitted])
  show "(\<forall>j\<le>mahler_odd_word_span as.
        0 \<le> incoming_balance + ledger_at D j) \<longleftrightarrow>
      0 \<le> incoming_balance + mahler_odd_word_minimum as"
    by (rule mahler_odd_word_prefix_safety_iff[OF admitted])
  show "cylinder_guard D (mahler_odd_word_span as) t \<longleftrightarrow>
      mahler_odd_word_guard D as t"
    by (rule mahler_odd_word_fractional_guard_decomposition)
  show "antihydra_family_orbit (D+1) (mahler_odd_word_span as) =
      mahler_odd_word_endpoint as D + 1"
    using antihydra_family_centered_orbit[of D "mahler_odd_word_span as"]
      endpoint by simp
qed

text \<open>At each selected source seam the exponent is computed by the
existing exact two-adic split of 3D+1.  Its q divisibility test is the
source-local form of the ledger barrier.  The carried clock N is the logical
odd-return clock in the scheduler summary; the physical TM roof is retained
separately.\<close>

lemma mahler_affine_endpoint_defect_factorization:
  fixes A B D E :: int and L :: nat
  assumes endpoint: "(2::int)^L * E = A*D+B"
  shows "((2::int)^L-A)*D-B = (2::int)^L*(D-E)"
proof -
  have split:
    "((2::int)^L-A)*D-B = (2::int)^L*D-(A*D+B)"
    by (simp add: algebra_simps)
  also have "... = (2::int)^L*D-(2::int)^L*E"
    using endpoint by simp
  also have "... = (2::int)^L*(D-E)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma mahler_affine_endpoint_defect_dvd:
  fixes A B D E :: int and L :: nat
  assumes endpoint: "(2::int)^L * E = A*D+B"
  shows "(2::int)^L dvd ((2::int)^L*D-(A*D+B))"
proof -
  have factor:
    "(2::int)^L*D-(A*D+B) = (2::int)^L*(D-E)"
    using mahler_affine_endpoint_defect_factorization[OF endpoint]
    by (simp add: algebra_simps)
  show ?thesis
    unfolding factor dvd_def
    by (rule exI[of _ "D-E"]) (simp add: mult.commute)
qed

theorem mahler_source_scheduler_q_barrier:
  assumes odd_source: "odd D"
      and balance: "C = 3 * int I - int N"
  defines "a \<equiv> collatz_source_valuation D"
      and "u \<equiv> collatz_accelerated_target D"
  shows "2^N*(3*D+1) = 2^(N+a)*u"
    and "odd ((2^N*(3*D+1)) div 2^(N+a))"
    and "N+a \<ge> 3*I+4 \<longleftrightarrow> C+3-int a < 0"
    and "C+3-int a = 3*int (Suc I)-int (N+a)"
proof -
  have selected:
      "0 < a" "3*D+1 = 2^a*u" "odd u"
    using mahler_source_selected_odd_block[OF odd_source]
    by (simp_all add: a_def u_def)
  have q:
    "2^N*(3*D+1) = 2^(N+a)*u"
    and odd_q:
    "odd ((2^N*(3*D+1)) div 2^(N+a))"
    and barrier:
    "N+a \<ge> 3*I+4 \<longleftrightarrow> C+3-int a < 0"
    using mahler_odd_event_q_barrier_exact[
        where ledger=C and events=I and elapsed=N and exponent=a
          and source=D and u=u,
        OF balance selected(2) selected(3)]
    by (simp_all add: algebra_simps)
  show "2^N*(3*D+1) = 2^(N+a)*u" by (rule q)
  show "odd ((2^N*(3*D+1)) div 2^(N+a))" by (rule odd_q)
  show "N+a \<ge> 3*I+4 \<longleftrightarrow> C+3-int a < 0" by (rule barrier)
  show "C+3-int a = 3*int (Suc I)-int (N+a)"
    using balance by (simp add: algebra_simps)
qed

text \<open>The source word carries exactly one odd bit followed by a zero run
of length a-1.  The centered Antihydra family parity word is its complement,
derived from the live source rather than supplied as itinerary data.  Its
length is the normalized arithmetic macro extent, not the Turing physical
roof duration.\<close>

theorem mahler_source_odd_macro_bit_projection:
  assumes odd_source: "odd D"
      and a_def: "a = collatz_source_valuation D"
      and within: "j < a"
  shows "mahler_orbit D j mod 2 = (if j=0 then 1 else 0)"
proof (cases j)
  case 0
  then show ?thesis using odd_source
    by (simp add: odd_iff_mod_2_eq_one)
next
  case (Suc m)
  have positive: "0 < a"
    using odd_source odd_source_has_positive_valuation a_def by blast
  obtain k where a: "a = Suc k" using positive by (cases a) auto
  have m_lt: "m < k" using within Suc a by arith
  have source_split:
    "3*D+1 = 2^(Suc k)*collatz_accelerated_target D"
    using collatz_source_split_exact[of D] a_def a
    by (simp add: collatz_source_valuation_def collatz_accelerated_target_def)
  have step:
    "mahler_orbit D (Suc m) =
      collatz_accelerated_target D * 2^(k-m) * 3^m"
    using mahler_odd_run_intermediate_source[OF source_split, of m]
      m_lt collatz_accelerated_target_odd[of D]
    by (simp add: mult.commute)
  have exponent_positive: "0 < k-m" using m_lt by arith
  have even: "even (collatz_accelerated_target D * 2^(k-m) * 3^m)"
    using exponent_positive by simp
  show ?thesis using step even Suc by simp
qed

lemma antihydra_source_bit_is_complement:
  "antihydra_family_orbit (D+1) j mod 2 + mahler_orbit D j mod 2 = 1"
proof -
  have centered:
    "antihydra_family_orbit (D+1) j = mahler_orbit D j + 1"
    by (rule antihydra_family_centered_orbit)
  have bits: "mahler_orbit D j mod 2 < 2" by simp
  show ?thesis using centered bits by arith
qed

theorem antihydra_source_odd_macro_bit_projection:
  assumes odd_source: "odd D"
      and a_def: "a = collatz_source_valuation D"
      and within: "j < a"
  shows "antihydra_family_orbit (D+1) j mod 2 =
      (if j=0 then 0 else 1)"
proof -
  have d_bit:
    "mahler_orbit D j mod 2 = (if j=0 then 1 else 0)"
    by (rule mahler_source_odd_macro_bit_projection[OF odd_source a_def within])
  have complement:
    "antihydra_family_orbit (D+1) j mod 2 + mahler_orbit D j mod 2 = 1"
    by (rule antihydra_source_bit_is_complement)
  show ?thesis using complement d_bit by arith
qed

lemma zero_upt_suc:
  "[0..<Suc n] = 0 # map Suc [0..<n]"
proof -
  have cons: "[0..<Suc n] = 0 # [Suc 0..<Suc n]"
    by (rule upt_conv_Cons) simp
  have shifted: "map Suc [0..<n] = [Suc 0..<Suc n]"
    by (rule map_Suc_upt)
  show ?thesis using cons shifted by simp
qed

lemma antihydra_family_bits_are_orbit_parities:
  fixes h n :: nat
  shows "antihydra_family_bits h n =
    map (\<lambda>j. antihydra_family_orbit h j mod 2) [0..<n]"
proof (induct n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have interval: "[0..<Suc n] = 0 # map Suc [0..<n]"
    by (rule zero_upt_suc)
  have shifted:
    "map (\<lambda>j. antihydra_family_orbit (antihydra_family_step h) j mod 2)
        [0..<n] =
      map (\<lambda>j. antihydra_family_orbit h (Suc j) mod 2) [0..<n]"
  proof (rule map_cong)
    show "[0..<n] = [0..<n]" by simp
    fix j
    assume "j \<in> set [0..<n]"
    then show
      "antihydra_family_orbit (antihydra_family_step h) j mod 2 =
        antihydra_family_orbit h (Suc j) mod 2"
      by (simp add: antihydra_family_orbit_add)
  qed
  have ih:
    "antihydra_family_bits (antihydra_family_step h) n =
      map (\<lambda>j. antihydra_family_orbit (antihydra_family_step h) j mod 2)
        [0..<n]"
    using Suc.hyps[of "antihydra_family_step h"] .
  have rhs:
    "map (\<lambda>j. antihydra_family_orbit h j mod 2) [0..<Suc n] =
      h mod 2 # map (\<lambda>j. antihydra_family_orbit h (Suc j) mod 2)
        [0..<n]"
  proof -
    have first:
      "map (\<lambda>j. antihydra_family_orbit h j mod 2) [0..<Suc n] =
        map (\<lambda>j. antihydra_family_orbit h j mod 2)
          (0 # map Suc [0..<n])"
      by (simp only: interval)
    also have "... = h mod 2 #
        map (\<lambda>j. antihydra_family_orbit h (Suc j) mod 2) [0..<n]"
      by (simp only: list.map map_map comp_def
          antihydra_family_orbit.simps(1))
    finally show ?thesis .
  qed
  show ?case
    by (simp only: antihydra_family_bits.simps ih rhs shifted)
qed

theorem antihydra_source_odd_macro_family_parity_word:
  assumes odd_source: "odd D"
      and a_def: "a = collatz_source_valuation D"
  shows "antihydra_family_bits (D+1) a = 0 # replicate (a-1) 1"
proof -
  have positive: "0 < a"
    using odd_source odd_source_has_positive_valuation a_def by blast
  have bits:
    "antihydra_family_bits (D+1) a =
      map (\<lambda>j. antihydra_family_orbit (D+1) j mod 2) [0..<a]"
    by (rule antihydra_family_bits_are_orbit_parities)
  have indexed:
    "map (\<lambda>j. antihydra_family_orbit (D+1) j mod 2) [0..<a] =
      map (\<lambda>j. if j=0 then 0 else 1) [0..<a]"
  proof (rule map_cong)
    show "[0..<a] = [0..<a]" by simp
    fix j
    assume "j \<in> set [0..<a]"
    then have within: "j < a" by simp
    show "antihydra_family_orbit (D+1) j mod 2 =
        (if j=0 then 0 else 1)"
      by (rule antihydra_source_odd_macro_bit_projection[
        OF odd_source a_def within])
  qed
  have map_shape:
    "map (\<lambda>j. if j=0 then 0 else 1) [0..<n] =
      (if n=0 then [] else 0 # replicate (n-1) 1)" for n
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have interval: "[0..<Suc m] = 0 # map Suc [0..<m]"
      by (rule zero_upt_suc)
    have tail:
      "map (\<lambda>j. if j=0 then 0 else 1) (map Suc [0..<m]) =
        map (\<lambda>_. 1) [0..<m]"
    proof -
      have compose:
        "map (\<lambda>j. if j=0 then 0 else 1) (map Suc [0..<m]) =
          map ((\<lambda>j. if j=0 then 0 else 1) o Suc) [0..<m]"
        by (simp only: map_map)
      have pointwise:
        "map ((\<lambda>j. if j=0 then 0 else 1) o Suc) [0..<m] =
          map (\<lambda>_. 1) [0..<m]"
      proof (rule map_cong)
        show "[0..<m] = [0..<m]" by (rule refl)
        fix j
        assume "j \<in> set [0..<m]"
        show "((\<lambda>j. if j=0 then 0 else 1) o Suc) j = (\<lambda>_. 1) j"
          by simp
      qed
      show ?thesis by (rule trans[OF compose pointwise])
    qed
    have mapped: "map (\<lambda>j. if j=0 then 0 else 1) [0..<Suc m] =
        0 # map (\<lambda>_. 1) [0..<m]"
    proof -
      have head: "(if (0::nat)=0 then 0 else 1) = 0" by simp
      show ?thesis
        using interval tail head by (simp only: interval list.map tail head)
    qed
    have ones: "map (\<lambda>_. 1) [0..<m] = replicate m 1"
      by (rule map_replicate_trivial)
    have target:
      "map (\<lambda>j. if j=0 then 0 else 1) [0..<Suc m] =
        (if Suc m=0 then [] else 0 # replicate (Suc m-1) 1)"
      using mapped ones
      by (simp only: mapped ones Suc_not_Zero if_False diff_Suc_1)
    show ?thesis using Suc target by (simp only: Suc target)
  qed
  have shape:
    "map (\<lambda>j. if j=0 then 0 else 1) [0..<a] = 0 # replicate (a-1) 1"
  proof (cases a)
    case 0
    then show ?thesis using positive by simp
  next
    case (Suc m)
    then show ?thesis
      using map_shape[of "Suc m"]
      by (simp only: Suc Suc_not_Zero if_False diff_Suc_1)
  qed
  show ?thesis using bits indexed shape
    by (simp only: bits indexed shape)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms mahler_source_selected_odd_block
      mahler_source_odd_exponents_admitted mahler_source_odd_scheduler_trace
      mahler_source_scheduler_q_barrier mahler_source_odd_macro_bit_projection
      mahler_D_step_strict_positive mahler_orbit_lower_bound
      mahler_orbit_strict_positive_span
      mahler_odd_word_repeated_source_admission
      mahler_odd_word_source_capacity_bridge
      mahler_odd_word_source_capacity_trace
      mahler_odd_word_source_selected_capacity_trace})
    then () else error "Mahler source scheduler bridge depends on an oracle";
\<close>

end
