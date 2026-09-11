theory Decimal_Publisher_Constructor
  imports Decimal_Clock_Jumps Reverse_Residuals.Reverse_Threshold_Cocycle
begin

text \<open>This theory isolates the part of a decimal endpoint publisher that
can already be constructed from the checked local laws.  The value seam is
normalized before the threshold cocycle is observed.  Carry-domain geometry
alone is deliberately not claimed to determine the next domain.\<close>

definition decimal_nf :: "nat \<Rightarrow> nat" where
  "decimal_nf x = x mod 10"

definition decimal_publisher ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> carry_domain" where
  "decimal_publisher x y =
    (decimal_nf (x+y), cocycle_output_domain (decimal_nf x) (decimal_nf y))"

definition decimal_port_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "decimal_port_digit x c = decimal_nf (x + (if c then 1 else 0))"

definition decimal_open_publisher ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
      nat \<times> carry_domain" where
  "decimal_open_publisher x y c1 c2 =
    decimal_publisher (decimal_port_digit x c1) (decimal_port_digit y c2)"

lemma decimal_nf_idempotent:
  "decimal_nf (decimal_nf x) = decimal_nf x"
  by (simp add: decimal_nf_def)

lemma decimal_nf_add_seam:
  "decimal_nf (decimal_nf x + decimal_nf y) = decimal_nf (x+y)"
  by (simp add: decimal_nf_def mod_add_eq)

theorem decimal_publisher_consumes_normalized_seam:
  "decimal_publisher (decimal_nf x) (decimal_nf y) = decimal_publisher x y"
  by (simp add: decimal_publisher_def decimal_nf_idempotent decimal_nf_add_seam)

lemma decimal_port_digit_bounded:
  "decimal_port_digit x c < 10"
  by (simp add: decimal_port_digit_def decimal_nf_def)

lemma decimal_port_digit_consumes_normalized_seam:
  "decimal_port_digit (decimal_nf x) c = decimal_port_digit x c"
proof (cases c)
  case False
  then show ?thesis
    by (simp add: decimal_port_digit_def decimal_nf_def)
next
  case True
  have modular_add:
    "(x mod 10 + 1) mod 10 = (x+1) mod 10"
    by (rule mod_add_left_eq)
  show ?thesis using True modular_add
    by (simp add: decimal_port_digit_def decimal_nf_def)
qed

theorem decimal_open_publisher_consumes_normalized_seam:
  "decimal_open_publisher (decimal_nf x) (decimal_nf y) c1 c2 =
    decimal_open_publisher x y c1 c2"
  by (simp add: decimal_open_publisher_def
      decimal_port_digit_consumes_normalized_seam)

theorem decimal_publisher_exact_on_digits:
  assumes "x < 10" "y < 10"
  shows "decimal_publisher x y = ((x+y) mod 10, domain (x+y))"
proof -
  have x_nf: "decimal_nf x = x" using assms(1)
    by (simp add: decimal_nf_def)
  have y_nf: "decimal_nf y = y" using assms(2)
    by (simp add: decimal_nf_def)
  have output_domain: "cocycle_output_domain x y = domain (x+y)"
    by (rule kappa_and_eq_domain_exact(2)[OF assms])
  show ?thesis
    using x_nf y_nf output_domain
    by (simp add: decimal_publisher_def decimal_nf_def)
qed

theorem decimal_open_publisher_exact:
  "decimal_open_publisher x y c1 c2 =
    ((decimal_port_digit x c1 + decimal_port_digit y c2) mod 10,
      domain (decimal_port_digit x c1 + decimal_port_digit y c2))"
  unfolding decimal_open_publisher_def
  by (rule decimal_publisher_exact_on_digits;
      rule decimal_port_digit_bounded)

theorem decimal_open_publisher_has_all_port_alias:
  "decimal_open_publisher 0 3 c1 c2 =
    decimal_open_publisher 1 2 c1 c2"
  by (cases c1; cases c2;
      simp add: decimal_open_publisher_def decimal_port_digit_def
        decimal_publisher_def decimal_nf_def cocycle_output_domain_def
        decimal_kappa_def domain_def)

section \<open>Consumer pullback cylinder\<close>

definition eval_consumer :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" where
  "eval_consumer x D = D x"

definition consumer_pullback ::
    "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c" where
  "consumer_pullback P D = D \<circ> P"

lemma eval_consumer_pullback:
  "eval_consumer x (consumer_pullback P D) = eval_consumer (P x) D"
  by (simp add: eval_consumer_def consumer_pullback_def)

theorem consumer_pullback_contravariant:
  "consumer_pullback (P2 \<circ> P1) D =
    consumer_pullback P1 (consumer_pullback P2 D)"
  by (rule ext) (simp add: consumer_pullback_def)

definition affine_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "affine_int M b x = M*x+b"

definition threshold_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "threshold_int a t x = (t \<le> a*x)"

theorem affine_threshold_pullback:
  "consumer_pullback (affine_int M b) (threshold_int a t) =
    threshold_int (a*M) (t-a*b)"
proof (rule ext)
  fix x
  show "consumer_pullback (affine_int M b) (threshold_int a t) x =
      threshold_int (a*M) (t-a*b) x"
    by (simp add: consumer_pullback_def affine_int_def threshold_int_def
        algebra_simps)
qed

definition threshold_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "threshold_nat t s = (t \<le> s)"

definition domain_from_thresholds :: "bool \<Rightarrow> bool \<Rightarrow> carry_domain" where
  "domain_from_thresholds at_nine at_ten =
    (if at_ten then Above else if at_nine then Equal else Below)"

lemma carry_domain_is_threshold_readout:
  "domain s = domain_from_thresholds (threshold_nat 9 s) (threshold_nat 10 s)"
  by (simp add: domain_def domain_from_thresholds_def threshold_nat_def;
      arith)

lemma carry_ports_are_threshold_readouts:
  "carry_apply (domain s) c =
    (if c then threshold_nat 9 s else threshold_nat 10 s)"
  by (cases c) (auto simp: domain_def threshold_nat_def)

theorem pulled_thresholds_derive_published_domain:
  "domain (P s) = domain_from_thresholds
    (eval_consumer s (consumer_pullback P (threshold_nat 9)))
    (eval_consumer s (consumer_pullback P (threshold_nat 10)))"
  by (simp add: eval_consumer_def consumer_pullback_def
      carry_domain_is_threshold_readout)

theorem pulled_thresholds_derive_published_carry:
  "carry_apply (domain (P s)) c =
    (if c
     then eval_consumer s (consumer_pullback P (threshold_nat 9))
     else eval_consumer s (consumer_pullback P (threshold_nat 10)))"
  by (simp add: eval_consumer_def consumer_pullback_def
      carry_ports_are_threshold_readouts)

definition decimal_double :: "nat \<Rightarrow> nat" where
  "decimal_double s = 2*s"

lemma decimal_double_gt_pullback:
  "consumer_pullback decimal_double (threshold_nat 10) = threshold_nat 5"
  by (rule ext) (simp add: consumer_pullback_def decimal_double_def
      threshold_nat_def)

text \<open>Pair sums 2 and 8 have the same current Below readout and share
the same doubling action.  The action pulls the demanded future-GT predicate
back to threshold 5, which their distinct occurrence payloads evaluate
differently.  Thus the cylinder action is shared without using it as exact
occurrence identity.\<close>

theorem decimal_double_pullback_distinguishes_two_and_eight:
  "domain 2 = domain 8 \<and>
   eval_consumer 2 (consumer_pullback decimal_double (threshold_nat 10)) = False
   \<and> eval_consumer 8
      (consumer_pullback decimal_double (threshold_nat 10)) = True"
  by (simp add: domain_def eval_consumer_def consumer_pullback_def
      decimal_double_def threshold_nat_def)

section \<open>Bounded nilpotent decimal transport slots\<close>

definition decimal_transport_slot ::
    "'a::comm_ring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "decimal_transport_slot y q r x = 2^q * y^r * x"

definition decimal_live_slots :: "(nat \<times> nat) set" where
  "decimal_live_slots = {(q,r). q < 5 \<and> r < 5}"

lemma decimal_live_slots_product:
  "decimal_live_slots = {..<5} \<times> {..<5}"
  by (auto simp: decimal_live_slots_def)

theorem decimal_live_slots_cardinality:
  "card decimal_live_slots = 25"
  by (simp add: decimal_live_slots_product)

lemma decimal_transport_slot_compose:
  "decimal_transport_slot y q2 r2 (decimal_transport_slot y q1 r1 x) =
    decimal_transport_slot y (q1+q2) (r1+r2) x"
  by (simp add: decimal_transport_slot_def power_add algebra_simps)

lemma decimal_transport_itinerary_slot:
  "prod_list (map (decimal_kernel y) gs) * x =
    decimal_transport_slot y (count_list gs False) (count_list gs True) x"
  by (simp add: decimal_kernel_product decimal_transport_slot_def)

theorem decimal_transport_outside_live_slots_is_dead:
  fixes y x :: "'a::comm_ring_1"
  assumes two: "(2::'a)^5 = 0" and y_nilpotent: "y^5 = 0"
      and outside: "(q,r) \<notin> decimal_live_slots"
  shows "decimal_transport_slot y q r x = 0"
proof -
  have expired: "5 \<le> q \<or> 5 \<le> r"
    using outside by (auto simp: decimal_live_slots_def)
  from expired show ?thesis
  proof
    assume q_expired: "5 \<le> q"
    have "(2::'a)^q = 0"
      by (rule nilpotent_after_five[OF two q_expired])
    then show ?thesis by (simp add: decimal_transport_slot_def)
  next
    assume r_expired: "5 \<le> r"
    have "y^r = 0"
      by (rule nilpotent_after_five[OF y_nilpotent r_expired])
    then show ?thesis by (simp add: decimal_transport_slot_def)
  qed
qed

theorem decimal_itinerary_has_one_of_25_live_slots_or_is_dead:
  fixes y x :: "'a::comm_ring_1"
  assumes two: "(2::'a)^5 = 0" and y_nilpotent: "y^5 = 0"
  shows "(count_list gs False, count_list gs True) \<in> decimal_live_slots \<or>
    prod_list (map (decimal_kernel y) gs) * x = 0"
proof (cases "(count_list gs False, count_list gs True) \<in>
    decimal_live_slots")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule disjI2)
    show "prod_list (map (decimal_kernel y) gs) * x = 0"
    proof -
      have "prod_list (map (decimal_kernel y) gs) * x =
          decimal_transport_slot y (count_list gs False)
            (count_list gs True) x"
        by (rule decimal_transport_itinerary_slot)
      also have "... = 0"
        by (rule decimal_transport_outside_live_slots_is_dead[OF
          two y_nilpotent False])
      finally show ?thesis .
    qed
  qed
qed

text \<open>The 25-slot result bounds transported source and birth
contributions after their event itinerary is known.  It does not construct
future growth/birth itineraries, recursively substitute exact occurrence
morphisms, or bound first-use publisher DAG work.  Those remain the concrete
open-port constructor obligations.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms decimal_nf_idempotent decimal_nf_add_seam
      decimal_publisher_consumes_normalized_seam
      decimal_port_digit_consumes_normalized_seam
      decimal_open_publisher_consumes_normalized_seam
      decimal_open_publisher_exact
      decimal_open_publisher_has_all_port_alias
      decimal_publisher_exact_on_digits
      eval_consumer_pullback consumer_pullback_contravariant
      affine_threshold_pullback carry_domain_is_threshold_readout
      carry_ports_are_threshold_readouts
      pulled_thresholds_derive_published_domain
      pulled_thresholds_derive_published_carry
      decimal_double_gt_pullback
      decimal_double_pullback_distinguishes_two_and_eight
      decimal_live_slots_cardinality decimal_transport_slot_compose
      decimal_transport_itinerary_slot
      decimal_transport_outside_live_slots_is_dead
      decimal_itinerary_has_one_of_25_live_slots_or_is_dead})
    then () else error "Decimal publisher proof depends on an oracle";
\<close>

end
