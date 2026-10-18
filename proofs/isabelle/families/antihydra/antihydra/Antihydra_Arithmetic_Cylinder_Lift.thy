theory Antihydra_Arithmetic_Cylinder_Lift
  imports Antihydra_Family_Iteration
    Shared_S_Arithmetic.Dyadic_Source_Lift
    Shared_S_Arithmetic.Integer_Cylinder_Transport
begin

text \<open>The total Antihydra arithmetic recurrence is affine on every
dyadic source cylinder.  This is the refinement needed by the balanced
source-image constructor: a demanded block may retain the source residue and
transport the omitted quotient without replaying the omitted source values.

The statements in this theory concern only the total arithmetic coordinate.
They neither admit a physical TM block nor assert ledger safety or
non-halting.\<close>

lemma antihydra_family_step_even_translation:
  "antihydra_family_step (a + 2*q) =
    antihydra_family_step a + 3*q"
proof -
  have left:
    "2 * int (antihydra_family_step (a + 2*q)) =
      3 * int (a + 2*q) - int ((a + 2*q) mod 2)"
    by (rule antihydra_family_step_skew_equation)
  have right:
    "2 * int (antihydra_family_step a) =
      3 * int a - int (a mod 2)"
    by (rule antihydra_family_step_skew_equation)
  have parity: "(a + 2*q) mod 2 = a mod 2"
    by simp
  have doubled:
    "2 * int (antihydra_family_step (a + 2*q)) =
      2 * int (antihydra_family_step a + 3*q)"
    using left right parity by (simp add: algebra_simps)
  have "int (antihydra_family_step (a + 2*q)) =
      int (antihydra_family_step a + 3*q)"
    using doubled by simp
  then show ?thesis by simp
qed

interpretation antihydra_dyadic_source: dyadic_source_action
    antihydra_family_step "\<lambda>a. a mod 2" "\<lambda>_. 3"
proof
  show "\<And>(source::nat) (lift_amount::nat).
      (source + 2 * lift_amount) mod 2 = source mod 2"
    by simp
  show "\<And>(source::nat) (lift_amount::nat).
      antihydra_family_step (source + 2 * lift_amount) =
      antihydra_family_step source + 3 * lift_amount"
    by (rule antihydra_family_step_even_translation)
qed

lemma antihydra_family_orbit_is_dyadic_source_orbit:
  "antihydra_family_orbit a n =
    dyadic_source_orbit antihydra_family_step a n"
  by (induction n arbitrary: a) simp_all

lemma antihydra_family_bits_are_dyadic_source_word:
  "antihydra_family_bits a n =
    dyadic_source_word antihydra_family_step (\<lambda>a. a mod 2) a n"
  by (induction n arbitrary: a) simp_all

lemma antihydra_family_orbit_funpow:
  "antihydra_family_orbit a n = (antihydra_family_step ^^ n) a"
  by (induct n arbitrary: a)
    (simp_all del: funpow.simps(2) add: funpow_Suc_right)

theorem antihydra_family_orbit_cylinder_transport:
  "antihydra_family_orbit (r + 2^n*q) n =
    antihydra_family_orbit r n + 3^n*q"
  using antihydra_dyadic_source.exact_precision_source_lift[of r n q]
  by (simp add: antihydra_family_orbit_is_dyadic_source_orbit
      antihydra_family_bits_are_dyadic_source_word
      dyadic_constant_gain_product)

theorem antihydra_family_bits_cylinder_transport:
  "antihydra_family_bits (r + 2^n*q) n =
    antihydra_family_bits r n"
  using antihydra_dyadic_source.exact_precision_source_lift[of r n q]
  by (simp add: antihydra_family_bits_are_dyadic_source_word)

corollary antihydra_family_balance_cylinder_transport:
  "antihydra_family_balance (r + 2^n*q) initial n =
    antihydra_family_balance r initial n"
  using antihydra_family_bits_cylinder_transport[of r n q]
  by (simp add: antihydra_family_balance_def)

corollary antihydra_family_minimum_cylinder_transport:
  "antihydra_family_minimum (r + 2^n*q) initial n =
    antihydra_family_minimum r initial n"
  using antihydra_family_bits_cylinder_transport[of r n q]
  by (simp add: antihydra_family_minimum_def)

theorem antihydra_family_integer_progression_transport:
  "(\<lambda>q. int (antihydra_family_orbit (r + 2^n*q) n)) ` {..<count} =
    integer_progression
      (int (antihydra_family_orbit r n)) (int (3^n)) count"
proof -
  let ?denom = "(2::int)^n"
  let ?gain = "(3::int)^n"
  let ?offset =
    "?denom * int (antihydra_family_orbit r n) - ?gain * int r"
  have denominator: "0 < ?denom" by simp
  have first:
    "?gain * int r + ?offset =
      ?denom * int (antihydra_family_orbit r n)"
    by (simp add: algebra_simps)
  have stride: "?gain * ?denom = ?denom * ?gain"
    by (simp add: mult.commute)
  have affine_image:
    "(\<lambda>x. (?gain*x+?offset) div ?denom) `
        integer_progression (int r) ?denom count =
      integer_progression
        (int (antihydra_family_orbit r n)) ?gain count"
    by (rule integer_progression_affine_image[OF denominator first stride])
  have source_progression:
    "integer_progression (int r) ?denom count =
      (\<lambda>q. int (r + 2^n*q)) ` {..<count}"
    unfolding integer_progression_def
    by (simp add: algebra_simps)
  have pointwise:
    "\<And>q. (?gain * int (r + 2^n*q) + ?offset) div ?denom =
      int (antihydra_family_orbit (r + 2^n*q) n)"
  proof -
    fix q
    have orbit:
      "antihydra_family_orbit (r + 2^n*q) n =
        antihydra_family_orbit r n + 3^n*q"
      by (rule antihydra_family_orbit_cylinder_transport)
    show "(?gain * int (r + 2^n*q) + ?offset) div ?denom =
        int (antihydra_family_orbit (r + 2^n*q) n)"
      using orbit by (simp add: algebra_simps)
  qed
  have actual_image:
    "(\<lambda>q. int (antihydra_family_orbit (r + 2^n*q) n)) ` {..<count} =
      (\<lambda>q. (?gain * int (r + 2^n*q) + ?offset) div ?denom) `
        {..<count}"
    by (rule image_cong) (use pointwise in auto)
  have affine_parameterized:
    "(\<lambda>q. (?gain * int (r + 2^n*q) + ?offset) div ?denom) `
        {..<count} =
      integer_progression
        (int (antihydra_family_orbit r n)) ?gain count"
    using affine_image source_progression
    by (simp only: source_progression image_image)
  show ?thesis
    using actual_image affine_parameterized by simp
qed

corollary antihydra_family_safe_cylinder_transport:
  assumes safe: "antihydra_block_safe r initial n"
  shows "antihydra_block_safe (r + 2^n*q) initial n"
    and "antihydra_family_balance (r + 2^n*q) initial n =
      antihydra_family_balance r initial n"
    and "antihydra_family_minimum (r + 2^n*q) initial n =
      antihydra_family_minimum r initial n"
  using safe antihydra_family_balance_cylinder_transport[of r n q]
    antihydra_family_minimum_cylinder_transport[of r n q]
  by (simp_all add: antihydra_block_safe_def)

lemma ledger_word_delta_append:
  "ledger_word_delta (xs @ ys) =
    ledger_word_delta xs + ledger_word_delta ys"
proof -
  have equation:
    "sk_delta (skew_word (xs @ ys)) =
      sk_delta (skew_then (skew_word xs) (skew_word ys))"
    using skew_word_append[of xs ys] by simp
  show ?thesis
    using equation
    by (simp add: skew_then_def skew_word_induces_ledger_geometry)
qed

lemma ledger_word_minprefix_append:
  "ledger_word_minprefix (xs @ ys) =
    min (ledger_word_minprefix xs)
      (ledger_word_delta xs + ledger_word_minprefix ys)"
proof -
  have equation:
    "sk_minprefix (skew_word (xs @ ys)) =
      sk_minprefix (skew_then (skew_word xs) (skew_word ys))"
    using skew_word_append[of xs ys] by simp
  show ?thesis
    using equation
    by (simp add: skew_then_def skew_word_induces_ledger_geometry)
qed

lemma ledger_word_minprefix_le_delta:
  "ledger_word_minprefix bs \<le> ledger_word_delta bs"
  using skew_word_valid[of bs]
    skew_word_induces_ledger_geometry[of bs]
  by (simp add: skew_valid_def)

lemma ledger_word_append_binary_step:
  assumes binary: "b < 2"
  shows "ledger_word_delta (bs @ [b]) =
      ledger_word_delta bs + (2 - 3*int b)"
    and "ledger_word_minprefix (bs @ [b]) =
      min (ledger_word_minprefix bs)
        (ledger_word_delta bs + (2 - 3*int b))"
proof -
  show "ledger_word_delta (bs @ [b]) =
      ledger_word_delta bs + (2 - 3*int b)"
    by (simp add: ledger_word_delta_append)
  have lower:
    "ledger_word_minprefix bs \<le> ledger_word_delta bs"
    by (rule ledger_word_minprefix_le_delta)
  show "ledger_word_minprefix (bs @ [b]) =
      min (ledger_word_minprefix bs)
        (ledger_word_delta bs + (2 - 3*int b))"
  proof (cases b)
    case 0
    then show ?thesis
      using lower
      by (simp add: ledger_word_minprefix_append min_def)
  next
    case (Suc c)
    have "c = 0" using binary Suc by arith
    with Suc show ?thesis
      by (simp add: ledger_word_minprefix_append)
  qed
qed

record antihydra_leaf_loop_state =
  leaf_q :: nat
  leaf_delta :: int
  leaf_minimum :: int
  leaf_bits :: "nat list"

definition antihydra_leaf_initial :: "nat \<Rightarrow> antihydra_leaf_loop_state"
where
  "antihydra_leaf_initial residue = \<lparr>
    leaf_q = residue,
    leaf_delta = 0,
    leaf_minimum = 0,
    leaf_bits = []\<rparr>"

definition antihydra_leaf_step ::
    "antihydra_leaf_loop_state \<Rightarrow> antihydra_leaf_loop_state"
where
  "antihydra_leaf_step state =
    (let odd = leaf_q state mod 2;
         next_delta = leaf_delta state + (2 - 3*int odd)
     in \<lparr>
       leaf_q = (3*leaf_q state - odd) div 2,
       leaf_delta = next_delta,
       leaf_minimum = min (leaf_minimum state) next_delta,
       leaf_bits = leaf_bits state @ [odd]\<rparr>)"

fun antihydra_admitted_leaf_loop ::
    "nat \<Rightarrow> nat \<Rightarrow> antihydra_leaf_loop_state"
where
  "antihydra_admitted_leaf_loop residue 0 =
    antihydra_leaf_initial residue"
| "antihydra_admitted_leaf_loop residue (Suc width) =
    antihydra_leaf_step (antihydra_admitted_leaf_loop residue width)"

lemma antihydra_family_orbit_Suc_right:
  "antihydra_family_orbit a (Suc n) =
    antihydra_family_step (antihydra_family_orbit a n)"
  by (simp add: antihydra_family_orbit_funpow)

lemma antihydra_family_bits_Suc_right:
  "antihydra_family_bits a (Suc n) =
    antihydra_family_bits a n @
      [antihydra_family_orbit a n mod 2]"
  using antihydra_family_bits_append[of a n 1]
  by simp

lemma antihydra_leaf_step_q:
  "leaf_q (antihydra_leaf_step state) =
    antihydra_family_step (leaf_q state)"
  by (simp add: antihydra_leaf_step_def Let_def
      antihydra_family_step_is_total_skew antihydra_h_step_def)

theorem antihydra_admitted_leaf_loop_refinement:
  "antihydra_admitted_leaf_loop residue width = \<lparr>
    leaf_q = antihydra_family_orbit residue width,
    leaf_delta = ledger_word_delta (antihydra_family_bits residue width),
    leaf_minimum = ledger_word_minprefix (antihydra_family_bits residue width),
    leaf_bits = antihydra_family_bits residue width\<rparr>"
proof (induct width)
  case 0
  then show ?case
    by (simp add: antihydra_leaf_initial_def)
next
  case (Suc width)
  let ?q = "antihydra_family_orbit residue width"
  let ?bs = "antihydra_family_bits residue width"
  have binary: "?q mod 2 < 2" by simp
  have delta:
    "ledger_word_delta (?bs @ [?q mod 2]) =
      ledger_word_delta ?bs + (2 - 3*int (?q mod 2))"
    using ledger_word_append_binary_step(1)[OF binary] .
  have minimum:
    "ledger_word_minprefix (?bs @ [?q mod 2]) =
      min (ledger_word_minprefix ?bs)
        (ledger_word_delta ?bs + (2 - 3*int (?q mod 2)))"
    using ledger_word_append_binary_step(2)[OF binary] .
  show ?case
    using Suc.hyps delta minimum
    by (simp del: antihydra_family_orbit.simps(2)
          antihydra_family_bits.simps(2)
        add: antihydra_leaf_step_def Let_def
        antihydra_family_orbit_Suc_right
        antihydra_family_bits_Suc_right
        antihydra_family_step_is_total_skew antihydra_h_step_def)
qed

corollary antihydra_admitted_leaf_loop_fields:
  "leaf_q (antihydra_admitted_leaf_loop residue width) =
      antihydra_family_orbit residue width"
  "leaf_bits (antihydra_admitted_leaf_loop residue width) =
      antihydra_family_bits residue width"
  "leaf_delta (antihydra_admitted_leaf_loop residue width) =
      antihydra_family_balance residue 0 width"
  "leaf_minimum (antihydra_admitted_leaf_loop residue width) =
      antihydra_family_minimum residue 0 width"
  using antihydra_admitted_leaf_loop_refinement[of residue width]
  by (simp_all add: antihydra_family_balance_def antihydra_family_minimum_def)

corollary antihydra_family_funpow_cylinder_transport:
  "(antihydra_family_step ^^ n) (r + 2^n*q) =
    (antihydra_family_step ^^ n) r + 3^n*q"
  using antihydra_family_orbit_cylinder_transport[of r n q]
  by (simp add: antihydra_family_orbit_funpow)

corollary antihydra_arithmetic_source_image_endpoint:
  "3^n * lift + antihydra_family_orbit residue n =
    antihydra_family_orbit (residue + 2^n*lift) n"
  using antihydra_family_orbit_cylinder_transport[of residue n lift]
  by (simp add: algebra_simps)

definition antihydra_demanded_cylinder :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "antihydra_demanded_cylinder a n =
    3^n * (a div 2^n) +
      antihydra_family_orbit (a mod 2^n) n"

theorem antihydra_demanded_cylinder_exact:
  "antihydra_demanded_cylinder a n = antihydra_family_orbit a n"
proof -
  have source:
    "a = a mod 2^n + 2^n * (a div 2^n)"
    using div_mult_mod_eq[of a "2^n"]
    by (simp add: algebra_simps)
  have transported:
    "antihydra_family_orbit
        (a mod 2^n + 2^n * (a div 2^n)) n =
      antihydra_family_orbit (a mod 2^n) n +
        3^n * (a div 2^n)"
    by (rule antihydra_family_orbit_cylinder_transport)
  have rebuilt:
    "antihydra_family_orbit a n =
      antihydra_family_orbit
        (a mod 2^n + 2^n * (a div 2^n)) n"
    by (rule arg_cong[OF source])
  have endpoint:
    "antihydra_family_orbit a n =
      antihydra_family_orbit (a mod 2^n) n +
        3^n * (a div 2^n)"
    using rebuilt transported by simp
  show ?thesis
    unfolding antihydra_demanded_cylinder_def
    using endpoint by (simp add: algebra_simps)
qed

theorem antihydra_demanded_cylinder_composition:
  "antihydra_demanded_cylinder a (k+l) =
    antihydra_demanded_cylinder (antihydra_demanded_cylinder a k) l"
  using antihydra_demanded_cylinder_exact[of a "k+l"]
    antihydra_demanded_cylinder_exact[of a k]
    antihydra_demanded_cylinder_exact[
      of "antihydra_demanded_cylinder a k" l]
    antihydra_family_orbit_add[of a k l]
  by simp

corollary antihydra_demanded_cylinder_skew_application:
  "sk_D (antihydra_arithmetic_block a n) *
      int (antihydra_demanded_cylinder a n) =
    skew_numerator (antihydra_arithmetic_block a n) (int a)"
  using antihydra_arithmetic_block_skew_application[of a n]
    antihydra_demanded_cylinder_exact[of a n]
  by simp

corollary antihydra_demanded_cylinder_block_composition:
  "antihydra_arithmetic_block a (k+l) =
    skew_then (antihydra_arithmetic_block a k)
      (antihydra_arithmetic_block (antihydra_demanded_cylinder a k) l)"
  using antihydra_arithmetic_block_composition[of a k l]
    antihydra_demanded_cylinder_exact[of a k]
  by simp

theorem antihydra_demanded_cylinder_split:
  fixes a k l :: nat
  defines "first \<equiv>
    antihydra_family_orbit (a mod 2^k) k"
  defines "mid \<equiv> 3^k * (a div 2^k) + first"
  defines "second_source \<equiv> mid mod 2^l"
  defines "endpoint \<equiv>
    3^l * (mid div 2^l) +
      antihydra_family_orbit second_source l"
  shows "mid = antihydra_family_orbit a k"
    and "endpoint = antihydra_family_orbit a (k+l)"
proof -
  show mid: "mid = antihydra_family_orbit a k"
    using antihydra_demanded_cylinder_exact[of a k]
    unfolding antihydra_demanded_cylinder_def first_def mid_def
    by simp
  have second:
    "endpoint = antihydra_family_orbit mid l"
    using antihydra_demanded_cylinder_exact[of mid l]
    unfolding antihydra_demanded_cylinder_def second_source_def endpoint_def
    by simp
  show "endpoint = antihydra_family_orbit a (k+l)"
    using second mid antihydra_family_orbit_add[of a k l]
    by simp
qed

theorem antihydra_demanded_cylinder_bits_split:
  fixes a k l :: nat
  defines "first_source \<equiv> a mod 2^k"
  defines "first \<equiv> antihydra_family_orbit first_source k"
  defines "mid \<equiv> 3^k * (a div 2^k) + first"
  defines "second_source \<equiv> mid mod 2^l"
  shows "antihydra_family_bits a (k+l) =
    antihydra_family_bits first_source k @
      antihydra_family_bits second_source l"
proof -
  have first_endpoint: "mid = antihydra_family_orbit a k"
    using antihydra_demanded_cylinder_exact[of a k]
    unfolding antihydra_demanded_cylinder_def
      first_source_def first_def mid_def
    by simp
  have first_bits:
    "antihydra_family_bits a k =
      antihydra_family_bits first_source k"
  proof -
    have source: "a = first_source + 2^k * (a div 2^k)"
      using div_mult_mod_eq[of a "2^k"]
      unfolding first_source_def by (simp add: algebra_simps)
    have transported:
      "antihydra_family_bits
          (first_source + 2^k * (a div 2^k)) k =
        antihydra_family_bits first_source k"
      by (rule antihydra_family_bits_cylinder_transport)
    have rebuilt:
      "antihydra_family_bits a k =
        antihydra_family_bits
          (first_source + 2^k * (a div 2^k)) k"
      by (rule arg_cong[OF source])
    show ?thesis using rebuilt transported by simp
  qed
  have second_bits:
    "antihydra_family_bits mid l =
      antihydra_family_bits second_source l"
  proof -
    have source: "mid = second_source + 2^l * (mid div 2^l)"
      using div_mult_mod_eq[of mid "2^l"]
      unfolding second_source_def by (simp add: algebra_simps)
    have transported:
      "antihydra_family_bits
          (second_source + 2^l * (mid div 2^l)) l =
        antihydra_family_bits second_source l"
      by (rule antihydra_family_bits_cylinder_transport)
    have rebuilt:
      "antihydra_family_bits mid l =
        antihydra_family_bits
          (second_source + 2^l * (mid div 2^l)) l"
      by (rule arg_cong[OF source])
    show ?thesis using rebuilt transported by simp
  qed
  show ?thesis
    using antihydra_family_bits_append[of a k l]
      first_endpoint first_bits second_bits
    by simp
qed

theorem antihydra_demanded_cylinder_ledger_split:
  fixes a k l :: nat
  defines "first_source \<equiv> a mod 2^k"
  defines "first \<equiv> antihydra_family_orbit first_source k"
  defines "mid \<equiv> 3^k * (a div 2^k) + first"
  defines "second_source \<equiv> mid mod 2^l"
  shows "antihydra_family_balance a 0 (k+l) =
      antihydra_family_balance first_source 0 k +
        antihydra_family_balance second_source 0 l"
    and "antihydra_family_minimum a 0 (k+l) =
      min (antihydra_family_minimum first_source 0 k)
        (antihydra_family_balance first_source 0 k +
          antihydra_family_minimum second_source 0 l)"
proof -
  have bits:
    "antihydra_family_bits a (k+l) =
      antihydra_family_bits first_source k @
        antihydra_family_bits second_source l"
    using antihydra_demanded_cylinder_bits_split[of a k l]
    unfolding first_source_def first_def mid_def second_source_def .
  show "antihydra_family_balance a 0 (k+l) =
      antihydra_family_balance first_source 0 k +
        antihydra_family_balance second_source 0 l"
    using bits
    by (simp add: antihydra_family_balance_def ledger_word_delta_append)
  show "antihydra_family_minimum a 0 (k+l) =
      min (antihydra_family_minimum first_source 0 k)
        (antihydra_family_balance first_source 0 k +
          antihydra_family_minimum second_source 0 l)"
    using bits
    by (simp add: antihydra_family_balance_def antihydra_family_minimum_def
        ledger_word_minprefix_append)
qed

corollary antihydra_source_eight_demanded_cylinder:
  "antihydra_demanded_cylinder 8 n = mahler_orbit 7 n + 1"
  using antihydra_demanded_cylinder_exact[of 8 n]
    antihydra_source_eight_centered_orbit[of n]
  by simp

text \<open>The split theorem is an endpoint refinement for the balanced
arithmetic image.  Ledger minima, physical roofs, tape projections and a
construction-cost bound remain separate obligations.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms antihydra_family_step_even_translation
      antihydra_family_orbit_funpow
      antihydra_family_orbit_cylinder_transport
      antihydra_family_bits_cylinder_transport
      antihydra_family_balance_cylinder_transport
      antihydra_family_minimum_cylinder_transport
      ledger_word_delta_append ledger_word_minprefix_append
      ledger_word_minprefix_le_delta ledger_word_append_binary_step
      antihydra_family_orbit_Suc_right antihydra_family_bits_Suc_right
      antihydra_leaf_step_q antihydra_admitted_leaf_loop_refinement
      antihydra_admitted_leaf_loop_fields
      antihydra_family_funpow_cylinder_transport
      antihydra_arithmetic_source_image_endpoint
      antihydra_demanded_cylinder_exact
      antihydra_demanded_cylinder_composition
      antihydra_demanded_cylinder_skew_application
      antihydra_demanded_cylinder_block_composition
      antihydra_demanded_cylinder_split
      antihydra_demanded_cylinder_bits_split
      antihydra_demanded_cylinder_ledger_split
      antihydra_source_eight_demanded_cylinder}) then ()
    else error "Antihydra arithmetic cylinder lift depends on an oracle";
\<close>

end
