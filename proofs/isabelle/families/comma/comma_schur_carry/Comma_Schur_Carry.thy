theory Comma_Schur_Carry
  imports Shared_Carry_Dynamics.Shared_Decimal_Cocycle_Core
begin

text \<open>
The decimal split below is a small algebraic constructor.  It factors a
base-ten multiply into a binary carry and a radix-five carry.  It does not
construct the larger phase, reset-germ, or block quotient suggested by the
research notes.
\<close>

abbreviation comma_schur_quotient :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_schur_quotient alpha beta \<equiv> digit_value alpha beta"

lemma comma_schur_quotient_def:
  "comma_schur_quotient alpha beta = alpha + 5 * beta"
  by (simp add: digit_value_def)

lemma comma_schur_decimal_split:
  assumes binary: "2 * u = beta * c + t"
      and radix_five: "5 * t = alpha * c + u'"
  shows "10 * u = comma_schur_quotient alpha beta * c + u'"
proof -
  have "10 * u = 5 * (2 * u)" by simp
  also have "... = 5 * (beta * c + t)" using binary by simp
  also have "... = 5 * beta * c + 5 * t"
    by (simp add: algebra_simps)
  also have "... = 5 * beta * c + (alpha * c + u')"
    using radix_five by simp
  also have "... = comma_schur_quotient alpha beta * c + u'"
    by (simp add: comma_schur_quotient_def algebra_simps)
  finally show ?thesis .
qed

lemma comma_schur_split_ranges:
  assumes c_pos: "0 < c"
      and u_range: "u < c"
      and binary: "2 * u = beta * c + t"
      and t_range: "t < c"
      and radix_five: "5 * t = alpha * c + u'"
      and u'_range: "u' < c"
  shows "beta < 2"
    and "alpha < 5"
    and "comma_schur_quotient alpha beta < 10"
proof -
  have beta_le: "beta * c \<le> 2 * u"
    using binary by arith
  have twice_u_lt: "2 * u < 2 * c"
    using u_range by simp
  have two_c_le: "2 * c \<le> beta * c"
    if "2 \<le> beta"
    using mult_le_mono1[OF that, of c] by (simp add: mult.commute)
  show "beta < 2"
  proof (rule ccontr)
    assume not_less: "\<not> beta < 2"
    then have "2 \<le> beta" by arith
    then have "2 * c \<le> beta * c" by (rule two_c_le)
    with beta_le twice_u_lt show False by arith
  qed

  have alpha_le: "alpha * c \<le> 5 * t"
    using radix_five by arith
  have five_t_lt: "5 * t < 5 * c"
    using t_range by simp
  have five_c_le: "5 * c \<le> alpha * c"
    if "5 \<le> alpha"
    using mult_le_mono1[OF that, of c] by (simp add: mult.commute)
  show "alpha < 5"
  proof (rule ccontr)
    assume not_less: "\<not> alpha < 5"
    then have "5 \<le> alpha" by arith
    then have "5 * c \<le> alpha * c" by (rule five_c_le)
    with alpha_le five_t_lt show False by arith
  qed

  show "comma_schur_quotient alpha beta < 10"
    using \<open>beta < 2\<close> \<open>alpha < 5\<close>
    by (simp add: comma_schur_quotient_def; arith)
qed

lemma comma_schur_exact_quotient:
  assumes c_pos: "0 < c"
      and split: "10 * u = comma_schur_quotient alpha beta * c + u'"
      and u'_range: "u' < c"
  shows "(10 * u) div c = comma_schur_quotient alpha beta"
    and "(10 * u) mod c = u'"
proof -
  have quotient: "(comma_schur_quotient alpha beta * c + u') div c =
      comma_schur_quotient alpha beta"
    using c_pos u'_range by simp
  have remainder: "(comma_schur_quotient alpha beta * c + u') mod c = u'"
    using u'_range by simp
  show "(10 * u) div c = comma_schur_quotient alpha beta"
    using arg_cong[OF split, of "\<lambda>value. value div c"] quotient by metis
  show "(10 * u) mod c = u'"
    using arg_cong[OF split, of "\<lambda>value. value mod c"] remainder by metis
qed


corollary comma_schur_split_exact_quotient:
  assumes c_pos: "0 < c"
      and u_range: "u < c"
      and binary: "2 * u = beta * c + t"
      and t_range: "t < c"
      and radix_five: "5 * t = alpha * c + u'"
      and u'_range: "u' < c"
  shows "comma_schur_quotient alpha beta < 10"
    and "(10 * u) div c = comma_schur_quotient alpha beta"
    and "(10 * u) mod c = u'"
proof -
  have split: "10 * u = comma_schur_quotient alpha beta * c + u'"
    by (rule comma_schur_decimal_split[OF binary radix_five])
  show "comma_schur_quotient alpha beta < 10"
    by (rule comma_schur_split_ranges(3)[OF c_pos u_range binary t_range
        radix_five u'_range])
  show "(10 * u) div c = comma_schur_quotient alpha beta"
    and "(10 * u) mod c = u'"
    by (rule comma_schur_exact_quotient[OF c_pos split u'_range])+
qed

lemma comma_schur_construct_refines:
  fixes u c :: nat
  assumes positive: "0 < c"
  shows "comma_schur_quotient ((5*((2*u) mod c)) div c) ((2*u) div c)
      = (10*u) div c"
    "(5*((2*u) mod c)) mod c = (10*u) mod c"
proof -
  have binary: "2*u = ((2*u) div c)*c + (2*u) mod c" by simp
  have radix_five: "5*((2*u) mod c) =
      ((5*((2*u) mod c)) div c)*c + (5*((2*u) mod c)) mod c" by simp
  have split: "10*u =
      comma_schur_quotient ((5*((2*u) mod c)) div c) ((2*u) div c)*c
      + (5*((2*u) mod c)) mod c"
    by (rule comma_schur_decimal_split[OF binary radix_five])
  have bound: "(5*((2*u) mod c)) mod c < c"
    by (rule mod_less_divisor[OF positive])
  show "comma_schur_quotient ((5*((2*u) mod c)) div c) ((2*u) div c)
      = (10*u) div c"
    "(5*((2*u) mod c)) mod c = (10*u) mod c"
    using comma_schur_exact_quotient[OF positive split bound] by simp_all
qed

text \<open>
Comma uses the shared `carry_domain` algebra from
`Shared_Carry_Dynamics.Shared_Carry_Domain`. Its identity, repeated-action,
and reset laws are family-independent; the polarity distinction below is
retained because it is observable by this family's richer state.
\<close>

lemma comma_schur_reset_polarities_are_distinct:
  "carry_apply Below False \<noteq>
    carry_apply Above False"
  by simp

text \<open>
The reset lemmas erase only the incoming Boolean carry from this monoid.
They do not erase the reset polarity, an F5 defect, an occurrence cocycle,
or a harmonic/phase coordinate.  In particular, identifying R0 and R1 is
false at a fixed Boolean input, and erasing a six-valued reset germ requires
an independent occurrence-conjugacy or dead-output theorem.
\<close>

ML \<open>
  val checked = @{thms comma_schur_decimal_split comma_schur_split_ranges
    comma_schur_exact_quotient comma_schur_split_exact_quotient
    comma_schur_construct_refines
    comma_schur_reset_polarities_are_distinct};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Schur carry proof depends on an oracle";
\<close>

end
