theory Comma_C1_Return
  imports Comma_C1_Phase Comma_Arithmetic.Comma_Finite_Period
    Comma_Arithmetic.Comma_Boundary_Primitives
begin

text \<open>The carry count is an additive cocycle over the finite CRT phase.
The literal sum is its specification. The fixed-sector arithmetic below
also identifies it with an exact quotient of the existing displacement
formula, so a caller can use complete periods and a bounded tail.\<close>

fun comma_c1_count :: "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_count C 0 = 0"
| "comma_c1_count C (Suc n) = comma_c1_count C n +
      (if comma_c1 (comma_c1_iter n C) then 1 else 0)"


lemma comma_c1_count_zero:
  "comma_c1_count C 0 = 0"
  by simp


lemma comma_c1_count_suc:
  "comma_c1_count C (Suc n) = comma_c1_count C n +
      (if comma_c1 (comma_c1_iter n C) then 1 else 0)"
  by simp


lemma comma_c1_iter_add:
  "comma_c1_iter (m + n) C = comma_c1_iter n (comma_c1_iter m C)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: add.assoc)
qed


lemma comma_c1_count_add:
  "comma_c1_count C (m + n) =
    comma_c1_count C m + comma_c1_count (comma_c1_iter m C) n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have iter: "comma_c1_iter (m + n) C =
      comma_c1_iter n (comma_c1_iter m C)"
    by (rule comma_c1_iter_add)
  show ?case using Suc.IH iter by (simp add: add.assoc)
qed


lemma comma_c1_iter_closed:
  assumes "comma_c1_phase_admitted C"
  shows "comma_c1_phase_admitted (comma_c1_iter n C)"
  using assms
  by (induction n) (simp_all add: comma_c1_step_closed)


lemma comma_c1_iter_physical:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_fixed_iter (c1_sector C) n
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) =
    100 * (H + comma_c1_count C n) +
      comma_c1_decode (c1_mod4 (comma_c1_iter n C))
        (c1_mod25 (comma_c1_iter n C))"
proof (induction n arbitrary: H)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?D = "comma_c1_iter n C"
  let ?N = "comma_c1_count C n"
  have D_admitted: "comma_c1_phase_admitted ?D"
    by (rule comma_c1_iter_closed[OF admitted])
  have low: "comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D) < 100"
    by (simp add: comma_c1_decode_def)
  have phase:
    "?D = comma_c1_phase_of (c1_sector ?D)
      (comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D))"
    by (rule sym, rule comma_c1_phase_of_decode[OF D_admitted])
  have sector: "c1_sector ?D = c1_sector C"
    by (rule comma_c1_iter_sector)
  have bound: "c1_sector ?D \<le> 9"
    using D_admitted by (simp add: comma_c1_phase_admitted_def)
  have carry_step:
    "(100 * (H + ?N) + comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)) +
        10 * ((100 * (H + ?N) +
          comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)) mod 10) +
        c1_sector C =
      100 * (H + ?N + (if comma_c1 ?D then 1 else 0)) +
        comma_c1_decode (c1_mod4 (comma_c1_step ?D))
          (c1_mod25 (comma_c1_step ?D))"
    using comma_c1_high_prefix_step[OF low phase bound, of "H + ?N"] sector
    by simp
  show ?case
    using Suc.IH[of H] carry_step sector
    by (simp add: comma_c1_count_suc algebra_simps)
qed


lemma comma_c1_count_displacement:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C n =
    (comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
      comma_period_displacement (c1_sector C)
        (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10) n) div 100"
proof -
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?D = "comma_c1_iter n C"
  let ?N = "comma_c1_count C n"
  have physical: "comma_fixed_iter (c1_sector C) n ?x = 100 * ?N +
      comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)"
    using comma_c1_iter_physical[OF admitted, where H=0] by simp
  have displacement: "comma_fixed_iter (c1_sector C) n ?x =
      ?x + comma_period_displacement (c1_sector C) (?x mod 10) n"
    by (rule comma_fixed_iter_displacement)
  have low: "comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D) < 100"
    by (simp add: comma_c1_decode_def)
  have quotient:
    "(100 * ?N + comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)) div 100 = ?N"
    using low by simp
  have equation:
    "?x + comma_period_displacement (c1_sector C) (?x mod 10) n =
       100 * ?N + comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)"
    by (rule trans[OF displacement[symmetric] physical])
  show ?thesis by (simp only: equation quotient)
qed

definition comma_c1_displacement_prefix ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_displacement_prefix C n =
    (let f = c1_sector C;
         d = comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10;
         L = comma_cycle_length f
     in n div L * comma_finite_period f d +
          comma_period_displacement f d (n mod L))"


lemma comma_c1_displacement_prefix_refines:
  assumes "comma_c1_phase_admitted C"
  shows "comma_c1_displacement_prefix C n =
    comma_period_displacement (c1_sector C)
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10) n"
proof -
  let ?f = "c1_sector C"
  let ?d = "comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10"
  let ?L = "comma_cycle_length ?f"
  have f_bounds: "1 \<le> ?f" "?f \<le> 9"
    using assms by (simp_all add: comma_c1_phase_admitted_def)
  have closes: "10 dvd ?L * ?f"
    using comma_cycle_length_admitted(2)[OF f_bounds] .
  have finite: "comma_finite_period ?f ?d =
      comma_period_displacement ?f ?d ?L"
    by (rule comma_finite_period_refines[OF f_bounds]; simp)
  have split: "n = (n div ?L) * ?L + n mod ?L"
    using comma_cycle_length_admitted(1)[OF f_bounds]
    by (simp add: div_mult_mod_eq mult.commute)
  have repeated:
    "comma_period_displacement ?f ?d n =
      (n div ?L) * comma_period_displacement ?f ?d ?L +
        comma_period_displacement ?f ?d (n mod ?L)"
    using comma_period_displacement_repeated[OF closes, of ?d "n div ?L" "n mod ?L"]
      split by (simp add: add.commute)
  show ?thesis
    unfolding comma_c1_displacement_prefix_def
    using finite repeated by (simp add: Let_def)
qed


lemma comma_c1_cycle_tail_below_ten:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "n mod comma_cycle_length (c1_sector C) < 10"
proof -
  let ?f = "c1_sector C"
  let ?L = "comma_cycle_length ?f"
  have f_bounds: "1 \<le> ?f" "?f \<le> 9"
    using admitted by (simp_all add: comma_c1_phase_admitted_def)
  have positive: "0 < ?L"
    using comma_cycle_length_admitted(1)[OF f_bounds] .
  have period: "n mod ?L < ?L"
    by (rule mod_less_divisor[OF positive])
  have at_most_ten: "?L \<le> 10"
    using f_bounds by (simp add: comma_cycle_length_def)
  show ?thesis using period at_most_ten by arith
qed

record comma_c1_return =
  c1_target :: comma_c1_phase
  c1_count :: nat

definition comma_c1_return :: "comma_c1_phase \<Rightarrow> nat \<Rightarrow> comma_c1_return" where
  "comma_c1_return C n =
    \<lparr>c1_target = comma_c1_iter n C, c1_count = comma_c1_count C n\<rparr>"


lemma comma_c1_count_complete_cycles:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C n =
    (comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
      comma_c1_displacement_prefix C n) div 100"
  using comma_c1_count_displacement[OF admitted, of n]
    comma_c1_displacement_prefix_refines[OF admitted, of n]
  by simp


lemma comma_c1_return_displacement:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_return C n =
    \<lparr>c1_target = comma_c1_phase_of (c1_sector C)
        ((comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
          comma_period_displacement (c1_sector C)
            (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10) n) mod 100),
      c1_count = (comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
          comma_period_displacement (c1_sector C)
            (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10) n) div 100\<rparr>"
proof -
  let ?f = "c1_sector C"
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?D = "comma_c1_iter n C"
  let ?N = "comma_c1_count C n"
  let ?P = "comma_period_displacement ?f (?x mod 10) n"
  have physical: "comma_fixed_iter ?f n ?x = 100 * ?N +
      comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)"
    using comma_c1_iter_physical[OF admitted, where H=0] by simp
  have displacement: "comma_fixed_iter ?f n ?x = ?x + ?P"
    by (rule comma_fixed_iter_displacement)
  have low: "comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D) < 100"
    by (simp add: comma_c1_decode_def)
  have equation: "100 * ?N + comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D) = ?x + ?P"
    using physical displacement by simp
  have target_low:
    "comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D) = (?x + ?P) mod 100"
  proof -
    have reduced:
      "(100 * ?N + comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)) mod 100 =
        comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)"
      using low by simp
    show ?thesis by (simp only: equation[symmetric] reduced)
  qed
  have D_admitted: "comma_c1_phase_admitted ?D"
    by (rule comma_c1_iter_closed[OF admitted])
  have D_phase:
    "comma_c1_phase_of (c1_sector ?D)
        (comma_c1_decode (c1_mod4 ?D) (c1_mod25 ?D)) = ?D"
    by (rule comma_c1_phase_of_decode[OF D_admitted])
  have D_sector: "c1_sector ?D = ?f"
    by (rule comma_c1_iter_sector)
  have target:
    "comma_c1_phase_of ?f ((?x + ?P) mod 100) = ?D"
    using D_phase D_sector target_low by simp
  have count:
    "?N = (?x + ?P) div 100"
    using comma_c1_count_displacement[OF admitted, of n] by simp
  show ?thesis
    unfolding comma_c1_return_def
    using target count by simp
qed


lemma comma_c1_return_complete_cycles:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_return C n =
    \<lparr>c1_target = comma_c1_phase_of (c1_sector C)
        ((comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
          comma_c1_displacement_prefix C n) mod 100),
      c1_count = (comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
          comma_c1_displacement_prefix C n) div 100\<rparr>"
proof -
  have displacement:
    "comma_c1_displacement_prefix C n =
      comma_period_displacement (c1_sector C)
        (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10) n"
    by (rule comma_c1_displacement_prefix_refines[OF admitted])
  show ?thesis
    using comma_c1_return_displacement[OF admitted, of n] displacement
    by simp
qed


text \<open>The executable constructor uses complete cycles and a bounded tail.
The iterated return above is its specification, not its evaluation recipe.\<close>

definition comma_c1_closed_return ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> comma_c1_return" where
  "comma_c1_closed_return C n =
    (let total = comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
       comma_c1_displacement_prefix C n
     in \<lparr>c1_target = comma_c1_phase_of (c1_sector C) (total mod 100),
          c1_count = total div 100\<rparr>)"

lemma comma_c1_closed_return_exact:
  assumes "comma_c1_phase_admitted C"
  shows "comma_c1_closed_return C n = comma_c1_return C n"
  by (simp only: comma_c1_closed_return_def Let_def
      comma_c1_return_complete_cycles[OF assms])

lemma comma_c1_checked_publication_exact:
  fixes count :: nat
  assumes source: "comma_c1_phase_admitted C"
    and target: "comma_c1_phase_admitted T"
    and sector: "c1_sector T = c1_sector C"
    and balance: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
      comma_c1_displacement_prefix C n =
      100 * count + comma_c1_decode (c1_mod4 T) (c1_mod25 T)"
  shows "\<lparr>c1_target = T, c1_count = count\<rparr> = comma_c1_return C n"
proof -
  let ?x = "comma_c1_decode (c1_mod4 T) (c1_mod25 T)"
  have low: "?x < 100" by (simp add: comma_c1_decode_def)
  have quotient: "(100 * count + ?x) div 100 = count"
    using low by simp
  have remainder: "(100 * count + ?x) mod 100 = ?x"
    using low by simp
  have phase: "comma_c1_phase_of (c1_sector C) ?x = T"
    using comma_c1_phase_of_decode[OF target] sector by simp
  show ?thesis
    by (simp only: comma_c1_return_complete_cycles[OF source]
      balance quotient remainder phase)
qed


lemma comma_c1_return_zero:
  "comma_c1_return C 0 = \<lparr>c1_target = C, c1_count = 0\<rparr>"
  by (simp add: comma_c1_return_def)


lemma comma_c1_return_one:
  "comma_c1_return C 1 =
    \<lparr>c1_target = comma_c1_step C,
      c1_count = (if comma_c1 C then 1 else 0)\<rparr>"
  by (simp add: comma_c1_return_def)

definition comma_c1_return_compose ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_c1_return" where
  "comma_c1_return_compose C m n =
    (let A = comma_c1_return C m;
         B = comma_c1_return (c1_target A) n
     in \<lparr>c1_target = c1_target B,
          c1_count = c1_count A + c1_count B\<rparr>)"


lemma comma_c1_return_compose_exact:
  "comma_c1_return_compose C m n = comma_c1_return C (m + n)"
proof -
  have target:
    "comma_c1_iter n (c1_target (comma_c1_return C m)) =
      comma_c1_iter (m + n) C"
    by (simp add: comma_c1_return_def comma_c1_iter_add)
  have count:
    "c1_count (comma_c1_return C m) +
      c1_count (comma_c1_return (c1_target (comma_c1_return C m)) n) =
      comma_c1_count C (m + n)"
    by (simp add: comma_c1_return_def comma_c1_count_add)
  show ?thesis
    unfolding comma_c1_return_compose_def
    using target count by (simp add: comma_c1_return_def Let_def)
qed


lemma comma_c1_return_add:
  "comma_c1_return C (m + n) = comma_c1_return_compose C m n"
  by (simp add: comma_c1_return_compose_exact)

fun comma_c1_power2 :: "nat \<Rightarrow> comma_c1_phase \<Rightarrow> comma_c1_return" where
  "comma_c1_power2 0 C = comma_c1_return C 1"
| "comma_c1_power2 (Suc k) C =
    (let A = comma_c1_power2 k C;
         B = comma_c1_power2 k (c1_target A)
     in \<lparr>c1_target = c1_target B,
          c1_count = c1_count A + c1_count B\<rparr>)"


lemma comma_c1_power2_exact:
  "comma_c1_power2 k C = comma_c1_return C (2 ^ k)"
proof (induction k arbitrary: C)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have doubled: "(2::nat) ^ Suc k = 2 ^ k + 2 ^ k"
    by (simp add: power_Suc)
  have composed: "comma_c1_power2 (Suc k) C =
      comma_c1_return_compose C (2 ^ k) (2 ^ k)"
    by (simp only: comma_c1_power2.simps Suc.IH comma_c1_return_compose_def)
  show ?case
    by (simp only: composed comma_c1_return_compose_exact doubled)
qed

definition comma_c1_source_admitted ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_c1_source_admitted C H p n \<longleftrightarrow>
    comma_c1_phase_admitted C \<and> 2 \<le> p \<and>
    comma_sector (c1_sector C) p
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) \<and>
    (n = 0 \<or> comma_c1_displacement_prefix C n +
      (if c1_sector C < 9 then 1 else 0) <
      comma_headroom (c1_sector C) p
        (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)))"

text \<open>This is strict interior admission, not a classifier at a fork.
It reserves the competing-child seam, including the 118 to 199/200 fork.\<close>


lemma comma_c1_source_guard:
  assumes admitted: "comma_c1_source_admitted C H p n" and positive: "0<n"
  shows "comma_phase_max_guard (c1_sector C)
      ((100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) mod 10) n <
    comma_headroom (c1_sector C) p
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
proof -
  have phase: "comma_c1_phase_admitted C"
    using admitted by (simp add: comma_c1_source_admitted_def)
  have digit: "c1_sector C \<le> 9"
    using phase by (simp add: comma_c1_phase_admitted_def)
  note displacement = comma_c1_displacement_prefix_refines[OF phase, of n]
  note guard = comma_phase_max_guard_closed[OF positive digit,
    of "comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10"]
  show ?thesis using admitted positive displacement guard
    by (simp add: comma_c1_source_admitted_def)
qed


lemma comma_c1_source_unique_child:
  assumes admitted: "comma_c1_source_admitted C H p n" and within: "j<n"
  defines "k \<equiv> 100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  shows "comma_child (comma_fixed_iter (c1_sector C) j k)
      (comma_fixed_iter (c1_sector C) (Suc j) k)"
    "\<And>v. comma_child (comma_fixed_iter (c1_sector C) j k) v \<Longrightarrow>
      v = comma_fixed_iter (c1_sector C) (Suc j) k"
proof -
  have source: "comma_sector (c1_sector C) p k" and exponent: "2 \<le> p"
    using admitted by (auto simp: comma_c1_source_admitted_def k_def)
  have positive: "0<n" using within by arith
  have guard: "comma_phase_max_guard (c1_sector C) (k mod 10) n <
      comma_headroom (c1_sector C) p k"
    using comma_c1_source_guard[OF admitted positive] by (simp add: k_def)
  show "comma_child (comma_fixed_iter (c1_sector C) j k)
      (comma_fixed_iter (c1_sector C) (Suc j) k)"
    by (rule comma_phase_guard_unique_step(1)[OF source exponent guard within])
  show "\<And>v. comma_child (comma_fixed_iter (c1_sector C) j k) v \<Longrightarrow>
      v = comma_fixed_iter (c1_sector C) (Suc j) k"
    by (rule comma_phase_guard_unique_step(2)[OF source exponent guard within])
qed


lemma comma_c1_source_endpoint:
  assumes admitted: "comma_c1_source_admitted C H p n"
  shows "comma_sector (c1_sector C) p
    (100 * (H + c1_count (comma_c1_return C n)) +
      comma_c1_decode (c1_mod4 (c1_target (comma_c1_return C n)))
        (c1_mod25 (c1_target (comma_c1_return C n))))"
proof -
  let ?k = "100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  have phase: "comma_c1_phase_admitted C" and source: "comma_sector (c1_sector C) p ?k"
    using admitted by (auto simp: comma_c1_source_admitted_def)
  have sector: "comma_sector (c1_sector C) p (comma_fixed_iter (c1_sector C) n ?k)"
  proof (cases "n=0")
    case True
    then show ?thesis using source by simp
  next
    case False
    then have positive: "0<n" by simp
    show ?thesis by (rule comma_phase_guard_endpoint_sector[OF source positive
      comma_c1_source_guard[OF admitted positive]])
  qed
  note exact = comma_c1_iter_physical[OF phase, where H=H and n=n]
  show ?thesis using sector exact by (simp add: comma_c1_return_def)
qed



lemma comma_c1_source_path:
  assumes admitted: "comma_c1_source_admitted C H p n"
  shows "rtranclp comma_child
    (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
    (100 * (H + c1_count (comma_c1_return C n)) +
      comma_c1_decode (c1_mod4 (c1_target (comma_c1_return C n)))
        (c1_mod25 (c1_target (comma_c1_return C n))))"
proof -
  let ?k = "100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  have phase: "comma_c1_phase_admitted C"
    and source: "comma_sector (c1_sector C) p ?k" and exponent: "2 \<le> p"
    using admitted by (auto simp: comma_c1_source_admitted_def)
  have path: "rtranclp comma_child ?k (comma_fixed_iter (c1_sector C) n ?k)"
  proof (cases "n=0")
    case True
    then show ?thesis by simp
  next
    case False
    then have positive: "0<n" by simp
    note guard = comma_c1_source_guard[OF admitted positive]
    show ?thesis
      using comma_exact_phase_unique_path(2)[OF source exponent guard] by blast
  qed
  note exact = comma_c1_iter_physical[OF phase, where H=H and n=n]
  show ?thesis using path exact by (simp add: comma_c1_return_def)
qed

ML \<open>
  val checked = @{thms comma_c1_count_zero comma_c1_count_suc
    comma_c1_count_add comma_c1_iter_physical comma_c1_count_displacement
    comma_c1_displacement_prefix_refines comma_c1_count_complete_cycles
    comma_c1_return_displacement comma_c1_return_complete_cycles
    comma_c1_closed_return_exact comma_c1_checked_publication_exact
    comma_c1_return_zero comma_c1_return_one
    comma_c1_return_compose_exact comma_c1_power2_exact
    comma_c1_source_guard comma_c1_source_unique_child comma_c1_source_endpoint
    comma_c1_source_path};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 return proof depends on an oracle";
\<close>
end
