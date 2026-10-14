theory Collatz_Edge_Digit_Cycle_Refinement
  imports Collatz_Border_Return_Refinement
begin

text \<open>The finite physical last-digit graph is selected by a residue modulo
20.  These results classify finite source transitions and certify the two
newly powered guarded return words.  They make no claim that arbitrary
trajectories enter one of these cylinders or that their construction cost is
uniformly bounded.\<close>

lemma collatz_physical_decimal_output_exact:
  "physical_collatz x mod 10 =
    collatz_decimal_boundary_output ((x div 10) mod 2) (x mod 10)"
proof -
  have split: "x = 10 * (x div 10) + x mod 10"
    using div_mult_mod_eq[of x 10] by (simp add: mult.commute)
  show ?thesis
  proof (cases "even x")
    case True
    have digit_even: "even (x mod 10)"
      using True split by presburger
    obtain d where digit: "x mod 10 = 2*d"
      using digit_even by (auto elim: evenE)
    have digit_range: "x mod 10 < 10" by simp
    have d_bound: "d < 5"
      using digit digit_range by presburger
    have half: "x div 2 = 5*(x div 10) + d"
      using split digit by presburger
    have div_by_twenty: "(x div 10) div 2=x div 20"
      by (simp only: div_mult2_eq)
    have quotient_mod:
      "x div 10=2*((x div 10) div 2)+(x div 10) mod 2"
      using div_mult_mod_eq[of "x div 10" 2]
      by (simp add: mult.commute)
    have quotient_split:
      "x div 10 = 2*(x div 20) + (x div 10) mod 2"
      using quotient_mod div_by_twenty by simp
    have parity_bound: "(x div 10) mod 2 < 2" by simp
    have small_output: "d + 5*((x div 10) mod 2) < 10"
      using d_bound parity_bound by arith
    have reconstructed:
      "d + 5*(x div 10) =
        (d + 5*((x div 10) mod 2)) + 10*(x div 20)"
      using quotient_split by (simp add: algebra_simps)
    have sum_mod:
      "((d + 5*((x div 10) mod 2)) + 10*(x div 20)) mod 10 =
        (((d + 5*((x div 10) mod 2)) mod 10) +
          (10*(x div 20)) mod 10) mod 10"
      by (rule mod_add_eq[symmetric])
    have output_mod:
      "(d + 5*(x div 10)) mod 10 = d + 5*((x div 10) mod 2)"
      using reconstructed sum_mod small_output by (simp add: algebra_simps)
    show ?thesis
      using True digit half output_mod
      by (simp add: physical_collatz_def collatz_decimal_boundary_output_def
          algebra_simps)
  next
    case False
    have digit: "(x mod 10) mod 2 = 1"
      using False split by presburger
    have odd_digit: "odd (x mod 10)"
      using digit by presburger
    have residue:
      "(3*x+1) mod 10 = (3*(x mod 10)+1) mod 10"
    proof -
      have decomposition:
        "3*x+1 = (3*(x mod 10)+1) + 30*(x div 10)"
        using split by linarith
      have modular_sum:
        "((3*(x mod 10)+1) + 30*(x div 10)) mod 10 =
          (((3*(x mod 10)+1) mod 10) +
            (30*(x div 10)) mod 10) mod 10"
        by (rule mod_add_eq[symmetric])
      show ?thesis
        using decomposition modular_sum by simp
    qed
    show ?thesis
      using False odd_digit residue
      by (simp add: physical_collatz_def collatz_decimal_boundary_output_def)
  qed
qed

lemma collatz_decimal_quotient_remainder_unique:
  fixes x q r :: nat
  assumes decomposition: "x=10*q+r" and remainder: "r<10"
  shows "x div 10=q" and "x mod 10=r"
proof -
  have canonical: "x=10*(x div 10)+x mod 10"
    using div_mult_mod_eq[of x 10] by (simp add: mult.commute)
  have canonical_remainder: "x mod 10 < 10" by simp
  have quotient: "x div 10=q"
    using decomposition remainder canonical canonical_remainder by linarith
  show "x div 10=q" by (rule quotient)
  show "x mod 10=r"
  proof -
    have "10*q + x mod 10 = 10*q + r"
      using decomposition canonical quotient by simp
    then show ?thesis by simp
  qed
qed

definition collatz_physical_digit_edges :: "(nat \<times> nat) set" where
  "collatz_physical_digit_edges =
    set (map (\<lambda>r. (r mod 10,
      collatz_decimal_boundary_output (r div 10) (r mod 10))) [0..<20])"

lemma collatz_physical_digit_edges_exact:
  "collatz_physical_digit_edges =
    {(0,0),(0,5),(1,4),(2,1),(2,6),(3,0),(4,2),(4,7),
      (5,6),(6,3),(6,8),(7,2),(8,4),(8,9),(9,8)}"
  unfolding collatz_physical_digit_edges_def
    collatz_decimal_boundary_output_def
  by code_simp

theorem collatz_physical_digit_edge_selected_by_mod20:
  assumes guard: "x mod 20 = r" and range: "r < 20"
  shows "(x mod 10, physical_collatz x mod 10) =
      (r mod 10,
        collatz_decimal_boundary_output (r div 10) (r mod 10))"
    and "(x mod 10, physical_collatz x mod 10) \<in>
      collatz_physical_digit_edges"
proof -
  have x20: "x=20*(x div 20)+r"
    using div_mult_mod_eq[of x 20] guard by (simp add: mult.commute)
  have r10: "r=10*(r div 10)+r mod 10"
    using div_mult_mod_eq[of r 10] by (simp add: mult.commute)
  have x10: "x=10*(2*(x div 20)+r div 10)+r mod 10"
    using x20 r10 by (simp add: algebra_simps)
  have r_remainder: "r mod 10<10" by simp
  have quotient:
    "x div 10=2*(x div 20)+r div 10"
    and decimal: "x mod 10=r mod 10"
    using collatz_decimal_quotient_remainder_unique[OF x10 r_remainder]
    by simp_all
  have r_quotient_small: "r div 10<2"
    using range r10 r_remainder by linarith
  have parity_sum:
    "(2*(x div 20)+r div 10) mod 2 = r div 10"
  proof -
    have sum:
      "(2*(x div 20)+r div 10) mod 2 =
        ((2*(x div 20) mod 2)+(r div 10 mod 2)) mod 2"
      by (rule mod_add_eq[symmetric])
    have even_mod: "(2*(x div 20)) mod 2=0" by simp
    have residue_mod: "(r div 10) mod 2=r div 10"
      using r_quotient_small by simp
    show ?thesis using sum even_mod residue_mod by simp
  qed
  have quotient_parity: "(x div 10) mod 2 = r div 10"
    using quotient parity_sum by simp
  show edge:
    "(x mod 10, physical_collatz x mod 10) =
      (r mod 10,
        collatz_decimal_boundary_output (r div 10) (r mod 10))"
    using collatz_physical_decimal_output_exact decimal quotient_parity by simp
  show "(x mod 10, physical_collatz x mod 10) \<in>
      collatz_physical_digit_edges"
    using edge range
    unfolding collatz_physical_digit_edges_def
    by (auto intro!: image_eqI[where x=r])
qed

definition collatz_physical_digit_successors :: "nat \<Rightarrow> nat list" where
  "collatz_physical_digit_successors d =
    (if d=0 then [0,5] else if d=1 then [4] else if d=2 then [1,6]
     else if d=3 then [0] else if d=4 then [2,7] else if d=5 then [6]
     else if d=6 then [3,8] else if d=7 then [2] else if d=8 then [4,9]
     else [8])"

lemma collatz_physical_digit_successors_match_edges:
  assumes digit: "d < 10"
  shows "set (collatz_physical_digit_successors d) =
    {e. (d,e) \<in> collatz_physical_digit_edges}"
proof -
  have cases: "d=0 \<or> d=1 \<or> d=2 \<or> d=3 \<or> d=4 \<or>
      d=5 \<or> d=6 \<or> d=7 \<or> d=8 \<or> d=9"
    using digit by presburger
  show ?thesis
    using cases collatz_physical_digit_edges_exact
    unfolding collatz_physical_digit_successors_def
    by (elim disjE; auto simp: collatz_physical_digit_edges_exact)
qed

fun collatz_digit_cycle_walk :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
    nat list list" where
  "collatz_digit_cycle_walk start path 0 = []"
| "collatz_digit_cycle_walk start path (Suc fuel) =
    concat (map (\<lambda>next.
      if next = start then [path]
      else if next \<le> start \<or> next \<in> set path then []
      else collatz_digit_cycle_walk start (path @ [next]) fuel)
      (collatz_physical_digit_successors (last path)))"

definition collatz_physical_elementary_digit_cycles :: "nat list set" where
  "collatz_physical_elementary_digit_cycles =
    set (concat (map (\<lambda>start.
      collatz_digit_cycle_walk start [start] 10) [0..<10]))"

lemma collatz_physical_elementary_digit_cycles_exact:
  "collatz_physical_elementary_digit_cycles =
    {[0], [0,5,6,3], [1,4,2], [1,4,7,2], [2,6,8,4],
      [2,6,8,4,7], [8,9]}"
  unfolding collatz_physical_elementary_digit_cycles_def
    collatz_physical_digit_successors_def
  by code_simp

text \<open>The cycle walk prunes every repeated vertex and starts at the least
digit in each cycle, so rotations are represented once.  The evaluated set
above is an enumeration of the finite digit graph, not a statement about
which cycle an unbounded Collatz orbit follows.\<close>

lemma collatz_true_run_endpoint_exact:
  assumes divisible: "2^n dvd x+1"
  shows "collatz_guarded_normalized_word_admitted (replicate n True) x \<and>
    collatz_guarded_normalized_word_endpoint (replicate n True) x + 1 =
      3^n * ((x+1) div 2^n)"
  using divisible
proof (induction n arbitrary: x)
  case 0
  show ?case
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
next
  case (Suc n)
  obtain k where numerator: "x+1 = 2^(Suc n)*k"
    using Suc.prems unfolding dvd_def by blast
  have even_power: "even (2^(Suc n)*k)" by simp
  have even_next: "even (x+1)"
    using numerator even_power by simp
  have odd_x: "odd x"
    using even_next by presburger
  have first_plus:
    "collatz_guarded_normalized_source_step True x + 1 = 3*(2^n*k)"
    using collatz_guarded_true_step_plus_one[OF odd_x] numerator
    by (simp add: power_Suc algebra_simps)
  have tail_divisible:
    "2^n dvd collatz_guarded_normalized_source_step True x + 1"
    unfolding first_plus dvd_def by (rule exI[where x="3*k"]) simp
  have induction:
    "collatz_guarded_normalized_word_admitted
        (replicate n True) (collatz_guarded_normalized_source_step True x) \<and>
      collatz_guarded_normalized_word_endpoint
        (replicate n True) (collatz_guarded_normalized_source_step True x) + 1 =
        3^n * ((collatz_guarded_normalized_source_step True x + 1) div 2^n)"
    using Suc.IH[OF tail_divisible] .
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted
      (replicate n True) (collatz_guarded_normalized_source_step True x)"
    using induction by blast
  have tail_endpoint:
    "collatz_guarded_normalized_word_endpoint
      (replicate n True) (collatz_guarded_normalized_source_step True x) + 1 =
      3^n * ((collatz_guarded_normalized_source_step True x + 1) div 2^n)"
    using induction by blast
  have quotient: "(x+1) div 2^(Suc n) = k"
    using numerator by (simp add: power_Suc)
  have admitted:
    "collatz_guarded_normalized_word_admitted (replicate (Suc n) True) x"
    using odd_x tail_admitted
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
  have endpoint:
    "collatz_guarded_normalized_word_endpoint
      (replicate (Suc n) True) x + 1 =
      3^(Suc n) * ((x+1) div 2^(Suc n))"
    using odd_x tail_endpoint first_plus numerator quotient
    by (simp add: collatz_guarded_normalized_word_endpoint.simps
        power_Suc algebra_simps)
  show ?case using admitted endpoint by blast
qed

definition collatz_0563_word :: "nat \<Rightarrow> bool list" where
  "collatz_0563_word r = False # replicate (2*r) True"

theorem collatz_0563_guarded_action:
  assumes source: "x = 40*k+30"
    and positive: "0 < r"
    and divisor: "2^(2*r+1) dvd x+2"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_0563_word r) x"
    and "collatz_guarded_normalized_word_endpoint
      (collatz_0563_word r) x + 1 =
        3^(2*r) * ((x+2) div 2^(2*r+1))"
    and "length (collatz_0563_word r) = 2*r+1"
    and "count_list (collatz_0563_word r) True = 2*r"
    and "length (collatz_0563_word r) +
        count_list (collatz_0563_word r) True = 4*r+1"
proof -
  let ?y = "20*k+15"
  obtain h where h: "x+2 = 2^(2*r+1)*h"
    using divisor unfolding dvd_def by blast
  have even_x: "even x" using source by simp
  have prefix:
    "collatz_guarded_normalized_source_step False x = ?y"
    using source collatz_guarded_false_step_exact[OF even_x] by simp
  have y_plus: "?y+1 = 2^(2*r)*h"
    using h source by (simp add: power_Suc algebra_simps)
  have y_divisible: "2^(2*r) dvd ?y+1"
    unfolding y_plus dvd_def by blast
  have true_run:
    "collatz_guarded_normalized_word_admitted (replicate (2*r) True) ?y \<and>
      collatz_guarded_normalized_word_endpoint (replicate (2*r) True) ?y + 1 =
        3^(2*r) * ((?y+1) div 2^(2*r))"
    using collatz_true_run_endpoint_exact[OF y_divisible] .
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted (replicate (2*r) True) ?y"
    using true_run by blast
  have tail_endpoint:
    "collatz_guarded_normalized_word_endpoint (replicate (2*r) True) ?y + 1 =
      3^(2*r) * h"
    using true_run y_plus
    by simp
  have admitted:
    "collatz_guarded_normalized_word_admitted
      (False # replicate (2*r) True) x"
    using even_x prefix tail_admitted
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
  have endpoint:
    "collatz_guarded_normalized_word_endpoint
      (False # replicate (2*r) True) x + 1 = 3^(2*r)*h"
    using prefix tail_endpoint
    by (simp add: collatz_guarded_normalized_word_endpoint.simps)
  have word: "collatz_0563_word r = False # replicate (2*r) True"
    by (simp add: collatz_0563_word_def)
  have quotient: "(x+2) div 2^(2*r+1) = h"
    using h by (simp add: power_Suc)
  show "collatz_guarded_normalized_word_admitted
      (collatz_0563_word r) x"
    using admitted word by simp
  show "collatz_guarded_normalized_word_endpoint
      (collatz_0563_word r) x + 1 =
        3^(2*r) * ((x+2) div 2^(2*r+1))"
    using endpoint quotient word by simp
  show "length (collatz_0563_word r) = 2*r+1"
    by (simp add: collatz_0563_word_def)
  show "count_list (collatz_0563_word r) True = 2*r"
    by (simp add: collatz_0563_word_def collatz_count_list_replicate_true)
  show "length (collatz_0563_word r) +
      count_list (collatz_0563_word r) True = 4*r+1"
    by (simp add: collatz_0563_word_def collatz_count_list_replicate_true)
qed

theorem collatz_0563_physical_rotation:
  assumes source: "x = 40*k+30"
  shows "physical_collatz x = 20*k+15"
    and "physical_collatz (20*k+15) = 60*k+46"
    and "physical_collatz (60*k+46) = 30*k+23"
    and "physical_collatz (30*k+23) = 90*k+70"
    and "(physical_collatz ^^ 4) x = 90*k+70"
    and "(physical_collatz ^^ 4) x + 2 = 9*((x+2) div 4)"
proof -
  have t0: "physical_collatz x = 20*k+15"
    using source by (simp add: physical_collatz_def)
  have t1: "physical_collatz (20*k+15) = 60*k+46"
    by (simp add: physical_collatz_def)
  have t2: "physical_collatz (60*k+46) = 30*k+23"
    by (simp add: physical_collatz_def)
  have t3: "physical_collatz (30*k+23) = 90*k+70"
    by (simp add: physical_collatz_def)
  have four: "4 = Suc (Suc (Suc (Suc 0)))" by simp
  have iter: "(physical_collatz ^^ 4) x =
      physical_collatz (physical_collatz
        (physical_collatz (physical_collatz x)))"
    by (simp only: four funpow.simps comp_apply id_apply)
  have endpoint: "(physical_collatz ^^ 4) x = 90*k+70"
    using iter t0 t1 t2 t3 by simp
  have quotient: "(x+2) div 4 = 10*k+8"
  proof -
    have "x+2=4*(10*k+8)" using source by algebra
    then show ?thesis by simp
  qed
  show "physical_collatz x = 20*k+15" using t0 .
  show "physical_collatz (20*k+15) = 60*k+46" using t1 .
  show "physical_collatz (60*k+46) = 30*k+23" using t2 .
  show "physical_collatz (30*k+23) = 90*k+70" using t3 .
  show "(physical_collatz ^^ 4) x = 90*k+70"
    using endpoint .
  show "(physical_collatz ^^ 4) x + 2 = 9*((x+2) div 4)"
    using endpoint quotient by simp
qed

definition collatz_26847_step :: "nat \<Rightarrow> nat" where
  "collatz_26847_step y = (3*y+1) div 16"

fun collatz_26847_iterate :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_26847_iterate 0 y = y"
| "collatz_26847_iterate (Suc n) y =
    collatz_26847_iterate n (collatz_26847_step y)"

fun collatz_26847_tail :: "nat \<Rightarrow> bool list" where
  "collatz_26847_tail 0 = [True]"
| "collatz_26847_tail (Suc n) =
    [True,False,False,False] @ collatz_26847_tail n"

lemma collatz_26847_block:
  assumes odd_y: "odd y" and divisible: "16 dvd 3*y+1"
  shows "collatz_guarded_normalized_word_admitted [True,False,False,False] y"
    and "collatz_guarded_normalized_word_endpoint
      [True,False,False,False] y = collatz_26847_step y"
proof -
  obtain z where numerator: "3*y+1=16*z"
    using divisible unfolding dvd_def by blast
  have first:
    "collatz_guarded_normalized_source_step True y = 8*z"
    using collatz_guarded_true_step_exact[OF odd_y] numerator
    by (simp add: collatz_guarded_normalized_source_step_def
        physical_collatz_def)
  have zero_run:
    "collatz_guarded_normalized_word_admitted (replicate 3 False) (8*z) \<and>
      collatz_guarded_normalized_word_endpoint (replicate 3 False) (8*z)=z"
    using collatz_guarded_false_run_exact[of 3 "8*z"] by simp
  have zero_admitted:
    "collatz_guarded_normalized_word_admitted (replicate 3 False) (8*z)"
    using zero_run by blast
  have zero_endpoint:
    "collatz_guarded_normalized_word_endpoint (replicate 3 False) (8*z)=z"
    using zero_run by blast
  have false_word: "[False,False,False] = replicate 3 False" by code_simp
  show "collatz_guarded_normalized_word_admitted [True,False,False,False] y"
  proof -
    have tail_admitted:
      "collatz_guarded_normalized_word_admitted [False,False,False] (8*z)"
      using zero_admitted by (simp only: false_word)
    show ?thesis
      using odd_y first tail_admitted
      by (simp add: collatz_guarded_normalized_word_admitted.simps
          collatz_guarded_normalized_source_step_def)
  qed
  have tail_endpoint:
    "collatz_guarded_normalized_word_endpoint [False,False,False] (8*z)=z"
    using zero_endpoint by (simp only: false_word)
  show "collatz_guarded_normalized_word_endpoint
      [True,False,False,False] y = collatz_26847_step y"
    using first tail_endpoint numerator
    by (simp add: collatz_guarded_normalized_word_endpoint.simps
        collatz_26847_step_def)
qed

lemma collatz_26847_step_guard:
  assumes odd_y: "odd y"
    and divisible: "2^(4*n+5) dvd 13*y-1"
  shows "odd (collatz_26847_step y)"
    and "16 dvd 3*y+1"
    and "2^(4*n+1) dvd 13*collatz_26847_step y-1"
proof -
  obtain k where h: "13*y-1=2^(4*n+5)*k"
    using divisible unfolding dvd_def by blast
  have power: "(2::nat)^(4*n+5) = 32 * (2::nat)^(4*n)"
    by (simp add: power_add mult.commute)
  have h32: "13*y-1 = 32*(2^(4*n)*k)"
    using h power by (simp add: algebra_simps)
  have y_positive: "0 < y"
    using odd_y by (cases y) auto
  have y_lower: "1 \<le> 13*y" using y_positive by arith
  have restore: "(13*y-1)+1=13*y" using y_lower by simp
  have y_equation: "13*y=32*(2^(4*n)*k)+1"
    using h32 restore by linarith
  let ?t = "2^(4*n)*k"
  have times_five: "65*y=32*(5*?t)+5"
    using y_equation by (simp add: algebra_simps)
  have multiple_mod: "(32*(5*?t)) mod 32=0"
    by (simp add: mult.commute)
  have add_mod:
    "(32*(5*?t)+5) mod 32 =
      ((32*(5*?t)) mod 32+5 mod 32) mod 32"
    by (rule mod_add_eq[symmetric])
  have residue_five: "(65*y) mod 32=5"
    using times_five multiple_mod add_mod by simp
  have product_mod:
    "(65*y) mod 32 = ((65 mod 32)*(y mod 32)) mod 32"
    by (rule mod_mult_eq[symmetric])
  have sixty_five_mod: "(65::nat) mod 32=1" by simp
  have y_residue: "y mod 32=5"
    using residue_five product_mod sixty_five_mod by simp
  have y_decomposition: "y=32*(y div 32)+y mod 32"
    using div_mult_mod_eq[of y 32] by (simp add: mult.commute)
  have y_form: "y=32*(y div 32)+5"
    using y_decomposition y_residue by simp
  let ?z = "6*(y div 32)+1"
  have numerator: "3*y+1=16*?z"
    using y_form by (simp add: algebra_simps)
  have odd_z: "odd ?z" by simp
  have step: "collatz_26847_step y = ?z"
    using numerator by (simp add: collatz_26847_step_def)
  have cocycle:
    "16*(13*?z-1) = 3*(13*y-1)"
    using numerator by (simp add: algebra_simps)
  have new_value:
    "13*?z-1 = 2^(4*n+1)*(3*k)"
  proof -
    have "16*(13*?z-1) = 16*(2^(4*n+1)*(3*k))"
      using cocycle h power by (simp add: algebra_simps power_add)
    then show ?thesis by simp
  qed
  show "odd (collatz_26847_step y)" using step odd_z by simp
  show "16 dvd 3*y+1"
    using numerator by (auto intro: dvdI)
  have transported:
    "13*collatz_26847_step y-1 = 2^(4*n+1)*(3*k)"
    using step new_value by simp
  show "2^(4*n+1) dvd 13*collatz_26847_step y-1"
    using transported unfolding dvd_def by blast
qed

lemma collatz_26847_tail_length:
  "length (collatz_26847_tail n) = 4*n+1"
  by (induction n) simp_all

lemma collatz_26847_tail_true_count:
  "count_list (collatz_26847_tail n) True = n+1"
  by (induction n) simp_all

theorem collatz_26847_tail_guarded_action:
  assumes odd_y: "odd y"
    and divisor: "2^(4*n+1) dvd 13*y-1"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_26847_tail n) y"
    and "collatz_guarded_normalized_word_endpoint
      (collatz_26847_tail n) y =
        (3*collatz_26847_iterate n y+1) div 2"
proof -
  show admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_tail n) y"
    using odd_y divisor
  proof (induction n arbitrary: y)
    case 0
    then show ?case by (simp add: collatz_guarded_normalized_word_admitted.simps)
  next
    case (Suc n)
    have strong_divisor: "2^(4*n+5) dvd 13*y-1"
      using Suc.prems(2) by (simp add: algebra_simps)
    have step_guard:
      "odd (collatz_26847_step y) \<and>
        16 dvd 3*y+1 \<and>
        2^(4*n+1) dvd 13*collatz_26847_step y-1"
      using collatz_26847_step_guard[OF Suc.prems(1) strong_divisor]
      by blast
    have block:
      "collatz_guarded_normalized_word_admitted
        [True,False,False,False] y"
      using step_guard Suc.prems(1)
      by (blast intro: collatz_26847_block(1))
    have block_endpoint:
      "collatz_guarded_normalized_word_endpoint
        [True,False,False,False] y = collatz_26847_step y"
      using step_guard Suc.prems(1)
      by (blast intro: collatz_26847_block(2))
    have tail:
      "collatz_guarded_normalized_word_admitted
        (collatz_26847_tail n) (collatz_26847_step y)"
      using Suc.IH step_guard by blast
    show ?case
      using collatz_guarded_normalized_word_admitted_append[of
        "[True,False,False,False]" "collatz_26847_tail n" y]
        block tail block_endpoint
      by (simp add: collatz_26847_tail.simps)
  qed
  show endpoint:
    "collatz_guarded_normalized_word_endpoint
      (collatz_26847_tail n) y =
        (3*collatz_26847_iterate n y+1) div 2"
    using odd_y divisor
  proof (induction n arbitrary: y)
    case 0
    have one_step:
      "collatz_guarded_normalized_word_endpoint [True] y =
        (3*y+1) div 2"
    proof -
      have endpoint_step:
        "collatz_guarded_normalized_word_endpoint [True] y =
          collatz_guarded_normalized_source_step True y"
        by (simp add: collatz_guarded_normalized_word_endpoint.simps)
      have true_step:
        "collatz_guarded_normalized_source_step True y = (3*y+1) div 2"
        using collatz_guarded_true_step_exact[OF "0.prems"(1)] .
      show ?thesis using endpoint_step true_step by simp
    qed
    then show ?case by simp
  next
    case (Suc n)
    have strong_divisor: "2^(4*n+5) dvd 13*y-1"
      using Suc.prems(2) by (simp add: algebra_simps)
    have step_guard:
      "odd (collatz_26847_step y) \<and>
        16 dvd 3*y+1 \<and>
        2^(4*n+1) dvd 13*collatz_26847_step y-1"
      using collatz_26847_step_guard[OF Suc.prems(1) strong_divisor]
      by blast
    have block:
      "collatz_guarded_normalized_word_endpoint
        [True,False,False,False] y = collatz_26847_step y"
      using step_guard Suc.prems(1)
      by (blast intro: collatz_26847_block(2))
    have tail:
      "collatz_guarded_normalized_word_endpoint
        (collatz_26847_tail n) (collatz_26847_step y) =
        (3*collatz_26847_iterate n (collatz_26847_step y)+1) div 2"
      using Suc.IH step_guard by blast
    have joined:
      "collatz_guarded_normalized_word_endpoint
        ([True,False,False,False] @ collatz_26847_tail n) y =
        collatz_guarded_normalized_word_endpoint
          (collatz_26847_tail n) (collatz_26847_step y)"
      using block by (simp add: collatz_guarded_normalized_word_endpoint_append)
    show ?case
      using joined tail
      by (simp add: collatz_26847_tail.simps collatz_26847_iterate.simps)
  qed
qed

definition collatz_26847_word :: "nat \<Rightarrow> bool list" where
  "collatz_26847_word r = replicate 4 False @ collatz_26847_tail (r-1)"

theorem collatz_26847_guarded_action:
  assumes source: "x=160*k+112"
    and positive: "0 < r"
    and divisor: "2^(4*r+1) dvd 13*x-16"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_26847_word r) x"
    and "collatz_guarded_normalized_word_endpoint
      (collatz_26847_word r) x =
        (3*collatz_26847_iterate (r-1) (10*k+7)+1) div 2"
    and "length (collatz_26847_word r) = 4*r+1"
    and "count_list (collatz_26847_word r) True = r"
    and "length (collatz_26847_word r) +
        count_list (collatz_26847_word r) True = 5*r+1"
proof -
  obtain n where r: "r=Suc n" using positive by (cases r) auto
  let ?y = "10*k+7"
  have x16: "x=16*?y" using source by (simp add: algebra_simps)
  have odd_y: "odd ?y" by simp
  have h_factor: "13*x-16=16*(13*?y-1)"
    using x16 by (simp add: algebra_simps)
  obtain a where h: "13*x-16=2^(4*r+1)*a"
    using divisor unfolding dvd_def by blast
  have exponent: "(2::nat)^(4*r+1)=16*(2::nat)^(4*n+1)"
    using r by (simp add: power_add algebra_simps)
  have cancel:
    "16*(13*?y-1)=16*(2^(4*n+1)*a)"
    using h h_factor exponent by (simp add: algebra_simps)
  have factor: "13*?y-1=2^(4*n+1)*a"
    using cancel by simp
  have y_divisor: "2^(4*n+1) dvd 13*?y-1"
    using factor unfolding dvd_def by blast
  have prefix_divisible: "2^4 dvd x"
  proof -
    have "x=2^4*?y" using x16 by simp
    then show ?thesis unfolding dvd_def by blast
  qed
  have prefix:
    "collatz_guarded_normalized_word_admitted (replicate 4 False) x \<and>
      collatz_guarded_normalized_word_endpoint (replicate 4 False) x = ?y"
    using collatz_guarded_false_run_exact[OF prefix_divisible] x16 by simp
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_tail n) ?y"
    by (rule collatz_26847_tail_guarded_action(1)[OF odd_y y_divisor])
  have tail_endpoint:
    "collatz_guarded_normalized_word_endpoint
      (collatz_26847_tail n) ?y =
        (3*collatz_26847_iterate n ?y+1) div 2"
    by (rule collatz_26847_tail_guarded_action(2)[OF odd_y y_divisor])
  have expanded:
    "collatz_26847_word r = replicate 4 False @ collatz_26847_tail n"
    using r by (simp add: collatz_26847_word_def)
  show admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_word r) x"
    using prefix tail_admitted expanded
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show endpoint:
    "collatz_guarded_normalized_word_endpoint
      (collatz_26847_word r) x =
        (3*collatz_26847_iterate (r-1) ?y+1) div 2"
  proof -
    have appended:
      "collatz_guarded_normalized_word_endpoint
          (replicate 4 False @ collatz_26847_tail n) x =
        collatz_guarded_normalized_word_endpoint (collatz_26847_tail n)
          (collatz_guarded_normalized_word_endpoint (replicate 4 False) x)"
      by (rule collatz_guarded_normalized_word_endpoint_append)
    show ?thesis
      using prefix tail_endpoint expanded appended r by simp
  qed
  show "length (collatz_26847_word r) = 4*r+1"
    using collatz_26847_tail_length[of n] r
    by (simp add: collatz_26847_word_def)
  show "count_list (collatz_26847_word r) True = r"
    using collatz_26847_tail_true_count[of n] r
    by (simp add: collatz_26847_word_def)
  show "length (collatz_26847_word r) +
      count_list (collatz_26847_word r) True = 5*r+1"
    using collatz_26847_tail_length[of n]
      collatz_26847_tail_true_count[of n] r
    by (simp add: collatz_26847_word_def)
qed

definition collatz_26847_phase_word :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "collatz_26847_phase_word p r =
    replicate (4-p) False @ collatz_26847_tail (r-1)"

theorem collatz_26847_phase_guarded_action:
  assumes phase: "p \<le> 4"
    and source: "2^p*x=160*k+112"
    and positive: "0<r"
    and divisor: "2^(4*r+1) dvd 13*(2^p*x)-16"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_26847_phase_word p r) x"
    and "collatz_guarded_normalized_word_endpoint
      (collatz_26847_phase_word p r) x =
        (3*collatz_26847_iterate (r-1) (10*k+7)+1) div 2"
    and "length (collatz_26847_phase_word p r)=4*r+1-p"
    and "count_list (collatz_26847_phase_word p r) True=r"
    and "length (collatz_26847_phase_word p r) +
        count_list (collatz_26847_phase_word p r) True=5*r+1-p"
    and "(physical_collatz ^^ (5*r+1-p)) x =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
proof -
  have p_sum: "p+(4-p)=4" using phase by arith
  have replicated:
    "replicate 4 False = replicate p False @ replicate (4-p) False"
    using replicate_add[of p "4-p" False] p_sum by simp
  have base_split:
    "collatz_26847_word r =
      replicate p False @ collatz_26847_phase_word p r"
    unfolding collatz_26847_word_def collatz_26847_phase_word_def
    using replicated by simp
  have prefix_divisor: "2^p dvd 2^p*x"
    unfolding dvd_def by (rule exI[of _ x]) simp
  have prefix:
    "collatz_guarded_normalized_word_admitted (replicate p False) (2^p*x)
      \<and> collatz_guarded_normalized_word_endpoint
        (replicate p False) (2^p*x)=x"
    using collatz_guarded_false_run_exact[OF prefix_divisor] by simp
  have base_admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_word r) (2^p*x)"
    by (rule collatz_26847_guarded_action(1)[OF source positive divisor])
  have split_admitted:
    "collatz_guarded_normalized_word_admitted
        (replicate p False @ collatz_26847_phase_word p r) (2^p*x)"
    using base_admitted base_split by simp
  have phase_admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_phase_word p r) x"
    using collatz_guarded_normalized_word_admitted_append[of
        "replicate p False" "collatz_26847_phase_word p r" "2^p*x"]
      split_admitted prefix by simp
  have base_endpoint:
    "collatz_guarded_normalized_word_endpoint
      (collatz_26847_word r) (2^p*x) =
        (3*collatz_26847_iterate (r-1) (10*k+7)+1) div 2"
    by (rule collatz_26847_guarded_action(2)[OF source positive divisor])
  have split_endpoint:
    "collatz_guarded_normalized_word_endpoint
        (collatz_26847_word r) (2^p*x) =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
    using base_split prefix
    by (simp add: collatz_guarded_normalized_word_endpoint_append)
  have phase_endpoint:
    "collatz_guarded_normalized_word_endpoint
      (collatz_26847_phase_word p r) x =
        (3*collatz_26847_iterate (r-1) (10*k+7)+1) div 2"
    using split_endpoint base_endpoint by simp
  have pred: "r-1+1=r" using positive by simp
  have tail_length:
    "length (collatz_26847_tail (r-1))=4*(r-1)+1"
    by (rule collatz_26847_tail_length)
  have phase_length:
    "length (collatz_26847_phase_word p r)=4*r+1-p"
    unfolding collatz_26847_phase_word_def
    using tail_length pred phase
    by (simp only: length_append length_replicate; arith)
  have tail_count:
    "count_list (collatz_26847_tail (r-1)) True=(r-1)+1"
    by (rule collatz_26847_tail_true_count)
  have phase_count:
    "count_list (collatz_26847_phase_word p r) True=r"
    using tail_count pred by (simp add: collatz_26847_phase_word_def)
  have p_bound: "p \<le> 4*r+1"
    using phase positive by linarith
  have phase_duration:
    "length (collatz_26847_phase_word p r) +
      count_list (collatz_26847_phase_word p r) True=5*r+1-p"
  proof -
    have first:
      "length (collatz_26847_phase_word p r) +
          count_list (collatz_26847_phase_word p r) True =
        (4*r+1-p)+r"
      using phase_length phase_count by simp
    have second: "(4*r+1-p)+r=(4*r+1+r)-p"
      by (rule add_diff_assoc2[OF p_bound])
    have third: "(4*r+1+r)-p=5*r+1-p"
      by (simp add: algebra_simps)
    show ?thesis using first second third
      by (simp only: first second third)
  qed
  have phase_physical:
    "(physical_collatz ^^ (5*r+1-p)) x =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
  proof -
    have endpoint_physical:
      "collatz_guarded_normalized_word_endpoint
          (collatz_26847_phase_word p r) x =
        (physical_collatz ^^
          (length (collatz_26847_phase_word p r) +
            count_list (collatz_26847_phase_word p r) True)) x"
      using collatz_guarded_normalized_word_refines_physical[
          OF phase_admitted] by (rule conjunct2)
    show ?thesis using endpoint_physical phase_duration by simp
  qed
  show "collatz_guarded_normalized_word_admitted
      (collatz_26847_phase_word p r) x" using phase_admitted .
  show "collatz_guarded_normalized_word_endpoint
      (collatz_26847_phase_word p r) x =
        (3*collatz_26847_iterate (r-1) (10*k+7)+1) div 2"
    using phase_endpoint .
  show "length (collatz_26847_phase_word p r)=4*r+1-p"
    using phase_length .
  show "count_list (collatz_26847_phase_word p r) True=r"
    using phase_count .
  show "length (collatz_26847_phase_word p r) +
      count_list (collatz_26847_phase_word p r) True=5*r+1-p"
    using phase_duration .
  show "(physical_collatz ^^ (5*r+1-p)) x =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
    using phase_physical .
qed

lemma collatz_26847_phase_selector_guard_lifts:
  fixes x p r :: nat
  assumes phase: "p \<le> 4"
    and positive: "0<r"
    and divisor: "2^(4*r+1-p) dvd 13*x-2^(4-p)"
  shows "2^(4*r+1) dvd 13*(2^p*x)-16"
proof -
  obtain w where source_equation:
    "13*x-2^(4-p)=2^(4*r+1-p)*w"
    using divisor unfolding dvd_def by blast
  have phase_exponents:
    "p+(4-p)=4" "p+(4*r+1-p)=4*r+1"
    using phase positive by arith+
  have factor: "(2::nat)^p*(2::nat)^(4-p)=16"
    using phase_exponents(1)
    by (simp only: power_add[symmetric] phase_exponents(1); simp)
  have product: "13*(2^p*x)=2^p*(13*x)"
    by (simp add: algebra_simps)
  have factored:
    "13*(2^p*x)-16=2^p*(13*x)-2^p*2^(4-p)"
    using product factor by simp
  have distribute:
    "2^p*(13*x)-2^p*2^(4-p)=2^p*(13*x-2^(4-p))"
    by (rule diff_mult_distrib2[symmetric])
  have scaled_subtraction:
    "13*(2^p*x)-16=2^p*(13*x-2^(4-p))"
    using factored distribute by simp
  have powers:
    "(2::nat)^p*(2::nat)^(4*r+1-p)=2^(4*r+1)"
    using phase_exponents(2)
    by (simp only: power_add[symmetric] phase_exponents(2))
  have powered_witness:
    "2^p*(13*x-2^(4-p))=2^(4*r+1)*w"
    by (simp only: source_equation mult.assoc[symmetric] powers)
  have result: "13*(2^p*x)-16=2^(4*r+1)*w"
    using scaled_subtraction powered_witness by simp
  show ?thesis unfolding dvd_def using result by blast
qed

corollary collatz_26847_phase_selector_refines:
  assumes phase: "p \<le> 4"
    and source: "2^p*x=160*k+112"
    and positive: "0<r"
    and divisor: "2^(4*r+1-p) dvd 13*x-2^(4-p)"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_26847_phase_word p r) x \<and>
    (physical_collatz ^^ (5*r+1-p)) x =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
proof -
  have lifted: "2^(4*r+1) dvd 13*(2^p*x)-16"
    by (rule collatz_26847_phase_selector_guard_lifts[OF phase positive divisor])
  have admitted:
    "collatz_guarded_normalized_word_admitted
      (collatz_26847_phase_word p r) x"
    by (rule collatz_26847_phase_guarded_action(1)[OF phase source positive lifted])
  have physical:
    "(physical_collatz ^^ (5*r+1-p)) x =
      collatz_guarded_normalized_word_endpoint
        (collatz_26847_phase_word p r) x"
    by (rule collatz_26847_phase_guarded_action(6)[OF phase source positive lifted])
  show ?thesis using admitted physical by blast
qed

lemma collatz_26847_physical_rotation:
  assumes source: "x=160*k+112"
  shows "physical_collatz x=80*k+56"
    and "physical_collatz (80*k+56)=40*k+28"
    and "physical_collatz (40*k+28)=20*k+14"
    and "physical_collatz (20*k+14)=10*k+7"
    and "physical_collatz (10*k+7)=30*k+22"
    and "(physical_collatz ^^ 5) x=30*k+22"
    and "(physical_collatz ^^ 5) x=(3*x+16) div 16"
proof -
  have t0: "physical_collatz x=80*k+56"
    using source by (simp add: physical_collatz_def)
  have t1: "physical_collatz (80*k+56)=40*k+28"
    by (simp add: physical_collatz_def)
  have t2: "physical_collatz (40*k+28)=20*k+14"
    by (simp add: physical_collatz_def)
  have t3: "physical_collatz (20*k+14)=10*k+7"
    by (simp add: physical_collatz_def)
  have t4: "physical_collatz (10*k+7)=30*k+22"
    by (simp add: physical_collatz_def)
  have five: "5 = Suc (Suc (Suc (Suc (Suc 0))))" by simp
  have iter: "(physical_collatz ^^ 5) x =
      physical_collatz (physical_collatz (physical_collatz
        (physical_collatz (physical_collatz x))))"
    by (simp only: five funpow.simps comp_apply id_apply)
  have endpoint: "(physical_collatz ^^ 5) x=30*k+22"
    using iter t0 t1 t2 t3 t4 by simp
  have affine: "3*x+16=16*(30*k+22)"
    using source by (simp add: algebra_simps)
  show "physical_collatz x=80*k+56" using t0 .
  show "physical_collatz (80*k+56)=40*k+28" using t1 .
  show "physical_collatz (40*k+28)=20*k+14" using t2 .
  show "physical_collatz (20*k+14)=10*k+7" using t3 .
  show "physical_collatz (10*k+7)=30*k+22" using t4 .
  show "(physical_collatz ^^ 5) x=30*k+22"
    using endpoint .
  show "(physical_collatz ^^ 5) x=(3*x+16) div 16"
    using endpoint affine by simp
qed

corollary collatz_0563_guarded_physical_refinement:
  assumes source: "x=40*k+30"
    and positive: "0<r"
    and divisor: "2^(2*r+1) dvd x+2"
  shows "(physical_collatz ^^ (4*r+1)) x =
      collatz_guarded_normalized_word_endpoint (collatz_0563_word r) x"
  using collatz_guarded_normalized_word_refines_physical[
      OF collatz_0563_guarded_action(1)[OF source positive divisor]]
    collatz_0563_guarded_action(3)[OF source positive divisor]
    collatz_0563_guarded_action(4)[OF source positive divisor]
  by (simp add: collatz_0563_word_def)

corollary collatz_26847_guarded_physical_refinement:
  assumes source: "x=160*k+112"
    and positive: "0<r"
    and divisor: "2^(4*r+1) dvd 13*x-16"
  shows "(physical_collatz ^^ (5*r+1)) x =
      collatz_guarded_normalized_word_endpoint (collatz_26847_word r) x"
proof -
  have refinement: "(physical_collatz ^^
        (length (collatz_26847_word r) +
          count_list (collatz_26847_word r) True)) x =
      collatz_guarded_normalized_word_endpoint (collatz_26847_word r) x"
  proof -
    have endpoint:
      "collatz_guarded_normalized_word_endpoint (collatz_26847_word r) x =
        (physical_collatz ^^
          (length (collatz_26847_word r) +
            count_list (collatz_26847_word r) True)) x"
      using collatz_guarded_normalized_word_refines_physical[
          OF collatz_26847_guarded_action(1)[OF source positive divisor]]
      by (rule conjunct2)
    show ?thesis using endpoint by (rule sym)
  qed
  have duration:
    "length (collatz_26847_word r) +
      count_list (collatz_26847_word r) True = 5*r+1"
    using collatz_26847_guarded_action(5)[OF source positive divisor] .
  show ?thesis using refinement duration by simp
qed

ML \<open>
  val checked = @{thms collatz_physical_decimal_output_exact
    collatz_physical_digit_edges_exact
    collatz_physical_digit_edge_selected_by_mod20
    collatz_physical_elementary_digit_cycles_exact
    collatz_true_run_endpoint_exact collatz_0563_guarded_action
    collatz_0563_physical_rotation collatz_26847_block
    collatz_26847_step_guard collatz_26847_tail_guarded_action
    collatz_26847_guarded_action collatz_26847_physical_rotation
    collatz_0563_guarded_physical_refinement
    collatz_26847_guarded_physical_refinement};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz edge-cycle refinement depends on an oracle";
\<close>

end
