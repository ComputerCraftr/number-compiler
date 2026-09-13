theory Runtime_Cylinder_Refinement
  imports Twisted_Support_Observers "HOL-Computational_Algebra.Polynomial"
begin

definition folded_difference ::
  "nat \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "folded_difference width sign d sheet k =
    (\<Sum>i<width. if i mod sheet = k
      then sign^(i div sheet) * (d i - d (width - Suc i)) else 0)"

lemma folded_mirror_vector_nonzero_implies_mismatch:
  assumes "\<exists>k<sheet. folded_difference width sign d sheet k \<noteq> 0"
  shows "\<exists>i<width. d i \<noteq> d (width - Suc i)"
proof (rule ccontr)
  assume zero: "\<not> (\<exists>i<width. d i \<noteq> d (width - Suc i))"
  have difference: "d i-d (width-Suc i)=0" if "i<width" for i
  proof -
    have "d i=d (width-Suc i)" using zero that by blast
    then show ?thesis by linarith
  qed
  have "folded_difference width sign d sheet k = 0" for k
    unfolding folded_difference_def
    by (rule sum.neutral) (simp add: difference)
  with assms show False by blast
qed

lemma folded_difference_no_wrap:
  assumes "width \<le> sheet"
  shows "folded_difference width sign d sheet k =
    (if k<width then d k-d (width-Suc k) else 0)"
proof -
  have each: "(if i mod sheet=k then sign^(i div sheet)*(d i-d (width-Suc i)) else 0) =
    (if i=k then d k-d (width-Suc k) else 0)" if "i<width" for i
    using that assms by auto
  have "folded_difference width sign d sheet k =
      (\<Sum>i<width. if i=k then d k-d (width-Suc k) else 0)"
    unfolding folded_difference_def by (rule sum.cong) (auto simp: each)
  also have "... = (if k<width then d k-d (width-Suc k) else 0)" by simp
  finally show ?thesis .
qed

theorem terminal_mirror_vector_zero_iff_palindrome:
  assumes "width \<le> sheet"
  shows "(\<forall>k<sheet. folded_difference width sign d sheet k=0) =
    (\<forall>i<width. d i=d (width-Suc i))"
  using assms by (auto simp: folded_difference_no_wrap[OF assms])

lemma doubling_reaches_target:
  assumes "0<first"
  shows "width \<le> first * 2^width"
proof -
  have growth: "n < (2::nat)^n" for n
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have step: "(2::nat)^(Suc n)=2*2^n" by (rule power_Suc)
    have positive: "0<(2::nat)^n" by simp
    show ?case using Suc.IH positive unfolding step by arith
  qed
  have bound: "2^width \<le> first * 2^width"
    using mult_right_mono[of 1 first "(2::nat)^width"] assms by simp
  show ?thesis using growth[of width] bound by arith
qed

datatype event_word = Empty | Event nat | Join event_word event_word

fun event_list :: "event_word \<Rightarrow> nat list" where
  "event_list Empty=[]"
| "event_list (Event k)=[k]"
| "event_list (Join A B)=event_list A @ event_list B"

fun event_clock :: "event_word \<Rightarrow> nat \<times> nat" where
  "event_clock Empty=(0,0)"
| "event_clock (Event k)=(1,k)"
| "event_clock (Join A B)=(fst (event_clock A)+fst (event_clock B),
    snd (event_clock A)+snd (event_clock B))"

theorem event_clock_refines_list:
  "event_clock A = (length (event_list A), sum_list (event_list A))"
  by (induction A) simp_all

theorem reassociation_preserves_every_clock_observer:
  "clock_transfer s z (event_list (Join (Join A B) C)) =
    clock_transfer s z (event_list (Join A (Join B C)))"
  by simp

theorem runtime_s_arithmetic_exponents:
  "-int (snd (event_clock A)) + int (sum_list (event_list A)) = 0"
  "int (fst (event_clock A)) - int (length (event_list A)) = 0"
  "fst (event_clock A) + snd (event_clock A) =
    length (event_list A) + sum_list (event_list A)"
  by (simp_all add: event_clock_refines_list)

text \<open>Executable counterexamples keep the root premise separate from the
actual coefficient probe. A zero root and a nonzero pair do not imply a split.\<close>

lemma zero_root_does_not_decide_M11:
  "2047 dvd (0::nat)*(0+2)" "\<not> prime (2047::nat)"
proof -
  show "2047 dvd (0::nat)*(0+2)" by simp
  have factor: "gcd (2047::nat) 23=23" by (simp add: gcd_nat.simps)
  have low: "1 < gcd (2047::nat) 23" by (simp only: factor; simp)
  have high: "gcd (2047::nat) 23 < 2047" by (simp only: factor; simp)
  show "\<not> prime (2047::nat)"
    by (rule coefficient_gcd_prints_exact_factor(3)[OF low high])
qed

lemma M11_frobenius_coordinates_are_not_roots:
  "\<not> (2047 dvd (391::nat)*(391+2))"
  "\<not> (2047 dvd (1474::nat)*(1474+2))"
  by (simp add: dvd_eq_mod_eq_0 gcd_nat.simps)+

lemma F5_nonzero_coefficients_need_not_split:
  "(163161656::nat) \<noteq> 0"
  "gcd (4294967297::nat) 163161656 = 1"
  "gcd (4294967297::nat) 1685016954 = 1"
  by (simp add: dvd_eq_mod_eq_0 gcd_nat.simps)+

fun tropical_min :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "tropical_min None y = y"
| "tropical_min (Some x) None = Some x"
| "tropical_min (Some x) (Some y) = Some (min x y)"

fun tropical_plus :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "tropical_plus None y = None"
| "tropical_plus (Some x) None = None"
| "tropical_plus (Some x) (Some y) = Some (x+y)"

lemma tropical_min_associative:
  "tropical_min (tropical_min x y) z = tropical_min x (tropical_min y z)"
  by (cases x; cases y; cases z) (simp_all add: min.assoc)

lemma tropical_shift_min:
  "tropical_plus (Some a) (tropical_min x y) =
    tropical_min (tropical_plus (Some a) x) (tropical_plus (Some a) y)"
  by (cases x; cases y) (auto simp: min_def)

fun support_min :: "int list \<Rightarrow> int option" where
  "support_min [] = None"
| "support_min (x#xs) = tropical_min (Some x) (support_min xs)"

lemma support_min_append:
  "support_min (xs@ys) = tropical_min (support_min xs) (support_min ys)"
  by (induction xs) (simp_all add: tropical_min_associative)

lemma support_min_shift:
  "support_min (map ((+) a) xs) = tropical_plus (Some a) (support_min xs)"
  by (induction xs) (simp_all add: tropical_shift_min)

lemma tropical_min_present [simp]:
  "tropical_min (Some x) y \<noteq> None"
  by (cases y) simp_all

lemma support_min_empty [simp]: "support_min xs=None \<longleftrightarrow> xs=[]"
  by (cases xs) simp_all

lemma support_min_exact:
  "support_min xs = Some q \<Longrightarrow> q \<in> set xs \<and> (\<forall>r\<in>set xs. q\<le>r)"
proof (induction xs arbitrary: q)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases "support_min xs") (auto simp: min_def split: if_splits)
qed

definition tropical_then :: "int option skew_transfer \<Rightarrow> int option skew_transfer \<Rightarrow> int option skew_transfer" where
  "tropical_then A B = \<lparr>
     upper=tropical_plus (upper B) (upper A),
     offset=tropical_min (tropical_plus (upper B) (offset A))
                        (tropical_plus (lower A) (offset B)),
     lower=tropical_plus (lower B) (lower A)\<rparr>"

fun tropical_clock :: "int \<Rightarrow> int \<Rightarrow> nat list \<Rightarrow> int option skew_transfer" where
  "tropical_clock a b [] = \<lparr>upper=Some 0,offset=None,lower=Some 0\<rparr>"
| "tropical_clock a b (k#ks) = tropical_then
    \<lparr>upper=Some a,offset=Some 0,lower=Some (b*int k)\<rparr> (tropical_clock a b ks)"

fun clock_weights :: "int \<Rightarrow> int \<Rightarrow> nat list \<Rightarrow> int list" where
  "clock_weights a b []=[]"
| "clock_weights a b (k#ks) = (a*int (length ks)) # map ((+) (b*int k)) (clock_weights a b ks)"

lemma tropical_clock_diagonals:
  "upper (tropical_clock a b ks) = Some (a*int (length ks))"
  "lower (tropical_clock a b ks) = Some (b*int (sum_list ks))"
  by (induction ks) (simp_all add: tropical_then_def algebra_simps)

theorem tropical_clock_support_refinement:
  "offset (tropical_clock a b ks) = support_min (clock_weights a b ks)"
  by (induction ks) (simp_all add: tropical_then_def tropical_clock_diagonals support_min_shift)

theorem tropical_clock_returns_minimum:
  assumes "offset (tropical_clock a b ks) = Some q"
  shows "q \<in> set (clock_weights a b ks)" "\<forall>r\<in>set (clock_weights a b ks). q\<le>r"
proof -
  have eq: "support_min (clock_weights a b ks)=Some q"
    using assms by (simp only: tropical_clock_support_refinement)
  from support_min_exact[OF eq]
  show "q \<in> set (clock_weights a b ks)" "\<forall>r\<in>set (clock_weights a b ks). q\<le>r"
    by auto
qed

lemma tropical_min_commute:
  "tropical_min x y = tropical_min y x"
  by (cases x; cases y) (simp_all add: min.commute)

lemma tropical_min_left_commute:
  "tropical_min x (tropical_min y z) = tropical_min y (tropical_min x z)"
  by (metis tropical_min_associative tropical_min_commute)

lemma tropical_plus_associative:
  "tropical_plus (tropical_plus x y) z = tropical_plus x (tropical_plus y z)"
  by (cases x; cases y; cases z) (simp_all add: add.assoc)

lemma tropical_plus_commute:
  "tropical_plus x y = tropical_plus y x"
  by (cases x; cases y) (simp_all add: add.commute)

lemma tropical_plus_left_commute:
  "tropical_plus x (tropical_plus y z) = tropical_plus y (tropical_plus x z)"
  by (metis tropical_plus_associative tropical_plus_commute)

lemma tropical_distribute:
  "tropical_plus x (tropical_min y z) = tropical_min (tropical_plus x y) (tropical_plus x z)"
  "tropical_plus (tropical_min x y) z = tropical_min (tropical_plus x z) (tropical_plus y z)"
  by (cases x; cases y; cases z; auto simp: min_def)+

lemma tropical_plus_absorb [simp]: "tropical_plus x None=None"
  by (cases x) simp_all

lemma tropical_plus_zero [simp]:
  "tropical_plus x (Some 0)=x" "tropical_plus (Some 0) x=x"
  by (cases x; simp)+

lemma tropical_then_associative:
  "tropical_then (tropical_then A B) C = tropical_then A (tropical_then B C)"
  by (cases A; cases B; cases C)
    (simp add: tropical_then_def tropical_distribute tropical_plus_associative
      tropical_plus_commute tropical_plus_left_commute tropical_min_associative
      tropical_min_commute tropical_min_left_commute)

lemma tropical_clock_append:
  "tropical_clock a b (xs@ys) = tropical_then (tropical_clock a b xs) (tropical_clock a b ys)"
proof (induction xs)
  case Nil then show ?case
    by (cases "tropical_clock a b ys") (simp add: tropical_then_def)
next
  case (Cons k ks) then show ?case by (simp add: tropical_then_associative)
qed

fun tropical_word :: "int \<Rightarrow> int \<Rightarrow> event_word \<Rightarrow> int option skew_transfer" where
  "tropical_word a b Empty = tropical_clock a b []"
| "tropical_word a b (Event k) = tropical_clock a b [k]"
| "tropical_word a b (Join A B) = tropical_then (tropical_word a b A) (tropical_word a b B)"

theorem tropical_event_dag_refines_support:
  "offset (tropical_word a b A) = support_min (clock_weights a b (event_list A))"
proof -
  have "tropical_word a b A = tropical_clock a b (event_list A)"
    by (induction A) (simp_all add: tropical_clock_append)
  then show ?thesis by (simp add: tropical_clock_support_refinement)
qed

definition mirror_sheet :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mirror_sheet first k = (if k=0 then first else first * 2^(k-1))"

definition mirror_sign :: "nat \<Rightarrow> int" where
  "mirror_sign k = (if k=0 then 1 else -1)"

lemma mirror_ladder_initial:
  "mirror_sheet first 0=first" "mirror_sign 0=1"
  "mirror_sheet first 1=first" "mirror_sign 1=-1"
  by (simp_all add: mirror_sheet_def mirror_sign_def)

lemma mirror_ladder_next:
  assumes "0<k"
  shows "mirror_sheet first (Suc k)=2*mirror_sheet first k" "mirror_sign (Suc k)=-1"
  using assms by (cases k; simp add: mirror_sheet_def mirror_sign_def power_Suc algebra_simps)+

definition mirror_stop :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "mirror_stop width d first k =
    ((\<exists>i<mirror_sheet first k. folded_difference width (mirror_sign k) d (mirror_sheet first k) i \<noteq> 0)
      \<or> width \<le> mirror_sheet first k)"

lemma mirror_ladder_terminal:
  assumes "0<first"
  shows "mirror_stop width d first (Suc width)"
  using doubling_reaches_target[OF assms, of width]
  by (simp add: mirror_stop_def mirror_sheet_def)

definition mirror_index :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat" where
  "mirror_index width d first = (LEAST k. mirror_stop width d first k)"

lemma mirror_index_stops:
  assumes "0<first"
  shows "mirror_stop width d first (mirror_index width d first)"
  unfolding mirror_index_def
  by (rule LeastI[where P="mirror_stop width d first" and k="Suc width"])
    (rule mirror_ladder_terminal[OF assms])

lemma mirror_index_bounded:
  assumes "0<first"
  shows "mirror_index width d first \<le> Suc width"
  unfolding mirror_index_def
  by (rule Least_le) (rule mirror_ladder_terminal[OF assms])

definition mirror_none :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> bool" where
  "mirror_none width d first =
    (\<forall>i<mirror_sheet first (mirror_index width d first).
      folded_difference width (mirror_sign (mirror_index width d first)) d
        (mirror_sheet first (mirror_index width d first)) i = 0)"

theorem mirror_ladder_none_iff_palindrome:
  assumes "0<first"
  shows "mirror_none width d first \<longleftrightarrow> (\<forall>i<width. d i=d (width-Suc i))"
proof
  assume zero: "mirror_none width d first"
  have bound: "width \<le> mirror_sheet first (mirror_index width d first)"
    using mirror_index_stops[OF assms, of width d] zero
    unfolding mirror_stop_def mirror_none_def by blast
  show "\<forall>i<width. d i=d (width-Suc i)"
    using terminal_mirror_vector_zero_iff_palindrome[OF bound] zero
    unfolding mirror_none_def by blast
next
  assume palindrome: "\<forall>i<width. d i=d (width-Suc i)"
  show "mirror_none width d first"
    unfolding mirror_none_def
    using folded_mirror_vector_nonzero_implies_mismatch palindrome by blast
qed

text \<open>The runtime pullback computes the displayed residue from a modular
inverse. This is an affine preimage theorem, not a valuation itinerary theorem.\<close>

lemma modular_inverse_affine_preimage:
  fixes M a inv x t :: int
  assumes inverse: "M dvd a*inv-1"
  shows "(M dvd x-inv*t) = (M dvd a*x-t)"
proof
  assume residue: "M dvd x-inv*t"
  have first: "M dvd a*(x-inv*t)"
    using residue by (rule dvd_mult)
  have second: "M dvd (a*inv-1)*t"
    using inverse by (rule dvd_mult2)
  have "M dvd a*(x-inv*t) + (a*inv-1)*t"
    using first second by (rule dvd_add)
  then show "M dvd a*x-t" by (simp add: algebra_simps)
next
  assume numerator: "M dvd a*x-t"
  have first: "M dvd inv*(a*x-t)"
    using numerator by (rule dvd_mult)
  have second: "M dvd (a*inv-1)*x"
    using inverse by (rule dvd_mult2)
  have "M dvd inv*(a*x-t) - (a*inv-1)*x"
    using first second by (rule dvd_diff)
  then show "M dvd x-inv*t" by (simp add: algebra_simps)
qed

theorem runtime_hensel_returned_residue:
  fixes a inv b r x :: int
  assumes inverse: "(2::int)^(q+E) dvd a*inv-1"
  shows "(x mod (2::int)^(q+E) =
      (inv*((2::int)^E*r-b)) mod (2::int)^(q+E)) =
    ((2::int)^(q+E) dvd a*x+b-(2::int)^E*r)"
  using modular_inverse_affine_preimage[OF inverse, of x "(2::int)^E*r-b"]
  by (simp add: mod_eq_dvd_iff algebra_simps)

theorem runtime_hensel_integral_target:
  fixes a b r x :: int
  shows "((2::int)^(q+E) dvd a*x+b-(2::int)^E*r) =
    (\<exists>y. a*x+b=(2::int)^E*y \<and> y mod (2::int)^q=r mod (2::int)^q)"
proof
  assume "(2::int)^(q+E) dvd a*x+b-(2::int)^E*r"
  then obtain k where k: "a*x+b-(2::int)^E*r = (2::int)^(q+E)*k"
    by (auto simp: dvd_def)
  have eq: "a*x+b=(2::int)^E*(r+2^q*k)"
    using k by (simp add: power_add algebra_simps)
  show "\<exists>y. a*x+b=(2::int)^E*y \<and> y mod (2::int)^q=r mod (2::int)^q"
    by (intro exI[of _ "r+2^q*k"]) (simp add: eq)
next
  assume "\<exists>y. a*x+b=(2::int)^E*y \<and> y mod (2::int)^q=r mod (2::int)^q"
  then obtain y where eq: "a*x+b=(2::int)^E*y"
    and congruent: "y mod (2::int)^q=r mod (2::int)^q" by blast
  have "(2::int)^q dvd y-r" using congruent by (simp add: mod_eq_dvd_iff)
  then obtain k where k: "y-r=(2::int)^q*k" by (auto simp: dvd_def)
  have "a*x+b-(2::int)^E*r=(2::int)^(q+E)*k"
    using eq k by (simp add: power_add algebra_simps)
  then show "(2::int)^(q+E) dvd a*x+b-(2::int)^E*r" by (auto simp: dvd_def)
qed


lemma polynomial_word_append:
  fixes z :: "'a::comm_semiring_1"
  shows "poly (Poly (xs@ys)) z = poly (Poly xs) z + z^(length xs)*poly (Poly ys) z"
  by (induction xs) (simp_all add: Poly.simps algebra_simps)

record 'a cylinder_word_state =
  cylinder_span :: nat
  cylinder_forward :: 'a
  cylinder_reverse :: 'a

definition cylinder_word :: "'a::comm_semiring_1 \<Rightarrow> 'a list \<Rightarrow> 'a cylinder_word_state" where
  "cylinder_word z xs = \<lparr>cylinder_span=length xs,
     cylinder_forward=poly (Poly xs) z, cylinder_reverse=poly (Poly (rev xs)) z\<rparr>"

definition cylinder_word_join ::
  "'a::comm_semiring_1 \<Rightarrow> 'a cylinder_word_state \<Rightarrow> 'a cylinder_word_state \<Rightarrow> 'a cylinder_word_state" where
  "cylinder_word_join z A B = \<lparr>cylinder_span=cylinder_span A+cylinder_span B,
     cylinder_forward=cylinder_forward A+z^(cylinder_span A)*cylinder_forward B,
     cylinder_reverse=cylinder_reverse B+z^(cylinder_span B)*cylinder_reverse A\<rparr>"

theorem cylinder_word_append_refinement:
  "cylinder_word z (xs@ys) = cylinder_word_join z (cylinder_word z xs) (cylinder_word z ys)"
  by (simp add: cylinder_word_def cylinder_word_join_def polynomial_word_append)

theorem cylinder_word_clip_refinement:
  "cylinder_word z (take n (xs@ys)) = cylinder_word_join z
     (cylinder_word z (take n xs)) (cylinder_word z (take (n-length xs) ys))"
  by (simp add: take_append cylinder_word_append_refinement)

theorem cylinder_word_join_associative:
  "cylinder_word_join z (cylinder_word_join z A B) C =
    cylinder_word_join z A (cylinder_word_join z B C)"
  by (cases A; cases B; cases C) (simp add: cylinder_word_join_def power_add algebra_simps)

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms
   cylinder_word_append_refinement cylinder_word_clip_refinement
   cylinder_word_join_associative
   modular_inverse_affine_preimage runtime_hensel_returned_residue
   runtime_hensel_integral_target
   mirror_ladder_initial mirror_ladder_next mirror_index_bounded
   mirror_ladder_none_iff_palindrome
   folded_mirror_vector_nonzero_implies_mismatch folded_difference_no_wrap
   terminal_mirror_vector_zero_iff_palindrome doubling_reaches_target
   event_clock_refines_list reassociation_preserves_every_clock_observer
   runtime_s_arithmetic_exponents tropical_clock_support_refinement
   tropical_clock_returns_minimum tropical_event_dag_refines_support
   tropical_then_associative zero_root_does_not_decide_M11
   M11_frobenius_coordinates_are_not_roots F5_nonzero_coefficients_need_not_split})
   then () else error "Runtime cylinder refinement oracle dependency";
\<close>
end
