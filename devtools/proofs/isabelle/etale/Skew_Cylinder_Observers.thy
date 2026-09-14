theory Skew_Cylinder_Observers
  imports Etale_Primality_Bridge "HOL.Rat" "Shared_S_Arithmetic.S_Arithmetic_Skew"
begin

definition skew_then :: "'a::comm_semiring_1 skew_transfer \<Rightarrow> 'a skew_transfer \<Rightarrow> 'a skew_transfer" where
  "skew_then A B = shared_skew_then A B"

definition skew_identity :: "'a::comm_semiring_1 skew_transfer" where
  "skew_identity = shared_skew_identity"

lemma skew_associative:
  "skew_then (skew_then A B) C = skew_then A (skew_then B C)"
  unfolding skew_then_def by (rule shared_skew_associative)

lemma skew_identities [simp]:
  "skew_then skew_identity A = A" "skew_then A skew_identity = A"
  by (simp_all add: skew_then_def shared_skew_then_def skew_identity_def shared_skew_identity_def)

definition skew_map where
  "skew_map f A = \<lparr>upper=f (upper A), offset=f (offset A), lower=f (lower A)\<rparr>"

theorem observer_commutes_with_composition:
  fixes f :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes plus: "\<And>x y. f (x+y) = f x + f y"
    and times: "\<And>x y. f (x*y) = f x * f y"
  shows "skew_map f (skew_then A B) = skew_then (skew_map f A) (skew_map f B)"
  by (simp add: skew_map_def skew_then_def shared_skew_then_def plus times)

fun clock_transfer :: "'a::comm_semiring_1 \<Rightarrow> 'a \<Rightarrow> nat list \<Rightarrow> 'a skew_transfer" where
  "clock_transfer s z [] = skew_identity"
| "clock_transfer s z (k#ks) = skew_then \<lparr>upper=s, offset=1, lower=z^k\<rparr> (clock_transfer s z ks)"

lemma clock_diagonals:
  "upper (clock_transfer s z ks) = s^(length ks)"
  "lower (clock_transfer s z ks) = z^(sum_list ks)"
  by (induction ks) (simp_all add: skew_then_def shared_skew_then_def skew_identity_def shared_skew_identity_def power_add algebra_simps)

lemma clock_append:
  "clock_transfer s z (xs@ys) = skew_then (clock_transfer s z xs) (clock_transfer s z ys)"
  by (induction xs) (simp_all add: skew_associative)

theorem clock_offset_skew:
  "offset (clock_transfer s z (xs@ys)) =
    s^(length ys) * offset (clock_transfer s z xs) +
    z^(sum_list xs) * offset (clock_transfer s z ys)"
  by (simp add: clock_append skew_then_def shared_skew_then_def clock_diagonals)

theorem skew_transport_composes:
  fixes A B :: "'a::comm_ring_1 skew_transfer"
  assumes first: "upper A*x + offset A = lower A*y"
    and second: "upper B*y + offset B = lower B*z"
  shows "upper (skew_then A B)*x + offset (skew_then A B) = lower (skew_then A B)*z"
  unfolding skew_then_def
  by (rule shared_skew_transport[OF first second])

theorem s_arithmetic_product_formula:
  "((3::rat)^n / 2^k) * 2^k * (1 / 3^n) = 1"
  by simp

lemma physical_tick_cocycle:
  "length (xs@ys) + sum_list (xs@ys) =
    (length xs + sum_list xs) + (length ys + sum_list ys)"
  by simp

text \<open>Backward demands compose contravariantly. This is independent of
whether an observer admits a smaller or cheaper representation.\<close>

definition demand_pullback where "demand_pullback f D = (\<lambda>x. D (f x))"

lemma demand_pullback_compose:
  "demand_pullback (g \<circ> f) D = demand_pullback f (demand_pullback g D)"
  by (simp add: demand_pullback_def fun_eq_iff)

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms skew_associative
   observer_commutes_with_composition clock_diagonals clock_append clock_offset_skew
   skew_transport_composes s_arithmetic_product_formula physical_tick_cocycle
   demand_pullback_compose}) then () else error "Skew observer oracle dependency";
\<close>
end
