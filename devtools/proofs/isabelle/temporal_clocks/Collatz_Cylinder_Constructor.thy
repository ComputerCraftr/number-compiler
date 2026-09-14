theory Collatz_Cylinder_Constructor
  imports Collatz_Clock_Jumps
begin

text \<open>A concrete source-derived accelerated Collatz constructor.  Unlike
the block equations in Collatz_Clock_Jumps, the valuation below is computed
from the current exact occurrence.  No valuation itinerary is an argument.

This theory proves exact prefix composition and weights.  It does not claim
that constructing all first-use prefixes has logarithmic cost or that the
resulting occurrence DAG has bounded size.\<close>

function strip_twos :: "nat \<Rightarrow> nat \<times> nat" where
  "strip_twos n =
    (if 0 < n \<and> even n then
      (let tail = strip_twos (n div 2) in (Suc (fst tail), snd tail))
     else (0,n))"
  by pat_completeness auto
termination
  by (relation "measure id") auto

declare strip_twos.simps [simp del]

lemma strip_twos_spec:
  assumes positive: "0 < n"
  shows "n = 2^(fst (strip_twos n)) * snd (strip_twos n) \<and>
    odd (snd (strip_twos n))"
using positive
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "even n")
    case False
    then show ?thesis using less.prems
      by (simp add: strip_twos.simps)
  next
    case True
    have half_less: "n div 2 < n" using less.prems by simp
    have not_one: "n \<noteq> 1" using True by auto
    have one_less: "1 < n" using less.prems not_one by linarith
    have half_positive: "0 < n div 2" using one_less by simp
    have half_spec:
      "n div 2 = 2^(fst (strip_twos (n div 2))) *
          snd (strip_twos (n div 2)) \<and>
       odd (snd (strip_twos (n div 2)))"
      using less.IH[OF half_less half_positive] .
    have split: "n = 2 * (n div 2)" using True by simp
    have split_equation: "strip_twos n =
        (if 0 < n \<and> even n then
          (let tail = strip_twos (n div 2) in (Suc (fst tail), snd tail))
         else (0,n))"
      by (rule strip_twos.simps)
    have unfolded: "strip_twos n =
        (Suc (fst (strip_twos (n div 2))), snd (strip_twos (n div 2)))"
      using split_equation less.prems True by (simp add: Let_def)
    have reconstructed: "n =
        2^Suc (fst (strip_twos (n div 2))) * snd (strip_twos (n div 2))"
      using half_spec split by (simp add: power_Suc)
    show ?thesis using unfolded reconstructed half_spec by simp
  qed
qed

definition collatz_source_split :: "nat \<Rightarrow> nat \<times> nat" where
  "collatz_source_split x = strip_twos (3*x+1)"

definition collatz_source_valuation :: "nat \<Rightarrow> nat" where
  "collatz_source_valuation x = fst (collatz_source_split x)"

definition collatz_accelerated_target :: "nat \<Rightarrow> nat" where
  "collatz_accelerated_target x = snd (collatz_source_split x)"

lemma collatz_source_split_exact:
  "3*x+1 = 2^(collatz_source_valuation x) * collatz_accelerated_target x"
  using strip_twos_spec[of "3*x+1"]
  by (simp add: collatz_source_split_def collatz_source_valuation_def
    collatz_accelerated_target_def)

lemma collatz_accelerated_target_odd:
  "odd (collatz_accelerated_target x)"
  using strip_twos_spec[of "3*x+1"]
  by (simp add: collatz_source_split_def collatz_accelerated_target_def)

lemma odd_source_has_positive_valuation:
  assumes "odd x"
  shows "0 < collatz_source_valuation x"
proof (rule ccontr)
  assume "\<not> 0 < collatz_source_valuation x"
  then have zero: "collatz_source_valuation x = 0" by simp
  have "odd (3*x+1)"
    using collatz_source_split_exact[of x]
      collatz_accelerated_target_odd[of x] zero by simp
  moreover have "even (3*x+1)" using assms by simp
  ultimately show False by simp
qed

definition physical_collatz :: "nat \<Rightarrow> nat" where
  "physical_collatz x = (if even x then x div 2 else 3*x+1)"

lemma physical_collatz_removes_dyadic_prefix:
  "(physical_collatz ^^ k) (2^k*y) = y"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (simp del: funpow.simps(2)
      add: physical_collatz_def funpow_Suc_right power_Suc)
qed

lemma physical_collatz_three_cycle:
  "(physical_collatz ^^ 3) 1 = 1"
proof -
  have expansion: "(physical_collatz ^^ 3) 1 =
      physical_collatz (physical_collatz (physical_collatz 1))"
    by (simp only: numeral_3_eq_3 funpow.simps comp_apply id_apply)
  show ?thesis using expansion by (simp add: physical_collatz_def)
qed

theorem physical_collatz_power_two_cycle_tail:
  "(physical_collatz ^^ (k+t)) (2^k) = (physical_collatz ^^ t) 1"
proof -
  have "(physical_collatz ^^ (k+t)) (2^k) =
      (physical_collatz ^^ (t+k)) (2^k)"
    by (simp add: add.commute)
  also have "... = (physical_collatz ^^ t)
      ((physical_collatz ^^ k) (2^k))"
    by (simp add: funpow_add)
  also have "... = (physical_collatz ^^ t) 1"
    using physical_collatz_removes_dyadic_prefix[of k 1] by simp
  finally show ?thesis .
qed

theorem source_split_embeds_physical_ticks:
  assumes "odd x"
  shows "(physical_collatz ^^ Suc (collatz_source_valuation x)) x =
    collatz_accelerated_target x"
  using physical_collatz_removes_dyadic_prefix[
      of "collatz_source_valuation x" "collatz_accelerated_target x"]
    collatz_source_split_exact[of x] assms
  by (simp del: funpow.simps(2)
    add: physical_collatz_def funpow_Suc_right)

definition collatz_normalized :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "collatz_normalized n x = inverse_three_coordinate n (int x)"

definition collatz_root_prefix :: "nat \<Rightarrow> rat" where
  "collatz_root_prefix n = -1 / (3::rat)^(Suc n)"

lemma collatz_source_split_int:
  "3 * int x + 1 =
    (2::int)^(collatz_source_valuation x) * int (collatz_accelerated_target x)"
proof -
  have casted:
    "int (3*x+1) = int
      (2^(collatz_source_valuation x) * collatz_accelerated_target x)"
    by (rule arg_cong[OF collatz_source_split_exact])
  show ?thesis using casted by simp
qed

theorem collatz_source_derived_cylinder_step:
  "collatz_normalized n x - collatz_root_prefix n =
    (2::rat)^(collatz_source_valuation x) *
      collatz_normalized (Suc n) (collatz_accelerated_target x)"
proof -
  have conjugacy:
    "inverse_three_coordinate (Suc n) (int (collatz_accelerated_target x)) =
      (inverse_three_coordinate n (int x) + 1/(3::rat)^(Suc n)) /
        (2::rat)^(collatz_source_valuation x)"
    using inverse_three_clock_conjugacy[OF collatz_source_split_int, of n] .
  show ?thesis
    using conjugacy
    by (simp add: collatz_normalized_def collatz_root_prefix_def field_simps)
qed

type_synonym cylinder_prefix = "rat \<times> nat"

definition cylinder_prefix_identity :: cylinder_prefix where
  "cylinder_prefix_identity = (0,0)"

definition cylinder_prefix_then ::
    "cylinder_prefix \<Rightarrow> cylinder_prefix \<Rightarrow> cylinder_prefix" where
  "cylinder_prefix_then first second =
    (fst first + (2::rat)^(snd first) * fst second,
      snd first + snd second)"

definition cylinder_prefix_projection ::
    "cylinder_prefix \<Rightarrow> rat skew_transfer" where
  "cylinder_prefix_projection A =
    \<lparr>upper = 1, offset = fst A, lower = (2::rat)^(snd A)\<rparr>"

lemma cylinder_prefix_projection_identity:
  "cylinder_prefix_projection cylinder_prefix_identity = shared_skew_identity"
  by (simp add: cylinder_prefix_projection_def
      cylinder_prefix_identity_def shared_skew_identity_def)

lemma cylinder_prefix_projection_then:
  "cylinder_prefix_projection (cylinder_prefix_then A B) = shared_skew_then
    (cylinder_prefix_projection A) (cylinder_prefix_projection B)"
  by (cases A; cases B)
    (simp add: cylinder_prefix_projection_def cylinder_prefix_then_def
      shared_skew_then_def power_add algebra_simps)

lemma cylinder_prefix_then_identity [simp]:
  "cylinder_prefix_then cylinder_prefix_identity A = A"
  "cylinder_prefix_then A cylinder_prefix_identity = A"
  by (auto simp: cylinder_prefix_identity_def cylinder_prefix_then_def)

lemma cylinder_prefix_then_associative:
  "cylinder_prefix_then (cylinder_prefix_then A B) C =
    cylinder_prefix_then A (cylinder_prefix_then B C)"
  by (cases A; cases B; cases C)
    (simp add: cylinder_prefix_then_def power_add algebra_simps)

theorem cylinder_prefix_then_exact:
  assumes first: "W - fst A = (2::rat)^(snd A) * V"
      and second: "V - fst B = (2::rat)^(snd B) * Z"
  shows "W - fst (cylinder_prefix_then A B) =
    (2::rat)^(snd (cylinder_prefix_then A B)) * Z"
proof -
  have "W - (fst A + (2::rat)^(snd A) * fst B) =
      (2::rat)^(snd A) * (V - fst B)"
    using first by (simp add: algebra_simps)
  also have "... = (2::rat)^(snd A + snd B) * Z"
    using second by (simp add: power_add algebra_simps)
  finally show ?thesis by (simp add: cylinder_prefix_then_def)
qed

definition collatz_cylinder_atom :: "nat \<Rightarrow> nat \<Rightarrow> cylinder_prefix" where
  "collatz_cylinder_atom n x =
    (collatz_root_prefix n, collatz_source_valuation x)"

fun collatz_cylinder_block ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cylinder_prefix" where
  "collatz_cylinder_block n x 0 = cylinder_prefix_identity"
| "collatz_cylinder_block n x (Suc events) =
    cylinder_prefix_then (collatz_cylinder_atom n x)
      (collatz_cylinder_block (Suc n) (collatz_accelerated_target x) events)"

theorem collatz_cylinder_block_exact:
  "collatz_normalized n x - fst (collatz_cylinder_block n x events) =
    (2::rat)^(snd (collatz_cylinder_block n x events)) *
      collatz_normalized (n+events)
        ((collatz_accelerated_target ^^ events) x)"
proof (induction events arbitrary: n x)
  case 0
  then show ?case
    by (simp add: cylinder_prefix_identity_def)
next
  case (Suc events)
  have first:
    "collatz_normalized n x - fst (collatz_cylinder_atom n x) =
      (2::rat)^(snd (collatz_cylinder_atom n x)) *
        collatz_normalized (Suc n) (collatz_accelerated_target x)"
    using collatz_source_derived_cylinder_step[of n x]
    by (simp add: collatz_cylinder_atom_def)
  have second:
    "collatz_normalized (Suc n) (collatz_accelerated_target x) -
        fst (collatz_cylinder_block (Suc n)
          (collatz_accelerated_target x) events) =
      (2::rat)^(snd (collatz_cylinder_block (Suc n)
          (collatz_accelerated_target x) events)) *
        collatz_normalized (Suc n+events)
          ((collatz_accelerated_target ^^ events)
            (collatz_accelerated_target x))"
    using Suc.IH[of "Suc n" "collatz_accelerated_target x"] .
  show ?case
    using cylinder_prefix_then_exact[OF first second]
    by (simp del: funpow.simps(2) add: funpow_Suc_right)
qed

theorem collatz_cylinder_block_compose:
  "collatz_cylinder_block n x (events+extra) =
    cylinder_prefix_then (collatz_cylinder_block n x events)
      (collatz_cylinder_block (n+events)
        ((collatz_accelerated_target ^^ events) x) extra)"
proof (induction events arbitrary: n x)
  case 0
  then show ?case by simp
next
  case (Suc events)
  note tail = Suc.IH[of "Suc n" "collatz_accelerated_target x"]
  show ?case
    using tail cylinder_prefix_then_associative[of
      "collatz_cylinder_atom n x"
      "collatz_cylinder_block (Suc n) (collatz_accelerated_target x) events"
      "collatz_cylinder_block (Suc n+events)
        ((collatz_accelerated_target ^^ events)
          (collatz_accelerated_target x)) extra"]
    by (simp del: funpow.simps(2) add: funpow_Suc_right)
qed

definition collatz_cylinder_physical_ticks ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_cylinder_physical_ticks n x events =
    events + snd (collatz_cylinder_block n x events)"

theorem collatz_cylinder_physical_ticks_compose:
  "collatz_cylinder_physical_ticks n x (events+extra) =
    collatz_cylinder_physical_ticks n x events +
      collatz_cylinder_physical_ticks (n+events)
        ((collatz_accelerated_target ^^ events) x) extra"
  using collatz_cylinder_block_compose[of n x events extra]
  by (simp add: collatz_cylinder_physical_ticks_def
    cylinder_prefix_then_def algebra_simps)

lemma collatz_cylinder_physical_ticks_Suc [simp]:
  "collatz_cylinder_physical_ticks n x (Suc events) =
    Suc (collatz_source_valuation x) +
      collatz_cylinder_physical_ticks (Suc n)
        (collatz_accelerated_target x) events"
  by (simp add: collatz_cylinder_physical_ticks_def
    collatz_cylinder_atom_def cylinder_prefix_then_def)

theorem collatz_cylinder_events_embed_physical_time:
  assumes "odd x"
  shows "(physical_collatz ^^
      collatz_cylinder_physical_ticks n x events) x =
    (collatz_accelerated_target ^^ events) x"
using assms
proof (induction events arbitrary: n x)
  case 0
  then show ?case by (simp add: collatz_cylinder_physical_ticks_def
    cylinder_prefix_identity_def)
next
  case (Suc events)
  have atom:
    "(physical_collatz ^^ Suc (collatz_source_valuation x)) x =
      collatz_accelerated_target x"
    using source_split_embeds_physical_ticks Suc.prems by blast
  have target_odd: "odd (collatz_accelerated_target x)"
    by (rule collatz_accelerated_target_odd)
  have tail:
    "(physical_collatz ^^
        collatz_cylinder_physical_ticks (Suc n)
          (collatz_accelerated_target x) events)
        (collatz_accelerated_target x) =
      (collatz_accelerated_target ^^ events)
        (collatz_accelerated_target x)"
    using Suc.IH[OF target_odd, of "Suc n"] .
  have tick_order:
    "collatz_cylinder_physical_ticks n x (Suc events) =
      collatz_cylinder_physical_ticks (Suc n)
        (collatz_accelerated_target x) events +
      Suc (collatz_source_valuation x)"
    by (simp add: add.commute)
  have "(physical_collatz ^^
        collatz_cylinder_physical_ticks n x (Suc events)) x =
      (physical_collatz ^^
        (collatz_cylinder_physical_ticks (Suc n)
          (collatz_accelerated_target x) events +
         Suc (collatz_source_valuation x))) x"
      by (simp only: tick_order)
    also have "... =
      (physical_collatz ^^
        collatz_cylinder_physical_ticks (Suc n)
          (collatz_accelerated_target x) events)
        ((physical_collatz ^^ Suc (collatz_source_valuation x)) x)"
      by (simp only: funpow_add comp_apply)
    also have "... =
      (physical_collatz ^^
        collatz_cylinder_physical_ticks (Suc n)
          (collatz_accelerated_target x) events)
        (collatz_accelerated_target x)"
      using atom by simp
    also have "... =
      (collatz_accelerated_target ^^ events)
        (collatz_accelerated_target x)"
      using tail .
    also have "... =
      (collatz_accelerated_target ^^ Suc events) x"
      by (simp only: funpow_Suc_right comp_apply)
    finally show ?case .
qed

fun collatz_cylinder_constructor_evaluations ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_cylinder_constructor_evaluations n x 0 = 0"
| "collatz_cylinder_constructor_evaluations n x (Suc events) =
    Suc (collatz_cylinder_constructor_evaluations (Suc n)
      (collatz_accelerated_target x) events)"

theorem collatz_cylinder_constructor_evaluations_exact:
  "collatz_cylinder_constructor_evaluations n x events = events"
  by (induction events arbitrary: n x) simp_all

text \<open>Fixed-precision phase death is not weighted successor closure.  At
q=3 the inverse-three phase has period two, so both rows below return to phase
zero after two events.  Their source-derived prefix weights
still differ.  A residual grammar must therefore consume the exact source
cylinder; clock phase alone cannot be its action identity.\<close>

lemma phase_neutrality_does_not_fix_cylinder_action:
  "(0+2) mod 2 = (0::nat) \<and>
   (collatz_accelerated_target ^^ 2) 1 = 1 \<and>
   snd (collatz_cylinder_block 0 1 2) = 4 \<and>
   collatz_cylinder_physical_ticks 0 1 2 = 6 \<and>
   (collatz_accelerated_target ^^ 2) 3 = 1 \<and>
   snd (collatz_cylinder_block 0 3 2) = 5 \<and>
   collatz_cylinder_physical_ticks 0 3 2 = 7"
  by code_simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms cylinder_prefix_projection_identity cylinder_prefix_projection_then strip_twos_spec collatz_source_split_exact
      collatz_accelerated_target_odd odd_source_has_positive_valuation
      physical_collatz_removes_dyadic_prefix physical_collatz_three_cycle
      physical_collatz_power_two_cycle_tail source_split_embeds_physical_ticks
      collatz_source_derived_cylinder_step
      cylinder_prefix_then_identity cylinder_prefix_then_associative
      cylinder_prefix_then_exact collatz_cylinder_block_exact
      collatz_cylinder_block_compose collatz_cylinder_physical_ticks_compose
      collatz_cylinder_events_embed_physical_time
      collatz_cylinder_constructor_evaluations_exact
      phase_neutrality_does_not_fix_cylinder_action}) then ()
    else error "Collatz cylinder constructor proof depends on an oracle";
\<close>

end
