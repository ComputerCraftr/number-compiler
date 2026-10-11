theory Comma_Semantic_Producer_Coefficients
  imports Comma_Semantic_Producer_Refinement
begin

text \<open>The indexed publisher stores common-denominator triples, while the
runtime macro exposes a source constructor, terminal outcome, destination,
ordered children, and final affine prefix entries.  This theory records
those fields directly and gives coefficient-level facts; agreement at one
chosen decimal scale is not used to infer equality of affine coefficients.\<close>

definition comma_python_affine_raw ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> comma_python_affine_weight" where
  "comma_python_affine_raw A B D =
    \<lparr>comma_python_affine_scale=A, comma_python_affine_offset=B,
     comma_python_affine_denominator=D\<rparr>"

lemma comma_python_affine_normalize_equivalent_raw:
  fixes A B :: int and D :: nat
  assumes positive: "0 < D"
  shows "comma_python_affine_equivalent
    (comma_python_affine_normalize A B D)
    (comma_python_affine_raw A B D)"
proof -
  let ?g = "gcd (gcd (nat (abs A)) (nat (abs B))) D"
  have g_positive: "0 < ?g" using positive by simp
  have gA_nat: "?g dvd nat (abs A)" by simp
  have gB_nat: "?g dvd nat (abs B)" by simp
  have gD: "?g dvd D" by simp
  have gA_abs: "int ?g dvd abs A"
  proof -
    have "int ?g dvd int (nat (abs A))"
      using gA_nat by exact_mod_cast
    then show ?thesis by simp
  qed
  have gB_abs: "int ?g dvd abs B"
  proof -
    have "int ?g dvd int (nat (abs B))"
      using gB_nat by exact_mod_cast
    then show ?thesis by simp
  qed
  have gA: "int ?g dvd A" using gA_abs by (cases A) auto
  have gB: "int ?g dvd B" using gB_abs by (cases B) auto
  have A_mod: "A mod int ?g = 0"
    using gA g_positive by (simp add: dvd_eq_mod_eq_0)
  have B_mod: "B mod int ?g = 0"
    using gB g_positive by (simp add: dvd_eq_mod_eq_0)
  have D_mod: "D mod ?g = 0"
    using gD by (simp add: dvd_eq_mod_eq_0)
  have A_factor:
    "A = int ?g * (A div int ?g)"
    using A_mod by (simp add: div_mult_mod_eq mult.commute)
  have B_factor:
    "B = int ?g * (B div int ?g)"
    using B_mod by (simp add: div_mult_mod_eq mult.commute)
  have D_factor: "D = ?g * (D div ?g)"
    using D_mod by (simp add: div_mult_mod_eq mult.commute)
  have d_positive: "0 < D div ?g"
    using positive g_positive D_factor by (cases "D div ?g") auto
  show ?thesis
    unfolding comma_python_affine_equivalent_def
      comma_python_affine_normalize_def comma_python_affine_raw_def Let_def
    using A_factor B_factor D_factor
    by (simp add: algebra_simps positive d_positive)
qed

lemma comma_python_affine_equivalent_refl [simp]:
  assumes positive: "0 < comma_python_affine_denominator a"
  shows "comma_python_affine_equivalent a a"
  using positive by (simp add: comma_python_affine_equivalent_def)

lemma comma_python_affine_equivalent_sym:
  assumes "comma_python_affine_equivalent a b"
  shows "comma_python_affine_equivalent b a"
  using assms by (simp add: comma_python_affine_equivalent_def mult.commute)

lemma comma_python_affine_equivalent_trans:
  assumes ab: "comma_python_affine_equivalent a b"
    and bc: "comma_python_affine_equivalent b c"
    and positive:
      "0 < comma_python_affine_denominator b"
  shows "comma_python_affine_equivalent a c"
proof -
  have slope_ab:
    "comma_python_affine_scale a *
      int (comma_python_affine_denominator b) =
     comma_python_affine_scale b *
      int (comma_python_affine_denominator a)"
    and offset_ab:
    "comma_python_affine_offset a *
      int (comma_python_affine_denominator b) =
     comma_python_affine_offset b *
      int (comma_python_affine_denominator a)"
    using ab by (simp_all add: comma_python_affine_equivalent_def)
  have slope_bc:
    "comma_python_affine_scale b *
      int (comma_python_affine_denominator c) =
     comma_python_affine_scale c *
      int (comma_python_affine_denominator b)"
    and offset_bc:
    "comma_python_affine_offset b *
      int (comma_python_affine_denominator c) =
     comma_python_affine_offset c *
      int (comma_python_affine_denominator b)"
    using bc by (simp_all add: comma_python_affine_equivalent_def)
  have middle: "int (comma_python_affine_denominator b) \<noteq> 0"
    using positive by simp
  have slope:
    "comma_python_affine_scale a *
      int (comma_python_affine_denominator c) =
     comma_python_affine_scale c *
      int (comma_python_affine_denominator a)"
  proof -
    have cancel:
      "int (comma_python_affine_denominator b) *
        (comma_python_affine_scale a *
          int (comma_python_affine_denominator c)) =
       int (comma_python_affine_denominator b) *
        (comma_python_affine_scale c *
          int (comma_python_affine_denominator a))"
      using slope_ab slope_bc by (simp add: algebra_simps)
    show ?thesis using cancel middle by (metis mult_left_cancel)
  qed
  have offset:
    "comma_python_affine_offset a *
      int (comma_python_affine_denominator c) =
     comma_python_affine_offset c *
      int (comma_python_affine_denominator a)"
  proof -
    have cancel:
      "int (comma_python_affine_denominator b) *
        (comma_python_affine_offset a *
          int (comma_python_affine_denominator c)) =
       int (comma_python_affine_denominator b) *
        (comma_python_affine_offset c *
          int (comma_python_affine_denominator a))"
      using offset_ab offset_bc by (simp add: algebra_simps)
    show ?thesis using cancel middle by (metis mult_left_cancel)
  qed
  show ?thesis using slope offset ab bc
    by (auto simp: comma_python_affine_equivalent_def)
qed

lemma comma_python_affine_times_raw:
  assumes positive: "0 < comma_python_affine_denominator a"
  shows "comma_python_affine_equivalent
    (comma_python_affine_times n a)
    (comma_python_affine_raw
      (int n * comma_python_affine_scale a)
      (int n * comma_python_affine_offset a)
      (comma_python_affine_denominator a))"
  using comma_python_affine_normalize_equivalent_raw[OF positive,
      of "int n * comma_python_affine_scale a"
        "int n * comma_python_affine_offset a"]
  by (simp add: comma_python_affine_times_def
      comma_python_affine_raw_def)

lemma comma_python_affine_add_raw:
  assumes left: "0 < comma_python_affine_denominator a"
    and right: "0 < comma_python_affine_denominator b"
  shows "comma_python_affine_equivalent
    (comma_python_affine_add a b)
    (comma_python_affine_raw
      (comma_python_affine_scale a * int (comma_python_affine_denominator b) +
       comma_python_affine_scale b * int (comma_python_affine_denominator a))
      (comma_python_affine_offset a * int (comma_python_affine_denominator b) +
       comma_python_affine_offset b * int (comma_python_affine_denominator a))
      (comma_python_affine_denominator a * comma_python_affine_denominator b))"
proof -
  have product_positive:
    "0 < comma_python_affine_denominator a *
      comma_python_affine_denominator b"
    using left right by simp
  show ?thesis
    using comma_python_affine_normalize_equivalent_raw
      [OF product_positive, of
        "comma_python_affine_scale a *
          int (comma_python_affine_denominator b) +
         comma_python_affine_scale b *
          int (comma_python_affine_denominator a)"
        "comma_python_affine_offset a *
          int (comma_python_affine_denominator b) +
         comma_python_affine_offset b *
          int (comma_python_affine_denominator a)"]
    by (simp add: comma_python_affine_add_def comma_python_affine_raw_def)
qed

lemma comma_python_affine_times_cong:
  assumes equivalent: "comma_python_affine_equivalent a b"
  shows "comma_python_affine_equivalent
    (comma_python_affine_times n a) (comma_python_affine_times n b)"
proof -
  have den_a: "0 < comma_python_affine_denominator a"
    and den_b: "0 < comma_python_affine_denominator b"
    using equivalent by (simp_all add: comma_python_affine_equivalent_def)
  have left:
    "comma_python_affine_equivalent
      (comma_python_affine_times n a)
      (comma_python_affine_raw
        (int n * comma_python_affine_scale a)
        (int n * comma_python_affine_offset a)
        (comma_python_affine_denominator a))"
    by (rule comma_python_affine_times_raw[OF den_a])
  have raw_equiv:
    "comma_python_affine_equivalent
      (comma_python_affine_raw
        (int n * comma_python_affine_scale a)
        (int n * comma_python_affine_offset a)
        (comma_python_affine_denominator a))
      (comma_python_affine_raw
        (int n * comma_python_affine_scale b)
        (int n * comma_python_affine_offset b)
        (comma_python_affine_denominator b))"
    using equivalent
    by (auto simp: comma_python_affine_equivalent_def
        comma_python_affine_raw_def algebra_simps)
  have right:
    "comma_python_affine_equivalent
      (comma_python_affine_times n b)
      (comma_python_affine_raw
        (int n * comma_python_affine_scale b)
        (int n * comma_python_affine_offset b)
        (comma_python_affine_denominator b))"
    by (rule comma_python_affine_times_raw[OF den_b])
  have first:
    "comma_python_affine_equivalent (comma_python_affine_times n a)
      (comma_python_affine_raw
        (int n * comma_python_affine_scale b)
        (int n * comma_python_affine_offset b)
        (comma_python_affine_denominator b))"
    by (rule comma_python_affine_equivalent_trans[OF left raw_equiv den_a])
  show ?thesis
  proof -
    have right_sym:
      "comma_python_affine_equivalent
        (comma_python_affine_raw
          (int n * comma_python_affine_scale b)
          (int n * comma_python_affine_offset b)
          (comma_python_affine_denominator b))
        (comma_python_affine_times n b)"
      by (rule comma_python_affine_equivalent_sym[OF right])
    show ?thesis
      by (rule comma_python_affine_equivalent_trans[OF first right_sym den_b])
  qed
qed

lemma comma_python_affine_add_cong:
  assumes left: "comma_python_affine_equivalent a c"
    and right: "comma_python_affine_equivalent b d"
  shows "comma_python_affine_equivalent
    (comma_python_affine_add a b) (comma_python_affine_add c d)"
proof -
  have da: "0 < comma_python_affine_denominator a"
    and db: "0 < comma_python_affine_denominator b"
    and dc: "0 < comma_python_affine_denominator c"
    and dd: "0 < comma_python_affine_denominator d"
    using left right by (simp_all add: comma_python_affine_equivalent_def)
  let ?raw_ab = "comma_python_affine_raw
    (comma_python_affine_scale a * int (comma_python_affine_denominator b) +
     comma_python_affine_scale b * int (comma_python_affine_denominator a))
    (comma_python_affine_offset a * int (comma_python_affine_denominator b) +
     comma_python_affine_offset b * int (comma_python_affine_denominator a))
    (comma_python_affine_denominator a * comma_python_affine_denominator b)"
  let ?raw_cd = "comma_python_affine_raw
    (comma_python_affine_scale c * int (comma_python_affine_denominator d) +
     comma_python_affine_scale d * int (comma_python_affine_denominator c))
    (comma_python_affine_offset c * int (comma_python_affine_denominator d) +
     comma_python_affine_offset d * int (comma_python_affine_denominator c))
    (comma_python_affine_denominator c * comma_python_affine_denominator d)"
  have add_ab:
    "comma_python_affine_equivalent (comma_python_affine_add a b) ?raw_ab"
    by (rule comma_python_affine_add_raw[OF da db])
  have add_cd:
    "comma_python_affine_equivalent (comma_python_affine_add c d) ?raw_cd"
    by (rule comma_python_affine_add_raw[OF dc dd])
  have raw_equiv: "comma_python_affine_equivalent ?raw_ab ?raw_cd"
    using left right
    by (auto simp: comma_python_affine_equivalent_def
        comma_python_affine_raw_def algebra_simps)
  have dab: "0 < comma_python_affine_denominator a *
      comma_python_affine_denominator b"
    using da db by simp
  have dcd: "0 < comma_python_affine_denominator c *
      comma_python_affine_denominator d"
    using dc dd by simp
  have first:
    "comma_python_affine_equivalent (comma_python_affine_add a b) ?raw_cd"
    by (rule comma_python_affine_equivalent_trans[OF add_ab raw_equiv dab])
  have add_cd_sym:
    "comma_python_affine_equivalent ?raw_cd (comma_python_affine_add c d)"
    by (rule comma_python_affine_equivalent_sym[OF add_cd])
  show ?thesis
    by (rule comma_python_affine_equivalent_trans[OF first add_cd_sym dcd])
qed

lemma comma_python_affine_times_normalize_scaled:
  fixes A B :: int and D :: nat
  assumes positive: "0 < D"
  shows "comma_python_affine_equivalent
    (comma_python_affine_times n
      (comma_python_affine_normalize A B D))
    (comma_python_affine_normalize (int n * A) (int n * B) D)"
proof -
  let ?raw = "comma_python_affine_raw A B D"
  let ?scaled_raw = "comma_python_affine_raw
    (int n * A) (int n * B) D"
  let ?scaled_normal =
    "comma_python_affine_normalize (int n * A) (int n * B) D"
  have reduced:
    "comma_python_affine_equivalent
      (comma_python_affine_normalize A B D) ?raw"
    by (rule comma_python_affine_normalize_equivalent_raw[OF positive])
  have scaled:
    "comma_python_affine_equivalent
      (comma_python_affine_times n
        (comma_python_affine_normalize A B D))
      (comma_python_affine_times n ?raw)"
    by (rule comma_python_affine_times_cong[OF reduced])
  have raw_times:
    "comma_python_affine_equivalent (comma_python_affine_times n ?raw)
      ?scaled_raw"
    by (rule comma_python_affine_times_raw[OF positive])
  have middle_positive:
    "0 < comma_python_affine_denominator (comma_python_affine_times n ?raw)"
    using positive
    by (simp add: comma_python_affine_times_def comma_python_affine_raw_def
        comma_python_affine_normalize_positive_denominator)
  have first:
    "comma_python_affine_equivalent
      (comma_python_affine_times n
        (comma_python_affine_normalize A B D)) ?scaled_raw"
    by (rule comma_python_affine_equivalent_trans
      [OF scaled raw_times middle_positive])
  have normalized_scaled:
    "comma_python_affine_equivalent
      ?scaled_normal ?scaled_raw"
    by (rule comma_python_affine_normalize_equivalent_raw[OF positive])
  have raw_to_normal:
    "comma_python_affine_equivalent ?scaled_raw ?scaled_normal"
    by (rule comma_python_affine_equivalent_sym[OF normalized_scaled])
  show ?thesis
    by (rule comma_python_affine_equivalent_trans
      [OF first raw_to_normal positive])
qed

lemma comma_python_entry_fragment_weight_affine_coefficient:
  fixes f delta offset h :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
  defines "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "fragment \<equiv>
      comma_python_entry_sector_fragment f delta offset h"
    and "chart_weight \<equiv>
      Comma_Chart_Weight L delta (- int (L * (offset + h))) P"
  shows "comma_python_affine_equivalent
    (comma_python_fragment_weight_affine fragment)
    (comma_python_chart_affine_weight delta chart_weight)"
proof -
  have f_positive: "0 < f" using f by simp
  have period_positive:
    "0 < comma_period_displacement f (offset mod 10)
      (comma_cycle_length f)"
    by (rule comma_period_displacement_admitted[OF f_positive
      comma_cycle_length_admitted(1)[OF f]])
  have period_exact:
    "comma_finite_period f (offset mod 10) =
      comma_period_displacement f (offset mod 10)
        (comma_cycle_length f)"
    by (rule comma_finite_period_refines[OF f]; simp)
  have P_positive: "0 < P"
    using period_positive period_exact by (simp add: P_def)
  have cycle_affine:
    "comma_python_fragment_complete_cycles fragment =
      comma_python_affine_normalize
        (int (10 ^ delta)) (- int (offset + h)) P"
    by (simp add: fragment_def comma_python_entry_sector_fragment_def
        Let_def P_def)
  have scaled:
    "comma_python_affine_equivalent
      (comma_python_affine_times L
        (comma_python_affine_normalize
          (int (10 ^ delta)) (- int (offset + h)) P))
      (comma_python_affine_normalize
        (int (L * 10 ^ delta)) (- int (L * (offset + h))) P)"
    using comma_python_affine_times_normalize_scaled
      [OF P_positive, of L "int (10 ^ delta)" "- int (offset + h)"]
    by (simp add: algebra_simps)
  have literal_zero:
    "comma_python_constant_affine 0 = comma_python_affine_zero"
    by (simp add: comma_python_constant_affine_def
        comma_python_affine_zero_def comma_python_affine_normalize_def Let_def)
  have cycle_equiv:
    "comma_python_affine_equivalent
      (comma_python_affine_times L
        (comma_python_fragment_complete_cycles fragment))
      (comma_python_affine_normalize
        (int (L * 10 ^ delta)) (- int (L * (offset + h))) P)"
    using scaled cycle_affine by simp
  have chart_triple_positive:
    "0 < comma_python_affine_denominator
      (comma_python_affine_normalize
        (int (L * 10 ^ delta)) (- int (L * (offset + h))) P)"
    by (rule comma_python_affine_normalize_positive_denominator[OF P_positive])
  let ?chart = "comma_python_affine_normalize
    (int (L * 10 ^ delta)) (- int (L * (offset + h))) P"
  have sums:
    "comma_python_affine_equivalent
      (comma_python_affine_add
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment))
        (comma_python_constant_affine 0))
      (comma_python_affine_add ?chart comma_python_affine_zero)"
  proof -
    have zero_equiv:
      "comma_python_affine_equivalent
        (comma_python_constant_affine 0) comma_python_affine_zero"
      using literal_zero by simp
    show ?thesis
      by (rule comma_python_affine_add_cong[OF cycle_equiv zero_equiv])
  qed
  have add_raw:
    "comma_python_affine_equivalent
      (comma_python_affine_add ?chart comma_python_affine_zero)
      (comma_python_affine_raw
        (comma_python_affine_scale ?chart)
        (comma_python_affine_offset ?chart)
        (comma_python_affine_denominator ?chart))"
    by (rule comma_python_affine_add_raw[OF chart_triple_positive]) simp
  have raw_chart_eq:
    "comma_python_affine_raw
      (comma_python_affine_scale ?chart)
      (comma_python_affine_offset ?chart)
      (comma_python_affine_denominator ?chart) = ?chart"
    by (cases ?chart) (simp add: comma_python_affine_raw_def)
  have add_chart:
    "comma_python_affine_equivalent
      (comma_python_affine_add ?chart comma_python_affine_zero) ?chart"
    using add_raw by (simp only: raw_chart_eq)
  have fragment_formula:
    "comma_python_fragment_weight_affine fragment =
      comma_python_affine_add
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment))
        (comma_python_constant_affine 0)"
    by (simp add: comma_python_fragment_weight_affine_def
        fragment_def comma_python_entry_sector_fragment_def Let_def)
  have affine_equiv:
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine fragment) ?chart"
    using sums add_chart fragment_formula by simp
  show ?thesis
    using affine_equiv
    by (simp add: chart_weight_def comma_python_chart_affine_weight_def)
qed

lemma comma_python_near_fragment_weight_affine_coefficient:
  fixes f p delta headroom :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and headroom: "1 \<le> headroom" "headroom \<le> 540"
    and step: "comma_weighted_step (p mod 924)
      (Comma_Near f delta headroom) = Comma_WNext successor weight"
  obtains increment where
    "comma_chart_value p successor =
      comma_chart_value p (Comma_Near f delta headroom) + increment"
    "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) successor weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine
        (comma_python_literal_fragment f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10)
          1 increment))
      (comma_python_chart_affine_weight 0 weight)"
proof -
  have weight_shape:
    "weight = Comma_Chart_Weight 0 0 1 1"
    using step by (auto simp: comma_weighted_step_def
      comma_weighted_step_with_headroom_def Let_def split: if_splits)
  obtain increment where endpoint:
    "comma_chart_value p successor =
      comma_chart_value p (Comma_Near f delta headroom) + increment"
    and record:
    "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) successor weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
    using comma_python_near_record_matches[OF f exponent headroom step] .
  have coefficient:
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine
        (comma_python_literal_fragment f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10)
          1 increment))
      (comma_python_chart_affine_weight 0 weight)"
    using weight_shape
    by (simp add: comma_python_literal_fragment_weight_affine_unit)
  show thesis using endpoint record coefficient by (rule that)
qed

definition comma_python_boundary_initial_position ::
  "comma_boundary_state \<Rightarrow> comma_finite_position" where
  "comma_python_boundary_initial_position = comma_finite_initial"

fun comma_python_position_affine ::
  "comma_finite_position \<Rightarrow> comma_python_affine_weight" where
  "comma_python_position_affine (Comma_Entry f delta offset) =
    comma_python_affine_normalize (int (f * 10 ^ delta)) (int offset) 1"
| "comma_python_position_affine (Comma_Near f delta headroom) =
    comma_python_affine_normalize
      (int ((f + 1) * 10 ^ delta)) (- int headroom) 1"

fun comma_python_boundary_source_affine ::
  "comma_boundary_state \<Rightarrow> comma_python_affine_weight" where
  "comma_python_boundary_source_affine source =
    (case source of
      (Comma_N,a,r) \<Rightarrow> comma_python_affine_normalize (int a) (-1) 1
    | (Comma_Z,a,r) \<Rightarrow> comma_python_affine_normalize (int a) 0 1)"

lemma comma_python_boundary_source_affine_binding:
  assumes valid: "comma_boundary_valid source"
  shows "comma_python_position_affine
      (comma_python_boundary_initial_position source) =
    comma_python_boundary_source_affine source"
proof -
  obtain kind a r where source: "source=(kind,a,r)"
    by (cases source) auto
  have a: "2 \<le> a" using valid by (simp add: source comma_boundary_valid_def)
  show ?thesis
    using source a
    by (cases kind)
      (simp_all add: comma_python_boundary_initial_position_def
        comma_finite_initial_def comma_python_boundary_source_affine.simps
        comma_python_affine_normalize_def Let_def)
qed

lemma comma_python_boundary_source_value_binding:
  fixes p :: nat
  assumes valid: "comma_boundary_valid source"
  shows "comma_chart_value p
      (comma_python_boundary_initial_position source) =
    comma_boundary_value source p"
  using comma_chart_initial_refines_boundary[OF valid, of p]
  by (simp add: comma_python_boundary_initial_position_def)

record comma_python_indexed_macro_output =
  comma_python_macro_source :: comma_boundary_state
  comma_python_macro_outcome :: comma_finite_outcome
  comma_python_macro_exponent_delta :: nat
  comma_python_macro_destination_a :: "nat option"
  comma_python_macro_weight :: comma_python_affine_weight
  comma_python_macro_endpoint :: comma_python_affine_weight
  comma_python_macro_ordered_children :: "comma_boundary_state list"
  comma_python_macro_fragments :: "comma_python_sector_fragment list"
  comma_python_macro_prefix_weights :: "comma_python_affine_weight list"
  comma_python_macro_prefix_displacements :: "comma_python_affine_weight list"

definition comma_python_make_indexed_macro_output ::
  "comma_boundary_state \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_python_sector_fragment list \<Rightarrow>
    comma_python_indexed_macro_output" where
  "comma_python_make_indexed_macro_output source outcome fragments =
    (let arrays=comma_python_publish_fragments fragments
     in \<lparr>comma_python_macro_source=source,
       comma_python_macro_outcome=outcome,
       comma_python_macro_exponent_delta=
         (case outcome of Comma_Fork_At a d \<Rightarrow> d
           | Comma_Landmine_At d \<Rightarrow> d),
       comma_python_macro_destination_a=
         (case outcome of Comma_Fork_At a d \<Rightarrow> Some a
           | Comma_Landmine_At d \<Rightarrow> None),
       comma_python_macro_weight=comma_python_published_total_weight fragments,
       comma_python_macro_endpoint=comma_python_affine_add
         (comma_python_boundary_source_affine source)
         (comma_python_published_total_displacement fragments),
       comma_python_macro_ordered_children=
         comma_native_boundary_children source outcome,
       comma_python_macro_fragments=fragments,
       comma_python_macro_prefix_weights=comma_python_published_weights arrays,
       comma_python_macro_prefix_displacements=
         comma_python_published_displacements arrays\<rparr>)"

lemma comma_python_indexed_macro_output_fields:
  "comma_python_macro_source
      (comma_python_make_indexed_macro_output source outcome fragments) = source"
  "comma_python_macro_outcome
      (comma_python_make_indexed_macro_output source outcome fragments) = outcome"
  "comma_python_macro_exponent_delta
      (comma_python_make_indexed_macro_output source outcome fragments) =
    (case outcome of Comma_Fork_At a d \<Rightarrow> d
      | Comma_Landmine_At d \<Rightarrow> d)"
  "comma_python_macro_destination_a
      (comma_python_make_indexed_macro_output source outcome fragments) =
    (case outcome of Comma_Fork_At a d \<Rightarrow> Some a
      | Comma_Landmine_At d \<Rightarrow> None)"
  "comma_python_macro_weight
      (comma_python_make_indexed_macro_output source outcome fragments) =
    foldl comma_python_affine_add comma_python_affine_zero
      (map comma_python_fragment_weight_affine fragments)"
  "comma_python_macro_endpoint
      (comma_python_make_indexed_macro_output source outcome fragments) =
    comma_python_affine_add (comma_python_boundary_source_affine source)
      (foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_displacement_affine fragments))"
  "comma_python_macro_ordered_children
      (comma_python_make_indexed_macro_output source outcome fragments) =
    comma_native_boundary_children source outcome"
  "comma_python_macro_fragments
      (comma_python_make_indexed_macro_output source outcome fragments) = fragments"
  "comma_python_macro_prefix_weights
      (comma_python_make_indexed_macro_output source outcome fragments) =
    comma_python_published_weights (comma_python_publish_fragments fragments)"
  "comma_python_macro_prefix_displacements
      (comma_python_make_indexed_macro_output source outcome fragments) =
    comma_python_published_displacements
      (comma_python_publish_fragments fragments)"
  by (simp_all add: comma_python_make_indexed_macro_output_def Let_def
      comma_python_published_total_weight_def
      comma_python_published_total_displacement_def
      comma_python_published_total_affine_fields)

definition comma_python_published_total_weight ::
  "comma_python_sector_fragment list \<Rightarrow> comma_python_affine_weight" where
  "comma_python_published_total_weight fragments =
    comma_python_published_weights
      (comma_python_publish_fragments fragments) ! length fragments"

definition comma_python_published_total_displacement ::
  "comma_python_sector_fragment list \<Rightarrow> comma_python_affine_weight" where
  "comma_python_published_total_displacement fragments =
    comma_python_published_displacements
      (comma_python_publish_fragments fragments) ! length fragments"

lemma comma_python_published_total_affine_fields:
  "comma_python_published_total_weight fragments =
    foldl comma_python_affine_add comma_python_affine_zero
      (map comma_python_fragment_weight_affine fragments)"
  "comma_python_published_total_displacement fragments =
    foldl comma_python_affine_add comma_python_affine_zero
      (map comma_python_fragment_displacement_affine fragments)"
  using comma_python_publish_fragments_nth[of "length fragments" fragments]
  by (simp_all add: comma_python_published_total_weight_def
      comma_python_published_total_displacement_def)

text \<open>The macro header now uses the repository's actual boundary tuple
and ordered child constructor.  The following bridge starts from either
runtime constructor, not only from the canonical decade root Entry 1 0 x.
For a crossing it composes the round prefix and its unit crossing edge with
the exact next-decade summary trace.\<close>

theorem comma_python_boundary_indexed_trace:
  assumes provider: "comma_semantic_decade_provider_exact provider"
    and valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  obtains rows outcome terminal where
    "comma_indexed_trace p (comma_finite_initial q) rows outcome terminal"
    "comma_semantic_boundary_step provider q = Some outcome"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have r_bound: "r<924"
    using valid by (simp add: q comma_boundary_valid_def)
  have source_valid: "comma_round_admitted (comma_finite_initial q)"
    using valid by (cases kind)
      (simp_all add: q comma_boundary_valid_def comma_finite_initial_def)
  have phase_r: "r mod 924=p mod 924"
    using phase q r_bound by simp
  obtain n terminal_position event where close:
      "comma_round_close r (comma_finite_initial q) =
        (n,terminal_position,event)"
    by (cases "comma_round_close r (comma_finite_initial q)") auto
  have event_valid: "event \<noteq> Comma_Round_Invalid"
    using comma_round_close_admitted(2)[OF close source_valid] .
  show thesis
  proof (cases event)
    case (Comma_Round_Fork a' delta)
    have close_fork:
      "comma_round_close r (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Fork a' delta)"
      using close Comma_Round_Fork by simp
    have finite:
      "comma_finite_step (r mod 924) terminal_position =
        Comma_Fork a' delta"
      using comma_round_close_refines_trace[OF close_fork] by simp
    have stop:
      "comma_weighted_step (p mod 924) terminal_position =
        Comma_WFork terminal_position a' delta"
      using comma_finite_terminal_weighted_shape[OF finite] phase_r by simp
    obtain weight where prefix:
        "comma_round_weighted_prefix p r n (comma_finite_initial q)
          terminal_position weight"
      using comma_round_close_has_weighted_prefix[OF close_fork] by blast
    obtain rows where trace:
        "comma_indexed_trace p (comma_finite_initial q) rows
          (Comma_Fork_At a' delta) terminal_position"
      using comma_round_weighted_prefix_indexed_trace_fork
        [OF phase_r prefix stop] by blast
    have selected:
      "comma_semantic_boundary_step provider q =
        Some (Comma_Fork_At a' delta)"
      using valid q close_fork
      by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps
        comma_boundary_valid_def)
    show thesis using trace selected by (rule that)
  next
    case (Comma_Round_Landmine delta)
    have close_landmine:
      "comma_round_close r (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Landmine delta)"
      using close Comma_Round_Landmine by simp
    have finite:
      "comma_finite_step (r mod 924) terminal_position =
        Comma_Landmine delta"
      using comma_round_close_refines_trace[OF close_landmine] by simp
    have stop:
      "comma_weighted_step (p mod 924) terminal_position =
        Comma_WLandmine terminal_position delta"
      using comma_finite_landmine_weighted_shape[OF finite] phase_r by simp
    obtain weight where prefix:
        "comma_round_weighted_prefix p r n (comma_finite_initial q)
          terminal_position weight"
      using comma_round_close_has_weighted_prefix[OF close_landmine] by blast
    obtain rows where trace:
        "comma_indexed_trace p (comma_finite_initial q) rows
          (Comma_Landmine_At delta) terminal_position"
      using comma_round_weighted_prefix_indexed_trace_landmine
        [OF phase_r prefix stop] by blast
    have selected:
      "comma_semantic_boundary_step provider q =
        Some (Comma_Landmine_At delta)"
      using valid q close_landmine
      by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps
        comma_boundary_valid_def)
    show thesis using trace selected by (rule that)
  next
    case (Comma_Round_Cross target)
    have close_cross:
      "comma_round_close r (comma_finite_initial q) =
        (n,terminal_position,Comma_Round_Cross target)"
      using close Comma_Round_Cross by simp
    obtain x where x_bound: "x \<le> 90"
      and target_shape:
        "target=Comma_Entry 1
          (Suc (comma_round_delta (comma_finite_initial q))) x"
      using comma_round_close_crossing_phase[OF close_cross source_valid]
      by blast
    have target_entry:
      "target=Comma_Entry 1 1 x"
      using target_shape by (cases kind)
        (simp_all add: q comma_finite_initial_def)
    have decade:
      "comma_decade_admitted (Comma_Decade ((r+1) mod 924) x)"
      using x_bound by simp
    obtain h tau where selected_summary:
        "provider (Comma_Decade ((r+1) mod 924) x)=Some (h,tau)"
      and height: "h \<le> 26"
      and exact:
        "comma_decade_exact_summary
          (Comma_Decade ((r+1) mod 924) x) h tau"
      by (rule comma_semantic_decade_provider_lookup[OF provider decade])
    have phase_next:
      "(r+1) mod 924=(p+1) mod 924"
    proof -
      have shifted:
        "((r mod 924)+1) mod 924=((p mod 924)+1) mod 924"
        using phase_r by (rule arg_cong)
      have r_rebase: "(r+1) mod 924=((r mod 924)+1) mod 924"
        by (rule mod_add_left_eq[symmetric])
      have p_rebase: "(p+1) mod 924=((p mod 924)+1) mod 924"
        by (rule mod_add_left_eq[symmetric])
      show ?thesis using shifted r_rebase p_rebase by simp
    qed
    have summary_binding:
      "Comma_Decade ((r+1) mod 924) x =
        Comma_Decade ((p+1) mod 924) x"
      using phase_next by simp
    have child_exponent: "5 \<le> p+1" using exponent by arith
    obtain tail_rows final_position where tail:
        "comma_indexed_trace (p+1) (Comma_Entry 1 0 x) tail_rows
          (comma_summary_outcome h tau)
          (comma_shift_position h final_position)"
      using comma_decade_summary_weighted_indexed_trace
        [OF exact decade child_exponent summary_binding] by blast
    have finite_next:
      "comma_finite_step (r mod 924) terminal_position =
        Comma_Next (Comma_Entry 1 1 x)"
      and crossing:
      "comma_round_crossing terminal_position (Comma_Entry 1 1 x)"
      using comma_round_close_refines_trace[OF close_cross] target_entry
      by simp_all
    have next:
      "comma_weighted_step (p mod 924) terminal_position =
        Comma_WNext (Comma_Entry 1 1 x)
          (Comma_Chart_Weight 0 0 1 1)"
    proof -
      have finite_p:
        "comma_finite_step (p mod 924) terminal_position =
          Comma_Next (Comma_Entry 1 1 x)"
        using finite_next phase_r by simp
      show ?thesis
        using comma_round_crossing_weight_unit[OF finite_p crossing] .
    qed
    have shifted_tail:
      "comma_indexed_trace p (Comma_Entry 1 1 x) tail_rows
        (comma_shift_weighted_outcome 1 (comma_summary_outcome h tau))
        (comma_shift_position 1 (comma_shift_position h final_position))"
      using comma_indexed_trace_shift_position[OF tail] by simp
    obtain prefix_weight where prefix:
        "comma_round_weighted_prefix p r n (comma_finite_initial q)
          terminal_position prefix_weight"
      using comma_round_close_has_weighted_prefix[OF close_cross] by blast
    obtain rows where trace:
        "comma_indexed_trace p (comma_finite_initial q) rows
          (comma_shift_weighted_outcome 1 (comma_summary_outcome h tau))
          (comma_shift_position 1 (comma_shift_position h final_position))"
      using comma_round_weighted_prefix_indexed_trace_continue
        [OF phase_r prefix next shifted_tail] by blast
    have outcome_eq:
      "comma_shift_weighted_outcome 1 (comma_summary_outcome h tau) =
        comma_summary_outcome (h+1) tau"
      by (cases tau) (simp_all add: comma_summary_outcome.simps)
    have terminal_eq:
      "comma_shift_position 1 (comma_shift_position h final_position) =
        comma_shift_position (h+1) final_position"
      by (cases final_position) (simp_all add: add.assoc)
    have selected:
      "comma_semantic_boundary_step provider q =
        Some (comma_summary_outcome (h+1) tau)"
      using valid q close_cross target_entry selected_summary x_bound
      by (simp add: comma_semantic_boundary_step_def
        comma_semantic_boundary_event_outcome.simps
        comma_boundary_valid_def)
    show thesis using trace outcome_eq terminal_eq selected
      by (rule that) (simp_all)
  next
    case Comma_Round_Invalid
    have False using event_valid Comma_Round_Invalid by simp
    then show thesis by contradiction
  qed
qed

theorem comma_python_boundary_indexed_macro_fields:
  assumes provider: "comma_semantic_decade_provider_exact provider"
    and valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  obtains events terminal outcome fragments macro where
    "comma_python_first_terminal_walk p (comma_finite_initial q)
      events outcome terminal"
    "comma_semantic_boundary_step provider q = Some outcome"
    "comma_python_writer_run p (comma_finite_initial q) None events outcome
      terminal fragments"
    "macro=comma_python_make_indexed_macro_output q outcome fragments"
    "comma_python_macro_source macro=q"
    "comma_python_macro_outcome macro=outcome"
    "comma_python_macro_exponent_delta macro=comma_native_outcome_delta outcome"
    "comma_python_macro_destination_a macro=
      (case outcome of Comma_Fork_At a d \<Rightarrow> Some a
        | Comma_Landmine_At d \<Rightarrow> None)"
    "comma_python_macro_ordered_children macro=
      comma_native_boundary_children q outcome"
    "comma_python_macro_weight macro=
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_weight_affine fragments)"
    "comma_python_macro_endpoint macro=
      comma_python_affine_add (comma_python_boundary_source_affine q)
        (foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine fragments))"
    "comma_python_macro_fragments macro=fragments"
    "comma_python_macro_prefix_weights macro=
      comma_python_published_weights (comma_python_publish_fragments fragments)"
    "comma_python_macro_prefix_displacements macro=
      comma_python_published_displacements
        (comma_python_publish_fragments fragments)"
    "length (comma_python_macro_prefix_weights macro)=Suc (length fragments)"
    "length (comma_python_macro_prefix_displacements macro)=Suc (length fragments)"
    "\<forall>i\<le>length fragments.
      comma_python_macro_prefix_weights macro ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take i fragments)) \<and>
      comma_python_macro_prefix_displacements macro ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine (take i fragments))"
    "comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
      sum_list (map (\<lambda>event. int (fst (comma_python_event_row p event))) events)"
    "comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
      int (comma_chart_value p terminal) - int (comma_boundary_value q p)"
proof -
  obtain rows outcome terminal where trace:
      "comma_indexed_trace p (comma_finite_initial q) rows outcome terminal"
    and selected:
      "comma_semantic_boundary_step provider q=Some outcome"
    using comma_python_boundary_indexed_trace[OF provider valid exponent phase]
    by blast
  obtain events where walk:
      "comma_python_first_terminal_walk p (comma_finite_initial q)
        events outcome terminal"
    and rows: "rows=map (comma_python_event_row p) events"
    using comma_indexed_trace_to_python_first_terminal_walk[OF trace] by blast
  have source_admitted:
      "comma_round_admitted (comma_finite_initial q)"
  proof -
    obtain kind a r where q': "q=(kind,a,r)" by (cases q) auto
    show ?thesis using valid q'
      by (cases kind)
        (auto simp: comma_boundary_valid_def comma_finite_initial_def
          comma_round_admitted.simps)
  qed
  have pending: "comma_python_pending_phase p (comma_finite_initial q) None"
    by (simp add: comma_python_pending_phase_def)
  obtain fragments where run:
      "comma_python_writer_run p (comma_finite_initial q) None events outcome
        terminal fragments"
    using comma_python_first_terminal_walk_writer
      [OF exponent walk source_admitted pending] by blast
  let ?macro="comma_python_make_indexed_macro_output q outcome fragments"
  have macro_fields:
      "comma_python_macro_source ?macro=q"
      "comma_python_macro_outcome ?macro=outcome"
      "comma_python_macro_exponent_delta ?macro=comma_native_outcome_delta outcome"
      "comma_python_macro_destination_a ?macro=
        (case outcome of Comma_Fork_At a d \<Rightarrow> Some a
          | Comma_Landmine_At d \<Rightarrow> None)"
      "comma_python_macro_ordered_children ?macro=
        comma_native_boundary_children q outcome"
      "comma_python_macro_weight ?macro=
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine fragments)"
      "comma_python_macro_endpoint ?macro=
        comma_python_affine_add (comma_python_boundary_source_affine q)
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine fragments))"
      "comma_python_macro_fragments ?macro=fragments"
      "comma_python_macro_prefix_weights ?macro=
        comma_python_published_weights (comma_python_publish_fragments fragments)"
      "comma_python_macro_prefix_displacements ?macro=
        comma_python_published_displacements
          (comma_python_publish_fragments fragments)"
    using comma_python_indexed_macro_output_fields[of q outcome fragments]
    by (simp_all add: comma_native_outcome_delta_def)
  have lengths:
      "length (comma_python_macro_prefix_weights ?macro)=Suc (length fragments)"
      "length (comma_python_macro_prefix_displacements ?macro)=Suc (length fragments)"
    using macro_fields(9,10) comma_python_publish_fragments_lengths[of fragments]
    by simp_all
  have prefixes: "\<forall>i\<le>length fragments.
      comma_python_macro_prefix_weights ?macro ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take i fragments)) \<and>
      comma_python_macro_prefix_displacements ?macro ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine (take i fragments))"
  proof (intro allI impI)
    fix i
    assume index: "i \<le> length fragments"
    note nth = comma_python_publish_fragments_nth[OF index]
    show "comma_python_macro_prefix_weights ?macro ! i =
          foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)) \<and>
        comma_python_macro_prefix_displacements ?macro ! i =
          foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine (take i fragments))"
      using macro_fields(9,10) nth by simp
  qed
  note accounting = comma_python_writer_run_accounting[OF run]
  have chart_displacement:
      "sum_list (map snd rows) =
        int (comma_chart_value p terminal) -
          int (comma_chart_value p (comma_finite_initial q))"
    by (rule comma_indexed_trace_displacement[OF trace])
  have source_value:
      "comma_chart_value p (comma_finite_initial q)=comma_boundary_value q p"
    by (rule comma_python_boundary_source_value_binding[OF valid])
  have observed_weight:
      "comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
        sum_list (map
          (\<lambda>event. int (fst (comma_python_event_row p event))) events)"
    using accounting(1) by (simp add: comma_python_pending_weight_at_scale_def
        comma_python_fragment_list_weight_at_scale_def
        comma_python_flush_near_def)
  have observed_displacement:
      "comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
        int (comma_chart_value p terminal) - int (comma_boundary_value q p)"
    using accounting(2) chart_displacement rows source_value
    by (simp add: comma_python_pending_displacement_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_flush_near_def)
  show thesis
    using walk selected run macro_fields lengths prefixes
      observed_weight observed_displacement
    by (rule that)
qed
lemmas comma_python_producer_coefficients_oracle_audit_bundle = comma_python_entry_fragment_weight_affine_coefficient comma_python_near_fragment_weight_affine_coefficient comma_python_boundary_indexed_trace comma_python_boundary_indexed_macro_fields
ML \<open>val _ = if null (Thm_Deps.all_oracles @{thms comma_python_producer_coefficients_oracle_audit_bundle}) then () else error "Comma_Semantic_Producer_Coefficients local oracle audit failed"\<close>
end
