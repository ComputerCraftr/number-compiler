theory Comma_Boundary_Primitives
  imports Comma_Period_Guard Comma_Child_Classification
begin

text \<open>Neutral boundary states and complete literal child arithmetic.
These definitions are shared by the weighted chart and the bounded scalar
reference; neither depends on a temporal macro constructor.\<close>

text \<open>Boundary values are carried with their actual decimal exponent.
Only the constructor tag, leading coefficient, and exponent residue are
finite semantic coordinates; elapsed weights and endpoint values are not.\<close>

datatype comma_boundary_kind = Comma_N | Comma_Z

type_synonym comma_boundary_state = "comma_boundary_kind \<times> nat \<times> nat"

definition comma_boundary_states :: "comma_boundary_state list" where
  "comma_boundary_states =
    [(kind,a,r). kind \<leftarrow> [Comma_N,Comma_Z],
      a \<leftarrow> [2..<10], r \<leftarrow> [0..<924]]"

definition comma_boundary_valid :: "comma_boundary_state \<Rightarrow> bool" where
  "comma_boundary_valid q \<longleftrightarrow>
    (case q of (kind,a,r) \<Rightarrow> 2 \<le> a \<and> a \<le> 9 \<and> r < 924)"

definition comma_boundary_value :: "comma_boundary_state \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_boundary_value q p =
    (case q of (kind,a,r) \<Rightarrow>
      a * 10 ^ p - (if kind = Comma_N then 1 else 0))"

definition comma_boundary_sample_exponent :: "comma_boundary_state \<Rightarrow> nat" where
  "comma_boundary_sample_exponent q =
    (case q of (kind,a,r) \<Rightarrow> if r < 5 then r + 924 else r)"

lemma comma_boundary_states_set:
  "set comma_boundary_states = {q. comma_boundary_valid q}"
proof -
  have product_set: "set [(kind,a,r). kind \<leftarrow> xs,
      a \<leftarrow> ys, r \<leftarrow> zs] =
      {(kind,a,r) | kind a r. kind \<in> set xs \<and>
        a \<in> set ys \<and> r \<in> set zs}"
    for xs ys zs
    by auto
  have member: "((kind,a,r) \<in> set comma_boundary_states) \<longleftrightarrow>
      kind \<in> set [Comma_N,Comma_Z] \<and>
      a \<in> set [2..<10] \<and> r \<in> set [0..<924]"
    for kind a r
    unfolding comma_boundary_states_def
    by (simp only: product_set) auto
  have kind_member: "kind \<in> set [Comma_N,Comma_Z]" for kind
    by (cases kind) simp_all
  show ?thesis
    using member kind_member by (auto simp: comma_boundary_valid_def set_upt
      split: prod.splits)
qed

lemma comma_boundary_states_card: "length comma_boundary_states = 14784"
  by (simp add: comma_boundary_states_def)

lemma comma_boundary_sample_admitted:
  assumes "comma_boundary_valid q"
  shows "5 \<le> comma_boundary_sample_exponent q"
    "comma_boundary_sample_exponent q mod 924 = (case q of (_,_,r) \<Rightarrow> r)"
  using assms by (auto simp: comma_boundary_valid_def
      comma_boundary_sample_exponent_def split: prod.splits if_splits)

lemma comma_near_boundary_sector:
  assumes "2 \<le> a" "a \<le> 9" "1 \<le> p"
  shows "comma_sector (a - 1) p (comma_near_boundary a p)"
proof -
  have product: "a * 10 ^ p = (a - 1) * 10 ^ p + 10 ^ p"
    using assms by (simp add: algebra_simps)
  have power: "1 \<le> (10::nat) ^ p" by simp
  show ?thesis using assms product power
    by (auto simp: comma_sector_def comma_near_boundary_def; arith)
qed

lemma comma_zero_boundary_sector:
  assumes "2 \<le> a" "a \<le> 9"
  shows "comma_sector a p (comma_zero_boundary a p)"
  using assms by (auto simp: comma_sector_def comma_zero_boundary_def)

lemma comma_boundary_source_sector:
  assumes valid: "comma_boundary_valid q" and exponent: "5 \<le> p"
  shows "comma_sector
      (case q of (kind,a,r) \<Rightarrow> if kind = Comma_N then a - 1 else a)
      p (comma_boundary_value q p)"
proof -
  obtain kind a r where fields: "q = (kind,a,r)"
    by (cases q) auto
  have a: "2 \<le> a" "a \<le> 9"
    using valid by (simp_all add: fields comma_boundary_valid_def)
  show ?thesis
  proof (cases kind)
    case Comma_N
    then show ?thesis
      using comma_near_boundary_sector[OF a(1) a(2), of p] exponent
      by (simp add: fields comma_boundary_value_def
          comma_near_boundary_def)
  next
    case Comma_Z
    then show ?thesis
      using comma_zero_boundary_sector[OF a(1) a(2), of p]
      by (simp add: fields comma_boundary_value_def
          comma_zero_boundary_def)
  qed
qed

text \<open>The ordered executable child list has exactly the literal
children in every large decimal sector.  This is the only local branch
classifier used by the macro constructor.\<close>

definition comma_large_children :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "comma_large_children f p k =
    (let d = k mod 10; H = comma_headroom f p k in
      if f < 9 then
        (let low = k + 10 * d + f in
          if H > 10 * d + f + 1 then [low]
          else if H = 10 * d + f + 1 then [low,low+1]
          else [low+1])
      else if H > 10 * d + 9 then [k + 10 * d + 9]
      else if H \<le> 10 * d + 1 then [k + 10 * d + 1]
      else [])"

theorem comma_large_children_complete:
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
  shows "target \<in> set (comma_large_children f p k) \<longleftrightarrow>
    comma_child k target"
proof (cases "f < 9")
  case True
  show ?thesis
    using comma_below_nine_complete_children[OF source True exponent,
      of target] True
    by (auto simp: comma_large_children_def Let_def True split: if_splits)
next
  case False
  have nine: "f = 9" using source False
    by (auto simp: comma_sector_def)
  show ?thesis
    using comma_nine_complete_children[OF source[unfolded nine] exponent,
      of target] nine
    by (auto simp: comma_large_children_def Let_def nine split: if_splits)
qed

lemma comma_large_children_fork:
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and two: "length (comma_large_children f p k) = 2"
  shows "f < 9"
    "comma_large_children f p k =
      [comma_near_boundary (f + 1) p, comma_zero_boundary (f + 1) p]"
proof -
  have below: "f < 9"
    using two by (auto simp: comma_large_children_def Let_def split: if_splits)
  have boundary: "comma_headroom f p k = 10 * (k mod 10) + f + 1"
    using two below by (auto simp: comma_large_children_def Let_def
      split: if_splits)
  have near: "k + 10 * (k mod 10) + f =
      comma_near_boundary (f + 1) p"
    and zero: "k + 10 * (k mod 10) + f + 1 =
      comma_zero_boundary (f + 1) p"
    using comma_fork_normal_form_from_headroom[OF source _ below boundary]
      exponent by auto
  show "f < 9" by (rule below)
  show "comma_large_children f p k =
      [comma_near_boundary (f + 1) p, comma_zero_boundary (f + 1) p]"
    using two below boundary near zero
    by (simp add: comma_large_children_def Let_def)
qed

lemma comma_large_children_landmine:
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and empty: "comma_large_children f p k = []"
  shows "f = 9" "1 \<le> k mod 10" "k mod 10 \<le> 8"
    "k = 10 ^ (p + 1) - (10 + 9 * (k mod 10))"
proof -
  have nine: "f = 9"
    using source empty by (auto simp: comma_sector_def
      comma_large_children_def Let_def split: if_splits)
  have lower: "10 * (k mod 10) + 1 < comma_headroom 9 p k"
    and upper: "comma_headroom 9 p k \<le> 10 * (k mod 10) + 9"
    using empty by (auto simp: nine comma_large_children_def Let_def
      split: if_splits)
  show "f = 9" by (rule nine)
  show "1 \<le> k mod 10" "k mod 10 \<le> 8"
    "k = 10 ^ (p + 1) - (10 + 9 * (k mod 10))"
    using comma_nine_sector_landmine_normal_form[OF source[unfolded nine]
      _ lower upper] exponent by auto
qed

lemma comma_cycle_length_admitted:
  assumes f: "1 \<le> f" "f \<le> 9"
  shows "0 < comma_cycle_length f"
    "10 dvd comma_cycle_length f * f"
proof -
  let ?g = "gcd f 10"
  have g_pos: "0 < ?g" by simp
  have g_ten: "?g dvd 10" by simp
  have g_f: "?g dvd f" by simp
  obtain a where ten: "10 = ?g * a"
    using g_ten by (auto simp: dvd_def)
  obtain b where fv: "f = ?g * b"
    using g_f by (auto simp: dvd_def)
  have a_pos: "0 < a" using ten by (cases a) auto
  have length: "comma_cycle_length f = a"
  proof -
    have "comma_cycle_length f = 10 div ?g"
      by (simp add: comma_cycle_length_def)
    also have "... = (?g * a) div ?g" using ten by simp
    also have "... = a" using g_pos by simp
    finally show ?thesis .
  qed
  show "0 < comma_cycle_length f" using length a_pos by simp
  have "comma_cycle_length f * f = a * (?g * b)"
    using length fv by simp
  also have "... = (?g * a) * b" by (simp add: mult_ac)
  also have "... = 10 * b" using ten by simp
  finally have "comma_cycle_length f * f = 10 * b" .
  then show "10 dvd comma_cycle_length f * f" by simp
qed

lemma comma_period_displacement_admitted:
  assumes "0 < f" "0 < L"
  shows "0 < comma_period_displacement f d L"
proof -
  obtain j where L: "L = Suc j" using assms(2)
    by (cases L) auto
  show ?thesis using assms(1)
    by (simp add: L comma_period_displacement_succ)
qed

lemma comma_fixed_iter_complete_cycles:
  assumes closes: "10 dvd L * f"
  shows "comma_fixed_iter f (c * L) k =
    k + c * comma_period_displacement f (k mod 10) L"
proof -
  have "comma_period_displacement f (k mod 10) (c * L) =
    c * comma_period_displacement f (k mod 10) L"
    using comma_period_displacement_repeated[OF closes,
      of "k mod 10" c 0]
    by (simp add: comma_period_displacement_def)
  then show ?thesis by (simp add: comma_fixed_iter_displacement)
qed

lemma comma_singleton_step_chart:
  fixes H d f' p' :: nat and same :: bool
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and singleton: "comma_large_children f p k = [target]"
  defines "H \<equiv> comma_headroom f p k"
    and "d \<equiv> k mod 10"
    and "same \<equiv> (if f < 9 then H > 10 * d + f + 1
      else H > 10 * d + 9)"
    and "f' \<equiv> (if same then f else if f < 9 then f + 1 else 1)"
    and "p' \<equiv> (if same \<or> f < 9 then p else Suc p)"
  shows "comma_child k target" "comma_sector f' p' target" "2 \<le> p'"
proof -
  show "comma_child k target"
    using comma_large_children_complete[OF source exponent, of target]
      singleton by simp
  show "2 \<le> p'" using exponent by (simp add: p'_def)
  show "comma_sector f' p' target"
  proof (cases "f < 9")
    case True
    have less_nine: "f < 9" using True .
    let ?low = "k + 10 * d + f"
    let ?high = "?low + 1"
    let ?threshold = "10 * d + f + 1"
    show ?thesis
    proof (cases "H > ?threshold")
      case True
      have target_eq: "target = ?low"
        using singleton less_nine True
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector f p ?low"
        using comma_current_sector_candidate[OF source less_nine]
          True by (simp add: H_def d_def)
      then show ?thesis
        using less_nine True target_eq by (simp add: f'_def p'_def same_def)
    next
      case False
      have unequal: "H \<noteq> ?threshold"
        using singleton less_nine False
        by (auto simp: comma_large_children_def H_def d_def Let_def)
      have atmost: "H \<le> ?threshold" using False by simp
      have target_eq: "target = ?high"
        using singleton less_nine False unequal
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector (f + 1) p ?high"
        using comma_below_nine_next_sector_candidate[OF source less_nine exponent]
          atmost by (simp add: H_def d_def)
      then show ?thesis
        using less_nine False target_eq by (simp add: f'_def p'_def same_def)
    qed
  next
    case False
    have nine: "f = 9" using source False
      by (auto simp: comma_sector_def)
    let ?low = "k + 10 * d + 9"
    let ?high = "k + 10 * d + 1"
    show ?thesis
    proof (cases "H > 10 * d + 9")
      case True
      have target_eq: "target = ?low"
        using singleton True nine
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector 9 p ?low"
        using comma_nine_same_sector_candidate[OF source[unfolded nine]]
          True nine by (simp add: H_def d_def)
      then show ?thesis
        using nine True target_eq by (simp add: f'_def p'_def same_def)
    next
      case False
      have low: "H \<le> 10 * d + 1"
        using singleton False nine
        by (auto simp: comma_large_children_def H_def d_def Let_def
            split: if_splits)
      have target_eq: "target = ?high"
        using singleton False nine low
        by (simp add: comma_large_children_def H_def d_def Let_def)
      have "comma_sector 1 (Suc p) ?high"
        using comma_nine_power_crossing_candidate
          [OF source[unfolded nine] exponent] low nine
        by (simp add: H_def d_def)
      then show ?thesis
        using nine False target_eq by (simp add: f'_def p'_def same_def)
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_boundary_states_set comma_boundary_states_card
      comma_boundary_sample_admitted comma_boundary_source_sector
      comma_large_children_complete comma_large_children_fork
      comma_large_children_landmine comma_cycle_length_admitted
      comma_period_displacement_admitted comma_fixed_iter_complete_cycles
      comma_singleton_step_chart})
    then () else error "Comma boundary primitives depend on an oracle";
\<close>

end
