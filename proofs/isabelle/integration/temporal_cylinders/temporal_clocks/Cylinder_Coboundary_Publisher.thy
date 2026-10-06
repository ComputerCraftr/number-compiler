theory Cylinder_Coboundary_Publisher
  imports Cylinder_Innovation_Transport
begin

text \<open>
  Whole-function coefficient coboundary for one reverse/add publisher step.
  The carry function is represented by its outgoing boundaries Q_i=C_(i+1).
  The correction (z-b)Q therefore includes the leading carry coefficient at
  index m without storing a digit or carry word.
\<close>

definition cylinder_window :: "nat => int => bool" where
  "cylinder_window m i = (0 \<le> i \<and> i < int m)"

definition cylinder_coboundary ::
    "int => coefficient_function => coefficient_function" where
  "cylinder_coboundary b q i = q (i - 1) - b * q i"

definition cylinder_normalized ::
    "int => coefficient_function => coefficient_function => coefficient_function" where
  "cylinder_normalized b p q =
    innovation_add p (cylinder_coboundary b q)"

definition cylinder_next ::
    "int => coefficient_function => coefficient_function => coefficient_function" where
  "cylinder_next d p q =
    innovation_add (cylinder_normalized 10 p q)
      (innovation_reflect d (cylinder_normalized 10 p q))"

definition cylinder_carry_encoding ::
    "nat => coefficient_function => coefficient_function => bool" where
  "cylinder_carry_encoding m c q =
    (\<forall>i. q i = (if cylinder_window m i then c (i + 1) else 0))"

definition cylinder_source_symmetric ::
    "nat => coefficient_function => bool" where
  "cylinder_source_symmetric m p =
    (\<forall>i. cylinder_window m i --> p i = p (int m - 1 - i))"

definition cylinder_source_supported ::
    "nat => coefficient_function => bool" where
  "cylinder_source_supported m p =
    (\<forall>i. \<not> cylinder_window m i --> p i = 0)"

lemma cylinder_reflect_add:
  "innovation_reflect d (innovation_add f g) =
    innovation_add (innovation_reflect d f) (innovation_reflect d g)"
  by (rule ext) (simp add: innovation_reflect_def innovation_add_def)

lemma cylinder_source_reflect_no_growth:
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
  shows "innovation_reflect (int m - 1) p = p"
proof (rule ext)
  fix i
  show "innovation_reflect (int m - 1) p i = p i"
  proof (cases "cylinder_window m i")
    case True
    then have mirror: "p i = p (int m - 1 - i)"
      using symmetric unfolding cylinder_source_symmetric_def by blast
    then show ?thesis by (simp add: innovation_reflect_def)
  next
    case False
    have mirror_outside:
      "\<not> cylinder_window m (int m - 1 - i)"
    proof
      assume mirror_inside: "cylinder_window m (int m - 1 - i)"
      have lower: "0 \<le> int m - 1 - i"
        using mirror_inside unfolding cylinder_window_def by arith
      have upper: "int m - 1 - i < int m"
        using mirror_inside unfolding cylinder_window_def by arith
      have left: "i < int m"
        using lower by arith
      have right: "0 \<le> i"
        using upper by arith
      have "cylinder_window m i"
        unfolding cylinder_window_def using left right by simp
      with False show False by simp
    qed
    have source_zero: "p i = 0"
      using supported False unfolding cylinder_source_supported_def by blast
    have mirror_zero: "p (int m - 1 - i) = 0"
      using supported mirror_outside unfolding cylinder_source_supported_def by blast
    then show ?thesis using source_zero
      by (simp add: innovation_reflect_def)
  qed
qed

lemma cylinder_source_reflect_growth:
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
  shows "innovation_reflect (int m) p = innovation_translate 1 p"
proof (rule ext)
  fix i
  have no_growth:
    "innovation_reflect (int m - 1) p (i - 1) = p (i - 1)"
    using fun_cong[
      OF cylinder_source_reflect_no_growth[OF positive symmetric supported],
      of "i - 1"] by simp
  show "innovation_reflect (int m) p i = innovation_translate 1 p i"
    using no_growth
    by (simp add: innovation_reflect_def innovation_translate_def)
qed

lemma cylinder_source_plus_reflect_growth:
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
  shows "innovation_add p (innovation_reflect (int m) p) =
    innovation_neighbor p"
  using cylinder_source_reflect_growth[OF positive symmetric supported]
  by (simp add: innovation_add_def innovation_neighbor_def
      innovation_translate_def fun_eq_iff)

lemma cylinder_normalized_active:
  assumes encoding: "cylinder_carry_encoding m c q"
      and initial: "c 0 = 0"
      and active: "cylinder_window m i"
  shows "cylinder_normalized b p q i =
    p i + c i - b * c (i + 1)"
proof (cases "i = 0")
  case True
  then show ?thesis
    using encoding active initial
    unfolding cylinder_normalized_def cylinder_coboundary_def
      innovation_add_def cylinder_carry_encoding_def cylinder_window_def
    by simp
next
  case False
  have previous: "cylinder_window m (i - 1)"
    using active False unfolding cylinder_window_def by arith
  have qi: "q i = c (i + 1)"
    using encoding active unfolding cylinder_carry_encoding_def by simp
  have qprevious: "q (i - 1) = c i"
    using encoding previous unfolding cylinder_carry_encoding_def by simp
  show ?thesis
    using qi qprevious
    unfolding cylinder_normalized_def cylinder_coboundary_def innovation_add_def
    by simp
qed

definition cylinder_forward_carry ::
    "int => nat => coefficient_function => coefficient_function => bool" where
  "cylinder_forward_carry b m p c =
    (\<forall>i. cylinder_window m i -->
      c (i + 1) = (p i + c i) div b)"

lemma cylinder_normalized_active_mod:
  fixes b :: int
  assumes base: "0 < b"
      and encoding: "cylinder_carry_encoding m c q"
      and initial: "c 0 = 0"
      and active: "cylinder_window m i"
      and forward: "cylinder_forward_carry b m p c"
  shows "cylinder_normalized b p q i = (p i + c i) mod b"
    and "0 \<le> cylinder_normalized b p q i"
    and "cylinder_normalized b p q i < b"
proof -
  have normalized:
    "cylinder_normalized b p q i = p i + c i - b * c (i + 1)"
    using cylinder_normalized_active[OF encoding initial active] .
  have quotient: "c (i + 1) = (p i + c i) div b"
    using forward active unfolding cylinder_forward_carry_def by blast
  have split:
    "p i + c i = b * ((p i + c i) div b) + (p i + c i) mod b"
    using div_mult_mod_eq[of "p i + c i" b]
    by (simp add: algebra_simps)
  have exact:
    "p i + c i - b * c (i + 1) = (p i + c i) mod b"
    using split by (simp only: quotient; linarith)
  show equality: "cylinder_normalized b p q i = (p i + c i) mod b"
    using normalized exact by simp
  show "0 \<le> cylinder_normalized b p q i"
    using equality base by simp
  show "cylinder_normalized b p q i < b"
    using equality base by simp
qed

lemma cylinder_normalized_leading_carry:
  assumes positive: "0 < m"
      and encoding: "cylinder_carry_encoding m c q"
      and supported: "cylinder_source_supported m p"
      and terminal: "c (int m) = g"
      and carry_bit: "g = 0 \<or> g = 1"
  shows "cylinder_normalized b p q (int m) = g"
proof -
  have last: "cylinder_window m (int m - 1)"
    unfolding cylinder_window_def using positive by arith
  have qlast: "q (int m - 1) = g"
    using encoding last terminal
    unfolding cylinder_carry_encoding_def by simp
  have qoutside: "q (int m) = 0"
    using encoding unfolding cylinder_carry_encoding_def cylinder_window_def by simp
  have poutside: "p (int m) = 0"
    using supported unfolding cylinder_source_supported_def cylinder_window_def by simp
  show ?thesis
    using qlast qoutside poutside
    unfolding cylinder_normalized_def cylinder_coboundary_def innovation_add_def
    by simp
qed

lemma cylinder_normalized_exterior_zero:
  assumes encoding: "cylinder_carry_encoding m c q"
      and supported: "cylinder_source_supported m p"
      and exterior: "i < 0 \<or> int m < i"
  shows "cylinder_normalized b p q i = 0"
proof (cases "i < 0")
  case True
  have outside: "\<not> cylinder_window m i"
    using True unfolding cylinder_window_def by arith
  have pzero: "p i = 0"
    using supported outside unfolding cylinder_source_supported_def by blast
  have qzero: "q i = 0"
    using encoding unfolding cylinder_carry_encoding_def cylinder_window_def
    using True by simp
  have qprevious: "q (i - 1) = 0"
    using encoding unfolding cylinder_carry_encoding_def cylinder_window_def
    using True by simp
  show ?thesis
    using pzero qzero qprevious
    unfolding cylinder_normalized_def cylinder_coboundary_def innovation_add_def
    by simp
next
  case False
  have greater: "int m < i"
    using exterior False by blast
  have outside: "\<not> cylinder_window m i"
    using greater unfolding cylinder_window_def by arith
  have pzero: "p i = 0"
    using supported outside unfolding cylinder_source_supported_def by blast
  have qzero: "q i = 0"
    using encoding unfolding cylinder_carry_encoding_def cylinder_window_def
    using greater by simp
  have previous_outside: "int m \<le> i - 1" using greater by arith
  have qprevious: "q (i - 1) = 0"
    using encoding unfolding cylinder_carry_encoding_def cylinder_window_def
    using previous_outside by simp
  show ?thesis
    using pzero qzero qprevious
    unfolding cylinder_normalized_def cylinder_coboundary_def innovation_add_def
    by simp
qed

text \<open>
  This last identity is algebraic for arbitrary outgoing support q and a
  chosen binary growth flag.  The source-derived carry and emission bridge
  is proved separately; no unused carry hypotheses provide admission here.
\<close>

theorem cylinder_full_coboundary:
  fixes q :: coefficient_function
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
      and carry_bit: "g = 0 \<or> g = 1"
  defines "e \<equiv> cylinder_coboundary 10 q"
  shows "cylinder_next (int m + g - 1) p q =
    innovation_add (if g = 0 then innovation_double p else innovation_neighbor p)
      (innovation_add e (innovation_reflect (int m + g - 1) e))"
proof -
  have source_zero:
    "innovation_reflect (int m - 1) p = p"
    using cylinder_source_reflect_no_growth[OF positive symmetric supported] .
  have source_growth:
    "innovation_add p (innovation_reflect (int m) p) =
      innovation_neighbor p"
    using cylinder_source_plus_reflect_growth[OF positive symmetric supported] .
  have expand:
    "cylinder_next (int m + g - 1) p q =
      innovation_add
        (innovation_add p e)
        (innovation_reflect (int m + g - 1)
          (innovation_add p e))"
    unfolding cylinder_next_def cylinder_normalized_def e_def
      cylinder_coboundary_def innovation_add_def by simp
  have reflected:
    "innovation_reflect (int m + g - 1)
        (innovation_add p e) =
      innovation_add (innovation_reflect (int m + g - 1) p)
        (innovation_reflect (int m + g - 1) e)"
    using cylinder_reflect_add .
  have normal_form:
    "cylinder_next (int m + g - 1) p q =
      innovation_add
        (innovation_add p
          (innovation_reflect (int m + g - 1) p))
        (innovation_add e
          (innovation_reflect (int m + g - 1) e))"
    using expand reflected
    by (simp add: innovation_add_def innovation_reflect_def
        fun_eq_iff algebra_simps)
  have g_cases: "g = 0 \<or> g = 1" using carry_bit .
  then show ?thesis
  proof
    assume gzero: "g = 0"
    have source: "innovation_reflect (int m + g - 1) p = p"
      using source_zero gzero by simp
    show ?thesis
      using normal_form source gzero
      by (simp add: innovation_double_def innovation_add_def
          fun_eq_iff algebra_simps)
  next
    assume gone: "g = 1"
    have source: "innovation_add p
        (innovation_reflect (int m + g - 1) p) =
        innovation_neighbor p"
      using source_growth gone by simp
    show ?thesis
      using normal_form source gone
      by (simp add: innovation_neighbor_def innovation_add_def
          fun_eq_iff algebra_simps)
  qed
qed

ML \<open>
  val checked = @{thms cylinder_source_reflect_no_growth
    cylinder_source_reflect_growth cylinder_source_plus_reflect_growth
    cylinder_normalized_active cylinder_normalized_active_mod
    cylinder_normalized_leading_carry cylinder_normalized_exterior_zero
    cylinder_full_coboundary};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Cylinder coboundary publisher depends on an oracle";
\<close>

end
