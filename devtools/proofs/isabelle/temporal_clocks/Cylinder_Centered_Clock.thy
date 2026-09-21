theory Cylinder_Centered_Clock
  imports Cylinder_Source_Coboundary
begin

text \<open>
  Centered residual identities for the decimal source cylinder.  This theory
  keeps the source/carry factorization explicit.  It proves coefficient-level
  self-advance and a small signed-carry reset lemma; it does not construct a
  source extractor, a temporal normal form, or a pumping bound.
\<close>

definition centered_indicator :: "nat => coefficient_function" where
  "centered_indicator m i = (if cylinder_window m i then 1 else 0)"

definition centered_residual ::
    "coefficient_function => nat => coefficient_function" where
  "centered_residual p m i = p i - 9 * centered_indicator m i"

definition centered_scale :: "int => coefficient_function => coefficient_function" where
  "centered_scale a f i = a * f i"

definition centered_multiplier ::
    "nat => coefficient_function => coefficient_function" where
  "centered_multiplier g f =
    (if g = 0 then innovation_double f else innovation_neighbor f)"

definition centered_beta ::
    "nat => nat => coefficient_function => coefficient_function" where
  "centered_beta m g q =
    innovation_add (cylinder_coboundary 10 q)
      (innovation_reflect (int m + int g - 1)
        (cylinder_coboundary 10 q))"

definition centered_correction ::
    "nat => nat => coefficient_function" where
  "centered_correction m g =
    centered_scale 9
      (innovation_add (centered_multiplier g (centered_indicator m))
        (centered_scale (-1) (centered_indicator (m + g))))"

definition centered_carry_step :: "int => int => int" where
  "centered_carry_step s c =
    (if s < 0 then 0 else if s = 0 then c else 1)"

definition centered_domain :: "int => carry_domain" where
  "centered_domain d = (if d < 0 then Below else if d = 0 then Equal else Above)"

lemma centered_domain_source:
  "centered_domain (int s - 9) = domain s"
  by (auto simp: centered_domain_def domain_def)

lemma centered_step_monoid:
  "centered_carry_step d (int (carry_bit c)) =
    int (carry_bit (carry_apply (centered_domain d) c))"
  by (cases c; simp add: centered_carry_step_def centered_domain_def carry_bit_def)

lemma centered_indicator_zero:
  "centered_indicator 0 = (\<lambda>i. 0)"
  by (rule ext) (simp add: centered_indicator_def cylinder_window_def)

lemma centered_multiplier_zero:
  "centered_multiplier 0 f = innovation_double f"
  by (simp add: centered_multiplier_def)

lemma centered_multiplier_one:
  "centered_multiplier 1 f = innovation_neighbor f"
  by (simp add: centered_multiplier_def)

lemma centered_carry_step_range:
  assumes "c = 0 \<or> c = 1"
  shows "centered_carry_step s c = 0 \<or>
    centered_carry_step s c = 1"
  using assms by (simp add: centered_carry_step_def split: if_splits)

lemma centered_carry_step_neutral:
  "centered_carry_step 0 c = c"
  by (simp add: centered_carry_step_def)

lemma centered_carry_step_source:
  assumes valid: "source_pair_valid ss" and bound: "j < length ss"
  shows "centered_carry_step (int (ss ! j) - 9)
      (source_carry_state ss (int j)) =
      source_carry_state ss (int j + 1)"
proof -
  have division:
    "source_carry_state ss (int j + 1) =
      (int (ss ! j) + source_carry_state ss (int j)) div 10"
    using source_carry_step_div[OF valid bound] .
  have pair: "ss ! j < 19"
    using source_pair_bound[OF valid bound] .
  have state: "source_carry_state ss (int j) = 0 \<or>
      source_carry_state ss (int j) = 1"
    unfolding source_carry_state_def
    using bound by (simp add: carry_bit_def split: if_splits)
  show ?thesis
    using division pair state
    by (simp add: centered_carry_step_def split: if_splits; arith)
qed

lemma centered_indicator_neighbor:
  assumes positive: "0 < m"
  shows "innovation_neighbor (centered_indicator m) =
      innovation_add (centered_indicator (m + 1))
        (innovation_translate 1 (centered_indicator (m - 1)))"
proof (rule ext)
  fix i :: int
  have predecessor: "int (m - 1) = int m - 1"
    using positive by simp
  show "innovation_neighbor (centered_indicator m) i =
      innovation_add (centered_indicator (m + 1))
        (innovation_translate 1 (centered_indicator (m - 1))) i"
    using positive
    by (auto simp: innovation_neighbor_def innovation_add_def predecessor
      innovation_translate_def centered_indicator_def cylinder_window_def
      split: if_splits; linarith)
qed

lemma centered_correction_zero:
  "centered_correction m 0 = centered_scale 9 (centered_indicator m)"
  by (rule ext; simp add: centered_correction_def centered_multiplier_def
      centered_scale_def centered_indicator_def cylinder_window_def
      innovation_double_def innovation_add_def
      split: if_splits; arith)

lemma centered_correction_one:
  assumes positive: "0 < m"
  shows "centered_correction m 1 =
      centered_scale 9 (innovation_translate 1 (centered_indicator (m - 1)))"
proof -
  have neighbor:
    "innovation_neighbor (centered_indicator m) =
      innovation_add (centered_indicator (m + 1))
        (innovation_translate 1 (centered_indicator (m - 1)))"
    using centered_indicator_neighbor[OF positive] .
  show ?thesis
    unfolding centered_correction_def centered_multiplier_def
    by (simp add: neighbor centered_scale_def innovation_add_def fun_eq_iff)
qed

theorem centered_self_advance:
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
      and carry_bit: "g = 0 \<or> g = 1"
  shows "centered_residual
      (cylinder_next (int m + int g - 1) p q) (m + g) =
      innovation_add (centered_multiplier g (centered_residual p m))
        (innovation_add (centered_beta m g q)
          (centered_correction m g))"
proof -
  have carry_int: "int g = 0 \<or> int g = 1"
    using carry_bit by simp
  have publisher:
    "cylinder_next (int m + int g - 1) p q =
      innovation_add (centered_multiplier g p) (centered_beta m g q)"
    using cylinder_full_coboundary[OF positive symmetric supported carry_int,
      of q] by (simp add: centered_multiplier_def centered_beta_def)
  show ?thesis
  proof (rule ext)
    fix i :: int
    show "centered_residual
        (cylinder_next (int m + int g - 1) p q) (m + g) i =
        innovation_add (centered_multiplier g (centered_residual p m))
          (innovation_add (centered_beta m g q) (centered_correction m g)) i"
      using fun_cong[OF publisher, of i]
      by (simp add: centered_residual_def centered_correction_def
      centered_multiplier_def centered_scale_def centered_beta_def
      innovation_add_def innovation_double_def innovation_neighbor_def
      centered_indicator_def cylinder_window_def algebra_simps)
  qed
qed

fun centered_signed_run :: "(nat => int) => int => nat => int" where
  "centered_signed_run r c 0 = c"
| "centered_signed_run r c (Suc n) =
    centered_carry_step (r n) (centered_signed_run r c n)"

definition centered_factorization ::
    "(nat => int) => nat => int => (nat => int) => bool" where
  "centered_factorization r h d tail =
    ((\<forall>i<h. r i = 0) \<and> r h = d \<and>
      (\<forall>j. r (h + Suc j) = tail j))"

definition centered_reset_sign :: "int => int" where
  "centered_reset_sign d = (if 0 < d then 1 else 0)"

lemma centered_signed_run_neutral:
  assumes neutral: "\<forall>i<h. r i = 0"
      and incoming: "c = 0 \<or> c = 1"
  shows "centered_signed_run r c h = c"
  using neutral incoming
proof (induction h arbitrary: c)
  case 0
  then show ?case by simp
next
  case (Suc h)
  have previous: "\<forall>i<h. r i = 0"
    using Suc.prems(1) by (simp add: less_Suc_eq)
  have at: "r h = 0"
    using Suc.prems(1) by simp
  have zero: "centered_signed_run r c h = c"
    using Suc.IH[OF previous Suc.prems(2)] .
  show ?case
    using at zero by (simp add: centered_carry_step_def)
qed

lemma centered_first_reset:
  assumes factor: "centered_factorization r h d tail"
      and incoming: "c = 0 \<or> c = 1"
      and nonzero: "d \<noteq> 0"
  shows "centered_signed_run r c (Suc h) =
      centered_reset_sign d"
proof -
  have neutral: "\<forall>i<h. r i = 0"
    using factor unfolding centered_factorization_def by blast
  have at: "r h = d"
    using factor unfolding centered_factorization_def by blast
  have reset: "centered_signed_run r c h = c"
    using centered_signed_run_neutral[OF neutral incoming] .
  show ?thesis
    using at reset nonzero
    by (simp add: centered_reset_sign_def centered_carry_step_def
      split: if_splits; arith)
qed

lemma centered_tail_transport:
  assumes factor: "centered_factorization r h d tail"
      and incoming: "c = 0 \<or> c = 1"
      and nonzero: "d \<noteq> 0"
  shows "centered_signed_run r c (h + Suc k) =
      centered_signed_run tail (centered_reset_sign d) k"
proof (induction k)
  case 0
  show ?case using centered_first_reset[OF factor incoming nonzero] by simp
next
  case (Suc k)
  have tail_value: "r (h + Suc k) = tail k"
    using factor unfolding centered_factorization_def by blast
  show ?case using Suc.IH tail_value by simp
qed

definition centered_outgoing ::
    "nat => (nat => int) => int => nat => int" where
  "centered_outgoing ell r c i =
    (if i < ell then centered_signed_run r c (Suc i) else 0)"

text \<open>
  Coefficient form of C_ell = c E_h + b z^h + z^(h+1) C_(ell-h-1).
  The incoming bit is preserved on the neutral prefix, and the tail still
  denotes the entire remaining residual, not just its signs.
\<close>

lemma centered_outgoing_split:
  assumes factor: "centered_factorization r h d tail"
      and incoming: "c = 0 \<or> c = 1"
      and nonzero: "d \<noteq> 0"
      and active: "h < ell"
  shows "centered_outgoing ell r c i =
    (if i < h then c else if i = h then centered_reset_sign d
     else centered_outgoing (ell - h - 1) tail
       (centered_reset_sign d) (i - h - 1))"
proof (cases "i < h")
  case True
  have prefix: "\<forall>j<Suc i. r j = 0"
    using factor True unfolding centered_factorization_def by auto
  show ?thesis
    using centered_signed_run_neutral[OF prefix incoming] True active
    by (simp add: centered_outgoing_def)
next
  case False
  show ?thesis
  proof (cases "i = h")
    case True
    show ?thesis using centered_first_reset[OF factor incoming nonzero] True active
      by (simp add: centered_outgoing_def)
  next
    case unequal: False
    have greater: "h < i" using False unequal by arith
    have index: "h + Suc (i - h) = Suc i" using greater by arith
    have tail_index: "Suc (i - h - 1) = i - h" using greater by arith
    have window: "(i - h - 1 < ell - h - 1) = (i < ell)"
      using greater active by arith
    have transported:
      "centered_signed_run r c (Suc i) =
       centered_signed_run tail (centered_reset_sign d) (i - h)"
      using centered_tail_transport[OF factor incoming nonzero, of "i - h"]
      by (simp only: index)
    show ?thesis
      by (simp only: centered_outgoing_def False unequal if_False
          window tail_index transported)
  qed
qed

lemma centered_outgoing_neutral:
  assumes neutral: "\<forall>j<ell. r j = 0"
      and incoming: "c = 0 \<or> c = 1"
  shows "centered_outgoing ell r c i = (if i < ell then c else 0)"
proof (cases "i < ell")
  case True
  have prefix: "\<forall>j<Suc i. r j = 0" using neutral True by auto
  show ?thesis using centered_signed_run_neutral[OF prefix incoming] True
    by (simp only: centered_outgoing_def if_True)
next
  case False
  then show ?thesis by (simp add: centered_outgoing_def)
qed

text \<open>
  Boundary-relative carry events use exactly the outgoing carry above.
  Their neutral value is a terminal boundary, not a temporal identity.
\<close>

definition centered_jump ::
    "nat => (nat => int) => int => nat => int" where
  "centered_jump ell r c i = centered_outgoing ell r c i -
    (if i = 0 then c else centered_outgoing ell r c (i - 1))"

lemma centered_jump_neutral:
  assumes neutral: "\<forall>j<ell. r j = 0"
      and incoming: "c = 0 \<or> c = 1"
  shows "centered_jump ell r c i = (if i = ell then -c else 0)"
  unfolding centered_jump_def
  by (simp add: centered_outgoing_neutral[OF neutral incoming];
      auto split: if_splits; arith)

lemma centered_jump_split:
  assumes factor: "centered_factorization r h d tail"
      and incoming: "c = 0 \<or> c = 1"
      and nonzero: "d \<noteq> 0"
      and active: "h < ell"
  shows "centered_jump ell r c i =
    (if i < h then 0 else if i = h then centered_reset_sign d - c
     else centered_jump (ell - h - 1) tail
       (centered_reset_sign d) (i - h - 1))"
  unfolding centered_jump_def
  by (simp only: centered_outgoing_split[OF factor incoming nonzero active];
      auto split: if_splits; arith)

lemma centered_jump_same_reset:
  assumes factor: "centered_factorization r h d tail"
      and incoming: "c = 0 \<or> c = 1"
      and nonzero: "d \<noteq> 0"
      and active: "h < ell"
      and same: "centered_reset_sign d = c"
  shows "centered_jump ell r c i =
    (if i \<le> h then 0 else centered_jump (ell - h - 1) tail c (i - h - 1))"
  using centered_jump_split[OF factor incoming nonzero active, of i] same
  by auto

lemma centered_source_run:
  assumes valid: "source_pair_valid ss" and bound: "n \<le> length ss"
  shows "centered_signed_run (\<lambda>j. int (ss ! j) - 9) 0 n =
      source_carry_state ss (int n)"
  using bound
proof (induction n)
  case 0
  then show ?case by (simp add: source_initial_carry)
next
  case (Suc n)
  have active: "n < length ss" using Suc.prems by simp
  have previous: "centered_signed_run (\<lambda>j. int (ss ! j) - 9) 0 n =
      source_carry_state ss (int n)"
    using Suc.IH active by simp
  show ?case using centered_carry_step_source[OF valid active]
    by (simp add: previous add.commute)
qed

definition centered_event :: "coefficient_function => coefficient_function" where
  "centered_event f i = f i - f (i - 1)"

lemma centered_outgoing_source:
  assumes valid: "source_pair_valid ss"
  shows "centered_outgoing (length ss) (\<lambda>j. int (ss ! j) - 9) 0 i =
    source_carry_out ss (int i)"
proof (cases "i < length ss")
  case True
  have bound: "Suc i \<le> length ss" using True by simp
  show ?thesis
    using centered_source_run[OF valid bound] True
    by (simp add: centered_outgoing_def source_carry_out_def
        cylinder_window_def add.commute)
next
  case False
  then show ?thesis by (simp add: centered_outgoing_def
      source_carry_out_def cylinder_window_def)
qed

lemma centered_jump_source:
  assumes valid: "source_pair_valid ss"
  shows "centered_jump (length ss) (\<lambda>j. int (ss ! j) - 9) 0 i =
    centered_event (source_carry_out ss) (int i)"
proof (cases i)
  case 0
  then show ?thesis
    by (simp add: centered_jump_def centered_outgoing_source[OF valid]
        centered_event_def source_carry_out_def cylinder_window_def)
next
  case (Suc n)
  then show ?thesis
    by (simp add: centered_jump_def centered_outgoing_source[OF valid]
        centered_event_def)
qed

lemma centered_event_add:
  "centered_event (innovation_add f g) =
    innovation_add (centered_event f) (centered_event g)"
  by (rule ext; simp add: centered_event_def innovation_add_def)

lemma centered_event_scale:
  "centered_event (centered_scale a f) = centered_scale a (centered_event f)"
  by (rule ext; simp add: centered_event_def centered_scale_def algebra_simps)

lemma centered_event_neighbor:
  "centered_event (innovation_neighbor f) = innovation_neighbor (centered_event f)"
  by (rule ext; simp add: centered_event_def innovation_neighbor_def algebra_simps)

lemma centered_event_reflect:
  "centered_event (innovation_reflect d f) =
    centered_scale (-1) (innovation_reflect (d + 1) (centered_event f))"
  by (rule ext; simp add: centered_event_def innovation_reflect_def
      centered_scale_def algebra_simps)

lemma centered_event_interval:
  "centered_event (centered_indicator m) i =
    (if i = 0 then 1 else 0) - (if i = int m then 1 else 0)"
  by (auto simp: centered_event_def centered_indicator_def cylinder_window_def
      split: if_splits; linarith)

lemma centered_event_first_nonzero:
  assumes prefix: "\<forall>i<h. f i = 0"
  shows "centered_event f h = f h \<and> (\<forall>i<h. centered_event f i = 0)"
  using prefix by (auto simp: centered_event_def)

lemma centered_event_zero_iff:
  assumes supported: "cylinder_source_supported m f"
  shows "centered_event f = (\<lambda>i. 0) \<longleftrightarrow> f = (\<lambda>i. 0)"
proof
  assume zero: "centered_event f = (\<lambda>i. 0)"
  have recurrence: "f i = f (i - 1)" for i
    using fun_cong[OF zero, of i] by (simp add: centered_event_def)
  have initial: "f (-1) = 0"
    using supported by (simp add: cylinder_source_supported_def cylinder_window_def)
  have natural: "f (int n) = 0" for n
  proof (induction n)
    case 0
    then show ?case using recurrence[of 0] initial by simp
  next
    case (Suc n)
    then show ?case using recurrence[of "int (Suc n)"] by simp
  qed
  show "f = (\<lambda>i. 0)"
  proof (rule ext)
    fix i :: int
    show "f i = 0"
    proof (cases "i < 0")
      case True
      then show ?thesis using supported
        by (simp add: cylinder_source_supported_def cylinder_window_def)
    next
      case False
      then show ?thesis using natural[of "nat i"] by simp
    qed
  qed
next
  assume "f = (\<lambda>i. 0)"
  then show "centered_event f = (\<lambda>i. 0)"
    by (simp add: centered_event_def fun_eq_iff)
qed

lemma centered_event_coboundary:
  "centered_event (cylinder_coboundary b q) =
    cylinder_coboundary b (centered_event q)"
  by (rule ext; simp add: centered_event_def cylinder_coboundary_def algebra_simps)

lemma centered_event_beta:
  "centered_event (centered_beta m g q) =
    innovation_add (cylinder_coboundary 10 (centered_event q))
      (centered_scale (-1) (innovation_reflect (int m + int g)
        (cylinder_coboundary 10 (centered_event q))))"
  unfolding centered_beta_def
  by (simp add: centered_event_add centered_event_reflect centered_event_coboundary)

definition centered_spatial_tail ::
    "coefficient_function => int => int => coefficient_function" where
  "centered_spatial_tail f h d i = f (i + h + 1) - (if i = -1 then d else 0)"

lemma centered_event_tail_transport:
  "centered_event (centered_spatial_tail f h d) i =
    centered_event f (i + h + 1) - (if i = -1 then d else 0)
      + (if i = 0 then d else 0)"
  by (auto simp: centered_event_def centered_spatial_tail_def algebra_simps)

lemma centered_event_translate:
  "centered_event (innovation_translate a f) =
    innovation_translate a (centered_event f)"
  by (rule ext; simp add: centered_event_def innovation_translate_def algebra_simps)

lemma centered_event_multiplier:
  "centered_event (centered_multiplier g f) =
    centered_multiplier g (centered_event f)"
  by (rule ext; simp add: centered_event_def centered_multiplier_def
      innovation_double_def innovation_neighbor_def algebra_simps)

lemma centered_event_correction:
  assumes positive: "0 < m" and bit: "g = 0 \<or> g = 1"
  shows "centered_event (centered_correction m g) i =
    9 * ((if i = int g then 1 else 0) - (if i = int m then 1 else 0))"
proof (cases "g = 0")
  case True
  then show ?thesis by (simp add: centered_correction_zero centered_event_scale
      centered_scale_def centered_event_interval)
next
  case False
  have one: "g = 1" using bit False by blast
  have predecessor: "int (m - 1) = int m - 1" using positive by simp
  show ?thesis
    using predecessor
    unfolding one centered_correction_one[OF positive] centered_event_scale
        centered_event_translate centered_scale_def innovation_translate_def
    by (auto simp: centered_event_interval split: if_splits; linarith)
qed

theorem centered_event_successor:
  assumes positive: "0 < m"
      and symmetric: "cylinder_source_symmetric m p"
      and supported: "cylinder_source_supported m p"
      and bit: "g = 0 \<or> g = 1"
  shows "centered_event (centered_residual
      (cylinder_next (int m + int g - 1) p q) (m + g)) i =
    centered_multiplier g (centered_event (centered_residual p m)) i
    + cylinder_coboundary 10 (centered_event q) i
    - cylinder_coboundary 10 (centered_event q) (int m + int g - i)
    + 9 * ((if i = int g then 1 else 0) - (if i = int m then 1 else 0))"
proof -
  have before: "centered_residual
      (cylinder_next (int m + int g - 1) p q) (m + g) =
      innovation_add (centered_multiplier g (centered_residual p m))
        (innovation_add (centered_beta m g q) (centered_correction m g))"
    using centered_self_advance[OF positive symmetric supported bit] .
  show ?thesis
    unfolding before centered_event_add centered_event_multiplier centered_event_beta
    by (simp add: centered_event_correction[OF positive bit]
        innovation_add_def centered_scale_def innovation_reflect_def algebra_simps)
qed

text \<open>
  These event identities justify exact interval endpoint cancellation and
  transport. Equal normalized packets may cancel; different radial packets
  can still require higher jets. Neither a bounded jet dimension nor grammar
  closure follows from losslessness of the finite-difference coordinate.

  The factorization hypothesis is intentionally an input to these reset
  lemmas.  No theorem here claims that an extractor finds @{term h}, @{term d}
  or @{term tail}, or that doing so has bounded cost.
\<close>

ML \<open>
  val checked = @{thms centered_carry_step_range centered_carry_step_neutral
    centered_carry_step_source centered_indicator_neighbor
    centered_correction_zero centered_correction_one centered_self_advance
    centered_signed_run_neutral centered_first_reset centered_tail_transport
    centered_outgoing_split centered_outgoing_neutral centered_source_run
    centered_jump_neutral centered_jump_split centered_jump_same_reset
    centered_outgoing_source centered_jump_source
    centered_domain_source centered_step_monoid centered_event_add
    centered_event_scale centered_event_neighbor centered_event_reflect
    centered_event_interval centered_event_first_nonzero centered_event_zero_iff
    centered_event_coboundary centered_event_beta centered_event_tail_transport
    centered_event_translate centered_event_multiplier centered_event_correction
    centered_event_successor};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Centered clock theory depends on an oracle";
\<close>

end
