theory Collatz_Harmonic_Ports
  imports Shared_Carry_Dynamics.Shared_Carry_Tape
    Shared_Carry_Dynamics.Shared_Affine_Birth_Tape
begin

text \<open>An exact spatial projection from an emitting Collatz action onto
the two Boolean carry wires.  The three reachable carry ports are encoded by
(False,False), (True,False), and (True,True).  Emissions may retain a richer
harmonic response, but forgetting them commutes with spatial composition.

The nilpotence results below concern dependence on one already-present linear
harmonic source.  They do not construct the source-dependent births and do not assert nonlinear
temporal successor closure.  The spatial radix-64 cell index
and the binary temporal index are also kept distinct; relating their formal
variables requires the separate restriction z-cell = z-bit^6.\<close>

section \<open>Carry boundaries derived from exact domain geometry\<close>

definition domain_wires :: "carry_domain \<Rightarrow> carry_domain \<Rightarrow> carry_wires" where
  "domain_wires low high = (carry_apply low, carry_apply high)"

definition nonempty_collatz_generators :: "carry_wires set" where
  "nonempty_collatz_generators = {
    domain_wires Below Below,
    domain_wires Equal Below,
    domain_wires Above Below,
    domain_wires Above Equal,
    domain_wires Above Above}"

lemma five_generator_output_rows:
  "map (apply_wires (domain_wires Below Below)) [0,1,2] = [0,0,0]"
  "map (apply_wires (domain_wires Equal Below)) [0,1,2] = [0,1,1]"
  "map (apply_wires (domain_wires Above Below)) [0,1,2] = [1,1,1]"
  "map (apply_wires (domain_wires Above Equal)) [0,1,2] = [1,1,2]"
  "map (apply_wires (domain_wires Above Above)) [0,1,2] = [2,2,2]"
  by (simp_all add: apply_wires_def domain_wires_def carry_bits_def
      carry_from_bits_def)

lemma five_generators_are_valid:
  assumes "w \<in> nonempty_collatz_generators"
  shows "valid_wires w"
  using assms
  by (auto simp: nonempty_collatz_generators_def domain_wires_def
      valid_wires_def staircase_port_def)

lemma empty_interval_identity_row:
  "map (apply_wires (domain_wires Equal Equal)) [0,1,2] = [0,1,2]"
  by (simp add: apply_wires_def domain_wires_def carry_bits_def
      carry_from_bits_def)



lemma domain_wires_injective [simp]:
  "domain_wires a b = domain_wires c d \<longleftrightarrow> a=c \<and> b=d"
  by (cases a; cases b; cases c; cases d;
      auto simp: domain_wires_def fun_eq_iff)

lemma compose_domain_wires [simp]:
  "compose_wires (domain_wires a b) (domain_wires c d) =
    domain_wires (carry_then c a) (carry_then d b)"
  by (simp add: compose_wires_def domain_wires_def fun_eq_iff
      comp_def carry_then_apply)

section \<open>Closed spatial carry and phase macros\<close>

definition f5_spatial_alphabet_at :: "nat \<Rightarrow> (carry_wires \<times> nat) set" where
  "f5_spatial_alphabet_at n =
    ({domain_wires Below Below, domain_wires Above Below,
      domain_wires Above Above} \<times> {0..<5}) \<union>
    {(domain_wires Equal Below, n mod 5), (domain_wires Above Equal, 0)}"

definition f5_spatial_macros :: "(carry_wires \<times> nat) set" where
  "f5_spatial_macros = f5_spatial_alphabet_at 0"

definition compose_f5_spatial ::
    "carry_wires \<times> nat \<Rightarrow> carry_wires \<times> nat \<Rightarrow>
      carry_wires \<times> nat" where
  "compose_f5_spatial a b =
    (compose_wires (fst a) (fst b), (snd a + snd b) mod 5)"

lemma nonempty_generators_idempotent:
  assumes "w \<in> nonempty_collatz_generators"
  shows "compose_wires w w = w"
  using assms
  by (auto simp: nonempty_collatz_generators_def compose_wires_def
      domain_wires_def fun_eq_iff comp_def)


lemma f5_spatial_length_transport:
  assumes "a \<in> f5_spatial_alphabet_at n" "b \<in> f5_spatial_alphabet_at m"
  shows "compose_f5_spatial a b \<in> f5_spatial_alphabet_at (n+m)"
  using assms
  by (auto simp: f5_spatial_alphabet_at_def compose_f5_spatial_def
      carry_then_def mod_add_eq)

lemma f5_spatial_macros_closed:
  assumes "a \<in> f5_spatial_macros" "b \<in> f5_spatial_macros"
  shows "compose_f5_spatial a b \<in> f5_spatial_macros"
  using f5_spatial_length_transport[of a 0 b 0] assms
  by (simp add: f5_spatial_macros_def)

lemma f5_spatial_alphabet_card:
  "card (f5_spatial_alphabet_at n) = 17"
  by (simp add: f5_spatial_alphabet_at_def card_Un_disjoint disjoint_iff)

lemma f5_spatial_macros_card:
  "card f5_spatial_macros = 17"
  by (simp add: f5_spatial_macros_def f5_spatial_alphabet_card)

fun f5_spatial_repeat :: "nat \<Rightarrow> carry_wires \<times> nat \<Rightarrow>
    carry_wires \<times> nat" where
  "f5_spatial_repeat 0 a = (domain_wires Equal Equal, 0)"
| "f5_spatial_repeat (Suc n) a = compose_f5_spatial a (f5_spatial_repeat n a)"

lemma f5_spatial_repeat_closed_form:
  assumes "w \<in> nonempty_collatz_generators" "0 < n"
  shows "f5_spatial_repeat n (w,p) = (w, (n*p) mod 5)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Suc.prems
      by (simp add: compose_f5_spatial_def compose_wires_def domain_wires_def comp_def)
  next
    case (Suc k)
    have previous: "f5_spatial_repeat n (w,p) = (w, (n*p) mod 5)"
      using Suc.IH Suc.prems Suc by simp
    show ?thesis
      using nonempty_generators_idempotent[OF Suc.prems(1)]
      by (simp add: previous compose_f5_spatial_def mod_add_right_eq
          add.commute)
  qed
qed

text \<open>These are spatial macros of supplied occurrences. The fixed catalog
is not a finite temporal state space. Birth emissions and Hensel source
admission are not erased by this closure or repetition rule.\<close>

section \<open>Collatz two-wire prefix projection\<close>

definition collatz_prefix_carry ::
    "carry_wires list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_prefix_carry geometry i incoming =
    wire_word_scan incoming (take i geometry)"

theorem collatz_prefix_carry_composition:
  "collatz_prefix_carry geometry (i+j) incoming =
    wire_word_scan (collatz_prefix_carry geometry i incoming)
      (take j (drop i geometry))"
  by (simp add: collatz_prefix_carry_def take_add)

theorem collatz_prefix_carry_is_action_projection:
  assumes valid: "\<forall>wire \<in> set geometry. valid_wires wire"
      and incoming: "incoming < 3"
  shows "collatz_prefix_carry geometry i incoming =
    apply_wires (wire_word_action (take i geometry)) incoming"
proof -
  have valid_take:
      "\<forall>wire \<in> set (take i geometry). valid_wires wire"
  proof
    fix wire
    assume "wire \<in> set (take i geometry)"
    then have "wire \<in> set geometry" by (rule in_set_takeD)
    then show "valid_wires wire" using valid by blast
  qed
  have exact:
      "apply_wires (wire_word_action (take i geometry)) incoming =
        wire_word_scan incoming (take i geometry)"
    by (rule wire_word_action_exact[OF valid_take incoming])
  show ?thesis using exact by (simp add: collatz_prefix_carry_def)
qed

text \<open>Each Collatz carry boundary is therefore a prefix projection of the
same exact two-wire geometry.  This does not say that a harmonic projection
reconstructs pointwise geometry, nor does it establish temporal closure.\<close>

text \<open>Generic linear harmonic transport.  The element u represents any
phase multiplier, including a chosen inverse of z.  No property of u is needed:
five transported copies of y vanish solely because y^5 is zero.\<close>

text \<open>The future-consumer theorem permits erasing a dead input jet even
when more supplied actions follow. It does not replace the source authority
selecting those future births. In particular, a first-failure predicate on the
past trajectory need not factor through the final jet; its composed guard
remains a separate retained consumer. The number five counts multiplications,
not physical divisions or arbitrary accelerated blocks.\<close>

text \<open>This is the right-constant reduction implemented by the primary-jet
composition kernel. The suffix births are supplied and source-bound elsewhere;
this reduction does not discover them, or identify distinct source occurrences.
An Antihydra odd-event block with gap a contains a multiplications by three;
ordinary Collatz physical even steps contain none.\<close>

text \<open>The last corollary compares runs with the same event list, hence the
same births.  It must not be read as saying that source-dependent nonlinear
births die in five steps or that Hensel-admissible refinement has depth five.\<close>

ML \<open>
  val checked = @{thms five_generator_output_rows
    five_generators_are_valid empty_interval_identity_row
    collatz_prefix_carry_composition
    collatz_prefix_carry_is_action_projection
    domain_wires_injective compose_domain_wires
    nonempty_generators_idempotent f5_spatial_length_transport
    f5_spatial_alphabet_card f5_spatial_macros_closed
    f5_spatial_macros_card f5_spatial_repeat_closed_form};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz harmonic port proof depends on an oracle";
\<close>

end
