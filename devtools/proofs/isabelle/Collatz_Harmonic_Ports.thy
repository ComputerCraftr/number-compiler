theory Collatz_Harmonic_Ports
  imports Reverse_Carry_Harmonic_Ports
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

definition domain_prefix_carry ::
    "carry_domain list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool" where
  "domain_prefix_carry geometry i incoming =
    carry_finish incoming (take i geometry)"

theorem domain_prefix_carry_composition:
  "domain_prefix_carry geometry (i+j) incoming =
    carry_finish (domain_prefix_carry geometry i incoming)
      (take j (drop i geometry))"
  by (simp add: domain_prefix_carry_def take_add)

theorem all_equal_prefix_preserves_incoming:
  assumes "take i geometry = replicate i Equal"
  shows "domain_prefix_carry geometry i incoming = incoming"
  using assms by (simp add: domain_prefix_carry_def)

theorem last_decisive_domain_determines_prefix_carry:
  assumes prefix: "take i geometry = before @ d # replicate tail Equal"
      and decisive: "d \<noteq> Equal"
  shows "domain_prefix_carry geometry i incoming = (d = Above)"
  using decisive prefix
  by (cases d; simp_all add: domain_prefix_carry_def)

corollary last_below_resets_prefix_carry:
  assumes "take i geometry = before @ Below # replicate tail Equal"
  shows "domain_prefix_carry geometry i incoming = False"
proof -
  have "domain_prefix_carry geometry i incoming = (Below = Above)"
    by (rule last_decisive_domain_determines_prefix_carry[OF assms]) simp
  then show ?thesis by simp
qed

corollary last_above_sets_prefix_carry:
  assumes "take i geometry = before @ Above # replicate tail Equal"
  shows "domain_prefix_carry geometry i incoming = True"
proof -
  have "domain_prefix_carry geometry i incoming = (Above = Above)"
    by (rule last_decisive_domain_determines_prefix_carry[OF assms]) simp
  then show ?thesis by simp
qed

text \<open>Thus each pointwise Boolean carry boundary is a prefix query on the
same domain word.  The theorem introduces no independent carry-state field.\<close>

type_synonym carry_wires = "(bool \<Rightarrow> bool) \<times> (bool \<Rightarrow> bool)"

definition carry_bits :: "nat \<Rightarrow> bool \<times> bool" where
  "carry_bits c = (1 \<le> c, c = 2)"

definition staircase_port :: "bool \<times> bool \<Rightarrow> bool" where
  "staircase_port p \<longleftrightarrow> (snd p \<longrightarrow> fst p)"

definition carry_from_bits :: "bool \<times> bool \<Rightarrow> nat" where
  "carry_from_bits p = (if fst p then 1 else 0) + (if snd p then 1 else 0)"

definition apply_wires :: "carry_wires \<Rightarrow> nat \<Rightarrow> nat" where
  "apply_wires w c = carry_from_bits
    (fst w (fst (carry_bits c)), snd w (snd (carry_bits c)))"

definition compose_wires :: "carry_wires \<Rightarrow> carry_wires \<Rightarrow> carry_wires" where
  "compose_wires left right =
    (fst right \<circ> fst left, snd right \<circ> snd left)"

definition valid_wires :: "carry_wires \<Rightarrow> bool" where
  "valid_wires w \<longleftrightarrow>
    (\<forall>p. staircase_port p \<longrightarrow>
      staircase_port (fst w (fst p), snd w (snd p)))"

lemma three_reachable_carry_ports:
  assumes "c < 3"
  shows "staircase_port (carry_bits c)"
    and "carry_from_bits (carry_bits c) = c"
proof -
  have cases: "c = 0 \<or> c = 1 \<or> c = 2" using assms by arith
  then show "staircase_port (carry_bits c)"
    by (auto simp: carry_bits_def staircase_port_def)
  from cases show "carry_from_bits (carry_bits c) = c"
    by (auto simp: carry_bits_def carry_from_bits_def)
qed

lemma valid_wires_stay_reachable:
  assumes "valid_wires w" "c < 3"
  shows "apply_wires w c < 3"
proof -
  have source: "staircase_port (carry_bits c)"
    using assms(2) by (rule three_reachable_carry_ports)
  have target: "staircase_port
      (fst w (fst (carry_bits c)), snd w (snd (carry_bits c)))"
    using assms(1) source by (auto simp: valid_wires_def)
  show ?thesis
    using target by (cases "fst w (fst (carry_bits c))";
        cases "snd w (snd (carry_bits c))";
        simp_all add: apply_wires_def carry_from_bits_def staircase_port_def)
qed

lemma valid_wires_compose:
  assumes "valid_wires left" "valid_wires right"
  shows "valid_wires (compose_wires left right)"
  using assms
  by (auto simp: valid_wires_def compose_wires_def staircase_port_def)

theorem carry_projection_spatial_composition:
  assumes "valid_wires left" "valid_wires right" "c < 3"
  shows "apply_wires (compose_wires left right) c =
    apply_wires right (apply_wires left c)"
proof -
  let ?p = "(fst left (fst (carry_bits c)),
      snd left (snd (carry_bits c)))"
  have source: "staircase_port (carry_bits c)"
    using assms(3) by (rule three_reachable_carry_ports)
  have middle: "staircase_port ?p"
    using assms(1) source by (auto simp: valid_wires_def)
  have middle_bound: "carry_from_bits ?p < 3"
    using middle by (cases "fst ?p"; cases "snd ?p";
        simp_all add: carry_from_bits_def staircase_port_def)
  have encode_middle: "carry_bits (carry_from_bits ?p) = ?p"
    using middle by (cases "fst ?p"; cases "snd ?p";
        simp_all add: carry_bits_def carry_from_bits_def staircase_port_def)
  show ?thesis
    using encode_middle
    by (simp add: apply_wires_def compose_wires_def comp_def)
qed

record 'a emitting_carry_action =
  action_wires :: carry_wires
  action_emission :: "nat \<Rightarrow> 'a"

definition compose_emitting ::
    "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a emitting_carry_action \<Rightarrow>
      'a emitting_carry_action \<Rightarrow> 'a emitting_carry_action" where
  "compose_emitting add left right = \<lparr>
    action_wires = compose_wires (action_wires left) (action_wires right),
    action_emission = (\<lambda>c. add (action_emission left c)
      (action_emission right (apply_wires (action_wires left) c))) \<rparr>"

definition carry_projection :: "'a emitting_carry_action \<Rightarrow> carry_wires" where
  "carry_projection action = action_wires action"

theorem emitting_action_projects_to_carry_composition:
  "carry_projection (compose_emitting add left right) =
    compose_wires (carry_projection left) (carry_projection right)"
  by (simp add: carry_projection_def compose_emitting_def)

corollary emitting_projection_application:
  assumes "valid_wires (carry_projection left)"
      and "valid_wires (carry_projection right)" "c < 3"
  shows "apply_wires
      (carry_projection (compose_emitting add left right)) c =
    apply_wires (carry_projection right)
      (apply_wires (carry_projection left) c)"
  using assms emitting_action_projects_to_carry_composition
    carry_projection_spatial_composition by metis

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

fun wire_word_action :: "carry_wires list \<Rightarrow> carry_wires" where
  "wire_word_action [] = domain_wires Equal Equal"
| "wire_word_action (wire # wires) =
    compose_wires wire (wire_word_action wires)"

fun wire_word_scan :: "nat \<Rightarrow> carry_wires list \<Rightarrow> nat" where
  "wire_word_scan c [] = c"
| "wire_word_scan c (wire # wires) =
    wire_word_scan (apply_wires wire c) wires"

lemma identity_wires_valid [simp]:
  "valid_wires (domain_wires Equal Equal)"
  by (simp add: valid_wires_def domain_wires_def staircase_port_def)

lemma identity_wires_apply [simp]:
  assumes "c < 3"
  shows "apply_wires (domain_wires Equal Equal) c = c"
  using assms three_reachable_carry_ports(2)[of c]
  by (simp add: apply_wires_def domain_wires_def)

lemma wire_word_action_valid:
  assumes "\<forall>wire \<in> set wires. valid_wires wire"
  shows "valid_wires (wire_word_action wires)"
  using assms
  by (induction wires) (simp_all add: valid_wires_compose)

theorem wire_word_action_exact:
  assumes valid: "\<forall>wire \<in> set wires. valid_wires wire"
      and incoming: "c < 3"
  shows "apply_wires (wire_word_action wires) c = wire_word_scan c wires"
  using valid incoming
proof (induction wires arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons wire wires)
  have wire_valid: "valid_wires wire" using Cons.prems by simp
  have rest_valid: "\<forall>w \<in> set wires. valid_wires w"
    using Cons.prems by simp
  have next_bound: "apply_wires wire c < 3"
    using wire_valid Cons.prems(2) by (rule valid_wires_stay_reachable)
  have rest_action_valid: "valid_wires (wire_word_action wires)"
    using rest_valid by (rule wire_word_action_valid)
  have composed:
      "apply_wires (wire_word_action (wire # wires)) c =
        apply_wires (wire_word_action wires) (apply_wires wire c)"
    using carry_projection_spatial_composition[OF wire_valid rest_action_valid
        Cons.prems(2)]
    by simp
  also have "... = wire_word_scan (apply_wires wire c) wires"
    using Cons.IH[OF rest_valid next_bound] .
  finally show ?case by simp
qed

lemma wire_word_scan_append [simp]:
  "wire_word_scan c (left @ right) =
    wire_word_scan (wire_word_scan c left) right"
  by (induction left arbitrary: c) simp_all

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

definition harmonic_multiplier :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "harmonic_multiplier u y e = u ^ e * y"

lemma harmonic_multiplier_product:
  fixes u y :: "'a::comm_ring_1"
  shows "prod_list (map (harmonic_multiplier u y) es) =
    u ^ sum_list es * y ^ length es"
  by (induction es) (simp_all add: harmonic_multiplier_def power_add
      power_Suc algebra_simps)

theorem five_step_linear_harmonic_source_death:
  fixes u y :: "'a::comm_ring_1"
  assumes nilpotent: "y ^ 5 = 0"
      and five_events: "length es = 5"
  shows "prod_list (map (harmonic_multiplier u y) es) = 0"
  using harmonic_multiplier_product[of u y es] nilpotent five_events by simp

fun harmonic_run ::
    "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "harmonic_run u y [] source = source"
| "harmonic_run u y ((e,birth) # events) source =
    harmonic_run u y events (harmonic_multiplier u y e * source + birth)"

lemma harmonic_run_source_difference:
  fixes u y :: "'a::comm_ring_1"
  shows "harmonic_run u y events source - harmonic_run u y events other =
    prod_list (map (\<lambda>event. harmonic_multiplier u y (fst event)) events) *
      (source - other)"
proof (induction events arbitrary: source other)
  case Nil
  then show ?case by simp
next
  case (Cons event events)
  obtain e birth where event: "event = (e,birth)" by (cases event)
  let ?m = "harmonic_multiplier u y e"
  let ?tail =
    "prod_list (map (\<lambda>item. harmonic_multiplier u y (fst item)) events)"
  have difference:
      "harmonic_run u y events (?m * source + birth) -
        harmonic_run u y events (?m * other + birth) =
        ?tail * ((?m * source + birth) - (?m * other + birth))"
    by (rule Cons.IH)
  also have "... = (?m * ?tail) * (source - other)"
    by (simp add: algebra_simps)
  finally show ?case
    by (simp add: event algebra_simps)
qed

corollary five_step_same_birth_source_independence:
  fixes u y :: "'a::comm_ring_1"
  assumes nilpotent: "y ^ 5 = 0"
      and five_events: "length events = 5"
  shows "harmonic_run u y events source = harmonic_run u y events other"
proof -
  have exponents: "length (map fst events) = 5" using five_events by simp
  have zero: "prod_list (map (harmonic_multiplier u y) (map fst events)) = 0"
    using five_step_linear_harmonic_source_death[OF nilpotent exponents] .
  have zero_expanded:
      "prod_list (map (\<lambda>event. harmonic_multiplier u y (fst event)) events) = 0"
    using zero by (simp add: comp_def)
  have "harmonic_run u y events source - harmonic_run u y events other = 0"
    using harmonic_run_source_difference[of u y events source other]
      zero_expanded by simp
  then show ?thesis by simp
qed


lemma harmonic_run_append:
  "harmonic_run u y (prefix @ suffix) source =
    harmonic_run u y suffix (harmonic_run u y prefix source)"
  by (induction prefix arbitrary: source) (auto split: prod.splits)

corollary last_five_births_erase_earlier_jet:
  fixes u y :: "'a::comm_ring_1"
  assumes "y ^ 5 = 0" "length suffix = 5"
  shows "harmonic_run u y (prefix @ suffix) source =
    harmonic_run u y suffix 0"
  unfolding harmonic_run_append
  by (rule five_step_same_birth_source_independence[OF assms])

text \<open>This is the right-constant reduction implemented by the primary-jet
composition kernel. The suffix births are supplied and source-bound elsewhere;
this reduction does not discover them, or identify distinct source occurrences.
An Antihydra odd-event block with gap a contains a multiplications by three;
ordinary Collatz physical even steps contain none.\<close>

text \<open>The last corollary compares runs with the same event list, hence the
same births.  It must not be read as saying that source-dependent nonlinear
births die in five steps or that Hensel-admissible refinement has depth five.\<close>

ML \<open>
  val checked = @{thms domain_prefix_carry_composition
    all_equal_prefix_preserves_incoming
    last_decisive_domain_determines_prefix_carry
    three_reachable_carry_ports valid_wires_compose
    carry_projection_spatial_composition
    emitting_action_projects_to_carry_composition
    emitting_projection_application five_generator_output_rows
    five_generators_are_valid empty_interval_identity_row wire_word_action_exact
    collatz_prefix_carry_composition
    collatz_prefix_carry_is_action_projection
    harmonic_multiplier_product five_step_linear_harmonic_source_death
    harmonic_run_source_difference five_step_same_birth_source_independence
    harmonic_run_append last_five_births_erase_earlier_jet
    domain_wires_injective compose_domain_wires
    nonempty_generators_idempotent f5_spatial_length_transport
    f5_spatial_alphabet_card f5_spatial_macros_closed
    f5_spatial_macros_card f5_spatial_repeat_closed_form};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz harmonic port proof depends on an oracle";
\<close>

end
