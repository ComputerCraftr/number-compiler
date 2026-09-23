theory Reverse_196_Complete_Interface_Substitution
  imports Decimal_Publisher_Constructor
    Reverse_Residuals.Reverse_196_Publisher_Refinement
begin

text \<open>The executable cocycle arena substitutes every output root from one
frozen source environment.  This is stronger than applying a sequence of
single-variable updates: a replacement may read another variable that is also
being replaced.  The definitions below specify that transaction directly.
They cover every root supplied to the transaction, including the admission
root, value ports, and residual observation roots.  They do not postulate a
recursive decimal normal form or a bound on circuit-DAG construction.\<close>

type_synonym ('v, 'a) interface_environment = "'v \<Rightarrow> 'a"
type_synonym ('v, 'a) interface_replacements =
  "'v \<Rightarrow> (('v, 'a) interface_environment \<Rightarrow> 'a) option"

definition simultaneous_environment ::
    "('v, 'a) interface_environment \<Rightarrow>
      ('v, 'a) interface_replacements \<Rightarrow>
      ('v, 'a) interface_environment" where
  "simultaneous_environment source replacements variable =
    (case replacements variable of
      None \<Rightarrow> source variable
    | Some replacement \<Rightarrow> replacement source)"

definition substitute_interface_root ::
    "((('v, 'a) interface_environment) \<Rightarrow> 'b) \<Rightarrow>
      ('v, 'a) interface_replacements \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b" where
  "substitute_interface_root root replacements source =
    root (simultaneous_environment source replacements)"

definition substitute_interface_many ::
    "((('v, 'a) interface_environment \<Rightarrow> 'b) list) \<Rightarrow>
      ('v, 'a) interface_replacements \<Rightarrow>
      ((('v, 'a) interface_environment \<Rightarrow> 'b) list)" where
  "substitute_interface_many roots replacements =
    map (\<lambda>root. substitute_interface_root root replacements) roots"

lemma substitute_interface_many_length [simp]:
  "length (substitute_interface_many roots replacements) = length roots"
  by (simp add: substitute_interface_many_def)

lemma substitute_interface_many_nth:
  assumes "i < length roots"
  shows "substitute_interface_many roots replacements ! i =
    substitute_interface_root (roots ! i) replacements"
  using assms by (simp add: substitute_interface_many_def)

theorem simultaneous_replacements_read_frozen_source:
  assumes "replacements x = Some rx" "replacements y = Some ry"
  shows "simultaneous_environment source replacements x = rx source"
    "simultaneous_environment source replacements y = ry source"
  using assms by (simp_all add: simultaneous_environment_def)

text \<open>Composition of two simultaneous substitutions must pull the
second replacement roots back through the first frozen environment.  Merely
concatenating an update list would give sequential rebinding semantics.\<close>

definition compose_interface_replacements ::
    "('v, 'a) interface_replacements \<Rightarrow>
      ('v, 'a) interface_replacements \<Rightarrow>
      ('v, 'a) interface_replacements" where
  "compose_interface_replacements before after variable =
    (case after variable of
      None \<Rightarrow> before variable
    | Some replacement \<Rightarrow>
        Some (substitute_interface_root replacement before))"

lemma simultaneous_environment_compose:
  "simultaneous_environment
      (simultaneous_environment source before) after =
    simultaneous_environment source
      (compose_interface_replacements before after)"
proof (rule ext)
  fix variable
  show "simultaneous_environment
      (simultaneous_environment source before) after variable =
    simultaneous_environment source
      (compose_interface_replacements before after) variable"
    by (cases "after variable";
        simp add: simultaneous_environment_def
          compose_interface_replacements_def substitute_interface_root_def)
qed

lemma substitute_interface_root_compose:
  "substitute_interface_root
      (substitute_interface_root root after) before =
    substitute_interface_root root
      (compose_interface_replacements before after)"
proof (rule ext)
  fix source
  show "substitute_interface_root
      (substitute_interface_root root after) before source =
    substitute_interface_root root
      (compose_interface_replacements before after) source"
    by (simp add: substitute_interface_root_def
        simultaneous_environment_compose)
qed

theorem substitute_interface_many_compose:
  "substitute_interface_many
      (substitute_interface_many roots after) before =
    substitute_interface_many roots
      (compose_interface_replacements before after)"
  by (simp add: substitute_interface_many_def
      substitute_interface_root_compose)

section \<open>Admission and complete batch observation\<close>

definition restrict_interface_root ::
    "((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> 'b) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b option" where
  "restrict_interface_root admitted root source =
    (if admitted source then Some (root source) else None)"

definition restrict_interface_many ::
    "((('v, 'a) interface_environment \<Rightarrow> 'b) list) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b option list" where
  "restrict_interface_many roots admitted source =
    map (\<lambda>root. restrict_interface_root admitted root source) roots"

definition complete_interface_packet ::
    "((('v, 'a) interface_environment \<Rightarrow> 'b) list) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b list option" where
  "complete_interface_packet roots admitted source =
    (if admitted source then Some (map (\<lambda>root. root source) roots)
     else None)"

lemma restrict_interface_many_length [simp]:
  "length (restrict_interface_many roots admitted source) = length roots"
  by (simp add: restrict_interface_many_def)

theorem complete_interface_packet_admitted:
  assumes "admitted source"
  shows "complete_interface_packet roots admitted source =
    Some (map (\<lambda>root. root source) roots)"
  using assms by (simp add: complete_interface_packet_def)

theorem complete_interface_packet_rejected:
  assumes "\<not> admitted source"
  shows "complete_interface_packet roots admitted source = None"
  using assms by (simp add: complete_interface_packet_def)

definition restrict_partial_interface_root ::
    "((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> 'b option) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b option" where
  "restrict_partial_interface_root admitted root source =
    (if admitted source then root source else None)"

definition all_interface_domains ::
    "((('v, 'a) interface_environment \<Rightarrow> bool) list) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> bool" where
  "all_interface_domains domains source = list_all (\<lambda>domain. domain source) domains"

lemma restrict_partial_interface_root_fusion:
  "restrict_partial_interface_root outer
      (restrict_partial_interface_root inner root) =
    restrict_partial_interface_root (\<lambda>source.
      outer source \<and> inner source) root"
  by (rule ext)
     (simp add: restrict_partial_interface_root_def)

theorem complete_interface_final_restriction_fusion:
  "restrict_partial_interface_root before
      (restrict_partial_interface_root pulled_after
        (restrict_partial_interface_root (all_interface_domains domains) root)) =
    restrict_partial_interface_root
      (\<lambda>source. before source \<and> pulled_after source \<and>
        all_interface_domains domains source) root"
  by (rule ext)
     (simp add: restrict_partial_interface_root_def)

theorem complete_interface_final_restriction_fusion_many:
  "map (\<lambda>root. restrict_partial_interface_root before
      (restrict_partial_interface_root pulled_after
        (restrict_partial_interface_root (all_interface_domains domains) root)))
      roots =
    map (\<lambda>root. restrict_partial_interface_root
      (\<lambda>source. before source \<and> pulled_after source \<and>
        all_interface_domains domains source) root) roots"
  by (simp add: complete_interface_final_restriction_fusion)

definition temporal_interface_packet ::
    "('v, 'a) interface_replacements \<Rightarrow>
      ((('v, 'a) interface_environment \<Rightarrow> 'b) list) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      (('v, 'a) interface_environment) \<Rightarrow> 'b list option" where
  "temporal_interface_packet transition roots admitted_before admitted_after
      source =
    (if admitted_before source \<and>
        admitted_after (simultaneous_environment source transition)
     then Some (map (\<lambda>root.
       root (simultaneous_environment source transition)) roots)
     else None)"

theorem temporal_interface_packet_is_simultaneous_substitute_and_restrict:
  "temporal_interface_packet transition roots admitted_before admitted_after
      source =
    complete_interface_packet
      (substitute_interface_many roots transition)
      (\<lambda>state. admitted_before state \<and>
        substitute_interface_root admitted_after transition state)
      source"
  by (simp add: temporal_interface_packet_def complete_interface_packet_def
      substitute_interface_many_def substitute_interface_root_def)

theorem temporal_interface_packet_exact_sequential_semantics:
  "temporal_interface_packet transition roots admitted_before admitted_after
      source =
    (if admitted_before source then
      complete_interface_packet roots admitted_after
        (simultaneous_environment source transition)
     else None)"
  by (simp add: temporal_interface_packet_def complete_interface_packet_def)

section \<open>Saturated complete-interface identity\<close>

text \<open>A saturated action exposes its entire next interface together with
the domain on which that interface is admitted.  The optional environment is
the semantic observation; elapsed time and the construction history of the
replacement roots are not part of this identity.  This result applies only
when the environment includes every port that a later consumer may read.\<close>

definition saturated_interface_image ::
    "('v, 'a) interface_replacements \<Rightarrow>
      ((('v, 'a) interface_environment) \<Rightarrow> bool) \<Rightarrow>
      ('v, 'a) interface_environment \<Rightarrow>
      ('v, 'a) interface_environment option" where
  "saturated_interface_image transition admitted source =
    (if admitted source then
      Some (simultaneous_environment source transition) else None)"

theorem saturated_interface_image_exact_consumer:
  "temporal_interface_packet transition roots admitted_before admitted_after
      source =
    (case saturated_interface_image transition admitted_before source of
      None \<Rightarrow> None
    | Some next \<Rightarrow> complete_interface_packet roots admitted_after next)"
  by (simp add: temporal_interface_packet_exact_sequential_semantics
      saturated_interface_image_def)

theorem saturated_interface_image_retained_consumer_congruence:
  assumes same_image:
    "saturated_interface_image first first_admitted =
      saturated_interface_image second second_admitted"
  shows "temporal_interface_packet first roots first_admitted admitted_after =
    temporal_interface_packet second roots second_admitted admitted_after"
proof (rule ext)
  fix source
  show "temporal_interface_packet first roots first_admitted admitted_after
      source =
    temporal_interface_packet second roots second_admitted admitted_after
      source"
    using same_image
    by (simp add: saturated_interface_image_exact_consumer)
qed

theorem saturated_interface_image_complete_outputs_and_admission:
  assumes same_admission: "\<And>source. first_admitted source = second_admitted source"
      and same_outputs: "\<And>source. first_admitted source \<Longrightarrow>
        simultaneous_environment source first =
        simultaneous_environment source second"
  shows "saturated_interface_image first first_admitted =
    saturated_interface_image second second_admitted"
proof (rule ext)
  fix source
  show "saturated_interface_image first first_admitted source =
    saturated_interface_image second second_admitted source"
    using same_admission[of source] same_outputs[of source]
    by (simp add: saturated_interface_image_def)
qed

section \<open>Extensional future composition and admission normalization\<close>

text \<open>A complete image is a partial function on the entire admitted
environment.  Composition below is the semantic reference for future action
equality.  The theorems require equality at every source environment, not
equality of observations at one concrete occurrence.  They do not implement
or bound the recursive reverse/add occurrence constructor.\<close>

definition chronological_partial_image ::
    "('s \<Rightarrow> 's option) \<Rightarrow> ('s \<Rightarrow> 's option) \<Rightarrow>
      's \<Rightarrow> 's option" where
  "chronological_partial_image before after source =
    (case before source of None \<Rightarrow> None | Some middle \<Rightarrow> after middle)"

theorem saturated_image_chronological_composition:
  "chronological_partial_image
      (saturated_interface_image before before_admitted)
      (saturated_interface_image after after_admitted) =
    saturated_interface_image
      (compose_interface_replacements before after)
      (\<lambda>source. before_admitted source \<and>
        after_admitted (simultaneous_environment source before))"
  by (rule ext)
     (simp add: chronological_partial_image_def saturated_interface_image_def
       simultaneous_environment_compose)

corollary saturated_image_right_congruence:
  assumes "saturated_interface_image first first_admitted =
      saturated_interface_image second second_admitted"
  shows "chronological_partial_image
      (saturated_interface_image first first_admitted) future =
    chronological_partial_image
      (saturated_interface_image second second_admitted) future"
  using assms by simp

text \<open>Partial Boolean guards have one canonical total admission bit.
Undefined and explicit false both mean rejection.  Keeping their raw option
representations in an action key would distinguish equal admitted behavior.\<close>

definition totalize_partial_guard ::
    "('s \<Rightarrow> bool option) \<Rightarrow> 's \<Rightarrow> bool" where
  "totalize_partial_guard guard source = (guard source = Some True)"

definition canonical_partial_guard ::
    "('s \<Rightarrow> bool option) \<Rightarrow> 's \<Rightarrow> bool option" where
  "canonical_partial_guard guard source =
    Some (totalize_partial_guard guard source)"

lemma canonical_partial_guard_total [simp]:
  "canonical_partial_guard guard source \<noteq> None"
  by (simp add: canonical_partial_guard_def)

lemma canonical_partial_guard_preserves_admission [simp]:
  "canonical_partial_guard guard source = Some True \<longleftrightarrow>
    guard source = Some True"
  by (simp add: canonical_partial_guard_def totalize_partial_guard_def)

theorem canonical_partial_guard_extensional:
  assumes "\<And>source. first source = Some True \<longleftrightarrow>
      second source = Some True"
  shows "canonical_partial_guard first = canonical_partial_guard second"
  by (rule ext) (simp add: canonical_partial_guard_def
      totalize_partial_guard_def assms)

lemma false_and_undefined_guard_have_one_admission:
  "canonical_partial_guard
      (\<lambda>x::nat. if x = 0 then Some True else None) =
    canonical_partial_guard
      (\<lambda>x::nat. Some (x = 0))"
  by (rule canonical_partial_guard_extensional) auto

text \<open>A single source observation does not imply right congruence.
The following bounded functions agree at source 0, but their second
applications differ at the shared successor 1.  This is a counterexample to
using one occurrence as a semantic ActionID equality test; it is not a
counterexample to the full extensional image quotient.\<close>

definition weak_first_action :: "nat \<Rightarrow> nat option" where
  "weak_first_action source = Some (if source = 0 then 1 else source)"

definition weak_second_action :: "nat \<Rightarrow> nat option" where
  "weak_second_action source =
    Some (if source = 0 then 1 else if source = 1 then 2 else source)"

lemma weak_actions_agree_at_initial_source:
  "weak_first_action 0 = weak_second_action 0"
  by (simp add: weak_first_action_def weak_second_action_def)

lemma weak_actions_diverge_after_square:
  "chronological_partial_image weak_first_action weak_first_action 0 \<noteq>
    chronological_partial_image weak_second_action weak_second_action 0"
  by (simp add: chronological_partial_image_def weak_first_action_def
      weak_second_action_def)


corollary saturated_interface_portwise_consumer_congruence:
  assumes same_admission: "\<And>source. first_admitted source = second_admitted source"
      and same_port: "\<And>source port. first_admitted source \<Longrightarrow>
        simultaneous_environment source first port =
        simultaneous_environment source second port"
  shows "temporal_interface_packet first roots first_admitted admitted_after =
    temporal_interface_packet second roots second_admitted admitted_after"
proof (rule saturated_interface_image_retained_consumer_congruence)
  show "saturated_interface_image first first_admitted =
    saturated_interface_image second second_admitted"
    by (rule saturated_interface_image_complete_outputs_and_admission
        [OF same_admission])
       (rule ext, rule same_port, assumption)
qed

text \<open>The converse constructor obligation is deliberately explicit:
one must prove that a recursive source or growth region is represented by
the complete environment above, including its admission and every retained
consumer port.  Equality of a recipe, or equality of one digit projection,
does not supply that obligation.\<close>

definition chronological_packet ::
    "nat \<Rightarrow> 'a \<Rightarrow> nat \<times> 'a" where
  "chronological_packet events packet = (events, packet)"

lemma chronological_packet_extent_injective:
  assumes "chronological_packet events packet =
      chronological_packet events' packet'"
  shows "events = events'"
  using assms by (simp add: chronological_packet_def)

lemma chronological_extent_is_not_observation_only:
  "chronological_packet 1 packet \<noteq> chronological_packet 2 packet"
  by (simp add: chronological_packet_def)

text \<open>The following two-variable model records the precise failure of
sequential rebinding.  It is an interface-algebra counterexample only; it is
not a counterexample to the reverse/add publisher.\<close>

datatype two_interface_ports = Left_Port | Right_Port

definition frozen_example_source ::
    "two_interface_ports \<Rightarrow> nat" where
  "frozen_example_source port = (case port of Left_Port \<Rightarrow> 2
    | Right_Port \<Rightarrow> 7)"

definition frozen_example_replacements ::
    "two_interface_ports \<Rightarrow>
      ((two_interface_ports \<Rightarrow> nat) \<Rightarrow> nat) option" where
  "frozen_example_replacements port =
    (case port of Left_Port \<Rightarrow> Some (\<lambda>source. source Right_Port)
    | Right_Port \<Rightarrow> Some (\<lambda>source. source Left_Port))"

theorem simultaneous_swap_uses_one_frozen_environment:
  "simultaneous_environment frozen_example_source
      frozen_example_replacements Left_Port = 7 \<and>
   simultaneous_environment frozen_example_source
      frozen_example_replacements Right_Port = 2"
  by (simp add: simultaneous_environment_def frozen_example_source_def
      frozen_example_replacements_def)

section \<open>Concrete reverse/add publisher consequence\<close>

definition reverse_196_observer_packet ::
    "(nat list \<Rightarrow> 'a) list \<Rightarrow> nat list \<Rightarrow>
      'a list option" where
  "reverse_196_observer_packet observers source =
    (if valid_pair source then
      Some (map (\<lambda>observer.
        observer (reverse_two_port_publisher source)) observers)
     else None)"

definition reverse_196_step_packet ::
    "(nat list \<Rightarrow> 'a) list \<Rightarrow> nat list \<Rightarrow>
      'a list option" where
  "reverse_196_step_packet observers source =
    (if valid_pair source then
      Some (map (\<lambda>observer. observer (step source)) observers)
     else None)"

theorem reverse_196_complete_observers_refine_one_step:
  "reverse_196_observer_packet observers source =
    reverse_196_step_packet observers source"
proof (cases "valid_pair source")
  case True
  then have publisher: "reverse_two_port_publisher source = step source"
    by (rule reverse_two_port_publisher_refines_step)
  show ?thesis using True publisher
    by (simp add: reverse_196_observer_packet_def reverse_196_step_packet_def)
next
  case False
  then show ?thesis
    by (simp add: reverse_196_observer_packet_def reverse_196_step_packet_def)
qed

theorem reverse_196_complete_observers_preserve_order_and_count:
  assumes "valid_pair source"
  obtains packet_values where
    "reverse_196_observer_packet observers source = Some packet_values"
    "length packet_values = length observers"
  using assms
  by (intro that[of "map (\<lambda>observer.
      observer (reverse_two_port_publisher source)) observers"])
     (simp_all add: reverse_196_observer_packet_def)

theorem reverse_196_two_publisher_steps_refine_two_steps:
  assumes valid: "valid_pair source"
  shows "reverse_two_port_publisher
      (reverse_two_port_publisher source) = step (step source)"
proof -
  have first: "reverse_two_port_publisher source = step source"
    by (rule reverse_two_port_publisher_refines_step[OF valid])
  have next_valid: "valid_pair (step source)"
    by (rule valid_pair_successor[OF valid])
  have second: "reverse_two_port_publisher (step source) = step (step source)"
    by (rule reverse_two_port_publisher_refines_step[OF next_valid])
  show ?thesis using first second by simp
qed

text \<open>This theory proves the extensional transaction implemented by
substitute-many/restrict-many and transports the already checked concrete
one-step reverse/add publisher through every supplied finite observer root.
The production instantiation must still relate finite circuit identifiers,
typed port cardinalities, atomic publication, cache authority, and ledger
charges to these semantic functions.  It also still needs the recursive
source-image constructor and a checked bound on its reachable canonical DAG;
none of those obligations follows from extensional composition.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms substitute_interface_many_compose
      complete_interface_final_restriction_fusion_many
      temporal_interface_packet_is_simultaneous_substitute_and_restrict
      temporal_interface_packet_exact_sequential_semantics
      saturated_interface_image_exact_consumer
      saturated_interface_image_retained_consumer_congruence
      saturated_interface_image_complete_outputs_and_admission
      saturated_interface_portwise_consumer_congruence
      saturated_image_chronological_composition
      saturated_image_right_congruence
      canonical_partial_guard_extensional
      false_and_undefined_guard_have_one_admission
      weak_actions_agree_at_initial_source
      weak_actions_diverge_after_square
      chronological_packet_extent_injective
      simultaneous_swap_uses_one_frozen_environment
      reverse_196_complete_observers_refine_one_step
      reverse_196_two_publisher_steps_refine_two_steps}) then ()
    else error "complete-interface substitution proof depends on an oracle";
\<close>

end
