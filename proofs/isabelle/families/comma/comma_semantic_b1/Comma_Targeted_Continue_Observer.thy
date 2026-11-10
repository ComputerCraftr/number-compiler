theory Comma_Targeted_Continue_Observer
  imports Comma_Targeted_Continue_Power Comma_Program_Continue_Guard
begin

text \<open>
Apply a powered Continue operator only to the demanded endpoint observer.
The operator is a source-free predicate transformer over the canonical
program-derived Continue columns; it does not construct a source/target
matrix.  Composition order is chronological: the right operator consumes
the suffix observer, then the left operator consumes its result.
\<close>

type_synonym comma_continue_observer =
  "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column"

type_synonym comma_continue_operator =
  "comma_continue_observer \<Rightarrow>
    comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> comma_crt_column"

definition comma_continue_endpoint_phase_column ::
    "nat \<Rightarrow> comma_crt_column" where
  "comma_continue_endpoint_phase_column target =
    comma_crt_collect_output Comma_Semantic_B1_Invalid
      (map (\<lambda>endpoint.
          (comma_crt_phase_point (fst endpoint), Comma_Semantic_B1_Invalid))
        (filter (\<lambda>endpoint. snd endpoint=target)
          comma_continue24_endpoint_list))"

definition comma_continue_bad_endpoint_observer ::
    comma_continue_observer where
  "comma_continue_bad_endpoint_observer target clock =
    comma_crt_negate
      (comma_crt_shift clock
        (comma_continue_endpoint_phase_column target))"

definition comma_continue_operator_step :: comma_continue_operator where
  "comma_continue_operator_step observer program clock =
    comma_crt_collect_output Comma_Semantic_B1_Invalid
      (map (\<lambda>target.
        (let edge=comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target
         in (if comma_crt_supported edge then
               comma_crt_apply Comma_CRT_And
                 (comma_crt_shift clock edge)
                 (observer target (Suc clock))
             else Comma_CRT_Bool False,
             Comma_Semantic_B1_Invalid))) [0..<46])"

definition comma_continue_operator_compose ::
    "comma_continue_operator \<Rightarrow> comma_continue_operator
      \<Rightarrow> comma_continue_operator" where
  "comma_continue_operator_compose first second observer program clock =
    first (\<lambda>target next_clock.
      case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> second observer child next_clock
      | None \<Rightarrow> Comma_CRT_Bool False)
      program clock"

definition comma_continue_operator_1 :: comma_continue_operator where
  "comma_continue_operator_1 = comma_continue_operator_step"

definition comma_continue_operator_2 :: comma_continue_operator where
  "comma_continue_operator_2 =
    comma_continue_operator_compose comma_continue_operator_1
      comma_continue_operator_1"

definition comma_continue_operator_4 :: comma_continue_operator where
  "comma_continue_operator_4 =
    comma_continue_operator_compose comma_continue_operator_2
      comma_continue_operator_2"

definition comma_continue_operator_8 :: comma_continue_operator where
  "comma_continue_operator_8 =
    comma_continue_operator_compose comma_continue_operator_4
      comma_continue_operator_4"

definition comma_continue_operator_16 :: comma_continue_operator where
  "comma_continue_operator_16 =
    comma_continue_operator_compose comma_continue_operator_8
      comma_continue_operator_8"

definition comma_continue_operator_24 :: comma_continue_operator where
  "comma_continue_operator_24 =
    comma_continue_operator_compose comma_continue_operator_16
      comma_continue_operator_8"

definition comma_continue24_bad_support_column ::
    "comma_semantic_port_program \<Rightarrow> comma_crt_column" where
  "comma_continue24_bad_support_column program =
    comma_continue_operator_24 comma_continue_bad_endpoint_observer
      program 0"

definition comma_semantic_phase_program_catalogue ::
    "comma_semantic_port_program list" where
  "comma_semantic_phase_program_catalogue = remdups
    (List.map_filter comma_semantic_phase_program_for_class [0..<46])"

definition comma_continue24_direct_image_certificate :: bool where
  "comma_continue24_direct_image_certificate =
    list_all (\<lambda>program.
      \<not> comma_crt_supported
        (comma_continue24_bad_support_column program))
      comma_semantic_phase_program_catalogue"

text \<open>The downstream operator-24 contract audit is rooted in
Comma_Targeted_Continue_Observer_Refinement; these defining equations are
checked here as the public observer implementation they consume.\<close>

ML \<open>
  val published = @{thms
    comma_continue_endpoint_phase_column_def
    comma_continue_bad_endpoint_observer_def
    comma_continue_operator_step_def
    comma_continue_operator_compose_def
    comma_continue_operator_1_def
    comma_continue_operator_2_def
    comma_continue_operator_4_def
    comma_continue_operator_8_def
    comma_continue_operator_16_def
    comma_continue_operator_24_def
    comma_continue24_bad_support_column_def}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Continue observer implementation definitions" published
\<close>

end
