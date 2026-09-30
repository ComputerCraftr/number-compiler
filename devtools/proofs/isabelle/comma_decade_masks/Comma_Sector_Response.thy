theory Comma_Sector_Response
  imports Comma_Decade_Masks Comma_Fast_Control.Comma_Fast_Kernel
begin

text \<open>A sector response branches on the short cyclotomic phase, never on
all 924 absolute phases. Leaves retain the exact round outcome, including the
raw crossing offset and exponent delta. Orbit projection is a later consumer.
The recursion budget here bounds the at most nine sectors inside ONE decade;
it is not a bound on the number of decades before termination.\<close>

datatype comma_sector_response =
    Comma_Response_Leaf comma_round_result
  | Comma_Response_Phases nat nat nat "comma_sector_response list"

primrec comma_response_value ::
  "nat \<Rightarrow> comma_sector_response \<Rightarrow> comma_round_result" where
  "comma_response_value r (Comma_Response_Leaf result)=result"
| "comma_response_value r (Comma_Response_Phases f delta x children)=
    (let k=comma_entry_alphabet_phase f r delta x in
      if k<length children then map (comma_response_value r) children ! k
      else Comma_Round_Invalid)"

text \<open>Select the demanded child before recursion. The primitive-recursion
specification uses map to express the recursive calls, but executable consumers
must not evaluate unselected siblings. Missing-child admission stays Invalid.\<close>

declare comma_response_value.simps(2) [simp del, code del]

lemma comma_response_value_selected [simp, code]:
  "comma_response_value r (Comma_Response_Phases f delta x children)=
    (let k=comma_entry_alphabet_phase f r delta x in
      if k<length children then comma_response_value r (children!k)
      else Comma_Round_Invalid)"
  by (cases "comma_entry_alphabet_phase f r delta x<length children")
    (simp_all only: comma_response_value.simps(2) Let_def if_True if_False nth_map)

lemma comma_response_value_missing_child:
  assumes "length children\<le>comma_entry_alphabet_phase f r delta x"
  shows "comma_response_value r (Comma_Response_Phases f delta x children)=
    Comma_Round_Invalid"
  using assms by (simp only: comma_response_value_selected Let_def; simp)

definition comma_response_after ::
  "(comma_finite_position \<Rightarrow> comma_sector_response) \<Rightarrow>
    comma_finite_position \<Rightarrow> comma_sector_response" where
  "comma_response_after next t =
    (case comma_fast_step 0 t of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing t target
        then Comma_Response_Leaf (Comma_Round_Cross target) else next target
    | Comma_Fork a d \<Rightarrow> Comma_Response_Leaf (Comma_Round_Fork a d)
    | Comma_Landmine d \<Rightarrow> Comma_Response_Leaf (Comma_Round_Landmine d)
    | Comma_Invalid \<Rightarrow> Comma_Response_Leaf Comma_Round_Invalid)"

fun comma_build_sector_response ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_sector_response" where
  "comma_build_sector_response 0 source=Comma_Response_Leaf Comma_Round_Invalid"
| "comma_build_sector_response (Suc n) (Comma_Entry f delta x)=
    (if f<1 \<or> 9<f \<or> 98<x then Comma_Response_Leaf Comma_Round_Invalid
     else Comma_Response_Phases f delta x
       (map (\<lambda>k. comma_response_after (comma_build_sector_response n)
         (Comma_Near f delta (comma_entry_alphabet_endpoint f x k)))
         [0..<comma_short_period (comma_finite_period_fast f (x mod 10))]))"
| "comma_build_sector_response (Suc n) (Comma_Near f delta h)=
    comma_response_after (comma_build_sector_response n)
      (Comma_Near f delta (snd (comma_near_closed_germ f h)))"

lemma comma_response_after_value:
  "comma_response_value r (comma_response_after next t)=
    (case comma_fast_step 0 t of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing t target then Comma_Round_Cross target
        else comma_response_value r (next target)
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
  by (simp add: comma_response_after_def split: comma_finite_move.splits)

lemma comma_response_round_successor:
  "comma_fast_round_aux (Suc n) r source =
    (let t=comma_fast_sector_target r source in
      case comma_fast_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then Comma_Round_Cross target
          else comma_fast_round_aux n r target
      | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
      | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
      | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
  using comma_fast_round_aux_eval[of "Suc n" r source]
  by (simp only: Suc_not_Zero if_False diff_Suc_1)

lemma comma_fast_near_phase:
  "comma_fast_step (r mod 924) (Comma_Near f delta h)=comma_fast_step 0 (Comma_Near f delta h)"
  by (simp only: comma_fast_step.simps)

lemma comma_response_phase_map:
  assumes bound: "comma_entry_alphabet_phase f r delta x<T"
  shows "comma_response_value r
      (Comma_Response_Phases f delta x (map branch [0..<T]))=
    comma_response_value r (branch (comma_entry_alphabet_phase f r delta x))"
  by (simp only: comma_response_value_selected Let_def length_map length_upt
    diff_zero bound if_True nth_map nth_upt add_0_left)

lemma comma_response_after_refines:
  assumes child: "\<And>source. comma_response_value r (continuation source)=F source"
  shows "comma_response_value r (comma_response_after continuation target)=
    (case comma_fast_step 0 target of
      Comma_Next source \<Rightarrow>
        if comma_round_crossing target source then Comma_Round_Cross source else F source
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
  by (simp only: comma_response_after_value child)

lemma comma_sector_response_refines:
  "comma_response_value r (comma_build_sector_response n source)=
    comma_fast_round_aux n r source"
proof (induction n arbitrary: source)
  case 0
  then show ?case by (simp only: comma_build_sector_response.simps
    comma_response_value.simps(1) comma_fast_round_aux.simps)
next
  case (Suc n)
  show ?case
  proof (cases source)
    case (Comma_Entry f delta x)
    show ?thesis
    proof (cases "f<1 \<or> 9<f \<or> 98<x")
      case True
      then show ?thesis
        by (simp only: Comma_Entry comma_build_sector_response.simps True if_True
          comma_response_value.simps(1) comma_response_value_selected
          comma_response_round_successor
          comma_sector_entry_alphabet Let_def comma_fast_step.simps
          comma_finite_move.case)
    next
      case False
      then have bound: "comma_entry_alphabet_phase f r delta x <
        comma_short_period (comma_finite_period_fast f (x mod 10))"
        by (intro comma_entry_alphabet_phase_bound) auto
      let ?k = "comma_entry_alphabet_phase f r delta x"
      let ?target = "Comma_Near f delta (comma_entry_alphabet_endpoint f x ?k)"
      have built: "comma_build_sector_response (Suc n) (Comma_Entry f delta x)=
        Comma_Response_Phases f delta x
          (map (\<lambda>k. comma_response_after (comma_build_sector_response n)
            (Comma_Near f delta (comma_entry_alphabet_endpoint f x k)))
            [0..<comma_short_period (comma_finite_period_fast f (x mod 10))])"
        by (simp only: comma_build_sector_response.simps False if_False)
      have observed: "comma_response_value r
          (comma_build_sector_response (Suc n) (Comma_Entry f delta x))=
        comma_response_value r (comma_response_after (comma_build_sector_response n) ?target)"
        unfolding built by (rule comma_response_phase_map[OF bound])
      have transported: "comma_response_value r
          (comma_response_after (comma_build_sector_response n) ?target)=
        comma_fast_round_aux (Suc n) r (Comma_Entry f delta x)"
        by (simp only: comma_response_after_value Suc.IH comma_response_round_successor
          comma_sector_entry_alphabet False if_False Let_def comma_fast_near_phase)
      show ?thesis using Comma_Entry observed transported by metis
    qed
  next
    case (Comma_Near f delta h)
    then show ?thesis
      by (simp only: Comma_Near comma_build_sector_response.simps comma_response_after_value
        Suc.IH comma_response_round_successor comma_sector_near_alphabet
        Let_def comma_fast_near_phase)
  qed
qed

lemma comma_sector_response_round:
  assumes valid: "comma_round_admitted source"
    and budget: "Suc (9-comma_sector_number source)\<le>n"
  shows "comma_response_value r (comma_build_sector_response n source)=
    snd (snd (comma_round_close r source))"
  by (simp only: comma_sector_response_refines
      comma_fast_round_aux_correct[OF valid budget])

corollary comma_entry_response_complete:
  assumes "x\<le>90"
  shows "comma_response_value r
    (comma_build_sector_response 9 (Comma_Entry 1 0 x))=
    snd (snd (comma_round_close r (Comma_Entry 1 0 x)))"
  by (rule comma_sector_response_round) (use assms in auto)

text \<open>The following bridge connects the constructed response to the
existing executable one-decade control. It supplies no candidate outcome table
and has no successful-evaluation premise. A proof-producing memo evaluator may
share response clauses by their complete source key before mask projection.\<close>
lemma comma_entry_response_control:
  "comma_decade_decode r
    (comma_response_value r (comma_build_sector_response 9 (Comma_Entry 1 0 x)))=
    comma_fast_decade_control (Comma_Decade r x)"
  by (simp only: comma_sector_response_refines comma_fast_decade_control.simps)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_response_value_selected comma_response_value_missing_child
      comma_sector_response_refines comma_sector_response_round
      comma_entry_response_complete comma_entry_response_control}) then ()
    else error "Sector response construction depends on an oracle";
\<close>
end
