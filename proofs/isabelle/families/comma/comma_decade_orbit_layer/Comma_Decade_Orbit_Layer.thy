theory Comma_Decade_Orbit_Layer
  imports Comma_Decade_Layer_Check.Comma_Decade_Layer_Check
begin

declare comma_decade_block_power.simps [simp del]

text \<open>The release B5 checker does not need ninety-one physical offset
cells.  The already checked sector-one orbit quotient has forty-six classes,
and decade control is exactly equal on equal orbit classes.  This layer keeps
one result per orbit class and reconstructs every admitted physical offset by
lookup.  No candidate rank or termination fact is introduced here.\<close>

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit proof: length"\<close>

lemma comma_offset_representatives_length [simp]:
  "length comma_offset_representatives = 46"
  by (simp add: comma_offset_representatives_def)

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit proof: comma_offset_representative_slot"\<close>

lemma comma_offset_representative_slot:
  assumes "i<46"
  shows "comma_offset_representatives!i\<le>90"
    "comma_offset_orbit (comma_offset_representatives!i)=i"
  using comma_offset_representatives_checked assms
  by (auto simp: list_all_iff)

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit proof: comma_decade_block_atom_orbit_congruent"\<close>

lemma comma_decade_block_atom_orbit_congruent:
  assumes x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_decade_block_atom (Comma_Decade r x)=
    comma_decade_block_atom (Comma_Decade r y)"
proof -
  have reps: "comma_offset_representative x=comma_offset_representative y"
    using same by (simp only: comma_offset_representative_def)
  have left: "comma_decade_block_atom (Comma_Decade r x)=
    comma_decade_block_atom (Comma_Decade r (comma_offset_representative x))"
    by (rule comma_decade_block_atom_orbit_representative[OF x])
  have right: "comma_decade_block_atom (Comma_Decade r y)=
    comma_decade_block_atom (Comma_Decade r (comma_offset_representative y))"
    by (rule comma_decade_block_atom_orbit_representative[OF y])
  show ?thesis using left right
    by (simp only: reps)
qed

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit proof: comma_decade_block_power_orbit_congruent"\<close>

lemma comma_decade_block_power_orbit_congruent:
  assumes x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_decade_block_power k (Comma_Decade r x)=
    comma_decade_block_power k (Comma_Decade r y)"
proof (induction k)
  case 0
  show ?case
    by (simp only: comma_decade_block_power.simps
      comma_decade_block_atom_orbit_congruent[OF x y same])
next
  case (Suc k)
  have prior: "comma_decade_block_power k (Comma_Decade r x)=
    comma_decade_block_power k (Comma_Decade r y)"
    by (rule Suc.IH)
  show ?case by (simp only: comma_decade_block_power.simps prior)
qed

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: comma_decade_orbit_layer_lookup"\<close>

definition comma_decade_orbit_layer_lookup ::
  "comma_decade_block_result list \<Rightarrow> nat \<Rightarrow> comma_decade_block_result" where
  "comma_decade_orbit_layer_lookup layer x =
    (if length layer=46 \<and> x<91 then layer!(comma_offset_orbit x)
      else Comma_Block_Invalid)"

definition comma_decade_orbit_layer_correct ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_decade_block_result list \<Rightarrow> bool" where
  "comma_decade_orbit_layer_correct k r layer =
    (length layer=46 \<and> (\<forall>i<46. layer!i=
      comma_decade_block_power k
        (Comma_Decade r (comma_offset_representatives!i))))"

definition comma_decade_orbit_base_layer ::
  "nat \<Rightarrow> comma_decade_block_result list" where
  "comma_decade_orbit_base_layer r = map (\<lambda>i.
    comma_decade_block_atom (Comma_Decade r (comma_offset_representatives!i))) [0..<46]"

lemma comma_decade_orbit_base_layer_correct:
  "comma_decade_orbit_layer_correct 0 r (comma_decade_orbit_base_layer r)"
  by (simp add: comma_decade_orbit_layer_correct_def
    comma_decade_orbit_base_layer_def comma_decade_block_power.simps(1))


lemma comma_decade_orbit_base_layer_valueI:
  assumes "comma_decade_orbit_base_layer r=layer"
  shows "comma_decade_orbit_layer_correct 0 r layer"
  using comma_decade_orbit_base_layer_correct[of r] assms by simp

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: local_setup"\<close>

local_setup \<open>fn lthy =>
  let
    val (certify, _) = Comma_Entry_Arithmetic.make_certifier lthy
    val arithmetic = Comma_Entry_Arithmetic.natural_context lthy addsimps
      @{thms comma_offset_representatives_def nth_Cons'}
    fun check i =
      let
        val source = @{term "nth comma_offset_representatives"} $
          HOLogic.mk_number @{typ nat} i
        val theorem = certify (Simplifier.rewrite arithmetic (Thm.cterm_of lthy source))
        val (typ, value) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem))
        val _ = if typ = @{typ nat} andalso 0 <= value andalso value <= 90 then ()
          else error "Invalid orbit-layer representative"
      in theorem end
    val facts = map check (0 upto 45)
    val (_, next) = Local_Theory.note
      ((Binding.name "comma_orbit_layer_representative_constants", []), facts) lthy
    val orbit_context = arithmetic addsimps
      @{thms comma_offset_orbit_def comma_digit_orbit_sum_def power2_eq_square
        of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if}
    fun orbit x =
      let
        val source = @{term comma_offset_orbit} $ HOLogic.mk_number @{typ nat} x
        val theorem = certify (Simplifier.rewrite orbit_context (Thm.cterm_of lthy source))
        val (typ, value) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem))
        val _ = if typ = @{typ nat} andalso 0 <= value andalso value < 46 then ()
          else error "Invalid orbit-layer slot"
      in theorem end
  in #2 (Local_Theory.note
    ((Binding.name "comma_orbit_layer_slot_constants", []), map orbit (0 upto 90)) next) end\<close>

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: comma_decade_orbit_layer_lookup_correct"\<close>

lemma comma_decade_orbit_layer_lookup_correct:
  assumes correct: "comma_decade_orbit_layer_correct k r layer"
    and x: "x<91"
  shows "comma_decade_orbit_layer_lookup layer x=
    comma_decade_block_power k (Comma_Decade r x)"
proof -
  have xb: "x\<le>90" using x by arith
  have oi: "comma_offset_orbit x<46" by (rule comma_offset_orbit_bound)
  have length: "length layer=46"
    using correct by (simp add: comma_decade_orbit_layer_correct_def)
  have slot: "layer!(comma_offset_orbit x)=
    comma_decade_block_power k
      (Comma_Decade r (comma_offset_representative x))"
    using correct oi
    by (simp add: comma_decade_orbit_layer_correct_def
      comma_offset_representative_def)
  have rep_bound: "comma_offset_representative x\<le>90"
    by (rule comma_offset_representative_admitted(1))
  have rep_orbit: "comma_offset_orbit (comma_offset_representative x)=comma_offset_orbit x"
    by (rule comma_offset_representative_admitted(2))
  have congruent: "comma_decade_block_power k
      (Comma_Decade r (comma_offset_representative x))=
    comma_decade_block_power k (Comma_Decade r x)"
    by (rule comma_decade_block_power_orbit_congruent[OF rep_bound xb rep_orbit])
  show ?thesis
    by (simp only: comma_decade_orbit_layer_lookup_def length x HOL.simp_thms
      if_True slot congruent)
qed

fun comma_decade_orbit_layer_resume ::
  "nat \<Rightarrow> comma_decade_block_result list \<Rightarrow>
    comma_decade_state \<Rightarrow> comma_decade_block_result" where
  "comma_decade_orbit_layer_resume phase layer (Comma_Decade r x)=
    (if phase<924 \<and> r=phase then comma_decade_orbit_layer_lookup layer x
      else Comma_Block_Invalid)"

definition comma_decade_orbit_layer_square ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_decade_block_result list \<Rightarrow>
   comma_decade_block_result list \<Rightarrow> comma_decade_block_result list" where
  "comma_decade_orbit_layer_square k r left right =
    (if r<924 \<and> length left=46 \<and> length right=46 then
      map (\<lambda>answer. comma_decade_block_then (2^k) answer
        (comma_decade_orbit_layer_resume ((r+2^k) mod 924) right)) left
     else [])"

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: comma_decade_orbit_layer_square_correct"\<close>

theorem comma_decade_orbit_layer_square_correct:
  assumes phase: "r<924"
    and left: "comma_decade_orbit_layer_correct k r left"
    and right: "comma_decade_orbit_layer_correct k ((r+2^k) mod 924) right"
  shows "comma_decade_orbit_layer_correct (Suc k) r
    (comma_decade_orbit_layer_square k r left right)"
proof -
  have lengths: "length left=46" "length right=46"
    using left right by (simp_all add: comma_decade_orbit_layer_correct_def)
  have point: "\<And>i. i<46 \<Longrightarrow>
    (comma_decade_orbit_layer_square k r left right)!i=
      comma_decade_block_power (Suc k)
        (Comma_Decade r (comma_offset_representatives!i))"
  proof -
    fix i :: nat assume i: "i<46"
    let ?x = "comma_offset_representatives!i"
    have x: "?x\<le>90" by (rule comma_offset_representative_slot(1)[OF i])
    have admitted: "comma_decade_admitted (Comma_Decade r ?x)"
      using phase x by simp
    have current: "left!i=comma_decade_block_power k (Comma_Decade r ?x)"
      using left i by (simp add: comma_decade_orbit_layer_correct_def)
    have index: "i<length left" using i lengths(1) by simp
    show "(comma_decade_orbit_layer_square k r left right)!i=
      comma_decade_block_power (Suc k) (Comma_Decade r ?x)"
    proof (cases "comma_decade_block_power k (Comma_Decade r ?x)")
      case (Comma_Block_Live t)
      obtain a b where t: "t=Comma_Decade a b" by (cases t) auto
      have live: "comma_decade_block_power k (Comma_Decade r ?x)=
        Comma_Block_Live (Comma_Decade a b)"
        using Comma_Block_Live by (simp only: t)
      have helix: "a=(r+2^k) mod 924" "b<91"
        using comma_decade_block_power_live_helix[OF admitted live] by auto
      have lookup: "comma_decade_orbit_layer_resume ((r+2^k) mod 924) right t=
        comma_decade_block_power k t"
        using comma_decade_orbit_layer_lookup_correct[OF right helix(2)]
        by (simp add: t helix(1))
      have guard: "r<924 \<and> length left=46 \<and> length right=46"
        using phase lengths by simp
      show ?thesis
        by (simp only: comma_decade_orbit_layer_square_def guard HOL.simp_thms if_True
          nth_map[OF index] current comma_decade_block_power.simps Comma_Block_Live
          comma_decade_block_then.simps lookup)
    qed (simp_all add: comma_decade_orbit_layer_square_def phase lengths current
      nth_map[OF index] comma_decade_block_power.simps(2))
  qed
  show ?thesis using phase lengths point
    by (simp add: comma_decade_orbit_layer_correct_def
      comma_decade_orbit_layer_square_def)
qed


ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: comma_decade_orbit_square_layer_valueI"\<close>

lemma comma_decade_orbit_square_layer_valueI:
  assumes level_eq: "next=Suc k" and shifted: "phase=(r+2^k) mod 924"
    and admitted: "r<924"
    and left: "comma_decade_orbit_layer_correct k r lhs"
    and right: "comma_decade_orbit_layer_correct k phase rhs"
    and evaluated: "comma_decade_orbit_layer_square k r lhs rhs=result"
  shows "comma_decade_orbit_layer_correct next r result"
proof -
  have transported: "comma_decade_orbit_layer_correct k ((r+2^k) mod 924) rhs"
    using right by (simp only: shifted)
  have joined: "comma_decade_orbit_layer_correct (Suc k) r
      (comma_decade_orbit_layer_square k r lhs rhs)"
    by (rule comma_decade_orbit_layer_square_correct[OF admitted left transported])
  show ?thesis using joined by (simp only: level_eq evaluated)
qed

definition comma_decade_orbit_layer_complete ::
  "nat \<Rightarrow> comma_decade_block_result list \<Rightarrow> bool" where
  "comma_decade_orbit_layer_complete bound layer =
    (length layer=46 \<and> list_all (comma_decade_block_stopped_below bound) layer)"

lemma comma_decade_orbit_layer_complete_sound:
  assumes correct: "comma_decade_orbit_layer_correct k r layer"
    and complete: "comma_decade_orbit_layer_complete bound layer"
    and x: "x<91"
  shows "\<exists>h terminal. comma_decade_block_power k (Comma_Decade r x)=
    Comma_Block_Stop h terminal \<and> h\<le>bound"
proof -
  have length: "length layer=46"
    using correct by (simp add: comma_decade_orbit_layer_correct_def)
  have oi: "comma_offset_orbit x<46" by (rule comma_offset_orbit_bound)
  have member: "layer!(comma_offset_orbit x) \<in> set layer"
    using oi length by simp
  have stopped: "comma_decade_block_stopped_below bound
      (layer!(comma_offset_orbit x))"
    using complete member
    by (auto simp: comma_decade_orbit_layer_complete_def list_all_iff)
  have lookup: "comma_decade_orbit_layer_lookup layer x=
    layer!(comma_offset_orbit x)"
    using length x by (simp add: comma_decade_orbit_layer_lookup_def)
  have evaluated: "comma_decade_orbit_layer_lookup layer x=
    comma_decade_block_power k (Comma_Decade r x)"
    by (rule comma_decade_orbit_layer_lookup_correct[OF correct x])
  show ?thesis using stopped lookup evaluated
    by (cases "layer!(comma_offset_orbit x)")
      (auto simp only: comma_decade_block_stopped_below.simps)
qed

lemma comma_decade_orbit_layer_rejects_malformed:
  "comma_decade_orbit_layer_lookup [] x=Comma_Block_Invalid"
  "comma_decade_orbit_layer_lookup layer 91=Comma_Block_Invalid"
  "comma_decade_orbit_layer_square k r [] right=[]"
  "comma_decade_orbit_layer_resume 924 layer s=Comma_Block_Invalid"
proof -
  show "comma_decade_orbit_layer_lookup [] x=Comma_Block_Invalid"
    by (simp add: comma_decade_orbit_layer_lookup_def)
  show "comma_decade_orbit_layer_lookup layer 91=Comma_Block_Invalid"
    by (simp add: comma_decade_orbit_layer_lookup_def)
  show "comma_decade_orbit_layer_square k r [] right=[]"
    by (simp add: comma_decade_orbit_layer_square_def)
  show "comma_decade_orbit_layer_resume 924 layer s=Comma_Block_Invalid"
    by (cases s) simp
qed

lemma comma_decade_orbit_layer_correct_length:
  "comma_decade_orbit_layer_correct k r layer \<Longrightarrow> length layer=46"
  by (simp add: comma_decade_orbit_layer_correct_def)

lemma comma_decade_orbit_layer_lookup_weak_cong:
  "x=y \<Longrightarrow> comma_decade_orbit_layer_lookup layer x=
    comma_decade_orbit_layer_lookup layer y"
  by simp

lemma comma_decade_orbit_layer_resume_weak_cong:
  "phase=phase' \<Longrightarrow> s=s' \<Longrightarrow>
    comma_decade_orbit_layer_resume phase layer s=
      comma_decade_orbit_layer_resume phase' layer s'"
  by simp

lemma comma_decade_orbit_layer_nth_weak_cong:
  "x=y \<Longrightarrow> (layer::comma_decade_block_result list)!x=layer!y"
  by simp

lemma comma_decade_orbit_layer_length_weak_cong:
  "length (layer::comma_decade_block_result list)=length layer"
  by (rule refl)

lemma comma_decade_orbit_layer_square_weak_cong:
  "k=k' \<Longrightarrow> r=r' \<Longrightarrow>
    comma_decade_orbit_layer_square k r left right=
      comma_decade_orbit_layer_square k' r' left right"
  by simp

ML \<open>if getenv "COMMA_PROFILE_LOG" = "" then () else Comma_Fast_Kernel.report "Orbit layer: ML_file"\<close>

ML_file "orbit_layer_check.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_block_power_orbit_congruent
      comma_decade_orbit_base_layer_correct comma_decade_orbit_base_layer_valueI
      comma_decade_orbit_square_layer_valueI comma_decade_orbit_layer_lookup_correct
      comma_decade_orbit_layer_square_correct comma_decade_orbit_layer_complete_sound
      comma_decade_orbit_layer_correct_length comma_decade_orbit_layer_rejects_malformed}) then ()
    else error "Orbit layer refinement depends on an oracle";
\<close>

end
