theory Comma_Decade_Layer_Check
  imports Comma_Decade_Blocks.Comma_Decade_Blocks
    Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
begin

text \<open>The evaluator publishes one checked 91-result layer. Arithmetic
is evaluated only for base phases; squares consume literal checked child
layers. Neither the scalar block-run specification nor block-power equations
belongs to the square evaluator. No complete catalog is built at theory load.\<close>

lemma comma_decade_base_layer_valueI:
  assumes "comma_decade_base_layer r=layer"
  shows "comma_decade_layer_correct 0 r layer"
  using comma_decade_base_layer_correct[of r] assms by simp

lemma comma_decade_block_atom_orbit_representative:
  assumes "x\<le>90"
  shows "comma_decade_block_atom (Comma_Decade r x)=
    comma_decade_block_atom (Comma_Decade r (comma_offset_representative x))"
proof -
  have control: "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r (comma_offset_representative x))"
    by (rule comma_decade_control_orbit_congruent[OF assms
      comma_offset_representative_admitted(1)])
      (simp only: comma_offset_representative_admitted(2))
  show ?thesis
    by (simp only: comma_decade_block_atom_def comma_decade_admitted.simps
      assms comma_offset_representative_admitted(1) control HOL.simp_thms)
qed

lemma comma_decade_base_layer_orbit:
  "comma_decade_base_layer r=map (\<lambda>x.
    comma_decade_block_atom (Comma_Decade r (comma_offset_representative x))) [0..<91]"
  unfolding comma_decade_base_layer_def
  by (rule map_cong) (auto intro: comma_decade_block_atom_orbit_representative)

text \<open>The coordinate-only representative equalities are compiled once.
Every phase uses the same ninety-one closed kernel equations; evaluating the
signed polynomial and list selection again per base phase would undo the
benefit of sharing the forty-six control representatives.\<close>

local_setup \<open>fn lthy =>
  let
    val (certify, _) = Comma_Entry_Arithmetic.make_certifier lthy
    val arithmetic = Comma_Entry_Arithmetic.natural_context lthy addsimps
      @{thms comma_offset_representative_def comma_offset_representatives_def
        comma_offset_orbit_def comma_digit_orbit_sum_def power2_eq_square
        nth_Cons' of_nat_numeral of_nat_0 of_nat_1
        zmod_zminus1_eq_if zmod_zminus2_eq_if}
    fun check x =
      let
        val source = @{term comma_offset_representative} $ HOLogic.mk_number @{typ nat} x
        val theorem = certify (Simplifier.rewrite arithmetic (Thm.cterm_of lthy source))
        val (typ, value) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem))
        val _ = if typ = @{typ nat} andalso 0 <= value andalso value <= 90 then ()
          else error "Invalid checked offset representative"
      in theorem end
    val facts = map check (0 upto 90)
  in #2 (Local_Theory.note
    ((Binding.name "comma_layer_offset_constants", []), facts) lthy) end\<close>

lemma comma_decade_square_layer_valueI:
  assumes level_eq: "next=Suc k" and shifted: "phase=(r+2^k) mod 924"
    and admitted: "r<924"
    and left: "comma_decade_layer_correct k r lhs"
    and right: "comma_decade_layer_correct k phase rhs"
    and evaluated: "comma_decade_layer_square k r lhs rhs=result"
  shows "comma_decade_layer_correct next r result"
proof -
  have transported: "comma_decade_layer_correct k ((r+2^k) mod 924) rhs"
    using right by (simp only: shifted)
  have joined: "comma_decade_layer_correct (Suc k) r
      (comma_decade_layer_square k r lhs rhs)"
    by (rule comma_decade_layer_square_correct[OF admitted left transported])
  show ?thesis using joined by (simp only: level_eq evaluated)
qed

lemma comma_decade_layer_rejects_malformed:
  "comma_decade_layer_lookup [] x=Comma_Block_Invalid"
  "comma_decade_layer_square k r [] right=[]"
  "comma_decade_layer_resume 924 layer s=Comma_Block_Invalid"
proof -
  show "comma_decade_layer_lookup [] x=Comma_Block_Invalid"
    by (simp add: comma_decade_layer_lookup_def)
  show "comma_decade_layer_square k r [] right=[]"
    by (simp add: comma_decade_layer_square_def)
  show "comma_decade_layer_resume 924 layer s=Comma_Block_Invalid"
    by (cases s) simp
qed

lemma comma_decade_layer_cache_key_injective:
  fixes level level' phase phase' :: nat
  assumes "phase<924" "phase'<924"
    "level*924+phase=level'*924+phase'"
  shows "level=level' \<and> phase=phase'"
proof -
  have levels: "level=level'"
    using arg_cong[OF assms(3), of "\<lambda>n. n div 924"] assms(1,2)
    by simp
  have phases: "phase=phase'"
    using assms(3) levels by simp
  show ?thesis using levels phases by simp
qed

lemma comma_decade_layer_correct_length:
  "comma_decade_layer_correct k r layer \<Longrightarrow> length layer=91"
  by (simp add: comma_decade_layer_correct_def)

text \<open>Completed child layers are immutable values. Only scalar routing
arguments need simplification while applying a layer; selected length facts
are retained at publication. These congruences do not alter lookup semantics.\<close>
lemma comma_decade_layer_lookup_weak_cong:
  "x=y \<Longrightarrow> comma_decade_layer_lookup layer x=comma_decade_layer_lookup layer y"
  by simp

lemma comma_decade_layer_resume_weak_cong:
  "phase=phase' \<Longrightarrow> s=s' \<Longrightarrow>
    comma_decade_layer_resume phase layer s=comma_decade_layer_resume phase' layer s'"
  by simp

lemma comma_decade_layer_nth_weak_cong:
  "x=y \<Longrightarrow> (layer::comma_decade_block_result list)!x=layer!y"
  by simp

lemma comma_decade_layer_length_weak_cong:
  "length (layer::comma_decade_block_result list)=length layer"
  by (rule refl)

lemma comma_decade_layer_square_weak_cong:
  "k=k' \<Longrightarrow> r=r' \<Longrightarrow>
    comma_decade_layer_square k r left right=comma_decade_layer_square k' r' left right"
  by simp

ML_file "decade_layer_check.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_base_layer_valueI comma_decade_square_layer_valueI
      comma_decade_block_atom_orbit_representative comma_decade_base_layer_orbit
      comma_layer_offset_constants
      comma_decade_layer_rejects_malformed comma_decade_layer_cache_key_injective
      comma_decade_layer_correct_length comma_decade_layer_lookup_weak_cong
      comma_decade_layer_resume_weak_cong comma_decade_layer_nth_weak_cong
      comma_decade_layer_length_weak_cong comma_decade_layer_square_weak_cong}) then ()
    else error "Layer construction bridge depends on an oracle";
\<close>
end
