theory Comma_Semantic_Phase_Action_Program
  imports Comma_Semantic_Phase_Class_Endpoint
    Comma_Near_Symbolic_Operator
begin

text \<open>
The program constructors below are control identities.  They contain no
absolute phase, source shift, complete-decade count, or concrete Near
headroom.  Those values remain application environment.  The entry payload
is a normalized residue together with the Frobenius core that owns its
selector; a Near payload is the reduced residual coordinate.  Boundary Near
programs have a source-independent control action: their application guard
forces headroom one. Physical headroom is checked at admission, rather than
passed into or interned with the normalized control action.
\<close>

datatype comma_phase_core_id =
    Comma_Core_1
  | Comma_Core_3
  | Comma_Core_7
  | Comma_Core_11
  | Comma_Core_13
  | Comma_Core_21
  | Comma_Core_23
  | Comma_Core_27
  | Comma_Core_29

fun comma_phase_core_modulus :: "comma_phase_core_id \<Rightarrow> nat" where
  "comma_phase_core_modulus Comma_Core_1 = 1"
| "comma_phase_core_modulus Comma_Core_3 = 3"
| "comma_phase_core_modulus Comma_Core_7 = 7"
| "comma_phase_core_modulus Comma_Core_11 = 11"
| "comma_phase_core_modulus Comma_Core_13 = 13"
| "comma_phase_core_modulus Comma_Core_21 = 21"
| "comma_phase_core_modulus Comma_Core_23 = 23"
| "comma_phase_core_modulus Comma_Core_27 = 27"
| "comma_phase_core_modulus Comma_Core_29 = 29"

lemma comma_phase_core_modulus_domain:
  "comma_phase_core_modulus core\<in>{1,3,7,11,13,21,23,27,29}"
  by (cases core) simp_all

lemma comma_phase_core_clock_value_bound:
  "comma_cyclotomic_clock_core_value C (comma_phase_core_modulus core) <
    comma_phase_core_modulus core"
  by (rule comma_cyclotomic_clock_core_value_bound
      [OF comma_phase_core_modulus_domain])

definition comma_phase_core_of_modulus :: "nat \<Rightarrow> comma_phase_core_id option" where
  "comma_phase_core_of_modulus c =
    (if c=1 then Some Comma_Core_1
     else if c=3 then Some Comma_Core_3
     else if c=7 then Some Comma_Core_7
     else if c=11 then Some Comma_Core_11
     else if c=13 then Some Comma_Core_13
     else if c=21 then Some Comma_Core_21
     else if c=23 then Some Comma_Core_23
     else if c=27 then Some Comma_Core_27
     else if c=29 then Some Comma_Core_29
     else None)"

lemma comma_phase_core_of_modulus_exact:
  "comma_phase_core_of_modulus c = Some core \<Longrightarrow>
   comma_phase_core_modulus core = c"
  by (cases core)
    (auto simp: comma_phase_core_of_modulus_def split: if_splits)

datatype comma_semantic_port_program =
    Comma_Entry_Core_Program nat nat nat comma_phase_core_id
  | Comma_Near_Residual_Program nat nat nat
  | Comma_Near_Boundary_Program nat

definition comma_entry_control_program ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_port_program option" where
  "comma_entry_control_program f x =
    (let d=x mod 10;
         P=comma_finite_period_fast f d;
         c=comma_core_modulus P
     in map_option (Comma_Entry_Core_Program f d (x mod P))
          (comma_phase_core_of_modulus c))"

definition comma_near_control_program ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_port_program" where
  "comma_near_control_program f H =
    (let g=(if f<9 then 1 else 0)+1;
         d=(10-H mod 10) mod 10
     in if g\<le>H then
          let P=comma_finite_period_fast f d
          in Comma_Near_Residual_Program f d ((H-g) mod P)
        else Comma_Near_Boundary_Program f)"

definition comma_phase_core_entry_key ::
    "comma_cyclotomic_clock \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_phase_core_id \<Rightarrow> (nat \<times> nat) option" where
  "comma_phase_core_entry_key C f d x core =
    (let P=comma_finite_period_fast f d;
         c=comma_core_modulus P;
         core_c=comma_phase_core_modulus core
     in if d<10 \<and> d=x mod 10 \<and> c=core_c then
          Some (comma_decisive_entry_clock_key_with_core C f x core_c)
        else None)"

definition comma_phase_program_at_entry ::
    "comma_semantic_port_program \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action option" where
  "comma_phase_program_at_entry program phase =
    (case program of
       Comma_Entry_Core_Program f d residue core \<Rightarrow>
         if comma_sector_entry_bound f residue \<and> d<10 \<and>
            residue mod 10=d \<and>
            residue<comma_finite_period_fast f d \<and>
            comma_phase_core_modulus core =
              comma_core_modulus (comma_finite_period_fast f d)
         then (case comma_phase_core_entry_key
                   (comma_cyclotomic_clock_of (phase mod 924))
                   f d residue core of
             None \<Rightarrow> None
           | Some (key_digit,key_residue) \<Rightarrow>
               (case comma_entry_port_refined_locator f key_digit key_residue of
                  Some (_,_,h) \<Rightarrow>
                    Some (comma_semantic_b1_near_control_port_action f 0 h)
                | None \<Rightarrow> Some Comma_Continuation_Invalid))
         else None
     | _ \<Rightarrow> None)"

definition comma_phase_program_apply_entry ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action option" where
  "comma_phase_program_apply_entry f x phase =
    (if comma_sector_entry_bound f x then
       (case comma_entry_control_program f x of
          None \<Rightarrow> None
        | Some program \<Rightarrow>
            (case program of
               Comma_Entry_Core_Program f' d residue core \<Rightarrow>
                 comma_phase_program_at_entry program
                   (phase mod comma_core_period (comma_phase_core_modulus core))
             | _ \<Rightarrow> None))
     else None)"

definition comma_phase_program_at_near ::
    "comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action option" where
  "comma_phase_program_at_near program H phase =
    (case program of
       Comma_Near_Residual_Program f d residual \<Rightarrow>
         (let g=(if f<9 then 1 else 0)+1;
              P=comma_finite_period_fast f d
         in if 1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
                d<10 \<and> residual<P \<and> g\<le>H \<and>
                d=(10-H mod 10) mod 10 \<and>
                residual=(H-g) mod P
             then Some (fst (comma_near_symbolic_port_operator f (g+residual) phase))
             else None)
     | Comma_Near_Boundary_Program f \<Rightarrow>
         (let e=(if f<9 then 1 else 0)
          in if 1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
                e\<ge>H then
               Some (fst (comma_near_symbolic_port_operator f H phase))
             else None)
     | _ \<Rightarrow> None)"

definition comma_semantic_port_program_of_source ::
    "comma_finite_position \<Rightarrow> comma_semantic_port_program option" where
  "comma_semantic_port_program_of_source source =
    (case comma_source_continuation_base source of
       Comma_Entry f delta x \<Rightarrow>
         if comma_canonical_position_admitted
             (comma_source_continuation_base source)
         then comma_entry_control_program f x else None
     | Comma_Near f delta H \<Rightarrow>
         if comma_canonical_position_admitted
             (comma_source_continuation_base source)
         then Some (comma_near_control_program f H) else None)"

lemma comma_semantic_port_program_shift_invariant:
  "comma_semantic_port_program_of_source (comma_shift_position k source) =
   comma_semantic_port_program_of_source source"
  by (cases source)
    (simp_all add: comma_semantic_port_program_of_source_def
      comma_shift_position.simps comma_source_continuation_base.simps)

lemma comma_semantic_port_program_of_entry:
  assumes admitted: "comma_sector_entry_bound f x"
  shows "comma_semantic_port_program_of_source (Comma_Entry f delta x) =
    comma_entry_control_program f x"
  using admitted
  by (simp add: comma_semantic_port_program_of_source_def
      comma_sector_entry_bound_def)

lemma comma_semantic_port_program_of_near:
  assumes admitted: "1\<le>f" "f\<le>9" "1\<le>H" "H\<le>540"
  shows "comma_semantic_port_program_of_source (Comma_Near f delta H) =
    Some (comma_near_control_program f H)"
  using assms
  by (simp add: comma_semantic_port_program_of_source_def
      comma_canonical_position_admitted_def)

lemma comma_phase_core_entry_key_refines_decisive:
  assumes digit: "d=x mod 10"
    and core: "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f d)"
  shows "comma_phase_core_entry_key
      (comma_cyclotomic_clock_of (phase mod 924))
      f d x core =
    Some (comma_decisive_entry_clock_key
      (comma_cyclotomic_clock_of (phase mod 924)) f x)"
proof -
  have core_for_x:
    "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f (x mod 10))"
    using core digit by simp
  have exact:
    "comma_decisive_entry_clock_key_with_core
        (comma_cyclotomic_clock_of (phase mod 924)) f x
        (comma_phase_core_modulus core) =
      comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of (phase mod 924)) f x"
    by (rule comma_decisive_entry_clock_key_with_core_exact[OF core_for_x])
  show ?thesis
    using digit core exact
    by (simp add: comma_phase_core_entry_key_def Let_def)
qed

lemma comma_phase_program_at_entry_core_refines:
  assumes canonical: "comma_sector_entry_bound f x"
    and digit: "d=x mod 10"
    and residue: "x<comma_finite_period_fast f d"
    and core: "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f d)"
  shows "comma_phase_program_at_entry
      (Comma_Entry_Core_Program f d x core) phase =
    Some (comma_c1_b1_entry_core_port_action f x phase)"
proof -
  have key:
    "comma_phase_core_entry_key
        (comma_cyclotomic_clock_of (phase mod 924))
        f d x core =
      Some (comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of (phase mod 924)) f x)"
    by (rule comma_phase_core_entry_key_refines_decisive[OF digit core])
  show ?thesis
    using key canonical digit residue core
    by (simp add: comma_phase_program_at_entry_def
      comma_c1_b1_entry_core_port_action_def
      split: prod.splits option.splits)
qed

lemma comma_entry_control_program_core:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "\<exists>core. comma_phase_core_of_modulus
      (comma_core_modulus (comma_finite_period_fast f (x mod 10))) = Some core
    \<and> comma_entry_control_program f x =
      Some (Comma_Entry_Core_Program f (x mod 10)
        (x mod comma_finite_period_fast f (x mod 10)) core)"
proof -
  let ?P="comma_finite_period_fast f (x mod 10)"
  let ?c="comma_core_modulus ?P"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have lift: "comma_core_lift_admitted ?P"
    by (rule comma_core_lift_catalog[OF catalog])
  have core: "?c\<in>{1,3,7,11,13,21,23,27,29}"
    using lift by (auto simp: comma_core_lift_admitted_def Let_def)
  obtain core where core_present: "comma_phase_core_of_modulus ?c=Some core"
    using core by (auto simp: comma_phase_core_of_modulus_def)
  show ?thesis
    using core_present
    by (intro exI[of _ core], simp add: comma_entry_control_program_def Let_def)
qed

lemma comma_entry_control_program_port_exact:
  fixes f x phase :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "comma_sector_entry_bound f x"
  shows "comma_phase_program_apply_entry f x phase =
    Some (comma_semantic_b1_source_port_action (Comma_Entry f 0 x)
      (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)))"
proof -
  let ?P="comma_finite_period_fast f (x mod 10)"
  let ?residue="x mod ?P"
  obtain core where core_present:
    "comma_phase_core_of_modulus (comma_core_modulus ?P)=Some core"
    and program:
    "comma_entry_control_program f x =
      Some (Comma_Entry_Core_Program f (x mod 10) ?residue core)"
    using comma_entry_control_program_core[OF sector] by blast
  have x_bound: "x\<le>98"
    using admitted by (auto simp: comma_sector_entry_bound_def)
  have x_sector_bound: "x\<le>89+f"
    using admitted by (simp add: comma_sector_entry_bound_def)
  have source_admitted:
    "comma_round_admitted (Comma_Entry f 0 x)"
    using sector admitted by (simp add: comma_sector_entry_bound_def)
  have source_period_positive:
    "0<comma_decisive_sector_period (Comma_Entry f 0 x)"
    by (rule comma_decisive_sector_period_admitted(1)[OF source_admitted])
  have core_exact:
    "comma_phase_core_modulus core = comma_core_modulus ?P"
    by (rule comma_phase_core_of_modulus_exact[OF core_present])
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have digit_residue: "?residue mod 10=x mod 10"
  proof -
    have ten_divides: "10 dvd ?P"
      by (rule comma_entry_period_decimal(2)[OF catalog])
    show ?thesis using ten_divides
      by (simp only: mod_mod_cancel[OF ten_divides])
  qed
  have period_positive: "0<?P"
    by (rule comma_entry_period_decimal(1)[OF catalog])
  have residue_le_source: "?residue\<le>x"
  proof -
    have equation: "x div ?P * ?P + x mod ?P = x"
      by (rule div_mult_mod_eq)
    show ?thesis using equation by arith
  qed
  have residue_bound: "?residue\<le>98"
    using x_bound residue_le_source by arith
  have residue_sector_bound: "?residue\<le>89+f"
    by (rule order_trans[OF residue_le_source x_sector_bound])
  have residue_canonical: "comma_sector_entry_bound f ?residue"
    using sector residue_sector_bound
    by (simp add: comma_sector_entry_bound_def)
  have residue_lt: "?residue<?P"
    using period_positive by simp
  have rebase:
    "comma_semantic_b1_entry_near_port_action f x
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
     comma_semantic_b1_entry_near_port_action f ?residue
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x))"
    by (rule comma_semantic_b1_entry_control_port_modular_rebase[OF sector
      digit_residue[symmetric]]) simp
  have core_action_exact:
    "comma_c1_b1_entry_core_port_action f ?residue
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
      comma_semantic_b1_entry_near_port_action f ?residue
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x))"
  proof -
    have source_exact:
      "comma_c1_b1_entry_core_port_action f ?residue
          (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
       comma_semantic_b1_source_port_action (Comma_Entry f 0 ?residue)
          (phase mod comma_decisive_sector_period (Comma_Entry f 0 x))"
      by (rule comma_c1_b1_entry_core_port_action_source_exact[OF sector residue_bound])
    have period:
      "comma_decisive_sector_period (Comma_Entry f 0 x) =
       comma_decisive_sector_period (Comma_Entry f 0 ?residue)"
      by (rule comma_semantic_b1_entry_local_period_modular_rebase
        [OF digit_residue[symmetric]])
    have slot:
      "phase mod comma_decisive_sector_period (Comma_Entry f 0 x) <
       comma_decisive_sector_period (Comma_Entry f 0 ?residue)"
      using period source_period_positive by simp
    have admitted_residue: "comma_round_admitted (Comma_Entry f 0 ?residue)"
      using sector residue_bound by simp
    have local:
      "comma_semantic_b1_source_port_action (Comma_Entry f 0 ?residue)
          (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
       comma_semantic_b1_entry_near_port_action f ?residue
          (phase mod comma_decisive_sector_period (Comma_Entry f 0 x))"
      by (rule comma_semantic_b1_entry_slot_action_near
        [OF admitted_residue slot])
    show ?thesis using source_exact local by simp
  qed
  have original_action:
    "comma_semantic_b1_entry_near_port_action f x
      (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
     comma_semantic_b1_source_port_action (Comma_Entry f 0 x)
      (phase mod comma_decisive_sector_period (Comma_Entry f 0 x))"
  proof -
    have slot:
      "phase mod comma_decisive_sector_period (Comma_Entry f 0 x) <
       comma_decisive_sector_period (Comma_Entry f 0 x)"
      using comma_decisive_sector_period_admitted(1)[OF source_admitted]
      by simp
    show ?thesis
      by (rule sym, rule comma_semantic_b1_entry_slot_action_near
        [OF source_admitted slot])
  qed
  have program_action:
    "comma_phase_program_at_entry
        (Comma_Entry_Core_Program f (x mod 10) ?residue core)
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
      Some (comma_c1_b1_entry_core_port_action f ?residue
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)))"
    by (rule comma_phase_program_at_entry_core_refines[OF residue_canonical
      digit_residue[symmetric] residue_lt core_exact])
  have program_action_exact:
    "comma_phase_program_at_entry
        (Comma_Entry_Core_Program f (x mod 10) ?residue core)
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)) =
      Some (comma_semantic_b1_source_port_action (Comma_Entry f 0 x)
        (phase mod comma_decisive_sector_period (Comma_Entry f 0 x)))"
    using program_action core_action_exact rebase original_action by simp
  show ?thesis
    using program program_action_exact core_exact admitted
    by (simp add: comma_phase_program_apply_entry_def
      comma_decisive_sector_period_def)
qed

lemma comma_near_residual_program_port_exact:
  fixes f H phase :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "1\<le>H" "H\<le>540"
    and interior: "(if f<9 then 1 else 0)<H"
  shows "comma_phase_program_at_near (comma_near_control_program f H) H phase =
    Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H)
      (phase mod comma_decisive_sector_period (Comma_Near f 0 H)))"
proof -
  let ?g="(if f<9 then 1 else 0)+1"
  let ?d="(10-H mod 10) mod 10"
  let ?P="comma_finite_period_fast f ?d"
  let ?b="(H-?g) mod ?P"
  let ?h0="?g+?b"
  have g_le: "?g\<le>H" using interior by arith
  have digit: "?d<10" by simp
  have period_positive:
    "0<?P"
    by (rule comma_near_fast_period_positive_decimal(1)[OF sector digit])
  have residual_bound: "?b<?P"
    using period_positive by simp
  have program:
    "comma_near_control_program f H =
      Comma_Near_Residual_Program f ?d ?b"
    using g_le by (simp add: comma_near_control_program_def Let_def)
  have residual_operator:
    "comma_near_symbolic_port_operator f H phase =
      (fst (comma_near_symbolic_port_operator f ?h0 phase),
       fst (snd (comma_near_residual_binding f H)) +
         snd (comma_near_symbolic_port_operator f ?h0 phase))"
    using comma_near_symbolic_port_operator_residual
      [OF sector admitted interior, of phase]
    by (simp add: comma_near_residual_binding_def Let_def)
  have same_action:
    "fst (comma_near_symbolic_port_operator f H phase) =
      fst (comma_near_symbolic_port_operator f ?h0 phase)"
    using residual_operator by (metis fst_conv)
  have source_operator:
    "fst (comma_near_symbolic_port_operator f H 0) =
      comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0"
    using comma_near_symbolic_port_operator_source[of f H 0]
    by simp
  have phase_independent:
    "fst (comma_near_symbolic_port_operator f H phase) =
      fst (comma_near_symbolic_port_operator f H 0)"
    by (simp only: comma_near_symbolic_port_operator_eval)
  have period:
    "comma_decisive_sector_period (Comma_Near f 0 H)=1"
    by (simp add: comma_decisive_sector_period_def)
  have guard: "1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
      ?d<10 \<and> ?b<?P \<and> ?g\<le>H \<and>
      ?d=(10-H mod 10) mod 10 \<and> ?b=(H-?g) mod ?P"
    using sector admitted digit residual_bound g_le by blast
  have image: "comma_phase_program_at_near
      (comma_near_control_program f H) H phase =
      Some (fst (comma_near_symbolic_port_operator f ?h0 phase))"
    by (simp only: program comma_phase_program_at_near_def
      comma_semantic_port_program.case Let_def if_P[OF guard])
  have value_exact: "fst (comma_near_symbolic_port_operator f ?h0 phase) =
      comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0"
    by (rule trans[OF same_action[symmetric]
      trans[OF phase_independent source_operator]])
  have exact: "comma_phase_program_at_near (comma_near_control_program f H) H phase =
      Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0)"
    using image by (simp only: value_exact)
  show ?thesis using exact by (simp only: period mod_by_1)
qed

lemma comma_near_boundary_program_port_exact:
  fixes f H phase :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "1\<le>H" "H\<le>540"
    and boundary: "(if f<9 then 1 else 0)\<ge>H"
  shows "comma_phase_program_at_near (comma_near_control_program f H) H phase =
    Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H)
      (phase mod comma_decisive_sector_period (Comma_Near f 0 H)))"
proof -
  have not_residual: "\<not> ((if f<9 then 1 else 0)+1\<le>H)"
    using boundary by arith
  have program:
    "comma_near_control_program f H = Comma_Near_Boundary_Program f"
    using not_residual
    by (simp add: comma_near_control_program_def Let_def)
  have source_operator:
    "fst (comma_near_symbolic_port_operator f H 0) =
      comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0"
    using comma_near_symbolic_port_operator_source[of f H 0] by simp
  have phase_independent:
    "fst (comma_near_symbolic_port_operator f H phase) =
      fst (comma_near_symbolic_port_operator f H 0)"
    by (simp only: comma_near_symbolic_port_operator_eval)
  have period:
    "comma_decisive_sector_period (Comma_Near f 0 H)=1"
    by (simp add: comma_decisive_sector_period_def)
  have guard: "1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
      (if f<9 then 1 else 0)\<ge>H"
    using sector admitted boundary by blast
  have image: "comma_phase_program_at_near
      (comma_near_control_program f H) H phase =
      Some (fst (comma_near_symbolic_port_operator f H phase))"
    by (simp only: program comma_phase_program_at_near_def
      comma_semantic_port_program.case Let_def if_P[OF guard])
  have value_exact: "fst (comma_near_symbolic_port_operator f H phase) =
      comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0"
    by (rule trans[OF phase_independent source_operator])
  have exact: "comma_phase_program_at_near (comma_near_control_program f H) H phase =
      Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H) 0)"
    using image by (simp only: value_exact)
  show ?thesis using exact by (simp only: period mod_by_1)
qed

text \<open>
The normalized action program's control selector depends only on its declared
core characters.  This is a local port fact; it does not claim that a
completed return word has period at most 28.  A Goto may enter another core
and composition may restore the full 924-phase dependence.
\<close>

lemma comma_phase_program_at_entry_core_periodic:
  fixes f d x r s T :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and canonical: "comma_sector_entry_bound f x"
    and digit: "d=x mod 10"
    and residue: "x<comma_finite_period_fast f d"
    and core: "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f d)"
    and period: "T=comma_core_period (comma_phase_core_modulus core)"
    and same: "r mod T=s mod T"
  shows "comma_phase_program_at_entry
      (Comma_Entry_Core_Program f d x core) r =
    comma_phase_program_at_entry
      (Comma_Entry_Core_Program f d x core) s"
proof -
  have core_period:
    "T=comma_core_period
      (comma_core_modulus (comma_finite_period_fast f (x mod 10)))"
    using period core digit by simp
  have at_r:
    "comma_phase_program_at_entry
        (Comma_Entry_Core_Program f d x core) r =
      Some (comma_c1_b1_entry_core_port_action f x r)"
    by (rule comma_phase_program_at_entry_core_refines
      [OF canonical digit residue core])
  have at_s:
    "comma_phase_program_at_entry
        (Comma_Entry_Core_Program f d x core) s =
      Some (comma_c1_b1_entry_core_port_action f x s)"
    by (rule comma_phase_program_at_entry_core_refines
      [OF canonical digit residue core])
  have core_action:
    "comma_c1_b1_entry_core_port_action f x r =
      comma_c1_b1_entry_core_port_action f x s"
    by (rule comma_c1_b1_entry_core_port_action_period
      [OF sector core_period same])
  show ?thesis using at_r at_s core_action by simp
qed

lemma comma_near_symbolic_port_action_phase_independent:
  "fst (comma_near_symbolic_port_operator f H r) =
    fst (comma_near_symbolic_port_operator f H s)"
  by (simp only: comma_near_symbolic_port_operator_eval)

lemma comma_phase_program_at_near_phase_independent:
  "comma_phase_program_at_near program H r =
    comma_phase_program_at_near program H s"
  by (cases program)
    (simp_all only: comma_phase_program_at_near_def
      comma_semantic_port_program.case Let_def comma_near_symbolic_port_operator_eval)

lemma comma_phase_program_at_near_output_unique:
  assumes left:
      "comma_phase_program_at_near program H phase = Some a"
    and right:
      "comma_phase_program_at_near program H' phase = Some b"
  shows "a=b"
proof (cases program)
  case (Comma_Near_Residual_Program f d residual)
  have left_value:
    "a = fst (comma_near_symbolic_port_operator f
      (((if f<9 then 1 else 0)+1)+residual) phase)"
    using left Comma_Near_Residual_Program
    by (auto simp only: comma_phase_program_at_near_def Let_def
        comma_semantic_port_program.case if_True if_False
        option.inject option.distinct split: if_splits)
  have right_value:
    "b = fst (comma_near_symbolic_port_operator f
      (((if f<9 then 1 else 0)+1)+residual) phase)"
    using right Comma_Near_Residual_Program
    by (auto simp only: comma_phase_program_at_near_def Let_def
        comma_semantic_port_program.case if_True if_False
        option.inject option.distinct split: if_splits)
  show ?thesis using left_value right_value by simp
next
  case (Comma_Near_Boundary_Program f)
  have left_facts:
    "1\<le>f" "f\<le>9" "1\<le>H" "H\<le>540"
    "(if f<9 then 1 else 0)\<ge>H"
    "a=fst (comma_near_symbolic_port_operator f H phase)"
    using left Comma_Near_Boundary_Program
    by (auto simp only: comma_phase_program_at_near_def Let_def
        comma_semantic_port_program.case if_True if_False
        option.inject option.distinct split: if_splits)
  have right_facts:
    "1\<le>f" "f\<le>9" "1\<le>H'" "H'\<le>540"
    "(if f<9 then 1 else 0)\<ge>H'"
    "b=fst (comma_near_symbolic_port_operator f H' phase)"
    using right Comma_Near_Boundary_Program
    by (auto simp only: comma_phase_program_at_near_def Let_def
        comma_semantic_port_program.case if_True if_False
        option.inject option.distinct split: if_splits)
  have f_below_nine: "f<9"
    using left_facts(2,3,5) by (cases "f<9") auto
  have H_one: "H=1"
    using left_facts(3,5) f_below_nine by arith
  have H'_one: "H'=1"
    using right_facts(3,5) f_below_nine by arith
  show ?thesis using left_facts(6) right_facts(6) H_one H'_one by simp
next
  case (Comma_Entry_Core_Program f d residue core)
  then show ?thesis using left by (simp add: comma_phase_program_at_near_def)
qed

lemma comma_phase_program_apply_entry_same_control:
  assumes left: "comma_sector_entry_bound f x"
    and right: "comma_sector_entry_bound f' x'"
    and same: "comma_entry_control_program f x =
      comma_entry_control_program f' x'"
  shows "comma_phase_program_apply_entry f x phase =
    comma_phase_program_apply_entry f' x' phase"
  using left right same
  by (simp add: comma_phase_program_apply_entry_def
      comma_sector_entry_bound_def)

text \<open>
The normalized program is applied with the physical occurrence shift kept
outside its identity.  Entry selectors receive the shifted 924-clock phase;
the resulting base action is then transported through the occurrence shift.
This is the consumer boundary used when a completed output diagram follows a
Goto into a child program.
\<close>

definition comma_phase_program_action_at_source ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_source_continuation_action option" where
  "comma_phase_program_action_at_source phase source =
    (case source of
       Comma_Entry f delta x \<Rightarrow>
         map_option (comma_source_continuation_transport delta)
           (comma_phase_program_apply_entry f x ((phase+delta) mod 924))
     | Comma_Near f delta H \<Rightarrow>
         map_option (comma_source_continuation_transport delta)
           (comma_phase_program_at_near
             (comma_near_control_program f H) H ((phase+delta) mod 924)))"

lemma comma_phase_program_action_at_source_exact:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
  shows "comma_phase_program_action_at_source phase source =
    Some (comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet phase source))"
proof (cases source)
  case (Comma_Entry f delta x)
  let ?base = "Comma_Entry f 0 x"
  let ?clock = "(phase+delta) mod 924"
  let ?period = "comma_decisive_sector_period ?base"
  have sector: "1\<le>f" "f\<le>9"
    using admitted Comma_Entry by simp_all
  have entry_bound: "comma_sector_entry_bound f x"
    using canonical Comma_Entry by simp
  have base_admitted: "comma_round_admitted ?base"
    using sector entry_bound by (simp add: comma_sector_entry_bound_def)
  have period_positive: "0<?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF base_admitted])
  have slot_bound: "?clock mod ?period<?period"
    using period_positive by simp
  have local_port:
    "comma_phase_program_apply_entry f x ?clock =
      Some (comma_semantic_b1_source_port_action ?base
        (?clock mod ?period))"
    by (rule comma_entry_control_program_port_exact[OF sector entry_bound])
  have local_action:
    "comma_source_continuation_action_at ?base ?clock =
      comma_semantic_b1_source_port_action ?base (?clock mod ?period)"
    by (rule comma_semantic_b1_action_at_selected_port[OF base_admitted]) simp
  have local_exact:
    "comma_phase_program_apply_entry f x ?clock =
      Some (comma_source_continuation_action_at ?base ?clock)"
    using local_port local_action by simp
  have applied:
    "comma_source_continuation_transport delta
       (comma_source_continuation_action_at ?base ?clock) =
     comma_source_continuation_action_of_packet
       (comma_decisive_endpoint_packet phase (Comma_Entry f delta x))"
    using comma_source_continuation_apply_exact[OF admitted, of phase]
    by (simp add: Comma_Entry comma_source_continuation_shift.simps
      comma_source_continuation_base.simps)
  show ?thesis
    using local_exact applied Comma_Entry
    by (simp add: comma_phase_program_action_at_source_def)
next
  case (Comma_Near f delta H)
  let ?base = "Comma_Near f 0 H"
  let ?clock = "(phase+delta) mod 924"
  have sector_f: "1\<le>f" and sector_f_bound: "f\<le>9"
    using admitted Comma_Near by simp_all
  have H_positive: "1\<le>H" and H_bound: "H\<le>540"
    using admitted Comma_Near by simp_all
  have base_admitted: "comma_round_admitted ?base"
    using admitted Comma_Near by simp
  have period: "comma_decisive_sector_period ?base=1"
    by (simp add: comma_decisive_sector_period_def)
  have slot_bound: "?clock mod comma_decisive_sector_period ?base <
      comma_decisive_sector_period ?base"
    using period by simp
  have local_port:
    "comma_phase_program_at_near (comma_near_control_program f H) H ?clock =
      Some (comma_semantic_b1_source_port_action ?base
        (?clock mod comma_decisive_sector_period ?base))"
  proof (cases "(if f<9 then 1 else 0)<H")
    case True
    have interior: "(if f<9 then 1 else 0)<H" using True .
    show ?thesis
      by (rule comma_near_residual_program_port_exact
        [OF sector_f sector_f_bound H_positive H_bound interior])
  next
    case False
    have boundary: "(if f<9 then 1 else 0)\<ge>H"
      using False by simp
    show ?thesis
      by (rule comma_near_boundary_program_port_exact
        [OF sector_f sector_f_bound H_positive H_bound boundary])
  qed
  have local_action:
    "comma_source_continuation_action_at ?base ?clock =
      comma_semantic_b1_source_port_action ?base
        (?clock mod comma_decisive_sector_period ?base)"
    by (rule comma_semantic_b1_action_at_selected_port[OF base_admitted]) simp
  have local_exact:
    "comma_phase_program_at_near (comma_near_control_program f H) H ?clock =
      Some (comma_source_continuation_action_at ?base ?clock)"
    using local_port local_action by simp
  have applied:
    "comma_source_continuation_transport delta
       (comma_source_continuation_action_at ?base ?clock) =
     comma_source_continuation_action_of_packet
       (comma_decisive_endpoint_packet phase (Comma_Near f delta H))"
    using comma_source_continuation_apply_exact[OF admitted, of phase]
    by (simp add: Comma_Near comma_source_continuation_shift.simps
      comma_source_continuation_base.simps)
  show ?thesis
    using local_exact applied Comma_Near
    by (simp add: comma_phase_program_action_at_source_def)
qed

lemma comma_phase_program_action_at_source_port_exact:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "comma_phase_program_action_at_source phase source =
    Some (comma_semantic_b1_source_port_action source phase)"
proof -
  have packet:
    "comma_phase_program_action_at_source phase source =
      Some (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
    by (rule comma_phase_program_action_at_source_exact
      [OF canonical admitted])
  have port:
    "comma_semantic_b1_source_port_action source phase =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source)"
    using comma_semantic_b1_source_port_action_packet[OF admitted, of phase]
      normalized by simp
  show ?thesis using packet port by simp
qed

lemma comma_phase_program_action_at_source_round_output:
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "\<exists>action.
    comma_phase_program_action_at_source phase source = Some action \<and>
    comma_semantic_b1_source_slot_output phase action =
      comma_semantic_b1_round_output phase source"
proof -
  have action:
    "comma_phase_program_action_at_source phase source =
      Some (comma_semantic_b1_source_port_action source phase)"
    by (rule comma_phase_program_action_at_source_port_exact
      [OF canonical admitted normalized])
  have output_fact:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action source phase) =
      comma_semantic_b1_round_output phase source"
    by (rule comma_semantic_b1_port_round_output[OF admitted normalized])
  show ?thesis using action output_fact by blast
qed

lemma comma_near_residual_program_at_sector_seam_f5:
  "comma_near_control_program 5 2 =
    Comma_Near_Residual_Program 5 ((10-2 mod 10) mod 10) 0"
  by (simp add: comma_near_control_program_def Let_def)

lemma comma_near_residual_program_at_sector_seam_f9:
  "comma_near_control_program 9 1 =
    Comma_Near_Residual_Program 9 ((10-1 mod 10) mod 10) 0"
  by (simp add: comma_near_control_program_def Let_def)

lemma comma_near_residual_program_port_at_sector_seam_f5:
  "comma_phase_program_at_near (comma_near_control_program 5 2) 2 phase =
    Some (comma_semantic_b1_source_port_action (Comma_Near 5 0 2) 0)"
  using comma_near_residual_program_port_exact[of 5 2 phase]
  by (simp add: comma_decisive_sector_period_def)

lemma comma_near_residual_program_port_at_sector_seam_f9:
  "comma_phase_program_at_near (comma_near_control_program 9 1) 1 phase =
    Some (comma_semantic_b1_source_port_action (Comma_Near 9 0 1) 0)"
  using comma_near_residual_program_port_exact[of 9 1 phase]
  by (simp add: comma_decisive_sector_period_def)

text \<open>
The program evaluator has a source-independent normal-form boundary. Entry
programs are guarded by their normalized residue and core. Concrete Near
headroom is checked at the application boundary, but is absent from the
control function. Residual programs already determine their reduced input;
an admitted boundary program has headroom one. Source shifts and exact Near
elapsed weights remain separate transports.
\<close>

datatype comma_phase_program_application =
    Comma_Entry_Program_Application
  | Comma_Near_Program_Application nat

fun comma_phase_program_application_admitted ::
    "comma_semantic_port_program \<Rightarrow> comma_phase_program_application \<Rightarrow> bool"
where
  "comma_phase_program_application_admitted
      (Comma_Entry_Core_Program f d residue core)
      Comma_Entry_Program_Application =
    (1\<le>f \<and> f\<le>9 \<and> comma_sector_entry_bound f residue \<and>
      d<10 \<and> residue mod 10=d \<and>
      residue<comma_finite_period_fast f d \<and>
      comma_phase_core_modulus core =
        comma_core_modulus (comma_finite_period_fast f d))"
| "comma_phase_program_application_admitted
      (Comma_Near_Residual_Program f d residual)
      (Comma_Near_Program_Application H) =
    (let g=(if f<9 then 1 else 0)+1;
         P=comma_finite_period_fast f d
     in 1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
        d<10 \<and> residual<P \<and> g\<le>H \<and>
        d=(10-H mod 10) mod 10 \<and> residual=(H-g) mod P)"
| "comma_phase_program_application_admitted
      (Comma_Near_Boundary_Program f) (Comma_Near_Program_Application H) =
    (1\<le>f \<and> f\<le>9 \<and> 1\<le>H \<and> H\<le>540 \<and>
      (if f<9 then 1 else 0)\<ge>H)"
| "comma_phase_program_application_admitted _ _ = False"

fun comma_phase_program_operator_nf ::
    "comma_semantic_port_program \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action"
where
  "comma_phase_program_operator_nf
      (Comma_Entry_Core_Program f d residue core)
      phase =
    comma_c1_b1_entry_core_port_action f residue phase"
| "comma_phase_program_operator_nf
      (Comma_Near_Residual_Program f d residual)
      phase =
    fst (comma_near_symbolic_port_operator f
      (((if f<9 then 1 else 0)+1)+residual) phase)"
| "comma_phase_program_operator_nf (Comma_Near_Boundary_Program f) phase =
    fst (comma_near_symbolic_port_operator f 1 phase)"

lemma comma_phase_program_operator_nf_entry_core_value:
  assumes digit: "d=residue mod 10"
    and core: "comma_phase_core_modulus core =
      comma_core_modulus (comma_finite_period_fast f d)"
  shows "comma_phase_program_operator_nf
      (Comma_Entry_Core_Program f d residue core) phase =
    (let key=comma_decisive_entry_clock_key_from_core_residue f residue
         (comma_phase_core_modulus core)
         (comma_cyclotomic_clock_core_value
           (comma_cyclotomic_clock_of (phase mod 924))
           (comma_phase_core_modulus core))
     in case comma_entry_port_refined_locator f (fst key) (snd key) of
       Some (active,residual,h) \<Rightarrow>
         comma_semantic_b1_near_control_port_action f 0 h
     | None \<Rightarrow> Comma_Continuation_Invalid)"
proof -
  have core_eq:
      "comma_core_modulus (comma_finite_period_fast f (residue mod 10)) =
        comma_phase_core_modulus core"
    using digit core by simp
  show ?thesis
    by (simp only: comma_phase_program_operator_nf.simps
        comma_c1_b1_entry_core_port_action_def
        comma_decisive_entry_clock_key_def
        comma_decisive_entry_clock_key_with_core_def core_eq)
qed

lemma comma_phase_program_boundary_application_headroom:
  assumes "comma_phase_program_application_admitted
      (Comma_Near_Boundary_Program f) (Comma_Near_Program_Application H)"
  shows "H=1"
  using assms
  by (auto simp: comma_phase_program_application_admitted.simps split: if_splits)

fun comma_phase_program_operator_eval ::
    "comma_semantic_port_program \<Rightarrow> comma_phase_program_application \<Rightarrow>
      nat \<Rightarrow> comma_source_continuation_action option"
where
  "comma_phase_program_operator_eval program
      Comma_Entry_Program_Application phase =
    comma_phase_program_at_entry program phase"
| "comma_phase_program_operator_eval program
      (Comma_Near_Program_Application H) phase =
    comma_phase_program_at_near program H phase"

lemma comma_phase_program_operator_contract:
  assumes admitted:
    "comma_phase_program_application_admitted program application"
  shows "comma_phase_program_operator_eval program application phase =
    Some (comma_phase_program_operator_nf program phase)"
proof (cases program)
  case (Comma_Entry_Core_Program f d residue core)
  then show ?thesis using admitted
    by (cases application)
      (auto simp: comma_phase_program_application_admitted.simps
        comma_phase_program_operator_eval.simps
        comma_phase_program_operator_nf.simps
        dest: comma_phase_program_at_entry_core_refines)
next
  case (Comma_Near_Residual_Program f d residual)
  then show ?thesis using admitted
    by (cases application)
      (auto simp: comma_phase_program_application_admitted.simps
        comma_phase_program_operator_eval.simps
        comma_phase_program_operator_nf.simps
        comma_phase_program_at_near_def Let_def)
next
  case (Comma_Near_Boundary_Program f)
  obtain H where application: "application=Comma_Near_Program_Application H"
    using admitted Comma_Near_Boundary_Program
    by (cases application) (auto simp: comma_phase_program_application_admitted.simps)
  have headroom: "H=1"
    by (rule comma_phase_program_boundary_application_headroom[where f=f and H=H])
      (use admitted Comma_Near_Boundary_Program application in simp)
  show ?thesis using admitted Comma_Near_Boundary_Program application headroom
    by (simp add: comma_phase_program_application_admitted.simps
      comma_phase_program_operator_eval.simps comma_phase_program_operator_nf.simps
      comma_phase_program_at_near_def Let_def)
qed

lemma comma_phase_program_at_entry_operator_nf:
  assumes admitted:
    "comma_phase_program_application_admitted program
      Comma_Entry_Program_Application"
  shows "comma_phase_program_at_entry program phase =
    Some (comma_phase_program_operator_nf program phase)"
  using comma_phase_program_operator_contract[OF admitted]
  by (simp add: comma_phase_program_operator_eval.simps)

ML \<open>
  val source_program_rules =
    @{thms comma_phase_core_clock_value_bound
      comma_phase_program_operator_nf_entry_core_value
      comma_phase_core_entry_key_refines_decisive
      comma_entry_control_program_port_exact
      comma_near_residual_program_port_exact
      comma_near_boundary_program_port_exact
      comma_phase_program_at_entry_core_refines
      comma_phase_program_at_entry_core_periodic
      comma_near_symbolic_port_action_phase_independent
      comma_near_symbolic_port_operator_residual
      comma_phase_program_at_near_phase_independent
      comma_phase_program_at_near_output_unique
      comma_phase_program_boundary_application_headroom
      comma_phase_program_operator_contract
      comma_phase_program_at_entry_operator_nf
      comma_phase_program_action_at_source_exact
      comma_phase_program_action_at_source_port_exact
      comma_phase_program_action_at_source_round_output};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma Semantic Phase Action Program" source_program_rules;
\<close>

end
