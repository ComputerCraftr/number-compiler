theory Comma_Symbolic_Phase_Masks
  imports Comma_Indexed_Mask_Quotient
begin

unbundle bit_operations_syntax

text \<open>
Canonical symbolic phase masks are represented by nested indexed unions over
the external cyclotomic clock.  This theory supplies the checked word laws
used by the symbolic MDD constructor: all results are exact 924-bit words,
operators are applied rowwise, and pullback rotation advances the selected
clock child while rotating its suffix mask.  The proofs quantify over phases;
they do not enumerate the 924 clock positions.
\<close>

lemma comma_symbolic_phase_mask_bounded:
  "take_bit 924 (comma_phase_mask P) = comma_phase_mask P"
  by (rule bit_eqI) (simp add: comma_phase_mask_bit bit_take_bit_iff)

lemma comma_symbolic_phase_mask_ext:
  assumes equal: "\<And>phase. phase<924 \<Longrightarrow> P phase=Q phase"
  shows "comma_phase_mask P=comma_phase_mask Q"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_phase_mask P) phase=bit (comma_phase_mask Q) phase"
  proof (cases "phase<924")
    case True
    then show ?thesis using equal by (simp add: comma_phase_mask_bit)
  next
    case False
    then show ?thesis by (simp add: comma_phase_mask_bit)
  qed
qed

lemma comma_symbolic_phase_bit_outside:
  assumes bounded: "take_bit 924 (bits::nat)=bits"
    and outside: "924\<le>phase"
  shows "bit bits phase=False"
proof -
  have bit_equality:
    "bit (take_bit 924 bits) phase=bit bits phase"
    by (rule arg_cong[OF bounded, where f="\<lambda>word. bit word phase"])
  show ?thesis using bit_equality outside by (simp add: bit_take_bit_iff)
qed

lemma comma_symbolic_mask_and_left_bounded:
  assumes bounded: "take_bit 924 (left::nat)=left"
  shows "take_bit 924 (left AND right)=left AND right"
proof (rule bit_eqI)
  fix phase
  show "bit (take_bit 924 (left AND right)) phase=
      bit (left AND right) phase"
  proof (cases "phase<924")
    case True
    then show ?thesis by (simp add: bit_take_bit_iff bit_simps)
  next
    case False
    have left_zero: "bit left phase=False"
    proof (rule comma_symbolic_phase_bit_outside[OF bounded])
      show "924\<le>phase" using False by arith
    qed
    then show ?thesis using False by (simp add: bit_take_bit_iff bit_simps)
  qed
qed

lemma comma_symbolic_mask_union_bounded:
  assumes bounded: "list_all (\<lambda>word. take_bit 924 word=word) words"
  shows "take_bit 924 (comma_mask_union words)=comma_mask_union words"
  using bounded
  by (induction words) (auto simp: take_bit_or)

lemma comma_indexed_phase_union_bounded:
  "take_bit 924 (comma_indexed_phase_union P words)=
    comma_indexed_phase_union P words"
proof -
  let ?rows = "map (\<lambda>(slot,bits). comma_phase_mask (P slot) AND bits)
      (zip [0..<length words] words)"
  have row_bounded:
    "list_all (\<lambda>word. take_bit 924 word=word) ?rows"
  proof (unfold list_all_iff, intro ballI)
    fix word
    assume member: "word\<in>set ?rows"
    then obtain slot bits where pair:
      "(slot,bits)\<in>set (zip [0..<length words] words)"
      and word: "word=comma_phase_mask (P slot) AND bits"
      by auto
    have bounded:
      "take_bit 924 (comma_phase_mask (P slot))=comma_phase_mask (P slot)"
      by (rule comma_symbolic_phase_mask_bounded)
    show "take_bit 924 word=word"
      unfolding word by (rule comma_symbolic_mask_and_left_bounded[OF bounded])
  qed
  show ?thesis
    unfolding comma_indexed_phase_union_def
    by (rule comma_symbolic_mask_union_bounded[OF row_bounded])
qed

lemma comma_phase_mask_and:
  "comma_phase_mask P AND comma_phase_mask Q=
    comma_phase_mask (\<lambda>phase. P phase \<and> Q phase)"
  by (rule bit_eqI) (auto simp: comma_phase_mask_bit bit_simps)

lemma comma_phase_mask_or:
  "comma_phase_mask P OR comma_phase_mask Q=
    comma_phase_mask (\<lambda>phase. P phase \<or> Q phase)"
  by (rule bit_eqI) (auto simp: comma_phase_mask_bit bit_simps)

lemma comma_indexed_phase_union_map_and:
  assumes positive: "0<period"
    and left_length: "length left_rows=period"
    and right_length: "length right_rows=period"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot)
      (map2 (\<lambda>a b. a AND b) left_rows right_rows) =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) left_rows
      AND comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) right_rows"
proof -
  let ?combined = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot)
      (map2 (\<lambda>a b. a AND b) left_rows right_rows)"
  let ?left = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) left_rows"
  let ?right = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) right_rows"
  have combined_length: "length (map2 (\<lambda>a b. a AND b) left_rows right_rows)=period"
    using left_length right_length by simp
  have combined_bounded: "take_bit 924 ?combined=?combined"
    by (rule comma_indexed_phase_union_bounded)
  have left_bounded: "take_bit 924 ?left=?left"
    by (rule comma_indexed_phase_union_bounded)
  have right_bounded: "take_bit 924 ?right=?right"
    by (rule comma_indexed_phase_union_bounded)
  have result_bounded: "take_bit 924 (?left AND ?right)=?left AND ?right"
    using left_bounded by (rule comma_symbolic_mask_and_left_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit ?combined phase=bit (?left AND ?right) phase"
    proof (cases "phase<924")
      case True
      let ?slot = "phase mod period"
      have slot_bound: "?slot<period" using positive by simp
      have combined_selection:
        "comma_phase_member ?combined phase=
          comma_phase_member (map2 (\<lambda>a b. a AND b) left_rows right_rows ! ?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive combined_length])
      have left_selection:
        "comma_phase_member ?left phase=comma_phase_member (left_rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive left_length])
      have right_selection:
        "comma_phase_member ?right phase=comma_phase_member (right_rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive right_length])
      have row_selection:
        "map2 (\<lambda>a b. a AND b) left_rows right_rows ! ?slot=
          left_rows!?slot AND right_rows!?slot"
        using slot_bound left_length right_length by simp
      have member_equality:
        "comma_phase_member ?combined phase=
          comma_phase_member (?left AND ?right) phase"
        using combined_selection left_selection right_selection row_selection
        by (simp add: comma_phase_member_and)
      show ?thesis using True member_equality
        by (simp add: comma_phase_member_def)
    next
      case False
      have combined_zero: "bit ?combined phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF combined_bounded])
          (use False in arith)
      have result_zero: "bit (?left AND ?right) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF result_bounded])
          (use False in arith)
      show ?thesis using combined_zero result_zero by simp
    qed
  qed
qed

lemma comma_indexed_phase_union_map_or:
  assumes positive: "0<period"
    and left_length: "length left_rows=period"
    and right_length: "length right_rows=period"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot)
      (map2 (\<lambda>a b. a OR b) left_rows right_rows) =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) left_rows
      OR comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) right_rows"
proof -
  let ?combined = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot)
      (map2 (\<lambda>a b. a OR b) left_rows right_rows)"
  let ?left = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) left_rows"
  let ?right = "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) right_rows"
  have combined_length: "length (map2 (\<lambda>a b. a OR b) left_rows right_rows)=period"
    using left_length right_length by simp
  have combined_bounded: "take_bit 924 ?combined=?combined"
    by (rule comma_indexed_phase_union_bounded)
  have left_bounded: "take_bit 924 ?left=?left"
    by (rule comma_indexed_phase_union_bounded)
  have right_bounded: "take_bit 924 ?right=?right"
    by (rule comma_indexed_phase_union_bounded)
  have result_bounded: "take_bit 924 (?left OR ?right)=?left OR ?right"
  proof (rule bit_eqI)
    fix phase
    show "bit (take_bit 924 (?left OR ?right)) phase=bit (?left OR ?right) phase"
      using left_bounded right_bounded
      by (cases "phase<924") (auto simp: bit_take_bit_iff bit_simps)
  qed
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit ?combined phase=bit (?left OR ?right) phase"
    proof (cases "phase<924")
      case True
      let ?slot = "phase mod period"
      have slot_bound: "?slot<period" using positive by simp
      have combined_selection:
        "comma_phase_member ?combined phase=
          comma_phase_member (map2 (\<lambda>a b. a OR b) left_rows right_rows ! ?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive combined_length])
      have left_selection:
        "comma_phase_member ?left phase=comma_phase_member (left_rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive left_length])
      have right_selection:
        "comma_phase_member ?right phase=comma_phase_member (right_rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive right_length])
      have row_selection:
        "map2 (\<lambda>a b. a OR b) left_rows right_rows ! ?slot=
          left_rows!?slot OR right_rows!?slot"
        using slot_bound left_length right_length by simp
      have member_equality:
        "comma_phase_member ?combined phase=
          comma_phase_member (?left OR ?right) phase"
        using combined_selection left_selection right_selection row_selection
        by (simp add: comma_phase_member_or)
      show ?thesis using True member_equality
        by (simp add: comma_phase_member_def)
    next
      case False
      have combined_zero: "bit ?combined phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF combined_bounded])
          (use False in arith)
      have result_zero: "bit (?left OR ?right) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF result_bounded])
          (use False in arith)
      show ?thesis using combined_zero result_zero by simp
    qed
  qed
qed

lemma comma_indexed_phase_union_replicate:
  assumes positive: "0<period"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) (replicate period word)=
    take_bit 924 word"
proof -
  have row_length: "length (replicate period word)=period" by simp
  have uniform_rows:
    "list_all (\<lambda>row. row=word) (replicate period word)"
    by (induction period) simp_all
  show ?thesis
    by (rule comma_indexed_phase_union_constant_rows
      [OF positive row_length uniform_rows])
qed

lemma comma_indexed_phase_union_replicate_bounded:
  assumes positive: "0<period"
    and bounded: "take_bit 924 (word::nat)=word"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) (replicate period word)=word"
proof -
  have "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod period=slot) (replicate period word)=
      take_bit 924 word"
    by (rule comma_indexed_phase_union_replicate[OF positive])
  then show ?thesis using bounded by simp
qed

lemma comma_indexed_phase_union_rotate1:
  assumes positive: "0<period"
    and divides: "period dvd 924"
    and row_length: "length rows=period"
  shows "comma_rotate_phase 1
      (comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows)=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot)
      (map (\<lambda>slot. comma_rotate_phase 1
        (rows!((slot+1) mod period))) [0..<period])"
proof -
  let ?source = "comma_indexed_phase_union
    (\<lambda>slot phase. phase mod period=slot) rows"
  let ?rotated_rows = "map (\<lambda>slot. comma_rotate_phase 1
    (rows!((slot+1) mod period))) [0..<period]"
  let ?target = "comma_indexed_phase_union
    (\<lambda>slot phase. phase mod period=slot) ?rotated_rows"
  have rotated_length: "length ?rotated_rows=period" by simp
  have target_bounded: "take_bit 924 ?target=?target"
    by (rule comma_indexed_phase_union_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit (comma_rotate_phase 1 ?source) phase=bit ?target phase"
    proof (cases "phase<924")
      case True
      let ?shifted = "(phase+1) mod 924"
      let ?slot = "phase mod period"
      have shifted_bound: "?shifted<924" by simp
      have slot_bound: "?slot<period" using positive by simp
      have clock_transport:
        "?shifted mod period=(?slot+1) mod period"
      proof -
        have reduce: "((phase+1) mod 924) mod period=(phase+1) mod period"
          by (rule mod_mod_cancel[OF divides])
        have step: "(phase+1) mod period=(phase mod period+1) mod period"
          by (simp only: mod_add_left_eq)
        show ?thesis using reduce step by simp
      qed
      have source_rotation:
        "comma_phase_member (comma_rotate_phase 1 ?source) phase=
          comma_phase_member ?source ?shifted"
        by (rule comma_rotate_phase_member[OF True])
      have source_selection:
        "comma_phase_member ?source ?shifted=
          comma_phase_member (rows!((?slot+1) mod period)) ?shifted"
        using comma_indexed_phase_union_select[OF positive row_length, of ?shifted]
          clock_transport shifted_bound by simp
      have target_selection:
        "comma_phase_member ?target phase=
          comma_phase_member (?rotated_rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive rotated_length])
      have target_row:
        "?rotated_rows!?slot=comma_rotate_phase 1
          (rows!((?slot+1) mod period))"
        using slot_bound by simp
      have row_rotation:
        "comma_phase_member
          (comma_rotate_phase 1 (rows!((?slot+1) mod period))) phase=
          comma_phase_member (rows!((?slot+1) mod period)) ?shifted"
        by (rule comma_rotate_phase_member[OF True])
      have member_eq: "comma_phase_member (comma_rotate_phase 1 ?source) phase=
          comma_phase_member ?target phase"
        using source_rotation source_selection target_selection target_row row_rotation
        by simp
      show ?thesis using True member_eq by (simp add: comma_phase_member_def)
    next
      case False
      have target_zero: "bit ?target phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF target_bounded])
          (use False in arith)
      show ?thesis using target_zero False
        by (simp add: comma_rotate_phase_def Let_def bit_simps)
    qed
  qed
qed

lemma comma_rotate_phase_one_zero:
  "comma_rotate_phase 1 (0::nat)=0"
  by (simp add: comma_rotate_phase_def Let_def)

lemma comma_rotate_phase_one_full_mask:
  "comma_rotate_phase 1 (mask 924::nat)=mask 924"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_rotate_phase 1 (mask 924::nat)) phase=
      bit (mask 924::nat) phase"
  proof (cases "phase<924")
    case True
    let ?shifted = "(phase+1) mod 924"
    have full_member: "comma_phase_member (mask 924::nat) ?shifted"
      by (simp add: comma_phase_member_def bit_simps)
    have rotated:
      "comma_phase_member (comma_rotate_phase 1 (mask 924::nat)) phase=
        comma_phase_member (mask 924::nat) ?shifted"
      by (rule comma_rotate_phase_member[OF True])
    have left: "bit (comma_rotate_phase 1 (mask 924::nat)) phase=True"
      using rotated full_member True by (simp add: comma_phase_member_def)
    have right: "bit (mask 924::nat) phase=True"
    proof -
      have bit_mask: "bit (mask 924::nat) phase=(phase<924)"
        by (simp only: bit_mask_iff possible_bit_nat simp_thms)
      show ?thesis using bit_mask True by simp
    qed
    show ?thesis using left right by simp
  next
    case False
    have rotated_bounded:
      "take_bit 924 (comma_rotate_phase 1 (mask 924::nat))=
        comma_rotate_phase 1 (mask 924::nat)"
      by (simp only: comma_rotate_phase_def Let_def take_bit_take_bit min.idem)
    have left: "bit (comma_rotate_phase 1 (mask 924::nat)) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF rotated_bounded])
        (use False in arith)
    have right: "bit (mask 924::nat) phase=False"
    proof -
      have bit_mask: "bit (mask 924::nat) phase=(phase<924)"
        by (simp only: bit_mask_iff possible_bit_nat simp_thms)
      show ?thesis using bit_mask False by simp
    qed
    show ?thesis using left right by simp
  qed
qed

lemma comma_indexed_phase_union_onehot:
  assumes positive: "0<period" and target: "target<period"
  shows "comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot)
      (map (\<lambda>slot. if slot=target then mask 924 else 0) [0..<period])=
    comma_phase_class period 0 target"
proof -
  let ?rows = "map (\<lambda>slot. if slot=target then mask 924 else 0) [0..<period]"
  let ?union = "comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) ?rows"
  have rows_length: "length ?rows=period" by simp
  have union_bounded: "take_bit 924 ?union=?union"
    by (rule comma_indexed_phase_union_bounded)
  have class_bounded:
    "take_bit 924 (comma_phase_class period 0 target)=comma_phase_class period 0 target"
    by (simp only: comma_phase_class_def comma_symbolic_phase_mask_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit ?union phase=bit (comma_phase_class period 0 target) phase"
    proof (cases "phase<924")
      case True
      have phase_bound: "phase<924" using True .
      let ?slot = "phase mod period"
      have slot_bound: "?slot<period" using positive by simp
      have select:
        "comma_phase_member ?union phase=comma_phase_member (?rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive rows_length])
      have row: "?rows!?slot=(if ?slot=target then mask 924 else 0)"
        using slot_bound by simp
      have union_bit: "bit ?union phase=(?slot=target)"
      proof (cases "?slot=target")
        case True
        have selected_full: "?rows!?slot=mask 924"
          using row True by simp
        have member_full: "comma_phase_member (mask 924::nat) phase=True"
          using phase_bound
          by (simp add: comma_phase_member_def bit_mask_iff)
        have selected_member:
          "comma_phase_member (?rows!?slot) phase=
            comma_phase_member (mask 924::nat) phase"
          by (rule arg_cong[OF selected_full,
            where f="\<lambda>word. comma_phase_member word phase"])
        have union_member:
          "comma_phase_member ?union phase=True"
        proof -
          have selected:
            "comma_phase_member ?union phase=
              comma_phase_member (mask 924::nat) phase"
            by (rule trans[OF select selected_member])
          show ?thesis using selected member_full by simp
        qed
        show ?thesis using phase_bound True union_member
          by (simp add: comma_phase_member_def)
      next
        case False
        have selected_empty: "?rows!?slot=0"
          using row False by simp
        have selected_member:
          "comma_phase_member (?rows!?slot) phase=comma_phase_member 0 phase"
          by (rule arg_cong[OF selected_empty,
            where f="\<lambda>word. comma_phase_member word phase"])
        have union_member:
          "comma_phase_member ?union phase=False"
        proof -
          have selected:
            "comma_phase_member ?union phase=comma_phase_member 0 phase"
            by (rule trans[OF select selected_member])
          show ?thesis using selected by simp
        qed
        show ?thesis using phase_bound False union_member
          by (simp add: comma_phase_member_def)
      qed
      have class_bit: "bit (comma_phase_class period 0 target) phase=(?slot=target)"
        using phase_bound by (simp add: comma_phase_class_def comma_phase_mask_bit)
      show ?thesis using union_bit class_bit by simp
    next
      case False
      have union_zero: "bit ?union phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF union_bounded])
          (use False in arith)
      have class_zero: "bit (comma_phase_class period 0 target) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF class_bounded])
          (use False in arith)
      show ?thesis using union_zero class_zero by simp
    qed
  qed
qed

lemma comma_mod_coprime_product_target:
  fixes left right first second :: nat
  assumes coprime: "coprime first second"
    and target: "right<first*second"
  shows "left mod (first*second)=right \<longleftrightarrow>
    (left mod first=right mod first \<and> left mod second=right mod second)"
proof -
  let ?difference = "nat \<bar>int left-int right\<bar>"
  have whole:
    "left mod (first*second)=right mod (first*second) \<longleftrightarrow>
      first*second dvd ?difference"
    by (rule mod_eq_iff_dvd_symdiff_nat)
  have first_residue:
    "left mod first=right mod first \<longleftrightarrow> first dvd ?difference"
    by (rule mod_eq_iff_dvd_symdiff_nat)
  have second_residue:
    "left mod second=right mod second \<longleftrightarrow> second dvd ?difference"
    by (rule mod_eq_iff_dvd_symdiff_nat)
  have product_divisibility:
    "first*second dvd ?difference \<longleftrightarrow>
      (first dvd ?difference \<and> second dvd ?difference)"
  proof
    assume product: "first*second dvd ?difference"
    have first_factor: "first dvd first*second" by simp
    have second_factor: "second dvd first*second"
      by (simp add: mult.commute)
    show "first dvd ?difference \<and> second dvd ?difference"
      using dvd_trans[OF first_factor product]
        dvd_trans[OF second_factor product] by blast
  next
    assume factors:
      "first dvd ?difference \<and> second dvd ?difference"
    have first_divisor: "first dvd ?difference" using factors by blast
    have second_divisor: "second dvd ?difference" using factors by blast
    show "first*second dvd ?difference"
      by (rule divides_mult[OF first_divisor second_divisor coprime])
  qed
  show ?thesis using whole first_residue second_residue product_divisibility target
    by auto
qed

lemma comma_phase_class_2_as_C4_parity:
  assumes target: "target<2"
  shows "comma_phase_class 2 shift target=
    comma_phase_class 4 shift target OR
    comma_phase_class 4 shift (target+2)"
proof -
  have predicate:
    "(phase+shift) mod 2=target =
      ((phase+shift) mod 4=target \<or> (phase+shift) mod 4=target+2)"
    for phase :: nat
  proof -
    let ?residue = "(phase+shift) mod 4"
    have residue_bound: "?residue<4" by simp
    have residue_parity:
      "((phase+shift) mod 4) mod 2=(phase+shift) mod 2"
      by (rule mod_mod_cancel) simp
    have parity: "(phase+shift) mod 2=?residue mod 2"
      using residue_parity by simp
    have residue_values:
      "?residue=0 \<or> ?residue=1 \<or> ?residue=2 \<or> ?residue=3"
      using residue_bound by arith
    have local:
      "?residue mod 2=target \<longleftrightarrow>
        (?residue=target \<or> ?residue=target+2)"
      using residue_values target by auto
    have transported:
      "((phase+shift) mod 2=target) = (?residue mod 2=target)"
      by (rule arg_cong[OF parity, where f="\<lambda>value::nat. value=target"])
    show ?thesis by (rule trans[OF transported local])
  qed
  have lhs: "comma_phase_class 2 shift target=
      comma_phase_mask (\<lambda>phase. (phase+shift) mod 2=target)"
    by (simp add: comma_phase_class_def)
  have rhs: "comma_phase_class 4 shift target OR
      comma_phase_class 4 shift (target+2)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 4=target \<or> (phase+shift) mod 4=target+2)"
    by (simp add: comma_phase_class_def comma_phase_mask_or)
  have mask_equality:
    "comma_phase_mask (\<lambda>phase. (phase+shift) mod 2=target)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 4=target \<or> (phase+shift) mod 4=target+2)"
    by (rule comma_symbolic_phase_mask_ext) (use predicate in simp)
  show ?thesis using lhs rhs mask_equality by simp
qed

lemma comma_phase_class_6_pair_factor:
  assumes target: "target<6"
  shows "comma_phase_class 6 shift target=
    comma_phase_class 2 shift (target mod 2) AND
      comma_phase_class 3 shift (target mod 3)"
proof -
  have predicate:
    "(phase+shift) mod 6=target =
      ((phase+shift) mod 2=target mod 2 \<and>
        (phase+shift) mod 3=target mod 3)"
    for phase :: nat
    using comma_mod_coprime_product_target
      [where left="phase+shift" and right=target and first=2 and second=3]
      target by simp
  have mask_equality:
    "comma_phase_mask (\<lambda>phase. (phase+shift) mod 6=target)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 2=target mod 2 \<and>
          (phase+shift) mod 3=target mod 3)"
    by (rule comma_symbolic_phase_mask_ext) (use predicate in simp)
  show ?thesis using mask_equality
    by (simp add: comma_phase_class_def comma_phase_mask_and)
qed

lemma comma_phase_class_22_pair_factor:
  assumes target: "target<22"
  shows "comma_phase_class 22 shift target=
    comma_phase_class 2 shift (target mod 2) AND
      comma_phase_class 11 shift (target mod 11)"
proof -
  have predicate:
    "(phase+shift) mod 22=target =
      ((phase+shift) mod 2=target mod 2 \<and>
        (phase+shift) mod 11=target mod 11)"
    for phase :: nat
    using comma_mod_coprime_product_target
      [where left="phase+shift" and right=target and first=2 and second=11]
      target by simp
  have mask_equality:
    "comma_phase_mask (\<lambda>phase. (phase+shift) mod 22=target)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 2=target mod 2 \<and>
          (phase+shift) mod 11=target mod 11)"
    by (rule comma_symbolic_phase_mask_ext) (use predicate in simp)
  show ?thesis using mask_equality
    by (simp add: comma_phase_class_def comma_phase_mask_and)
qed

lemma comma_phase_class_6_factor:
  assumes target: "target<6"
  shows "comma_phase_class 6 shift target=
    (comma_phase_class 4 shift (target mod 2) OR
      comma_phase_class 4 shift (target mod 2+2)) AND
      comma_phase_class 3 shift (target mod 3)"
proof -
  have target2: "target mod 2<2" by simp
  have pair: "comma_phase_class 6 shift target=
      comma_phase_class 2 shift (target mod 2) AND
        comma_phase_class 3 shift (target mod 3)"
    by (rule comma_phase_class_6_pair_factor[OF target])
  have factor2: "comma_phase_class 2 shift (target mod 2)=
      comma_phase_class 4 shift (target mod 2) OR
        comma_phase_class 4 shift (target mod 2+2)"
    by (rule comma_phase_class_2_as_C4_parity[OF target2])
  show ?thesis by (simp only: pair factor2)
qed

lemma comma_phase_class_22_factor:
  assumes target: "target<22"
  shows "comma_phase_class 22 shift target=
    (comma_phase_class 4 shift (target mod 2) OR
      comma_phase_class 4 shift (target mod 2+2)) AND
      comma_phase_class 11 shift (target mod 11)"
proof -
  have target2: "target mod 2<2" by simp
  have pair: "comma_phase_class 22 shift target=
      comma_phase_class 2 shift (target mod 2) AND
        comma_phase_class 11 shift (target mod 11)"
    by (rule comma_phase_class_22_pair_factor[OF target])
  have factor2: "comma_phase_class 2 shift (target mod 2)=
      comma_phase_class 4 shift (target mod 2) OR
        comma_phase_class 4 shift (target mod 2+2)"
    by (rule comma_phase_class_2_as_C4_parity[OF target2])
  show ?thesis by (simp only: pair factor2)
qed

lemma comma_phase_class_28_factor:
  assumes target: "target<28"
  shows "comma_phase_class 28 shift target=
    comma_phase_class 4 shift (target mod 4) AND
      comma_phase_class 7 shift (target mod 7)"
proof -
  have predicate:
    "(phase+shift) mod 28=target =
      ((phase+shift) mod 4=target mod 4 \<and>
        (phase+shift) mod 7=target mod 7)"
    for phase :: nat
    using comma_mod_coprime_product_target
      [where left="phase+shift" and right=target and first=4 and second=7]
      target by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
  have rhs: "comma_phase_class 4 shift (target mod 4) AND
        comma_phase_class 7 shift (target mod 7)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 4=target mod 4 \<and>
          (phase+shift) mod 7=target mod 7)"
    by (simp add: comma_phase_class_def comma_phase_mask_and)
  have lhs: "comma_phase_class 28 shift target=
      comma_phase_mask (\<lambda>phase. (phase+shift) mod 28=target)"
    by (simp add: comma_phase_class_def)
  have mask_equality:
    "comma_phase_mask (\<lambda>phase. (phase+shift) mod 28=target)=
      comma_phase_mask (\<lambda>phase.
        (phase+shift) mod 4=target mod 4 \<and>
          (phase+shift) mod 7=target mod 7)"
    by (rule comma_symbolic_phase_mask_ext) (use predicate in simp)
  show ?thesis using lhs rhs mask_equality by simp
qed

lemma comma_symbolic_phase_clock_axes:
  "(4::nat) dvd 924 \<and> (3::nat) dvd 924 \<and>
    (7::nat) dvd 924 \<and> (11::nat) dvd 924"
  by (simp add: dvd_eq_mod_eq_0)

lemma comma_crt_bounded_word_ext:
  fixes left right :: nat
  assumes left_bounded: "take_bit 924 left=left"
    and right_bounded: "take_bit 924 right=right"
    and bits: "\<And>phase::nat. phase<924 \<Longrightarrow>
      bit left phase=bit right phase"
  shows "left=right"
proof (rule bit_eqI)
  fix phase :: nat
  show "bit left phase=bit right phase"
  proof (cases "phase<924")
    case True
    show ?thesis by (rule bits[OF True])
  next
    case False
    have left_zero: "bit left phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF left_bounded])
        (use False in arith)
    have right_zero: "bit right phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF right_bounded])
        (use False in arith)
    show ?thesis using left_zero right_zero by simp
  qed
qed

ML \<open>
  val symbolic_phase_mask_rules = @{thms
    comma_indexed_phase_union_bounded
    comma_phase_mask_and comma_phase_mask_or
    comma_indexed_phase_union_map_and comma_indexed_phase_union_map_or
    comma_indexed_phase_union_replicate
    comma_indexed_phase_union_replicate_bounded
    comma_indexed_phase_union_rotate1 comma_rotate_phase_one_zero
    comma_rotate_phase_one_full_mask comma_indexed_phase_union_onehot
    comma_phase_class_2_as_C4_parity comma_phase_class_6_factor
    comma_phase_class_22_factor comma_phase_class_28_factor
    comma_mod_coprime_product_target
    comma_symbolic_phase_clock_axes comma_crt_bounded_word_ext};
  Thm.consolidate symbolic_phase_mask_rules;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Symbolic cyclotomic phase-mask algebra" symbolic_phase_mask_rules;
  if null (Thm_Deps.all_oracles symbolic_phase_mask_rules)
  then () else error "Symbolic phase-mask algebra depends on an oracle"
\<close>

end
