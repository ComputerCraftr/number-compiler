theory Comma_Response_Rows
  imports Comma_Sparse_Core.Comma_Sector_Rows_Core
begin

text \<open>Completed child rows are joined at the phase boundary, without
constructing a comma_sector_response parent.  Each child is restricted to
the phase class selecting it.  The remaining class is an explicit Invalid
row, so short child lists are total.  The parent is supplied as an extensional
function F and the child results as child_value; neither is a response tree.
This is the source-thunk boundary used by the producer.\<close>

definition comma_response_phase_guard ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_response_phase_guard f delta x k = comma_phase_mask
    (\<lambda>r. comma_entry_alphabet_phase f r delta x=k)"

definition comma_response_phase_missing_guard ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_response_phase_missing_guard f delta x arity = comma_phase_mask
    (\<lambda>r. arity \<le> comma_entry_alphabet_phase f r delta x)"

text \<open>Entry phase guards are short-period classes, not independent
924-phase predicates. Since every admitted short period divides 924, the
outer reduction modulo 924 can be removed before constructing the packed
mask. The executable publisher can then replace each class with a checked
binary-packed numeral from the existing Comma_Sector_Guards producer.\<close>

lemma comma_response_phase_guard_class:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "comma_response_phase_guard f delta x k =
    comma_phase_class
      (comma_short_period (comma_finite_period_fast f (x mod 10)))
      (delta+919) k"
proof -
  let ?P = "comma_finite_period_fast f (x mod 10)"
  let ?T = "comma_short_period ?P"
  have fast: "?P=comma_finite_period f (x mod 10)"
    by (rule comma_finite_period_fast_correct[OF sector]) simp
  have catalog: "?P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f "x mod 10"]
      sector fast by auto
  have divides: "?T dvd 924"
    using comma_short_period_catalog[OF catalog] by blast
  have phase: "comma_entry_alphabet_phase f r delta x =
      (r+delta+919) mod ?T" for r
  proof -
    have inner: "((r mod 924+delta) mod 924) mod ?T =
        (r+delta) mod ?T"
    proof -
      have "((r mod 924+delta) mod 924) mod ?T =
          (r mod 924+delta) mod ?T"
        by (rule mod_mod_cancel[OF divides])
      also have "... = ((r mod 924) mod ?T+delta) mod ?T"
        by (rule mod_add_left_eq[symmetric])
      also have "... = (r mod ?T+delta) mod ?T"
        by (simp only: mod_mod_cancel[OF divides])
      also have "... = (r+delta) mod ?T"
        by (rule mod_add_left_eq)
      finally show ?thesis .
    qed
    have "(((r mod 924+delta) mod 924+919) mod ?T) =
        ((((r mod 924+delta) mod 924) mod ?T)+919) mod ?T"
      by (rule mod_add_left_eq[symmetric])
    also have "... = ((r+delta) mod ?T+919) mod ?T"
      by (simp only: inner)
    also have "... = (r+delta+919) mod ?T"
      by (rule mod_add_left_eq)
    finally show ?thesis
      by (simp only: comma_entry_alphabet_phase_def)
  qed
  show ?thesis
    unfolding comma_response_phase_guard_def comma_phase_class_def
    by (rule arg_cong[where f=comma_phase_mask]; rule ext;
      simp only: phase add.assoc)
qed

lemma comma_response_phase_missing_guard_empty:
  assumes sector: "1\<le>f" "f\<le>9"
    and enough: "comma_short_period (comma_finite_period_fast f (x mod 10))\<le>arity"
  shows "comma_response_phase_missing_guard f delta x arity = 0"
proof (rule bit_eqI)
  fix r
  have phase: "comma_entry_alphabet_phase f r delta x < arity"
    using comma_entry_alphabet_phase_bound[OF sector, of r delta x] enough
    by arith
  show "bit (comma_response_phase_missing_guard f delta x arity) r =
      bit (0::nat) r"
    using phase
    by (simp add: comma_response_phase_missing_guard_def comma_phase_mask_bit)
qed

lemma comma_response_phase_missing_guard_full:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "comma_response_phase_missing_guard f delta x
      (comma_short_period (comma_finite_period_fast f (x mod 10))) = 0"
  by (rule comma_response_phase_missing_guard_empty[OF sector]) simp

definition comma_response_phase_pieces ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> comma_sector_rows list \<Rightarrow>
    (nat \<times> comma_sector_rows) list" where
  "comma_response_phase_pieces f delta x arity rows =
    map (\<lambda>(k,child_rows).
       (comma_response_phase_guard f delta x k,
       comma_sector_rows_filter_nonzero
         (comma_sector_rows_restrict
           (comma_response_phase_guard f delta x k) child_rows)))
      (zip [0..<arity] rows) @
    [(comma_response_phase_missing_guard f delta x arity,
      comma_sector_rows_filter_nonzero
        [(Comma_Round_Invalid, comma_response_phase_missing_guard
          f delta x arity)])]"

fun comma_response_position_key :: "comma_finite_position \<Rightarrow> nat list" where
  "comma_response_position_key (Comma_Entry f d x) = [0,f,d,x]"
| "comma_response_position_key (Comma_Near f d h) = [1,f,d,h]"

lemma comma_response_position_key_injective:
  "comma_response_position_key left = comma_response_position_key right \<Longrightarrow>
    left=right"
  by (cases left; cases right; auto)

fun comma_response_round_key :: "comma_round_result \<Rightarrow> nat list" where
  "comma_response_round_key Comma_Round_Invalid = [0]"
| "comma_response_round_key (Comma_Round_Fork a d) = [1,a,d]"
| "comma_response_round_key (Comma_Round_Landmine d) = [2,d]"
| "comma_response_round_key (Comma_Round_Cross p) =
    3 # comma_response_position_key p"

lemma comma_response_round_key_injective:
  "comma_response_round_key left = comma_response_round_key right \<Longrightarrow>
    left=right"
  by (cases left; cases right;
      auto dest: comma_response_position_key_injective)

definition comma_response_phase_rows ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> comma_sector_rows list \<Rightarrow>
    comma_sector_rows" where
  "comma_response_phase_rows f delta x arity rows =
    comma_mask_rows_normalize comma_response_round_key
      (concat (map snd (comma_response_phase_pieces f delta x arity rows)))"

text \<open>Completed child rows are advanced by one checked finite move.  The
operation deliberately carries only the row data: a non-crossing successor
reuses the completed child rows, while a crossing or terminal move publishes
one full-mask terminal row.  In particular, this is not a constructor for a
response tree and it has no internal theorem payload.\<close>
definition comma_response_after_rows ::
    "comma_finite_position \<Rightarrow>
      (comma_finite_position \<Rightarrow> comma_sector_rows) \<Rightarrow>
      comma_sector_rows" where
  "comma_response_after_rows target continuation =
    (case comma_fast_step 0 target of
      Comma_Next source \<Rightarrow>
        if comma_round_crossing target source then
          [(Comma_Round_Cross source, mask 924)] else continuation source
    | Comma_Fork a d \<Rightarrow> [(Comma_Round_Fork a d, mask 924)]
    | Comma_Landmine d \<Rightarrow> [(Comma_Round_Landmine d, mask 924)]
    | Comma_Invalid \<Rightarrow> [(Comma_Round_Invalid, mask 924)])"

lemma comma_response_after_rows_refine:
  assumes child: "\<And>source. comma_sector_rows_refine
    (G source) (mask 924) (rows source)"
  shows "comma_sector_rows_refine
    (\<lambda>r. case comma_fast_step 0 target of
      Comma_Next source \<Rightarrow>
        if comma_round_crossing target source then Comma_Round_Cross source
        else G source r
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)
    (mask 924) (comma_response_after_rows target rows)"
proof (cases "comma_fast_step 0 target")
  case (Comma_Next source)
  show ?thesis
  proof (cases "comma_round_crossing target source")
    case True
    then show ?thesis
      by (simp add: comma_response_after_rows_def
        Comma_Next True comma_sector_rows_singleton)
  next
    case False
    then show ?thesis
      using child[of source]
      by (simp add: comma_response_after_rows_def
        Comma_Next False)
  qed
next
  case (Comma_Fork a d)
  then show ?thesis
    by (simp add: comma_response_after_rows_def
      Comma_Fork comma_sector_rows_singleton)
next
  case (Comma_Landmine d)
  then show ?thesis
    by (simp add: comma_response_after_rows_def
      Comma_Landmine comma_sector_rows_singleton)
next
  case Comma_Invalid
  then show ?thesis
    by (simp add: comma_response_after_rows_def
      Comma_Invalid comma_sector_rows_singleton)
qed

text \<open>A data-only recurrence for a bounded sector response.  Its recursive
children are completed rows, and its only composition operation is the phase
join above.  The recurrence is useful to proof-producing publishers because
it has the same nine-step shape as the executable sector kernel without
retaining the symbolic response datatype.\<close>
fun comma_response_data_rows ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_sector_rows" where
  "comma_response_data_rows 0 source =
    [(Comma_Round_Invalid, mask 924)]"
| "comma_response_data_rows (Suc n) (Comma_Entry f delta x) =
    (if f<1 \<or> 9<f \<or> 98<x then
       [(Comma_Round_Invalid, mask 924)]
     else
       comma_response_phase_rows f delta x
         (comma_short_period (comma_finite_period_fast f (x mod 10)))
         (map (\<lambda>k. comma_response_after_rows
           (Comma_Near f delta (comma_entry_alphabet_endpoint f x k))
           (comma_response_data_rows n))
           [0..<comma_short_period (comma_finite_period_fast f (x mod 10))]))"
| "comma_response_data_rows (Suc n) (Comma_Near f delta h) =
    comma_response_after_rows
      (Comma_Near f delta (snd (comma_near_closed_germ f h)))
      (comma_response_data_rows n)"

lemma comma_response_phase_rows_function_refine:
  assumes lengths: "length rows=arity"
    and child: "\<And>k. k<arity \<Longrightarrow>
      comma_sector_rows_refine
        (child_value k) (mask 924) (rows!k)"
    and selected: "\<And>r k. comma_phase_member
        (comma_response_phase_guard f delta x k) r \<Longrightarrow>
        k<arity \<Longrightarrow> F r=child_value k r"
    and missing: "\<And>r. comma_phase_member
        (comma_response_phase_missing_guard f delta x arity) r \<Longrightarrow>
        F r=Comma_Round_Invalid"
  shows "comma_sector_rows_refine
    F (mask 924) (comma_response_phase_rows f delta x arity rows)"
proof -
  let ?pieces = "comma_response_phase_pieces f delta x arity rows"
  have child_piece:
    "\<And>k. k<arity \<Longrightarrow>
      comma_sector_rows_refine F
        (comma_response_phase_guard f delta x k AND mask 924)
        (comma_sector_rows_filter_nonzero
          (comma_sector_rows_restrict
            (comma_response_phase_guard f delta x k) (rows!k)))"
  proof -
    fix k
    assume k: "k<arity"
    have row: "comma_sector_rows_refine (child_value k)
        (mask 924) (rows!k)" using child k .
    have transport: "\<And>r. comma_phase_member
        (comma_response_phase_guard f delta x k) r \<Longrightarrow>
        F r=child_value k r"
    proof -
      fix r
      assume phase: "comma_phase_member
        (comma_response_phase_guard f delta x k) r"
      show "F r=child_value k r" by (rule selected[OF phase k])
    qed
    have restricted: "comma_sector_rows_refine F
        (comma_response_phase_guard f delta x k AND mask 924)
        (comma_sector_rows_restrict
          (comma_response_phase_guard f delta x k) (rows!k))"
      by (rule comma_sector_rows_restrict_refines[OF row transport])
    show "comma_sector_rows_refine F
        (comma_response_phase_guard f delta x k AND mask 924)
        (comma_sector_rows_filter_nonzero
          (comma_sector_rows_restrict
            (comma_response_phase_guard f delta x k) (rows!k)))"
      by (rule comma_sector_rows_filter_nonzero_refines[OF restricted])
  qed
  have missing_singleton:
    "comma_sector_rows_refine F
      (comma_response_phase_missing_guard f delta x arity)
      [(Comma_Round_Invalid, comma_response_phase_missing_guard
        f delta x arity)]"
  proof (rule comma_sector_rows_singleton)
    fix r
    assume phase: "comma_phase_member
      (comma_response_phase_missing_guard f delta x arity) r"
    show "F r=Comma_Round_Invalid"
      by (rule missing[of r]) (rule phase)
  qed
  have missing_piece:
    "comma_sector_rows_refine F
      (comma_response_phase_missing_guard f delta x arity)
      (comma_sector_rows_filter_nonzero
        [(Comma_Round_Invalid, comma_response_phase_missing_guard
          f delta x arity)])"
    by (rule comma_sector_rows_filter_nonzero_refines[OF missing_singleton])
  have pieces:
    "\<And>scope part_rows. (scope,part_rows)\<in>set ?pieces \<Longrightarrow>
      comma_sector_rows_refine F scope part_rows"
  proof -
    fix scope part_rows
    assume member: "(scope,part_rows)\<in>set ?pieces"
    show "comma_sector_rows_refine F scope part_rows"
    proof (cases "(scope,part_rows)=
        (comma_response_phase_missing_guard f delta x arity,
         comma_sector_rows_filter_nonzero
           [(Comma_Round_Invalid, comma_response_phase_missing_guard
             f delta x arity)])")
      case True
      then show ?thesis using missing_piece by simp
    next
      case False
      have member_map: "(scope,part_rows)\<in>set (map (\<lambda>(k,child_rows).
          (comma_response_phase_guard f delta x k,
           comma_sector_rows_filter_nonzero
             (comma_sector_rows_restrict
               (comma_response_phase_guard f delta x k) child_rows)))
          (zip [0..<arity] rows))"
        using member False by (auto simp: comma_response_phase_pieces_def)
      then obtain k child_rows where k:
          "(k,child_rows)\<in>set (zip [0..<arity] rows)" and eq:
          "(scope,part_rows)=(comma_response_phase_guard f delta x k,
            comma_sector_rows_filter_nonzero
              (comma_sector_rows_restrict
                (comma_response_phase_guard f delta x k) child_rows))"
        by (auto simp: set_map)
      have k_index: "k<arity" using k by (auto simp: set_zip)
      have row_index: "rows!k=child_rows" using k by (auto simp: set_zip)
      have guard: "comma_response_phase_guard f delta x k AND mask 924 =
          comma_response_phase_guard f delta x k"
        by (rule bit_eqI)
          (auto simp: comma_response_phase_guard_def comma_phase_mask_bit bit_simps)
      note piece = child_piece[OF k_index]
      show ?thesis using piece eq
        by (auto simp: row_index guard)
    qed
  qed
  have joined: "comma_sector_rows_refine F
      (comma_mask_union (map fst ?pieces))
      (concat (map snd ?pieces))"
    by (rule comma_sector_rows_concat[OF pieces])
  have scope: "comma_mask_union (map fst ?pieces)=mask 924"
  proof (rule bit_eqI)
    fix r
    have bounded: "bit (comma_mask_union (map fst ?pieces)) r \<Longrightarrow> r<924"
      by (auto simp: comma_mask_union_bit comma_response_phase_pieces_def
        comma_response_phase_guard_def comma_response_phase_missing_guard_def
        comma_phase_mask_bit)
    have covered: "r<924 \<Longrightarrow> bit (comma_mask_union (map fst ?pieces)) r"
    proof -
      assume phase: "r<924"
      let ?k = "comma_entry_alphabet_phase f r delta x"
      show "bit (comma_mask_union (map fst ?pieces)) r"
      proof (cases "?k<arity")
        case True
        have zipped: "(?k,rows!?k)\<in>set (zip [0..<arity] rows)"
          using nth_mem[of ?k "zip [0..<arity] rows"] True lengths by simp
        have member: "comma_response_phase_guard f delta x ?k \<in>
            set (map fst ?pieces)"
          using zipped by (force simp: comma_response_phase_pieces_def)
        have hit: "bit (comma_response_phase_guard f delta x ?k) r"
          using phase by (simp add: comma_response_phase_guard_def comma_phase_mask_bit)
        show ?thesis unfolding comma_mask_union_bit
          by (rule bexI[where x="comma_response_phase_guard f delta x ?k"])
            (fact hit, fact member)
      next
        case False
        have member: "comma_response_phase_missing_guard f delta x arity \<in>
            set (map fst ?pieces)"
          by (simp add: comma_response_phase_pieces_def)
        have hit: "bit (comma_response_phase_missing_guard f delta x arity) r"
          using phase False by (simp add: comma_response_phase_missing_guard_def
            comma_phase_mask_bit)
        show ?thesis unfolding comma_mask_union_bit
          by (rule bexI[where x="comma_response_phase_missing_guard f delta x arity"])
            (fact hit, fact member)
      qed
    qed
    show "bit (comma_mask_union (map fst ?pieces)) r=bit (mask 924::nat) r"
      using bounded covered by (auto simp: bit_simps)
  qed
  have normalized:
      "comma_sector_rows_refine F
        (comma_mask_union (map fst ?pieces))
        (comma_mask_rows_normalize comma_response_round_key
          (concat (map snd ?pieces)))"
    using joined by (simp only: comma_mask_rows_normalize_refines)
  show ?thesis using normalized scope
    by (simp only: comma_response_phase_rows_def)
qed


lemma comma_response_data_rows_refine:
  "comma_sector_rows_refine
    (\<lambda>r. comma_fast_round_aux n r source) (mask 924)
    (comma_response_data_rows n source)"
proof (induction n arbitrary: source)
  case 0
  show ?case
    by (simp add: comma_response_data_rows.simps
      comma_fast_round_aux.simps comma_sector_rows_refine_def
      comma_phase_member_def)
next
  case (Suc n)
  show ?case
  proof (cases source)
    case (Comma_Entry f delta x)
    show ?thesis
    proof (cases "f<1 \<or> 9<f \<or> 98<x")
      case True
      then show ?thesis
        by (simp add: comma_response_data_rows.simps
          Comma_Entry True comma_fast_round_aux.simps
          comma_fast_sector.simps comma_fast_sector_target.simps
          comma_fast_step.simps comma_sector_rows_refine_def
          comma_phase_member_def)
    next
      case False
      let ?period =
        "comma_short_period (comma_finite_period_fast f (x mod 10))"
      let ?target =
        "\<lambda>k. Comma_Near f delta
          (comma_entry_alphabet_endpoint f x k)"
      let ?child =
        "\<lambda>k r. case comma_fast_step 0 (?target k) of
          Comma_Next target \<Rightarrow>
            if comma_round_crossing (?target k) target then
              Comma_Round_Cross target
            else comma_fast_round_aux n r target
        | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
        | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
        | Comma_Invalid \<Rightarrow> Comma_Round_Invalid"
      have sector: "1\<le>f" "f\<le>9" "x\<le>98" using False by auto
      have bounded:
        "comma_entry_alphabet_phase f r delta x<?period"
        for r
        by (rule comma_entry_alphabet_phase_bound[OF sector(1,2)])
      have children:
        "comma_sector_rows_refine (?child k) (mask 924)
          (comma_response_after_rows (?target k)
            (comma_response_data_rows n))"
        if "k<?period" for k
      proof -
        have child_rows:
          "\<And>source. comma_sector_rows_refine
            (\<lambda>r. comma_fast_round_aux n r source)
            (mask 924) (comma_response_data_rows n source)"
          using Suc.IH by blast
        show ?thesis
          by (rule comma_response_after_rows_refine[OF child_rows])
      qed
      have selected:
        "comma_fast_round_aux (Suc n) r
            (Comma_Entry f delta x)=?child k r"
        if member:
          "comma_phase_member
            (comma_response_phase_guard f delta x k) r"
          and k: "k<?period" for r k
      proof -
        have phase: "r<924" and phase_eq:
            "comma_entry_alphabet_phase f r delta x=k"
          using member by (auto simp: comma_response_phase_guard_def
            comma_phase_mask_member)
        have target:
            "comma_fast_sector_target r (Comma_Entry f delta x)=?target k"
          by (simp only: comma_sector_entry_alphabet False if_False phase_eq)
        show ?thesis
          by (simp only: comma_response_round_successor target Let_def
            comma_fast_near_phase)
      qed
      have missing:
        "comma_fast_round_aux (Suc n) r
            (Comma_Entry f delta x)=Comma_Round_Invalid"
        if member:
          "comma_phase_member
            (comma_response_phase_missing_guard f delta x ?period) r"
        for r
      proof -
        have phase: "r<924" and lower:
            "?period\<le>comma_entry_alphabet_phase f r delta x"
          using member by (auto simp: comma_response_phase_missing_guard_def
            comma_phase_mask_member)
        have upper: "comma_entry_alphabet_phase f r delta x<?period"
          using bounded by blast
        have contradiction: False using lower upper by arith
        then show ?thesis by blast
      qed
      let ?row = "\<lambda>k. comma_response_after_rows (?target k)
        (comma_response_data_rows n)"
      have mapped_children: "comma_sector_rows_refine (?child k) (mask 924)
          (map ?row [0..<?period] ! k)" if kb: "k<?period" for k
      proof -
        have at: "map ?row [0..<?period] ! k = ?row k"
          using kb by simp
        show ?thesis unfolding at by (rule children[OF kb])
      qed
      have joined: "comma_sector_rows_refine
          (\<lambda>r. comma_fast_round_aux (Suc n) r (Comma_Entry f delta x))
          (mask 924) (comma_response_phase_rows f delta x ?period
            (map ?row [0..<?period]))"
        apply (rule comma_response_phase_rows_function_refine[where child_value="?child"])
           apply simp
          apply (fact mapped_children)
         apply (fact selected)
        apply (fact missing)
        done
      show ?thesis
        using joined by (simp only: Comma_Entry comma_response_data_rows.simps
          if_not_P[OF False])
    qed
  next
    case (Comma_Near f delta h)
    let ?target =
      "Comma_Near f delta (snd (comma_near_closed_germ f h))"
    have child_rows:
      "\<And>source. comma_sector_rows_refine
        (\<lambda>r. comma_fast_round_aux n r source)
        (mask 924) (comma_response_data_rows n source)"
      using Suc.IH by blast
    have advanced:
      "comma_sector_rows_refine
        (\<lambda>r. case comma_fast_step 0 ?target of
          Comma_Next source \<Rightarrow>
            if comma_round_crossing ?target source then
              Comma_Round_Cross source else comma_fast_round_aux n r source
        | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
        | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
        | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)
        (mask 924) (comma_response_after_rows ?target
          (comma_response_data_rows n))"
      by (rule comma_response_after_rows_refine[OF child_rows])
    show ?thesis using advanced
      by (simp only: Comma_Near comma_response_data_rows.simps
        comma_response_round_successor comma_sector_near_alphabet
        Let_def comma_fast_near_phase)
  qed
qed
ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_response_after_rows_refine comma_response_data_rows_refine
      comma_response_phase_rows_function_refine comma_response_round_key_injective
      comma_response_phase_guard_class comma_response_phase_missing_guard_empty
      comma_response_phase_missing_guard_full}) then ()
    else error "Response row refinement depends on an oracle";
\<close>

end
