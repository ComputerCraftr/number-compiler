theory Fermat_Source_Matrix_Refinement
  imports Power_Clock_Jumps
begin

text \<open>This theory gives the source-conditioned meaning of the finite
Fermat low-digit transfer used by the powered port matrix.  Its source is the
exact root \<open>3^(2^level)\<close>, its clock counts ordinary tripling ticks, and
each row is a conditional starting digit over one authenticated lower
residue.  The join theorem below checks every row's lower-port seam before
using the later row.  This is a finite low-modulus refinement; it does not
certify the entire signed source, infer future carry choices, or decide
primality.  The caller remains responsible for issued-source authority and
the Python tuple-to-list adapter.\<close>

definition fermat_matrix_source_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
  "fermat_matrix_source_residue level modulus offset =
    (3^(2^level + offset)) mod modulus"

definition fermat_matrix_modulus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
  "fermat_matrix_modulus base place = base * place"

lemma fermat_matrix_radix_window:
  "fermat_matrix_modulus base (base^position) = base^(Suc position)"
  by (simp add: fermat_matrix_modulus_def power_Suc mult.commute)

lemma fermat_matrix_source_residue_advance:
  assumes modulus: "0 < modulus"
  shows
  "fermat_matrix_source_residue level modulus (offset + steps) =
    (3^steps * fermat_matrix_source_residue level modulus offset) mod modulus"
proof -
  let ?root = "(3::nat)^(2^level)"
  have source_as_transfer:
    "fermat_matrix_source_residue level modulus offset =
      fermat_conditional_digit_transfer modulus 1 0 ?root offset"
    unfolding fermat_matrix_source_residue_def
      fermat_conditional_digit_transfer_def
    by (simp add: power_add mult.commute)
  have successor_as_transfer:
    "fermat_matrix_source_residue level modulus (offset + steps) =
      fermat_conditional_digit_transfer modulus 1 0 ?root (offset + steps)"
    unfolding fermat_matrix_source_residue_def
      fermat_conditional_digit_transfer_def
    by (simp add: power_add mult.commute)
  have split:
    "fermat_conditional_digit_transfer modulus 1 0 ?root (offset + steps) =
      (3^steps * fermat_conditional_digit_transfer
        modulus 1 0 ?root offset) mod modulus"
    by (rule fermat_conditional_digit_transfer_split[OF modulus])
  show ?thesis
    using source_as_transfer successor_as_transfer split by simp
qed

lemma fermat_matrix_source_residue_from_root:
  "fermat_matrix_source_residue level modulus offset =
    ((3^(2^level) mod modulus) * (3^offset mod modulus)) mod modulus"
proof -
  have reduced_product:
    "((3^(2^level) mod modulus) * (3^offset mod modulus)) mod modulus =
      (3^(2^level) * 3^offset) mod modulus"
    by (simp only: mod_mult_left_eq mod_mult_right_eq)
  show ?thesis
    unfolding fermat_matrix_source_residue_def
    using reduced_product by (simp add: power_add)
qed

lemma fermat_conditional_digit_transfer_modular_factor:
  "(low + digit * place) * (3^steps mod modulus) mod modulus =
    fermat_conditional_digit_transfer modulus place low digit steps"
proof -
  have factor:
    "(low + digit * place) * (3^steps mod modulus) mod modulus =
      ((low + digit * place) * 3^steps) mod modulus"
    by (rule mod_mult_right_eq)
  show ?thesis
    using factor unfolding fermat_conditional_digit_transfer_def
    by (simp add: mult.commute)
qed

lemma fermat_source_transfer_pointed_endpoint:
  assumes place: "0 < place"
      and source: "source = fermat_matrix_source_residue level modulus offset"
      and source_bound: "source < modulus"
  shows "fermat_conditional_digit_transfer modulus place
      (source mod place) (source div place) steps =
    fermat_matrix_source_residue level modulus (offset + steps)"
proof -
  have decomposition:
    "source mod place + (source div place) * place = source"
    using div_mult_mod_eq[of source place] by (simp add: mult.commute)
  have initial:
    "fermat_conditional_digit_transfer modulus place
        (source mod place) (source div place) steps =
      (3^steps * source) mod modulus"
    unfolding fermat_conditional_digit_transfer_def
    using decomposition by simp
  have modulus_positive: "0 < modulus"
    using source_bound by arith
  have advance:
    "fermat_matrix_source_residue level modulus (offset + steps) =
      (3^steps * source) mod modulus"
    using fermat_matrix_source_residue_advance[OF modulus_positive,
        of level offset steps] source by simp
  show ?thesis using initial advance by simp
qed

lemma fermat_conditional_digit_transfer_join:
  assumes modulus: "0 < modulus"
      and place: "0 < place"
      and lower_seam:
        "fermat_conditional_digit_transfer modulus place
            low_first digit first mod place = low_later"
  shows "fermat_conditional_digit_transfer modulus place low_later
      (fermat_conditional_digit_transfer modulus place low_first digit first
        div place) second =
    fermat_conditional_digit_transfer modulus place low_first digit
      (first + second)"
proof -
  let ?middle =
    "fermat_conditional_digit_transfer modulus place low_first digit first"
  have middle_decomposition:
    "low_later + (?middle div place) * place = ?middle"
    using lower_seam div_mult_mod_eq[of ?middle place]
    by (simp add: mult.commute)
  have later_row:
    "fermat_conditional_digit_transfer modulus place low_later
        (?middle div place) second = (3^second * ?middle) mod modulus"
  proof -
    have raw:
      "(3^second * (low_later + (?middle div place) * place)) mod modulus =
        (3^second * ?middle) mod modulus"
      using middle_decomposition by simp
    show ?thesis
      using raw unfolding fermat_conditional_digit_transfer_def by simp
  qed
  have chronological:
    "fermat_conditional_digit_transfer modulus place low_first digit
        (first + second) = (3^second * ?middle) mod modulus"
    using fermat_conditional_digit_transfer_split[OF modulus,
        of place low_first digit first second]
    by simp
  show ?thesis using later_row chronological by simp
qed

lemma fermat_conditional_transfer_lower_projection:
  assumes base: "0 < base"
      and place: "0 < place"
  shows "fermat_conditional_digit_transfer (base * place) place
      low digit steps mod place = (3^steps * low) mod place"
proof -
  have divides: "place dvd base * place"
    using base by (simp add: mult.commute)
  have representative:
    "(low + digit * place) mod place = low mod place"
    by (simp add: mult.commute)
  have raw_projection:
    "(3^steps * (low + digit * place)) mod place =
      (3^steps * low) mod place"
  proof -
    have "(3^steps * (low + digit * place)) mod place =
        (3^steps * ((low + digit * place) mod place)) mod place"
      by (rule mod_mult_right_eq[symmetric])
    also have "... = (3^steps * (low mod place)) mod place"
      using representative by simp
    also have "... = (3^steps * low) mod place"
      by (rule mod_mult_right_eq)
    finally show ?thesis .
  qed
  have outer_projection:
    "((3^steps * (low + digit * place)) mod (base * place)) mod place =
      (3^steps * (low + digit * place)) mod place"
    by (rule mod_mod_cancel[OF divides])
  show ?thesis
    unfolding fermat_conditional_digit_transfer_def
    using outer_projection raw_projection by simp
qed

lemma fermat_source_residue_lower_projection:
  assumes base: "0 < base"
      and place: "0 < place"
  shows "fermat_matrix_source_residue level (base * place)
        (offset + steps) mod place =
    (3^steps * (fermat_matrix_source_residue level (base * place) offset
        mod place)) mod place"
proof -
  have modulus_positive: "0 < base * place"
    using base place by simp
  have divides: "place dvd base * place"
    using base by (simp add: mult.commute)
  have advance:
    "fermat_matrix_source_residue level (base * place) (offset + steps) =
      (3^steps * fermat_matrix_source_residue level (base * place) offset)
        mod (base * place)"
    by (rule fermat_matrix_source_residue_advance[OF modulus_positive])
  show ?thesis
  proof -
    have "fermat_matrix_source_residue level (base * place) (offset + steps)
        mod place =
        ((3^steps * fermat_matrix_source_residue level (base * place) offset)
          mod (base * place)) mod place"
      by (simp only: advance)
    also have "... =
        (3^steps * fermat_matrix_source_residue level (base * place) offset)
          mod place"
      by (rule mod_mod_cancel[OF divides])
    also have "... =
        (3^steps * (fermat_matrix_source_residue level (base * place) offset
          mod place)) mod place"
      by (rule mod_mult_right_eq[symmetric])
    finally show ?thesis .
  qed
qed

definition fermat_source_matrix_admitted ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
  "fermat_source_matrix_admitted level base place offset steps source endpoint rows
    \<longleftrightarrow> 1 < base \<and> 0 < place
      \<and> source = fermat_matrix_source_residue level
          (fermat_matrix_modulus base place) offset
      \<and> endpoint = fermat_matrix_source_residue level
          (fermat_matrix_modulus base place) (offset + steps)
      \<and> source < fermat_matrix_modulus base place
      \<and> length rows = base
      \<and> (\<forall>digit < base. rows ! digit =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place (source mod place)
          digit steps)"

lemma fermat_source_matrix_selected_row:
  assumes admitted:
    "fermat_source_matrix_admitted level base place offset steps
      source endpoint rows"
  shows "rows ! (source div place) = endpoint"
proof -
  have base: "1 < base" and place: "0 < place"
      and source: "source = fermat_matrix_source_residue level
        (fermat_matrix_modulus base place) offset"
      and endpoint: "endpoint = fermat_matrix_source_residue level
        (fermat_matrix_modulus base place) (offset + steps)"
      and source_bound: "source < fermat_matrix_modulus base place"
      and row_length: "length rows = base"
      and rows_exact: "\<forall>digit < base. rows ! digit =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place (source mod place)
          digit steps"
    using admitted by (auto simp: fermat_source_matrix_admitted_def)
  have modulus_positive: "0 < fermat_matrix_modulus base place"
    using base place by (simp add: fermat_matrix_modulus_def)
  have source_digit: "source div place < base"
    using source_bound place
    by (simp only: fermat_matrix_modulus_def div_less_iff_less_mult[OF place])
  have row:
    "rows ! (source div place) =
      fermat_conditional_digit_transfer
        (fermat_matrix_modulus base place) place (source mod place)
        (source div place) steps"
    using rows_exact source_digit row_length by blast
  have transfer:
    "fermat_conditional_digit_transfer
        (fermat_matrix_modulus base place) place (source mod place)
        (source div place) steps = endpoint"
    using fermat_source_transfer_pointed_endpoint[OF place source source_bound]
      endpoint by simp
  show ?thesis using row transfer by simp
qed

lemma fermat_source_matrix_adjacent_seam:
  assumes first:
      "fermat_source_matrix_admitted level base place offset first_steps
        first_source first_endpoint first_rows"
      and later:
      "fermat_source_matrix_admitted level base place later_offset later_steps
        later_source later_endpoint later_rows"
      and adjacent: "later_offset = offset + first_steps"
  shows "later_source = first_endpoint"
  using first later adjacent
  by (simp add: fermat_source_matrix_admitted_def)

theorem fermat_source_matrix_join_rows_exact:
  assumes first:
      "fermat_source_matrix_admitted level base place offset first_steps
        first_source first_endpoint first_rows"
      and later:
      "fermat_source_matrix_admitted level base place later_offset later_steps
        later_source later_endpoint later_rows"
      and adjacent: "later_offset = offset + first_steps"
  shows "\<forall>digit < base.
      later_rows ! ((first_rows ! digit) div place) =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
proof -
  have first_base: "1 < base" and place_positive: "0 < place"
      and first_source_exact:
        "first_source = fermat_matrix_source_residue level
          (fermat_matrix_modulus base place) offset"
      and first_rows_length: "length first_rows = base"
      and first_rows_exact:
        "\<forall>digit < base. first_rows ! digit =
          fermat_conditional_digit_transfer
            (fermat_matrix_modulus base place) place
            (first_source mod place) digit first_steps"
    using first by (auto simp: fermat_source_matrix_admitted_def)
  have later_source_exact:
      "later_source = fermat_matrix_source_residue level
        (fermat_matrix_modulus base place) later_offset"
    and later_rows_length: "length later_rows = base"
    and later_rows_exact:
      "\<forall>digit < base. later_rows ! digit =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (later_source mod place) digit later_steps"
    using later by (auto simp: fermat_source_matrix_admitted_def)
  have modulus_positive:
    "0 < fermat_matrix_modulus base place"
    using first_base place_positive by (simp add: fermat_matrix_modulus_def)
  have source_lower:
    "later_source mod place =
      (3^first_steps * (first_source mod place)) mod place"
    using fermat_source_residue_lower_projection[of base place level offset
        first_steps] first_base place_positive first_source_exact
      later_source_exact adjacent
    by (simp add: fermat_matrix_modulus_def)
  have lower_seam:
    "\<forall>digit < base. (first_rows ! digit) mod place =
      later_source mod place"
  proof (intro allI impI)
    fix digit
    assume digit_bound: "digit < base"
    have first_index: "digit < length first_rows"
      using digit_bound first_rows_length by simp
    have row_exact:
      "first_rows ! digit = fermat_conditional_digit_transfer
        (fermat_matrix_modulus base place) place
        (first_source mod place) digit first_steps"
      using first_rows_exact digit_bound first_index by blast
    have row_lower:
      "(first_rows ! digit) mod place =
        (3^first_steps * (first_source mod place)) mod place"
      unfolding row_exact
      using fermat_conditional_transfer_lower_projection[of base place
          "first_source mod place" digit first_steps]
        first_base place_positive
      by (simp add: fermat_matrix_modulus_def)
    show "(first_rows ! digit) mod place = later_source mod place"
      using row_lower source_lower by simp
  qed
  show ?thesis
  proof (intro allI impI)
    fix digit
    assume digit_bound: "digit < base"
    have first_index: "digit < length first_rows"
      using digit_bound first_rows_length by simp
    let ?middle = "first_rows ! digit"
    have first_row:
      "?middle = fermat_conditional_digit_transfer
        (fermat_matrix_modulus base place) place
        (first_source mod place) digit first_steps"
      using first_rows_exact digit_bound first_index by blast
    have middle_bound:
      "?middle < fermat_matrix_modulus base place"
      unfolding first_row fermat_conditional_digit_transfer_def
      by (rule mod_less_divisor[OF modulus_positive])
    have middle_digit_bound: "?middle div place < base"
      using middle_bound place_positive
      by (simp only: fermat_matrix_modulus_def
          div_less_iff_less_mult[OF place_positive])
    have later_row:
      "later_rows ! (?middle div place) =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (later_source mod place) (?middle div place) later_steps"
      using later_rows_exact middle_digit_bound later_rows_length by blast
    have seam:
      "?middle mod place = later_source mod place"
      using lower_seam digit_bound first_index by blast
    have joined_row:
      "fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (later_source mod place) (?middle div place) later_steps =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
      using fermat_conditional_digit_transfer_join[OF modulus_positive
          place_positive, of "first_source mod place" digit first_steps
            "later_source mod place" later_steps] seam first_row by simp
    show "later_rows ! (first_rows ! digit div place) =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
      using later_row joined_row by simp
  qed
qed

theorem fermat_source_matrix_join_pointed_endpoint:
  assumes first:
      "fermat_source_matrix_admitted level base place offset first_steps
        first_source first_endpoint first_rows"
      and later:
      "fermat_source_matrix_admitted level base place later_offset later_steps
        later_source later_endpoint later_rows"
      and adjacent: "later_offset = offset + first_steps"
  shows "later_rows ! ((first_rows ! (first_source div place)) div place) =
    later_endpoint"
proof -
  have first_selected:
    "first_rows ! (first_source div place) = first_endpoint"
    by (rule fermat_source_matrix_selected_row[OF first])
  have later_selected:
    "later_rows ! (later_source div place) = later_endpoint"
    by (rule fermat_source_matrix_selected_row[OF later])
  have first_digit_bound: "first_source div place < base"
    using first by (auto simp: fermat_source_matrix_admitted_def
        fermat_matrix_modulus_def div_less_iff_less_mult)
  have source_seam:
    "later_source = first_endpoint"
    by (rule fermat_source_matrix_adjacent_seam[OF first later adjacent])
  have second_digit:
    "first_endpoint div place = later_source div place"
    using source_seam by simp
  show ?thesis using first_selected later_selected second_digit by simp
qed

lemma fermat_matrix_puncture_projection:
  assumes divides: "clock_modulus dvd modulus"
  shows "fermat_matrix_source_residue level modulus offset mod clock_modulus =
    (3^(2^level + offset)) mod clock_modulus"
  unfolding fermat_matrix_source_residue_def
  by (rule mod_mod_cancel[OF divides])

text \<open>The runtime \<open>then\<close> loop enumerates the first conditional endpoint
vector, divides each midpoint by the lower-place modulus, and indexes the
later endpoint vector.  The indexed form below is that same operation with
the row number explicit; the adapter lemma identifies both produced lists.
This isolates the functional row-list contract from the issuer and tuple
representation checks performed at the Python boundary.\<close>

definition fermat_source_matrix_join_rows ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "fermat_source_matrix_join_rows base place first_rows later_rows =
    map (\<lambda>digit. later_rows ! ((first_rows ! digit) div place)) [0..<base]"

definition fermat_source_matrix_join_rows_by_iteration ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "fermat_source_matrix_join_rows_by_iteration place first_rows later_rows =
    map (\<lambda>midpoint. later_rows ! (midpoint div place)) first_rows"

lemma fermat_source_matrix_join_rows_length:
  "length (fermat_source_matrix_join_rows base place first_rows later_rows) = base"
  by (simp add: fermat_source_matrix_join_rows_def)

lemma fermat_source_matrix_join_rows_at:
  assumes digit: "digit < base"
  shows "fermat_source_matrix_join_rows base place first_rows later_rows ! digit =
    later_rows ! ((first_rows ! digit) div place)"
  using digit by (simp add: fermat_source_matrix_join_rows_def nth_map nth_upt)

lemma fermat_source_matrix_join_rows_matches_iteration:
  assumes first:
    "fermat_source_matrix_admitted level base place offset first_steps
      first_source first_endpoint first_rows"
  shows "fermat_source_matrix_join_rows base place first_rows later_rows =
    fermat_source_matrix_join_rows_by_iteration place first_rows later_rows"
proof -
  have row_length: "length first_rows = base"
    using first by (auto simp: fermat_source_matrix_admitted_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (fermat_source_matrix_join_rows base place first_rows later_rows) =
        length (fermat_source_matrix_join_rows_by_iteration place first_rows later_rows)"
      using row_length by (simp add: fermat_source_matrix_join_rows_def
          fermat_source_matrix_join_rows_by_iteration_def)
  next
    fix digit
    assume digit:
      "digit < length (fermat_source_matrix_join_rows base place first_rows later_rows)"
    have bound: "digit < base"
      using digit by (simp add: fermat_source_matrix_join_rows_def)
    have index: "digit < length first_rows"
      using bound row_length by simp
    show "fermat_source_matrix_join_rows base place first_rows later_rows ! digit =
        fermat_source_matrix_join_rows_by_iteration place first_rows later_rows ! digit"
      using bound index
      by (simp add: fermat_source_matrix_join_rows_def
          fermat_source_matrix_join_rows_by_iteration_def nth_map nth_upt)
  qed
qed

theorem fermat_source_matrix_join_admitted:
  assumes first:
      "fermat_source_matrix_admitted level base place offset first_steps
        first_source first_endpoint first_rows"
      and later:
      "fermat_source_matrix_admitted level base place later_offset later_steps
        later_source later_endpoint later_rows"
      and adjacent: "later_offset = offset + first_steps"
  shows "fermat_source_matrix_admitted level base place offset
      (first_steps + later_steps) first_source later_endpoint
      (fermat_source_matrix_join_rows base place first_rows later_rows)"
proof -
  have length:
    "length (fermat_source_matrix_join_rows base place first_rows later_rows) = base"
    by (rule fermat_source_matrix_join_rows_length)
  have rows:
    "\<forall>digit < base.
      fermat_source_matrix_join_rows base place first_rows later_rows ! digit =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
  proof (intro allI impI)
    fix digit
    assume bound: "digit < base"
    have mapped:
      "fermat_source_matrix_join_rows base place first_rows later_rows ! digit =
        later_rows ! (first_rows ! digit div place)"
      by (rule fermat_source_matrix_join_rows_at[OF bound])
    have exact:
      "later_rows ! (first_rows ! digit div place) =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
      using fermat_source_matrix_join_rows_exact[OF first later adjacent]
        bound by blast
    show "fermat_source_matrix_join_rows base place first_rows later_rows ! digit =
        fermat_conditional_digit_transfer
          (fermat_matrix_modulus base place) place
          (first_source mod place) digit (first_steps + later_steps)"
      using mapped exact by simp
  qed
  show ?thesis
    using first later adjacent length rows
    by (auto simp: fermat_source_matrix_admitted_def add.assoc)
qed

corollary fermat_source_matrix_join_admitted_selected:
  assumes first:
      "fermat_source_matrix_admitted level base place offset first_steps
        first_source first_endpoint first_rows"
      and later:
      "fermat_source_matrix_admitted level base place later_offset later_steps
        later_source later_endpoint later_rows"
      and adjacent: "later_offset = offset + first_steps"
  shows "fermat_source_matrix_join_rows base place first_rows later_rows !
      (first_source div place) = later_endpoint"
  by (rule fermat_source_matrix_selected_row[
      OF fermat_source_matrix_join_admitted[OF first later adjacent]])

ML \<open>
  val checked = @{thms fermat_matrix_radix_window
    fermat_matrix_source_residue_advance
    fermat_matrix_source_residue_from_root
    fermat_conditional_digit_transfer_modular_factor
    fermat_source_transfer_pointed_endpoint
    fermat_conditional_digit_transfer_join
    fermat_conditional_transfer_lower_projection
    fermat_source_residue_lower_projection
    fermat_source_matrix_selected_row
    fermat_source_matrix_adjacent_seam
    fermat_source_matrix_join_rows_exact
    fermat_source_matrix_join_pointed_endpoint
    fermat_source_matrix_join_rows_length
    fermat_source_matrix_join_rows_at
    fermat_source_matrix_join_rows_matches_iteration
    fermat_source_matrix_join_admitted
    fermat_source_matrix_join_admitted_selected
    fermat_matrix_puncture_projection};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Fermat source matrix refinement depends on an oracle";
  val _ = if not (Thm_Deps.has_skip_proof checked) then ()
    else error "Fermat source matrix refinement contains a skipped proof";
\<close>

end
