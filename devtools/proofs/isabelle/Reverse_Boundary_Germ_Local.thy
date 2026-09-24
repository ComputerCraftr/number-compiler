theory Reverse_Boundary_Germ_Local
  imports Reverse_Factored_Channels
begin

text \<open>A three-cell boundary is an observation of an admitted Q95
occurrence.  The absent cell has a separate constructor: the integer 95 is
not a decimal pair coefficient and is never passed to the carry gate.
The left edge is in physical LSD-to-MSD order; the right edge is in reflected
coordinate order.  Reflection swaps edge observations.  It does not reverse
the direction of physical carry.\<close>

datatype q95_boundary_cell = Q95_Cell nat | Q95_Blank

definition q95_boundary_valid :: "q95_boundary_cell \<Rightarrow> bool" where
  "q95_boundary_valid cell \<longleftrightarrow>
    (case cell of Q95_Blank \<Rightarrow> True | Q95_Cell value \<Rightarrow> value < 95)"

definition q95_boundary_encode :: "q95_boundary_cell \<Rightarrow> nat" where
  "q95_boundary_encode cell =
    (case cell of Q95_Blank \<Rightarrow> 95 | Q95_Cell value \<Rightarrow> value)"

definition q95_boundary_decode :: "nat \<Rightarrow> q95_boundary_cell option" where
  "q95_boundary_decode value =
    (if value < 95 then Some (Q95_Cell value)
     else if value = 95 then Some Q95_Blank else None)"

lemma q95_boundary_roundtrip:
  assumes "q95_boundary_valid cell"
  shows "q95_boundary_decode (q95_boundary_encode cell) = Some cell"
  using assms by (cases cell) (simp_all add: q95_boundary_valid_def
    q95_boundary_decode_def q95_boundary_encode_def)

lemma q95_blank_not_a_pair:
  "q95_boundary_decode 95 = Some Q95_Blank"
  "q95_boundary_decode value = Some (Q95_Cell q) \<Longrightarrow> q < 95"
  by (auto simp: q95_boundary_decode_def split: if_splits)

definition q95_local_normalize ::
    "q95_boundary_cell \<Rightarrow> bool \<Rightarrow> (nat \<times> bool) option" where
  "q95_local_normalize cell incoming =
    (case cell of
      Q95_Blank \<Rightarrow> None
    | Q95_Cell q \<Rightarrow>
        if q < 95 then
          Some ((q div 5 + (if incoming then 1 else 0)) mod 10,
            carry_apply (domain (q div 5)) incoming)
        else None)"

lemma q95_local_rejects_blank [simp]:
  "q95_local_normalize Q95_Blank incoming = None"
  by (simp add: q95_local_normalize_def)

lemma q95_local_refines_decimal:
  assumes "symbol < 19" "forcing < 5"
  shows "q95_local_normalize
       (Q95_Cell (q95_encode symbol forcing)) incoming =
    Some ((symbol + (if incoming then 1 else 0)) mod 10,
      carry_apply (domain symbol) incoming)"
  using assms q95_decode[OF assms(2)] q95_range[OF assms]
  by (simp add: q95_local_normalize_def)

lemma q95_local_equality_wire:
  assumes "forcing < 5"
  shows "q95_local_normalize (Q95_Cell (q95_encode 9 forcing)) incoming =
    Some ((9 + (if incoming then 1 else 0)) mod 10, incoming)"
  using q95_local_refines_decimal[of 9 forcing incoming] assms
  by (simp add: domain_def)

lemma q95_local_carry_threshold:
  assumes "symbol < 19" "forcing < 5"
  shows "snd (the (q95_local_normalize
      (Q95_Cell (q95_encode symbol forcing)) incoming)) =
    (if symbol < 9 then False else if symbol = 9 then incoming else True)"
  using q95_local_refines_decimal[OF assms]
  by (simp add: domain_def)

definition boundary_pad3 :: "nat list \<Rightarrow> q95_boundary_cell list" where
  "boundary_pad3 values =
    map Q95_Cell (take 3 values) @
      replicate (3 - length (take 3 values)) Q95_Blank"

definition boundary_germ3 ::
    "nat list \<Rightarrow> q95_boundary_cell list \<times> q95_boundary_cell list" where
  "boundary_germ3 values = (boundary_pad3 values, boundary_pad3 (rev values))"

definition boundary_reflect3 ::
    "q95_boundary_cell list \<times> q95_boundary_cell list \<Rightarrow>
      q95_boundary_cell list \<times> q95_boundary_cell list" where
  "boundary_reflect3 germ = (snd germ, fst germ)"

lemma boundary_pad3_length [simp]: "length (boundary_pad3 values) = 3"
  by (simp add: boundary_pad3_def)

lemma boundary_pad3_all_valid:
  assumes "\<forall>q \<in> set values. q < 95"
  shows "\<forall>cell \<in> set (boundary_pad3 values). q95_boundary_valid cell"
proof -
  have "set (take 3 values) \<subseteq> set values"
    by (rule set_take_subset)
  with assms show ?thesis
    by (auto simp: boundary_pad3_def q95_boundary_valid_def)
qed

lemma boundary_reflection_exact:
  "boundary_germ3 (rev values) = boundary_reflect3 (boundary_germ3 values)"
  by (simp add: boundary_germ3_def boundary_reflect3_def)

lemma boundary_reflection_involution:
  "boundary_reflect3 (boundary_reflect3 germ) = germ"
  by (cases germ) (simp add: boundary_reflect3_def)

text \<open>Numeric pair reflection exchanges reset directions and fixes the
equality wire.  This is a theorem about the pair symbol.  It supplies no
F5 forcing transformation for the coupled Q95 cell.\<close>

lemma decimal_pair_complement_domain:
  assumes "symbol \<le> 18"
  shows "domain (18 - symbol) =
    (case domain symbol of Below \<Rightarrow> Above | Equal \<Rightarrow> Equal
      | Above \<Rightarrow> Below)"
  using assms by (auto simp: domain_def split: carry_domain.splits)

lemma decimal_pair_complement_carry:
  assumes "symbol \<le> 18"
  shows "carry_apply (domain (18 - symbol)) incoming =
    (\<not> carry_apply (domain symbol) (\<not> incoming))"
  using decimal_pair_complement_domain[OF assms]
  by (cases "domain symbol") simp_all

text \<open>Exact contextual criterion.  A three-cell observation can replace
the old temporal program only after the implemented complete action and its
source successor satisfy these equalities on every admitted occurrence.  The
finite 196 sample verifies instances, not these universally quantified
premises.\<close>

theorem boundary_germ_successor_factor_iff:
  "(\<exists>advance. \<forall>source \<in> admitted.
      advance (boundary_germ3 (word source)) =
        boundary_germ3 (word (successor source))) \<longleftrightarrow>
   (\<forall>left \<in> admitted. \<forall>right \<in> admitted.
      boundary_germ3 (word left) = boundary_germ3 (word right)
      \<longrightarrow> boundary_germ3 (word (successor left)) =
          boundary_germ3 (word (successor right)))"
  by (simp add: factor_through_iff comp_def)

text \<open>A bare radius-three boundary germ is not a successor state even
on symmetric, bounded pair fields.  These two witnesses have the same outer
three exact Q95 cells on both sides.  Their different fourth cells change
the physical carry reaching the right edge.  The proposed Frobenius clock
and source admission may further distinguish such witnesses; this theorem
does not claim a collision for that richer key.\<close>

definition boundary_witness_below :: "nat list" where
  "boundary_witness_below = [9,9,9,8,9,9,9]"

definition boundary_witness_above :: "nat list" where
  "boundary_witness_above = [9,9,9,10,9,9,9]"

definition pair_q95_zero :: "nat list \<Rightarrow> nat list" where
  "pair_q95_zero symbols = map (\<lambda>symbol. q95_encode symbol 0) symbols"

lemma boundary_witnesses_valid:
  "valid_pair boundary_witness_below"
  "valid_pair boundary_witness_above"
  by (simp_all add: valid_pair_def boundary_witness_below_def
      boundary_witness_above_def)

lemma boundary_witnesses_agree:
  "boundary_germ3 (pair_q95_zero boundary_witness_below) =
    boundary_germ3 (pair_q95_zero boundary_witness_above)"
  by (simp add: boundary_germ3_def boundary_pad3_def
      pair_q95_zero_def boundary_witness_below_def
      boundary_witness_above_def q95_encode_def)

lemma boundary_witnesses_successors_disagree:
  "boundary_germ3 (pair_q95_zero (step boundary_witness_below)) \<noteq>
    boundary_germ3 (pair_q95_zero (step boundary_witness_above))"
  by (simp add: boundary_germ3_def boundary_pad3_def
      pair_q95_zero_def boundary_witness_below_def
      boundary_witness_above_def q95_encode_def step_def digits_def
      carry_out_def domain_def)

theorem boundary_germ_alone_no_total_successor:
  "\<not> (\<exists>advance. \<forall>symbols.
      valid_pair symbols \<longrightarrow>
      advance (boundary_germ3 (pair_q95_zero symbols)) =
        boundary_germ3 (pair_q95_zero (step symbols)))"
  using boundary_witnesses_valid boundary_witnesses_agree
    boundary_witnesses_successors_disagree by metis

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms q95_boundary_roundtrip q95_blank_not_a_pair
      q95_local_rejects_blank q95_local_refines_decimal
      q95_local_equality_wire q95_local_carry_threshold
      boundary_pad3_length boundary_pad3_all_valid
      boundary_reflection_exact boundary_reflection_involution
      decimal_pair_complement_domain decimal_pair_complement_carry
      boundary_germ_successor_factor_iff boundary_witnesses_valid
      boundary_witnesses_agree boundary_witnesses_successors_disagree
      boundary_germ_alone_no_total_successor}) then ()
    else error "Boundary germ local proof depends on an oracle";
\<close>

end
