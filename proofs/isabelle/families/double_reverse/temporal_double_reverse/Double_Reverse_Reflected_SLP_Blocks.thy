theory Double_Reverse_Reflected_SLP_Blocks
  imports Double_Reverse_Reflected_SLP_Seams
begin

text \<open>The staged cell publisher joins the preceding and receiving
blocks, zero extending the source at both ends. An output reads backwards
from its position in the receiving half. The quarter proof applies to this
reversed query without changing the order of the two input carries.\<close>

definition reflected_slp_block_inlet ::
    "double_reverse_source_slp \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> double_reverse_source_slp" where
  "reflected_slp_block_inlet source start count =
    (let word = double_reverse_source_slp_word source;
         first = double_reverse_source_window_first start;
         n = double_reverse_source_window_middle_length word start count;
         middle = (if n = 0 then Double_Reverse_Source_Empty
                   else double_reverse_source_slp_part source first (first+n))
     in double_reverse_source_window_slp word start count middle)"

lemma reflected_slp_block_inlet_exact:
  "double_reverse_source_slp_word (reflected_slp_block_inlet source start count) =
    double_reverse_zero_extended_source_window (double_reverse_source_slp_word source) start count"
proof -
  let ?word = "double_reverse_source_slp_word source"
  let ?first = "double_reverse_source_window_first start"
  let ?n = "double_reverse_source_window_middle_length ?word start count"
  show ?thesis
    unfolding reflected_slp_block_inlet_def Let_def
  proof (rule double_reverse_source_window_slp_exact)
    show "double_reverse_source_slp_word
        (if ?n = 0 then Double_Reverse_Source_Empty
         else double_reverse_source_slp_part source ?first (?first+?n)) =
      take ?n (drop ?first ?word)"
    proof (cases "?n = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have geometry: "?n = 0 \<or> ?first+?n \<le> length ?word"
        by (rule double_reverse_source_window_fragment_geometry(2))
      have bound: "?first+?n \<le> double_reverse_source_slp_length source"
        using geometry False
        by (simp add: double_reverse_source_slp_word_length)
      show ?thesis
        using double_reverse_source_slp_part_exact[OF le_add1 bound] False by simp
    qed
  qed
qed

definition reflected_cell_at :: "nat list \<Rightarrow> int \<Rightarrow> nat" where
  "reflected_cell_at word i =
    (if 0 \<le> i \<and> i < int (length word) then word ! nat i else 0)"

fun reflected_cell_iter :: "nat \<Rightarrow> nat \<Rightarrow> (int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat" where
  "reflected_cell_iter m 0 source position = source position"
| "reflected_cell_iter m (Suc time) source position =
    reflected_H_cell m (reflected_cell_iter m time source (position-1))
      (reflected_cell_iter m time source position)"

lemma reflected_cell_overlap_iter:
  "overlap_run (\<lambda>current previous. reflected_H_cell m previous current) time
    (\<lambda>back. source (origin-int back)) index = reflected_cell_iter m time source (origin-int index)"
proof (induction time arbitrary: index)
  case 0
  then show ?case by simp
next
  case (Suc time)
  have previous: "origin - int (Suc index) = (origin - int index) - 1" by simp
  show ?case by (simp only: overlap_run.simps reflected_cell_iter.simps Suc.IH previous)
qed

theorem reflected_slp_block_output_exact:
  fixes order block offset span :: nat and start :: int
    and source inlet :: double_reverse_source_slp
  assumes offset: "offset < 2^order"
  defines "span \<equiv> (2::nat)^order"
    and "start \<equiv> int (block*span) - int span"
    and "inlet \<equiv> reflected_slp_block_inlet source start (2*span)"
  shows "overlap_recursive order (\<lambda>current previous. reflected_H_cell m previous current)
    (\<lambda>back. double_reverse_source_slp_word inlet ! (span+offset-back)) 0 =
    reflected_cell_iter m span (reflected_cell_at (double_reverse_source_slp_word source))
      (int (block*span+offset))"
proof -
  have close: "offset < span" using offset by (simp only: span_def)
  let ?word = "double_reverse_source_slp_word source"
  let ?action = "\<lambda>current previous. reflected_H_cell m previous current"
  have input: "double_reverse_source_slp_word inlet =
      double_reverse_zero_extended_source_window ?word start (2*span)"
    unfolding inlet_def by (rule reflected_slp_block_inlet_exact)
  have result: "overlap_run ?action span
      (\<lambda>back. double_reverse_source_slp_word inlet ! (span+offset-back)) 0 =
    overlap_run ?action span
      (\<lambda>back. reflected_cell_at ?word (int (block*span+offset) - int back)) 0"
  proof (rule overlap_run_local)
    fix hop
    assume "0 \<le> hop" "hop \<le> 0+span"
    then have before: "hop \<le> span+offset" by simp
    have index: "span+offset-hop < 2*span" using close by arith
    have pos: "start + int (span+offset-hop) = int (block*span+offset) - int hop"
      unfolding start_def using before by (simp add: of_nat_diff)
    show "double_reverse_source_slp_word inlet ! (span+offset-hop) =
      reflected_cell_at ?word (int (block*span+offset) - int hop)"
      unfolding input reflected_cell_at_def
      by (simp only: double_reverse_zero_extended_source_window_nth[OF index] pos)
  qed
  show ?thesis using result by (simp only: overlap_recursive_exact span_def
      reflected_cell_overlap_iter of_nat_0 diff_zero)
qed

text \<open>The periodic block publisher retains both ordered inlets. Its
phase cycle comes from the length of the certified finite repeated source;
the remainder is a finite prefix of the same ordered ring.\<close>

definition reflected_slp_pair_emit ::
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_slp_pair_emit m order previous current offset =
    (let span = (2::nat)^order; inlet = previous @ current
     in overlap_recursive order (\<lambda>current previous. reflected_H_cell m previous current)
       (\<lambda>back. inlet ! (span+offset-back)) 0)"

theorem reflected_slp_pair_emit_source:
  assumes offset: "offset < (2::nat)^order"
    and inlet: "double_reverse_source_slp_word
      (reflected_slp_block_inlet source (int (block*2^order)-int (2^order))
        (2*2^order)) = previous @ current"
  shows "reflected_slp_pair_emit m order previous current offset =
    reflected_cell_iter m (2^order)
      (reflected_cell_at (double_reverse_source_slp_word source))
      (int (block*2^order+offset))"
proof -
  have exact:
    "overlap_recursive order (\<lambda>current previous. reflected_H_cell m previous current)
      (\<lambda>back. double_reverse_source_slp_word
        (reflected_slp_block_inlet source (int (block*2^order)-int (2^order))
          (2*2^order)) ! (2^order+offset-back)) 0 =
      reflected_cell_iter m (2^order)
        (reflected_cell_at (double_reverse_source_slp_word source))
        (int (block*2^order+offset))"
    by (rule reflected_slp_block_output_exact[OF offset])
  show ?thesis using exact inlet by (simp add: reflected_slp_pair_emit_def Let_def)
qed

lemma reflected_slp_block_phase_cycle:
  assumes "0 < length motif"
  shows "(phase + (block + double_reverse_source_phase_cycle (length motif) span) * span)
      mod length motif = (phase + block * span) mod length motif"
proof -
  have zero: "(double_reverse_source_phase_cycle (length motif) span * span)
      mod length motif = 0"
    by (rule double_reverse_source_phase_cycle_annihilates[OF assms])
  have remainder:
    "(phase + block * span +
       (double_reverse_source_phase_cycle (length motif) span * span)
         mod length motif) mod length motif =
      (phase + block * span) mod length motif"
    by (simp add: zero)
  have unreduced:
    "(phase + block * span +
       double_reverse_source_phase_cycle (length motif) span * span)
       mod length motif = (phase + block * span) mod length motif"
    using remainder by (simp only: mod_add_right_eq)
  show ?thesis using unreduced by (simp only: add_mult_distrib add.assoc)
qed

lemma reflected_lsd_cells_decoded:
  "reflected_padded_source (reflected_lsd_digits_of_cells cells) (2*i) =
      reflected_padded_source cells i mod 10 \<and>
    reflected_padded_source (reflected_lsd_digits_of_cells cells) (2*i+1) =
      reflected_padded_source cells i div 10"
proof (induction cells arbitrary: i)
  case Nil
  then show ?case by (simp add: reflected_padded_source_def)
next
  case (Cons cell cells)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: reflected_padded_source_cons)
  next
    case (Suc j)
    have lower: "2 * Suc j = Suc (Suc (2*j))" by simp
    show ?thesis using Cons.IH[of j]
      by (simp only: Suc lower add_Suc reflected_lsd_digits_of_cells.simps
          reflected_padded_source_cons)
  qed
qed

lemmas reflected_lsd_digits_of_cells_pair =
  reflected_lsd_cells_decoded[THEN conjunct1] reflected_lsd_cells_decoded[THEN conjunct2]

lemma reflected_cell_iter_zero_halo:
  assumes negative: "position < 0"
  shows "reflected_cell_iter m time (reflected_cell_at cells) position = 0"
  using negative
proof (induction time arbitrary: position)
  case 0
  then show ?case by (simp add: reflected_cell_at_def)
next
  case (Suc time)
  have previous: "position - 1 < 0" using Suc.prems by arith
  show ?case using Suc.IH[OF Suc.prems] Suc.IH[OF previous]
    by (simp add: reflected_H_cell_def reflected_H_pair_def reflected_H_pair_parts_def Let_def)
qed

theorem reflected_cell_iter_digits:
  assumes m: "m = 2 \<or> m = 5"
    and decimal: "reflected_decimal (reflected_lsd_digits_of_cells cells)"
  defines "source \<equiv> reflected_padded_source (reflected_lsd_digits_of_cells cells)"
  shows "reflected_cell_iter m time (reflected_cell_at cells) (int i) =
    reflected_H_digit_iter m time source (2*i) +
        10 * reflected_H_digit_iter m time source (2*i+1)"
proof (induction time arbitrary: i)
  case 0
  have inlet: "reflected_cell_at cells (int i) = reflected_padded_source cells i"
    by (simp add: reflected_cell_at_def reflected_padded_source_def)
  show ?case
    unfolding source_def reflected_cell_iter.simps reflected_H_digit_iter.simps inlet
    by (simp only: reflected_lsd_digits_of_cells_pair mod_mult_div_eq)
next
  case (Suc time)
  note IH = Suc.IH
  let ?run = "reflected_H_digit_iter m time source"
  have in_range: "?run j < 10" for j
    unfolding source_def
    using reflected_padded_H_iter_decimal[OF m decimal, of time]
    by (simp only: reflected_padded_H_iter_source_digit[OF m decimal, symmetric])
      (auto simp: reflected_padded_source_def list_all_iff)
  show ?case
  proof (cases i)
    case 0
    have zero: "reflected_cell_iter m time (reflected_cell_at cells) (-1) = 0"
      by (rule reflected_cell_iter_zero_halo) simp
    have dummy: "(0::nat) < 10" by simp
    have cell: "reflected_H_cell m 0 (?run 0 + 10 * ?run 1) =
      reflected_H_pair m 0 0 (?run 0) (?run 1)"
      using reflected_H_cell_decodes_pairs[OF dummy in_range[of 0],
          where multiplier=m and previous_high=0 and current_high="?run 1"] by simp
    have emit: "reflected_H_cell m 0 (?run 0 + 10 * ?run 1) =
      reflected_H_digit m ?run 0 + 10 * reflected_H_digit m ?run 1"
      by (rule trans[OF cell reflected_H_pair_zero_bridge[symmetric]])
    show ?thesis using IH[of 0] zero emit by (simp add: 0)
  next
    case (Suc j)
    have positive: "0 < i" using Suc by simp
    have previous: "int i - 1 = int (i-1)" using Suc by simp
    have step: "reflected_H_cell m
      (?run (2*(i-1)) + 10 * ?run (2*(i-1)+1))
      (?run (2*i) + 10 * ?run (2*i+1)) =
      reflected_H_pair m (?run (2*(i-1))) (?run (2*(i-1)+1)) (?run (2*i)) (?run (2*i+1))"
      by (rule reflected_H_cell_decodes_pairs[OF in_range in_range])
    show ?thesis
      unfolding reflected_cell_iter.simps reflected_H_digit_iter.simps previous IH step
      by (rule reflected_H_pair_digit_bridge[OF positive, symmetric])
  qed
qed

definition reflected_slp_stage_cell :: "nat \<Rightarrow> nat \<Rightarrow> double_reverse_source_slp \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_slp_stage_cell m order source i =
    (let span = (2::nat)^order;
         block = i div span;
         offset = i mod span;
         inlet = reflected_slp_block_inlet source (int (block*span)-int span) (2*span)
     in overlap_recursive order (\<lambda>current previous. reflected_H_cell m previous current)
          (\<lambda>back. double_reverse_source_slp_word inlet ! (span+offset-back)) 0)"

lemma reflected_slp_stage_cell_exact:
  "reflected_slp_stage_cell m order source i =
   reflected_cell_iter m (2^order) (reflected_cell_at (double_reverse_source_slp_word source)) (int i)"
proof -
  let ?span = "(2::nat)^order"
  let ?block = "i div ?span"
  let ?offset = "i mod ?span"
  let ?start = "int (?block*?span)-int ?span"
  let ?inlet = "reflected_slp_block_inlet source ?start (2*?span)"
  have offset: "?offset < ?span" by simp
  have coordinate: "?block*?span+?offset = i" by (rule div_mult_mod_eq)
  have block:
    "overlap_recursive order (\<lambda>current previous. reflected_H_cell m previous current)
      (\<lambda>back. double_reverse_source_slp_word ?inlet ! (?span+?offset-back)) 0 =
      reflected_cell_iter m ?span (reflected_cell_at (double_reverse_source_slp_word source))
        (int (?block*?span+?offset))"
    by (rule reflected_slp_block_output_exact[OF offset])
  show ?thesis
    by (simp only: reflected_slp_stage_cell_def Let_def block coordinate)
qed

theorem reflected_slp_stage_cell_compiled:
  assumes m: "m=2 \<or> m=5"
    and decimal: "reflected_decimal (reflected_lsd_digits_of_cells
      (double_reverse_source_slp_word source))"
  defines "digits \<equiv> reflected_lsd_digits_of_cells (double_reverse_source_slp_word source)"
  shows "reflected_slp_stage_cell m order source i =
    reflected_compiled_digit m order digits (2*i) +
    10 * reflected_compiled_digit m order digits (2*i+1)"
  unfolding digits_def reflected_slp_stage_cell_exact
  by (simp only: reflected_cell_iter_digits[OF m decimal]
    reflected_compiled_digit_exact[OF m decimal] reflected_padded_H_iter_source_digit[OF m decimal])

lemma reflected_lsd_digits_of_cells_length[simp]:
  "length (reflected_lsd_digits_of_cells cells) = 2 * length cells"
  by (induction cells) simp_all

definition reflected_slp_stage_word :: "nat \<Rightarrow> nat \<Rightarrow> double_reverse_source_slp \<Rightarrow> nat list" where
  "reflected_slp_stage_word m order source =
    map (reflected_slp_stage_cell m order source) [0..<double_reverse_source_slp_length source + 2^order]"

theorem reflected_slp_stage_word_compiled:
  assumes m: "m=2 \<or> m=5"
    and decimal: "reflected_decimal (reflected_lsd_digits_of_cells
      (double_reverse_source_slp_word source))"
  defines "digits \<equiv> reflected_lsd_digits_of_cells (double_reverse_source_slp_word source)"
  shows "reflected_lsd_digits_of_cells (reflected_slp_stage_word m order source) =
    reflected_compiled_word m order digits"
proof (rule nth_equalityI)
  let ?raw = "reflected_slp_stage_word m order source"
  let ?compiled = "reflected_compiled_word m order digits"
  let ?bound = "double_reverse_source_slp_length source + (2::nat)^order"
  have extent: "length ?raw = ?bound" "length ?compiled = 2*?bound"
    by (simp_all add: reflected_slp_stage_word_def reflected_compiled_word_def
        digits_def double_reverse_source_slp_word_length)
  show "length (reflected_lsd_digits_of_cells ?raw) = length ?compiled"
    using extent by simp
  fix j
  assume j: "j < length (reflected_lsd_digits_of_cells ?raw)"
  let ?i = "j div 2"
  let ?digit = "reflected_compiled_digit m order digits"
  have i: "?i < ?bound" using j extent by (simp add: div_less_iff_less_mult mult.commute)
  have index: "2 * ?i + j mod 2 = j" using div_mult_mod_eq[of j 2] by simp
  have packed:
    "reflected_padded_source ?raw ?i = ?digit (2*?i) + 10 * ?digit (2*?i+1)"
    using i extent reflected_slp_stage_cell_compiled[OF m decimal, of order ?i]
    by (simp add: reflected_slp_stage_word_def reflected_padded_source_def digits_def)
  have digit_bound: "?digit x < 10" for x
    using reflected_padded_H_iter_decimal[OF m decimal, of "2^order"]
    unfolding digits_def reflected_compiled_digit_exact[OF m decimal]
    by (auto simp: reflected_padded_source_def list_all_iff)
  have low: "(?digit (2*?i) + 10 * ?digit (2*?i+1)) mod 10 = ?digit (2*?i)"
    using digit_bound[of "2*?i"] by simp
  have high: "(?digit (2*?i) + 10 * ?digit (2*?i+1)) div 10 = ?digit (2*?i+1)"
    using digit_bound[of "2*?i"] by simp
  have dec:
    "reflected_padded_source (reflected_lsd_digits_of_cells ?raw) (2*?i) = ?digit (2*?i)"
    "reflected_padded_source (reflected_lsd_digits_of_cells ?raw) (2*?i+1) = ?digit (2*?i+1)"
    by (simp_all only: reflected_lsd_digits_of_cells_pair packed low high)
  have parity: "j mod 2 < 2" by simp
  have "j = 2*?i \<or> j = 2*?i+1" using index parity by arith
  then have result: "reflected_padded_source (reflected_lsd_digits_of_cells ?raw) j = ?digit j"
    using dec by auto
  have read: "?compiled ! j = ?digit j"
    using j extent by (simp add: reflected_compiled_word_def)
  show "reflected_lsd_digits_of_cells ?raw ! j = ?compiled ! j"
    using j result read by (simp add: reflected_padded_source_def)
qed

ML \<open>
  val checked = @{thms reflected_slp_block_inlet_exact reflected_cell_overlap_iter
    reflected_slp_block_output_exact reflected_slp_pair_emit_source
    reflected_slp_block_phase_cycle double_reverse_source_repeat_word_take double_reverse_adjacent_repeat
    reflected_cell_iter_digits
    reflected_slp_stage_cell_exact reflected_slp_stage_cell_compiled reflected_slp_stage_word_compiled};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected SLP block refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped reflected SLP block proof" else ();
\<close>

end
