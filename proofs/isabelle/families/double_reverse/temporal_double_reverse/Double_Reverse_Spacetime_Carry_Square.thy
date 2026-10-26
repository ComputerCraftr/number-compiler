theory Double_Reverse_Spacetime_Carry_Square
  imports Double_Reverse_Periodic_Ring_Action
begin

text \<open>A finite causal T-squared cone.  One update consumes a three-digit
halo and removes one digit from each end.  The iterated action below is exact
on finite words; no source period, cyclic boundary, or infinite continuation is
assumed.\<close>

definition double_reverse_spacetime_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_spacetime_step word =
    map (\<lambda>i. double_reverse_t2_digit
      (word ! i) (word ! (i+1)) (word ! (i+2)))
      [0..<length word - 2]"

fun double_reverse_spacetime_power :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_spacetime_power 0 word = word"
| "double_reverse_spacetime_power (Suc steps) word =
    double_reverse_spacetime_step
      (double_reverse_spacetime_power steps word)"

fun double_reverse_spacetime_run ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_spacetime_run 0 source i = source i"
| "double_reverse_spacetime_run (Suc steps) source i =
    double_reverse_t2_digit
      (double_reverse_spacetime_run steps source i)
      (double_reverse_spacetime_run steps source (i+1))
      (double_reverse_spacetime_run steps source (i+2))"

lemma double_reverse_spacetime_run_shift:
  "double_reverse_spacetime_run steps (\<lambda>i. source (offset+i)) i0 =
    double_reverse_spacetime_run steps source (offset+i0)"
  by (induction steps arbitrary: i0) (simp_all add: add.assoc)

lemma double_reverse_spacetime_run_add:
  "double_reverse_spacetime_run (first+second) source i =
    double_reverse_spacetime_run second
      (\<lambda>j. double_reverse_spacetime_run first source j) i"
  by (induction second arbitrary: first source i)
    (simp_all add: add_Suc)

lemma double_reverse_spacetime_run_congruent:
  assumes agree:
    "\<And>j. i \<le> j \<Longrightarrow> j \<le> i + 2*steps \<Longrightarrow>
      left j = right j"
  shows "double_reverse_spacetime_run steps left i =
    double_reverse_spacetime_run steps right i"
  using agree
proof (induction steps arbitrary: i left right)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have at_i:
    "double_reverse_spacetime_run steps left i =
      double_reverse_spacetime_run steps right i"
    by (rule Suc.IH) (use Suc.prems in auto)
  have at_i1:
    "double_reverse_spacetime_run steps left (i+1) =
      double_reverse_spacetime_run steps right (i+1)"
    by (rule Suc.IH) (use Suc.prems in auto)
  have at_i2:
    "double_reverse_spacetime_run steps left (i+2) =
      double_reverse_spacetime_run steps right (i+2)"
    by (rule Suc.IH) (use Suc.prems in auto)
  show ?case using at_i at_i1 at_i2 by simp
qed

lemma double_reverse_spacetime_step_length:
  "length (double_reverse_spacetime_step word) = length word - 2"
  by (simp add: double_reverse_spacetime_step_def)

lemma double_reverse_spacetime_step_cell:
  assumes "i+2 < length word"
  shows "double_reverse_spacetime_step word ! i =
    double_reverse_t2_digit (word ! i) (word ! (i+1)) (word ! (i+2))"
proof -
  have index: "i < length word - 2"
    using assms by arith
  show ?thesis using index
    by (simp add: double_reverse_spacetime_step_def)
qed

lemma double_reverse_spacetime_power_length:
  "length (double_reverse_spacetime_power steps word) =
    length word - 2*steps"
  by (induction steps) (simp_all add:
    double_reverse_spacetime_step_length algebra_simps)

lemma double_reverse_spacetime_power_one:
  "double_reverse_spacetime_power 1 [a,b,c,d] =
    [double_reverse_t2_digit a b c,
     double_reverse_t2_digit b c d]"
  by (simp add: double_reverse_spacetime_step_def)

lemma double_reverse_spacetime_power_content_congruent:
  assumes "left = right"
  shows "double_reverse_spacetime_power steps left =
    double_reverse_spacetime_power steps right"
  using assms by simp

lemma double_reverse_spacetime_power_add:
  "double_reverse_spacetime_power (first+second) word =
    double_reverse_spacetime_power second
      (double_reverse_spacetime_power first word)"
  by (induction second arbitrary: first word)
    (simp_all add: add_Suc)

lemma double_reverse_spacetime_power_cell:
  assumes "i + 2*steps < length word"
  shows "double_reverse_spacetime_power steps word ! i =
    double_reverse_spacetime_run steps (\<lambda>j. word ! j) i"
  using assms
proof (induction steps arbitrary: word i)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have index_bound: "i+2 <
      length (double_reverse_spacetime_power steps word)"
    using Suc.prems double_reverse_spacetime_power_length[of steps word]
    by arith
  have cell0:
    "double_reverse_spacetime_power steps word ! i =
      double_reverse_spacetime_run steps (\<lambda>j. word ! j) i"
    by (rule Suc.IH) (use Suc.prems in arith)
  have cell1:
    "double_reverse_spacetime_power steps word ! (i+1) =
      double_reverse_spacetime_run steps (\<lambda>j. word ! j) (i+1)"
    by (rule Suc.IH) (use Suc.prems in arith)
  have cell2:
    "double_reverse_spacetime_power steps word ! (i+2) =
      double_reverse_spacetime_run steps (\<lambda>j. word ! j) (i+2)"
    by (rule Suc.IH) (use Suc.prems in arith)
  show ?case
    using cell0 cell1 cell2
    by (simp add: double_reverse_spacetime_step_cell[OF index_bound])
qed

lemma double_reverse_spacetime_window_power:
  assumes extent: "start + window_width + 2*steps \<le> length source"
  shows "double_reverse_spacetime_power steps
      (take (window_width + 2*steps) (drop start source)) =
    take window_width (drop start
      (double_reverse_spacetime_power steps source))"
proof (rule nth_equalityI)
  have window_length:
    "length (take (window_width + 2*steps) (drop start source)) =
      window_width + 2*steps"
    using extent by simp
  show lengths:
    "length (double_reverse_spacetime_power steps
        (take (window_width + 2*steps) (drop start source))) =
      length (take window_width (drop start
        (double_reverse_spacetime_power steps source)))"
    using extent window_length
    by (simp add: double_reverse_spacetime_power_length)
next
  fix i
  assume index: "i < length
      (double_reverse_spacetime_power steps
        (take (window_width + 2*steps) (drop start source)))"
  have window_length_local:
    "length (take (window_width + 2*steps) (drop start source)) =
      window_width + 2*steps"
    using extent by simp
  have i_window_width: "i < window_width"
    using index extent window_length_local
    by (simp add: double_reverse_spacetime_power_length)
  have left_bound: "i + 2*steps < window_width + 2*steps"
    using i_window_width by arith
  have right_bound: "start + i + 2*steps < length source"
    using extent i_window_width by arith
  have dropped_length: "window_width + 2*steps \<le> length (drop start source)"
    using extent by (simp; arith)
  have local_agreement:
    "\<And>j. i \<le> j \<Longrightarrow> j \<le> i + 2*steps \<Longrightarrow>
      (take (window_width + 2*steps) (drop start source)) ! j =
        source ! (start+j)"
  proof -
    fix j
    assume lower: "i \<le> j" and upper: "j \<le> i + 2*steps"
    have j_take: "j < window_width + 2*steps"
      using upper left_bound by arith
    have j_drop: "j < length (drop start source)"
      using j_take dropped_length by arith
    show "(take (window_width + 2*steps) (drop start source)) ! j =
        source ! (start+j)"
      using j_take j_drop by simp
  qed
  have run_agreement:
    "double_reverse_spacetime_run steps
       (\<lambda>j. (take (window_width + 2*steps) (drop start source)) ! j) i =
     double_reverse_spacetime_run steps (\<lambda>j. source ! (start+j)) i"
    by (rule double_reverse_spacetime_run_congruent[where steps=steps])
      (rule local_agreement)
  have left_halo_bound:
    "i + 2*steps < length (take (window_width + 2*steps) (drop start source))"
    using left_bound window_length_local by simp
  have cell_left:
    "double_reverse_spacetime_power steps
       (take (window_width + 2*steps) (drop start source)) ! i =
     double_reverse_spacetime_run steps
       (\<lambda>j. (take (window_width + 2*steps) (drop start source)) ! j) i"
    by (rule double_reverse_spacetime_power_cell[OF left_halo_bound])
  have cell_right:
    "double_reverse_spacetime_power steps source ! (start+i) =
     double_reverse_spacetime_run steps (\<lambda>j. source ! j) (start+i)"
    by (rule double_reverse_spacetime_power_cell[OF right_bound])
  have shifted:
    "double_reverse_spacetime_run steps (\<lambda>j. source ! (start+j)) i =
     double_reverse_spacetime_run steps (\<lambda>j. source ! j) (start+i)"
    by (rule double_reverse_spacetime_run_shift)
  have result_extent:
    "start + window_width \<le> length (double_reverse_spacetime_power steps source)"
    using extent
    by (simp add: double_reverse_spacetime_power_length; arith)
  have result_drop_extent:
    "window_width \<le> length (drop start
      (double_reverse_spacetime_power steps source))"
    using result_extent by simp
  have result_drop_index:
    "i < length (drop start
      (double_reverse_spacetime_power steps source))"
    using i_window_width result_drop_extent by arith
  show "double_reverse_spacetime_power steps
      (take (window_width + 2*steps) (drop start source)) ! i =
    take window_width (drop start
      (double_reverse_spacetime_power steps source)) ! i"
    using cell_left run_agreement shifted cell_right i_window_width result_drop_index
    by (simp add: add.commute)
qed

text \<open>The square law below is the exact temporal Hashlife split.  The input
has 8s cells; its four consecutive 2s blocks are A,B,C,D.  The three first
half cones are U_s(AB), U_s(BC), U_s(CD), then two overlapping 4s windows
are powered.  Their 2s outputs concatenate to the full 4s center.\<close>

theorem double_reverse_spacetime_temporal_square:
  assumes source_length: "length source = 8*steps"
  shows "double_reverse_spacetime_power (2*steps) source =
      double_reverse_spacetime_power steps
        (double_reverse_spacetime_power steps (take (4*steps) source) @
         double_reverse_spacetime_power steps
           (take (4*steps) (drop (2*steps) source))) @
      double_reverse_spacetime_power steps
        (double_reverse_spacetime_power steps
           (take (4*steps) (drop (2*steps) source)) @
         double_reverse_spacetime_power steps
           (take (4*steps) (drop (4*steps) source)))"
proof -
  let ?middle = "double_reverse_spacetime_power steps source"
  let ?u = "double_reverse_spacetime_power steps (take (4*steps) source)"
  let ?v = "double_reverse_spacetime_power steps
    (take (4*steps) (drop (2*steps) source))"
  let ?w = "double_reverse_spacetime_power steps
    (take (4*steps) (drop (4*steps) source))"
  have middle_length: "length ?middle = 6*steps"
    using source_length
    by (simp add: double_reverse_spacetime_power_length)
  have output_length: "length (double_reverse_spacetime_power steps ?middle) =
      4*steps"
    using middle_length
    by (simp add: double_reverse_spacetime_power_length)
  have u_exact: "?u = take (2*steps) ?middle"
    using double_reverse_spacetime_window_power[where source=source
      and start=0 and window_width="2*steps" and steps=steps] source_length
    by simp
  have v_exact: "?v = take (2*steps) (drop (2*steps) ?middle)"
    using double_reverse_spacetime_window_power[where source=source
      and start="2*steps" and window_width="2*steps" and steps=steps]
      source_length
    by simp
  have w_exact: "?w = take (2*steps) (drop (4*steps) ?middle)"
    using double_reverse_spacetime_window_power[where source=source
      and start="4*steps" and window_width="2*steps" and steps=steps]
      source_length
    by simp
  have four_parts: "4*steps = 2*steps + 2*steps" by arith
  have uv_exact: "?u @ ?v = take (4*steps) ?middle"
    using u_exact v_exact four_parts
    by (simp only: u_exact v_exact four_parts take_add)
  have vw_exact: "?v @ ?w = take (4*steps) (drop (2*steps) ?middle)"
    using v_exact w_exact four_parts
    by (simp only: v_exact w_exact four_parts take_add drop_drop)
  have left_exact:
    "double_reverse_spacetime_power steps (?u @ ?v) =
      take (2*steps) (double_reverse_spacetime_power steps ?middle)"
    using double_reverse_spacetime_window_power[where source="?middle"
      and start=0 and window_width="2*steps" and steps=steps]
      middle_length uv_exact by simp
  have right_exact:
    "double_reverse_spacetime_power steps (?v @ ?w) =
      take (2*steps) (drop (2*steps)
        (double_reverse_spacetime_power steps ?middle))"
    using double_reverse_spacetime_window_power[where source="?middle"
      and start="2*steps" and window_width="2*steps" and steps=steps]
      middle_length vw_exact by simp
  have split_output:
    "take (4*steps) (double_reverse_spacetime_power steps ?middle) =
       take (2*steps) (double_reverse_spacetime_power steps ?middle) @
       take (2*steps) (drop (2*steps)
         (double_reverse_spacetime_power steps ?middle))"
    using four_parts by (simp only: four_parts take_add)
  have full_output:
    "take (4*steps) (double_reverse_spacetime_power steps ?middle) =
      double_reverse_spacetime_power steps ?middle"
    using output_length by simp
  have output_partition:
    "take (2*steps) (double_reverse_spacetime_power steps ?middle) @
       take (2*steps) (drop (2*steps)
         (double_reverse_spacetime_power steps ?middle)) =
     take (4*steps) (double_reverse_spacetime_power steps ?middle)"
    by (rule split_output[symmetric])
  have square_join:
    "double_reverse_spacetime_power steps (?u @ ?v) @
       double_reverse_spacetime_power steps (?v @ ?w) =
     double_reverse_spacetime_power steps ?middle"
    using left_exact right_exact output_partition full_output by simp
  have temporal:
    "double_reverse_spacetime_power (2*steps) source =
      double_reverse_spacetime_power steps ?middle"
  proof -
    have doubled: "2*steps = steps + steps" by simp
    show ?thesis
      using doubled
      by (simp only: doubled double_reverse_spacetime_power_add)
  qed
  show ?thesis using temporal square_join by simp
qed

text \<open>The recursive dyadic constructor mirrors the production temporal
square schedule: it computes the three overlapping child halos, then recurses
on the two adjacent joined center tiles.  Its source contract is exactly one
complete finite halo; it issues no period or future-closure certificate.\<close>

fun double_reverse_spacetime_dyadic_cone ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_spacetime_dyadic_cone 0 source =
    double_reverse_spacetime_power 1 source"
| "double_reverse_spacetime_dyadic_cone (Suc level) source =
    (let span = 2^level;
         u = double_reverse_spacetime_dyadic_cone level
           (take (4*span) source);
         v = double_reverse_spacetime_dyadic_cone level
           (take (4*span) (drop (2*span) source));
         w = double_reverse_spacetime_dyadic_cone level
           (take (4*span) (drop (4*span) source))
     in double_reverse_spacetime_dyadic_cone level (u@v) @
        double_reverse_spacetime_dyadic_cone level (v@w))"

theorem double_reverse_spacetime_dyadic_cone_exact:
  assumes source_length: "length source = 4*2^level"
  shows "double_reverse_spacetime_dyadic_cone level source =
    double_reverse_spacetime_power (2^level) source"
  using source_length
proof (induction level arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc level)
  let ?span = "2^level"
  let ?left = "take (4*?span) source"
  let ?middle = "take (4*?span) (drop (2*?span) source)"
  let ?right = "take (4*?span) (drop (4*?span) source)"
  let ?u = "double_reverse_spacetime_dyadic_cone level ?left"
  let ?v = "double_reverse_spacetime_dyadic_cone level ?middle"
  let ?w = "double_reverse_spacetime_dyadic_cone level ?right"
  have source_extent: "length source = 8*?span"
    using Suc.prems by (simp add: power_Suc algebra_simps)
  have left_length: "length ?left = 4*?span"
    using source_extent by (simp; arith)
  have middle_length: "length ?middle = 4*?span"
    using source_extent by (simp; arith)
  have right_length: "length ?right = 4*?span"
    using source_extent by (simp; arith)
  have u_exact:
    "?u = double_reverse_spacetime_power ?span ?left"
    by (rule Suc.IH[OF left_length])
  have v_exact:
    "?v = double_reverse_spacetime_power ?span ?middle"
    by (rule Suc.IH[OF middle_length])
  have w_exact:
    "?w = double_reverse_spacetime_power ?span ?right"
    by (rule Suc.IH[OF right_length])
  have u_length: "length ?u = 2*?span"
    using u_exact left_length
    by (simp add: double_reverse_spacetime_power_length; arith)
  have v_length: "length ?v = 2*?span"
    using v_exact middle_length
    by (simp add: double_reverse_spacetime_power_length; arith)
  have w_length: "length ?w = 2*?span"
    using w_exact right_length
    by (simp add: double_reverse_spacetime_power_length; arith)
  have joined_left_length: "length (?u @ ?v) = 4*?span"
    using u_length v_length by (simp; arith)
  have joined_right_length: "length (?v @ ?w) = 4*?span"
    using v_length w_length by (simp; arith)
  have uv_exact:
    "double_reverse_spacetime_dyadic_cone level (?u @ ?v) =
      double_reverse_spacetime_power ?span (?u @ ?v)"
    by (rule Suc.IH[OF joined_left_length])
  have vw_exact:
    "double_reverse_spacetime_dyadic_cone level (?v @ ?w) =
      double_reverse_spacetime_power ?span (?v @ ?w)"
    by (rule Suc.IH[OF joined_right_length])
  have recursive:
    "double_reverse_spacetime_dyadic_cone (Suc level) source =
      double_reverse_spacetime_dyadic_cone level (?u @ ?v) @
      double_reverse_spacetime_dyadic_cone level (?v @ ?w)"
    by (simp add: double_reverse_spacetime_dyadic_cone.simps Let_def)
  have cone_value:
    "double_reverse_spacetime_dyadic_cone (Suc level) source =
      double_reverse_spacetime_power ?span
        (double_reverse_spacetime_power ?span ?left @
          double_reverse_spacetime_power ?span ?middle) @
      double_reverse_spacetime_power ?span
        (double_reverse_spacetime_power ?span ?middle @
          double_reverse_spacetime_power ?span ?right)"
    using recursive uv_exact vw_exact u_exact v_exact w_exact by simp
  have square:
    "double_reverse_spacetime_power (2*?span) source =
      double_reverse_spacetime_power ?span
        (double_reverse_spacetime_power ?span ?left @
          double_reverse_spacetime_power ?span ?middle) @
      double_reverse_spacetime_power ?span
        (double_reverse_spacetime_power ?span ?middle @
          double_reverse_spacetime_power ?span ?right)"
    by (rule double_reverse_spacetime_temporal_square[OF source_extent])
  have dyadic_double: "2 ^ Suc level = 2*?span"
    by (simp add: power_Suc mult.commute)
  show ?case
    using cone_value square dyadic_double
    by (simp only: dyadic_double square cone_value)
qed

corollary double_reverse_spacetime_dyadic_cone_length:
  assumes source_length: "length source = 4*2^level"
  shows "length (double_reverse_spacetime_dyadic_cone level source) =
    2*2^level"
  using double_reverse_spacetime_dyadic_cone_exact[OF source_length]
    source_length
  by (simp add: double_reverse_spacetime_power_length; arith)

text \<open>The exact content model for a perfect-binary tile.  The structural
identity is only canonical when child levels match; under that shape invariant,
flattened digit content and level uniquely determine the tile.  This rules out
hash-fingerprint and SLP-presentation identity in the semantic cone theorem.\<close>

datatype double_reverse_spacetime_tile =
    Double_Reverse_Tile_Leaf nat
  | Double_Reverse_Tile_Node
      double_reverse_spacetime_tile double_reverse_spacetime_tile

fun double_reverse_spacetime_tile_word ::
    "double_reverse_spacetime_tile \<Rightarrow> nat list" where
  "double_reverse_spacetime_tile_word (Double_Reverse_Tile_Leaf digit) =
    [digit]"
| "double_reverse_spacetime_tile_word
      (Double_Reverse_Tile_Node left right) =
    double_reverse_spacetime_tile_word left @
      double_reverse_spacetime_tile_word right"

fun double_reverse_spacetime_tile_height ::
    "double_reverse_spacetime_tile \<Rightarrow> nat" where
  "double_reverse_spacetime_tile_height (Double_Reverse_Tile_Leaf digit) = 0"
| "double_reverse_spacetime_tile_height
      (Double_Reverse_Tile_Node left right) =
    Suc (double_reverse_spacetime_tile_height left)"

fun double_reverse_spacetime_tile_perfect ::
    "double_reverse_spacetime_tile \<Rightarrow> bool" where
  "double_reverse_spacetime_tile_perfect (Double_Reverse_Tile_Leaf digit) = True"
| "double_reverse_spacetime_tile_perfect
      (Double_Reverse_Tile_Node left right) =
    (double_reverse_spacetime_tile_perfect left \<and>
     double_reverse_spacetime_tile_perfect right \<and>
     double_reverse_spacetime_tile_height left =
       double_reverse_spacetime_tile_height right)"

lemma double_reverse_spacetime_tile_word_length:
  assumes "double_reverse_spacetime_tile_perfect tile"
  shows "length (double_reverse_spacetime_tile_word tile) =
    2 ^ double_reverse_spacetime_tile_height tile"
  using assms
proof (induction tile)
  case (Double_Reverse_Tile_Leaf digit)
  then show ?case by simp
next
  case (Double_Reverse_Tile_Node left right)
  have perfect_left: "double_reverse_spacetime_tile_perfect left"
    using Double_Reverse_Tile_Node.prems by simp
  have perfect_right: "double_reverse_spacetime_tile_perfect right"
    using Double_Reverse_Tile_Node.prems by simp
  have level_equal:
    "double_reverse_spacetime_tile_height left =
      double_reverse_spacetime_tile_height right"
    using Double_Reverse_Tile_Node.prems by simp
  have left_length:
    "length (double_reverse_spacetime_tile_word left) =
      2 ^ double_reverse_spacetime_tile_height left"
    by (rule Double_Reverse_Tile_Node.IH(1)[OF perfect_left])
  have right_length:
    "length (double_reverse_spacetime_tile_word right) =
      2 ^ double_reverse_spacetime_tile_height right"
    by (rule Double_Reverse_Tile_Node.IH(2)[OF perfect_right])
  show ?case
    using left_length right_length level_equal
    by (simp add: power_Suc algebra_simps)
qed

theorem double_reverse_spacetime_tile_content_injective:
  assumes perfect_left: "double_reverse_spacetime_tile_perfect left"
      and perfect_right: "double_reverse_spacetime_tile_perfect right"
      and level: "double_reverse_spacetime_tile_height left =
        double_reverse_spacetime_tile_height right"
      and content: "double_reverse_spacetime_tile_word left =
        double_reverse_spacetime_tile_word right"
  shows "left = right"
  using perfect_left perfect_right level content
proof (induction left arbitrary: right)
  case (Double_Reverse_Tile_Leaf digit)
  note leaf_facts = Double_Reverse_Tile_Leaf.prems
  show ?case
  proof (cases right)
    case (Double_Reverse_Tile_Leaf other)
    then show ?thesis using leaf_facts by simp
  next
    case (Double_Reverse_Tile_Node a b)
    then show ?thesis using leaf_facts by simp
  qed
next
  case (Double_Reverse_Tile_Node left_a left_b)
  note node_facts = Double_Reverse_Tile_Node.prems
  note left_ih = Double_Reverse_Tile_Node.IH(1)
  note right_ih = Double_Reverse_Tile_Node.IH(2)
  show ?case
  proof (cases right)
    case (Double_Reverse_Tile_Leaf digit)
    then show ?thesis using node_facts by simp
  next
    case (Double_Reverse_Tile_Node right_a right_b)
    note right_shape = Double_Reverse_Tile_Node
    have perfect_left_a: "double_reverse_spacetime_tile_perfect left_a"
      using node_facts(1) by simp
    have perfect_left_b: "double_reverse_spacetime_tile_perfect left_b"
      using node_facts(1) by simp
    have perfect_right_a: "double_reverse_spacetime_tile_perfect right_a"
      using node_facts(2) right_shape by simp
    have perfect_right_b: "double_reverse_spacetime_tile_perfect right_b"
      using node_facts(2) right_shape by simp
    have level_left:
      "double_reverse_spacetime_tile_height left_a =
        double_reverse_spacetime_tile_height left_b"
      using node_facts(1) by simp
    have level_right:
      "double_reverse_spacetime_tile_height right_a =
        double_reverse_spacetime_tile_height right_b"
      using node_facts(2) right_shape by simp
    have level_a:
      "double_reverse_spacetime_tile_height left_a =
        double_reverse_spacetime_tile_height right_a"
      using node_facts(3) right_shape by simp
    have level_b:
      "double_reverse_spacetime_tile_height left_b =
        double_reverse_spacetime_tile_height right_b"
      using level_left level_right level_a by simp
    have left_length:
      "length (double_reverse_spacetime_tile_word left_a) =
        length (double_reverse_spacetime_tile_word right_a)"
      using double_reverse_spacetime_tile_word_length
        [OF perfect_left_a] double_reverse_spacetime_tile_word_length
        [OF perfect_right_a] level_a by simp
    have joined_content:
      "double_reverse_spacetime_tile_word left_a @
          double_reverse_spacetime_tile_word left_b =
        double_reverse_spacetime_tile_word right_a @
          double_reverse_spacetime_tile_word right_b"
      using node_facts(4) right_shape by simp
    have left_prefix:
      "take (length (double_reverse_spacetime_tile_word left_a))
          (double_reverse_spacetime_tile_word left_a @
            double_reverse_spacetime_tile_word left_b) =
        take (length (double_reverse_spacetime_tile_word left_a))
          (double_reverse_spacetime_tile_word right_a @
            double_reverse_spacetime_tile_word right_b)"
      using joined_content by simp
    have content_a:
      "double_reverse_spacetime_tile_word left_a =
        double_reverse_spacetime_tile_word right_a"
      using left_prefix left_length by simp
    have right_suffix:
      "drop (length (double_reverse_spacetime_tile_word left_a))
          (double_reverse_spacetime_tile_word left_a @
            double_reverse_spacetime_tile_word left_b) =
        drop (length (double_reverse_spacetime_tile_word left_a))
          (double_reverse_spacetime_tile_word right_a @
            double_reverse_spacetime_tile_word right_b)"
      using joined_content by simp
    have content_b:
      "double_reverse_spacetime_tile_word left_b =
        double_reverse_spacetime_tile_word right_b"
      using right_suffix left_length by simp
    have left_eq: "left_a = right_a"
      by (rule left_ih[OF perfect_left_a perfect_right_a level_a content_a])
    have right_eq: "left_b = right_b"
      by (rule right_ih[OF perfect_left_b perfect_right_b level_b content_b])
    show ?thesis using right_shape left_eq right_eq by simp
  qed
qed

lemma double_reverse_spacetime_exact_halo_length:
  assumes "length source = 4*steps"
  shows "length (double_reverse_spacetime_power steps source) = 2*steps"
  using assms by (simp add: double_reverse_spacetime_power_length)

lemma double_reverse_spacetime_output_uses_complete_halo:
  assumes length: "length source = 4*steps"
      and index: "i < 2*steps"
  shows "double_reverse_spacetime_power steps source ! i =
    double_reverse_spacetime_run steps (\<lambda>j. source ! j) i"
  by (rule double_reverse_spacetime_power_cell)
    (use length index in arith)

ML \<open>
  val checked = @{thms double_reverse_spacetime_run_shift
    double_reverse_spacetime_run_add
    double_reverse_spacetime_run_congruent
    double_reverse_spacetime_power_length
    double_reverse_spacetime_power_one
    double_reverse_spacetime_power_content_congruent
    double_reverse_spacetime_power_add
    double_reverse_spacetime_power_cell
    double_reverse_spacetime_window_power
    double_reverse_spacetime_temporal_square
    double_reverse_spacetime_dyadic_cone_exact
    double_reverse_spacetime_dyadic_cone_length
    double_reverse_spacetime_tile_word_length
    double_reverse_spacetime_tile_content_injective
    double_reverse_spacetime_exact_halo_length
    double_reverse_spacetime_output_uses_complete_halo};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Temporal carry square depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped temporal carry square proof" else ();
\<close>

end
