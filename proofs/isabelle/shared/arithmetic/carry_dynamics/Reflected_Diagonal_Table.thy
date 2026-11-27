theory Reflected_Diagonal_Table
  imports Reflected_H_Cells "HOL.Bit_Operations"
begin

text \<open>The reflected diagonal tables encode west and south boundaries in
mixed-radix order. Traversing a rectangle transports each complete ordered
boundary to the next rectangle at its receiving phase.\<close>

definition diagonal_table_ports :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "diagonal_table_ports m p digit =
    (let b = 10 div m
     in if even p then (digit div b, digit mod b) else (digit mod b, digit div b))"

definition diagonal_table_cell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "diagonal_table_cell m p west south =
    diagonal_table_ports m p (if even p then m * west + south else m * south + west)"

lemma diagonal_table_cell_transpose:
  "diagonal_table_cell m (Suc p) west south =
    prod.swap (diagonal_table_cell m p south west)"
  by (cases "even p") (simp_all add: diagonal_table_cell_def diagonal_table_ports_def Let_def)

lemma diagonal_table_cell_source_step:
  "diagonal_table_cell m (Suc p)
      (fst (diagonal_table_ports m p (reflected_previous row i)))
      (snd (diagonal_table_ports m p (row i))) =
    diagonal_table_ports m (Suc p)
      (if even p then reflected_M_digit m row i else reflected_E_digit m row i)"
  by (cases "even p")
     (simp_all add: diagonal_table_cell_def diagonal_table_ports_def
       reflected_M_digit_def reflected_E_digit_def Let_def add.commute)

lemma diagonal_table_cell_two_complement:
  assumes "west < 5" "south < 2"
  defines "out \<equiv> diagonal_table_cell 2 0 west south"
  shows "diagonal_table_cell 2 0 (4 - west) (1 - south) =
    (1 - fst out, 4 - snd out)"
proof -
  have w: "west = 0 \<or> west = 1 \<or> west = 2 \<or> west = 3 \<or> west = 4"
    using assms(1) by arith
  have s: "south = 0 \<or> south = 1" using assms(2) by arith
  show ?thesis using w s
    unfolding out_def diagonal_table_cell_def diagonal_table_ports_def
    by (elim disjE; simp)
qed

lemma diagonal_table_cell_five_inverse:
  assumes "west < 5" "south < 2"
  defines "out \<equiv> diagonal_table_cell 2 0 west south"
  shows "diagonal_table_cell 5 0 (fst out) (snd out) = (west, south)"
proof -
  have w: "west = 0 \<or> west = 1 \<or> west = 2 \<or> west = 3 \<or> west = 4"
    using assms(1) by arith
  have s: "south = 0 \<or> south = 1" using assms(2) by arith
  show ?thesis using w s
    unfolding out_def diagonal_table_cell_def diagonal_table_ports_def
    by (elim disjE; simp)
qed

lemma diagonal_table_cell_five_inverse_odd:
  assumes "west < 2" "south < 5"
  defines "out \<equiv> diagonal_table_cell 2 1 west south"
  shows "diagonal_table_cell 5 1 (fst out) (snd out) = (west, south)"
proof -
  have inverse: "diagonal_table_cell 5 0
      (fst (diagonal_table_cell 2 0 south west))
      (snd (diagonal_table_cell 2 0 south west)) = (south, west)"
    by (rule diagonal_table_cell_five_inverse[OF assms(2,1)])
  show ?thesis unfolding out_def One_nat_def
    by (simp only: diagonal_table_cell_transpose fst_swap snd_swap inverse swap_simp)
qed

lemma diagonal_table_trailing_zero:
  fixes m reversed :: nat
  assumes law: "m = 2 \<or> m = 5" and last: "\<not> 10 dvd reversed"
  defines "physical \<equiv> m * reversed"
  defines "core \<equiv> if 10 dvd physical then physical div 10 else physical"
  shows "physical = (if m dvd core then core else 10 * core)"
    and "\<not> 10 dvd core"
proof -
  obtain b where b: "m * b = 10" "0 < m"
  proof (cases "m = 2")
    case True
    show thesis using True by (intro that[of 5]) simp_all
  next
    case False
    with law have "m = 5" by simp
    then show thesis by (intro that[of 2]) simp_all
  qed
  have restored: "physical = (if m dvd core then core else 10 * core) \<and> \<not> 10 dvd core"
  proof (cases "10 dvd physical")
    case False
    then have eq: "core = physical" unfolding core_def by simp
    have "m dvd physical" unfolding physical_def by simp
    with False eq show ?thesis by simp
  next
    case True
    obtain q where pq: "physical = 10 * q" using True unfolding dvd_def by blast
    have rq: "reversed = b * q"
      using pq b(2) unfolding physical_def b(1)[symmetric] by (simp add: mult.assoc)
    have cq: "core = q" unfolding core_def using True pq by simp
    have nd: "\<not> m dvd q"
    proof
      assume "m dvd q"
      then obtain k where "q = m * k" unfolding dvd_def by blast
      then have "reversed = 10 * k"
        using b(1) by (simp add: rq mult_ac)
      with last show False by simp
    qed
    have equality: "physical = (if m dvd core then core else 10 * core)"
      by (simp add: pq cq nd)
    have "m dvd 10" unfolding b(1)[symmetric] by simp
    with nd have "\<not> 10 dvd core" unfolding cq by (meson dvd_trans)
    with equality show ?thesis by simp
  qed
  from restored show "physical = (if m dvd core then core else 10 * core)"
    and "\<not> 10 dvd core" by blast+
qed

fun diagonal_boundary_rank :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "diagonal_boundary_rank [] = 0"
| "diagonal_boundary_rank ((radix, digit) # ports) =
    digit + radix * diagonal_boundary_rank ports"

abbreviation diagonal_boundary_size :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "diagonal_boundary_size ports \<equiv> prod_list (map fst ports)"

lemma diagonal_boundary_rank_append:
  "diagonal_boundary_rank (left @ right) =
    diagonal_boundary_rank left + diagonal_boundary_size left * diagonal_boundary_rank right"
proof (induction left)
  case Nil
  then show ?case by simp
next
  case (Cons port rest)
  then show ?case by (cases port) (simp add: algebra_simps)
qed

lemma diagonal_boundary_rank_below_size:
  assumes "list_all (\<lambda>(radix, digit). digit < radix) ports"
  shows "diagonal_boundary_rank ports < diagonal_boundary_size ports"
  using assms
proof (induction ports)
  case Nil
  then show ?case by simp
next
  case (Cons port rest)
  obtain radix digit where this_port: "port = (radix, digit)" by (cases port) auto
  have digit: "digit < radix" using Cons.prems by (simp add: this_port)
  have rest: "diagonal_boundary_rank rest < diagonal_boundary_size rest"
    using Cons.IH Cons.prems by (simp add: this_port)
  have "digit + radix * diagonal_boundary_rank rest <
      radix * Suc (diagonal_boundary_rank rest)"
    using digit by simp
  also have "radix * Suc (diagonal_boundary_rank rest) \<le> radix * diagonal_boundary_size rest"
    by (rule mult_le_mono2) (use rest in simp)
  finally show ?case by (simp add: this_port)
qed

lemma diagonal_boundary_rank_split:
  assumes "list_all (\<lambda>(radix, digit). digit < radix) left"
  shows "diagonal_boundary_rank (left @ right) mod diagonal_boundary_size left =
      diagonal_boundary_rank left"
    and "diagonal_boundary_rank (left @ right) div diagonal_boundary_size left =
      diagonal_boundary_rank right"
proof -
  have less: "diagonal_boundary_rank left < diagonal_boundary_size left"
    by (rule diagonal_boundary_rank_below_size[OF assms])
  then have nonzero: "diagonal_boundary_size left \<noteq> 0" by arith
  show "diagonal_boundary_rank (left @ right) mod diagonal_boundary_size left =
      diagonal_boundary_rank left"
    and "diagonal_boundary_rank (left @ right) div diagonal_boundary_size left =
      diagonal_boundary_rank right"
    using less nonzero by (simp_all add: diagonal_boundary_rank_append)
qed

lemma diagonal_boundary_rank_complement:
  assumes "list_all (\<lambda>(radix, digit). digit < radix) ports"
  shows "diagonal_boundary_rank
      (map (\<lambda>(radix, digit). (radix, radix - Suc digit)) ports) =
    diagonal_boundary_size ports - Suc (diagonal_boundary_rank ports)"
proof -
  have exact: "Suc (diagonal_boundary_rank ports) + diagonal_boundary_rank
      (map (\<lambda>(radix, digit). (radix, radix - Suc digit)) ports) =
    diagonal_boundary_size ports"
    using assms
  proof (induction ports)
    case Nil
    then show ?case by simp
  next
    case (Cons port rest)
    obtain radix digit where this_port: "port = (radix, digit)" by (cases port) auto
    have digit: "digit < radix" using Cons.prems by (simp add: this_port)
    let ?complement = "diagonal_boundary_rank
      (map (\<lambda>(radix, digit). (radix, radix - Suc digit)) rest)"
    let ?rank = "diagonal_boundary_rank rest"
    have rest: "Suc ?rank + ?complement = diagonal_boundary_size rest"
      using Cons.IH Cons.prems by (simp add: this_port)
    have sum: "Suc digit + (radix - Suc digit) = radix" using digit by simp
    have "Suc (diagonal_boundary_rank (port # rest)) + diagonal_boundary_rank
        (map (\<lambda>(radix, digit). (radix, radix - Suc digit)) (port # rest)) =
        Suc (digit + radix * ?rank) + (radix - Suc digit + radix * ?complement)"
      by (simp add: this_port)
    also have "\<dots> = (Suc digit + (radix - Suc digit)) + radix * (?rank + ?complement)"
      by (simp only: distrib_left; arith)
    also have "\<dots> = radix + radix * (?rank + ?complement)" using sum by simp
    also have "\<dots> = radix * diagonal_boundary_size rest"
      using arg_cong[where f="(*) radix", OF rest] by simp
    also have "\<dots> = diagonal_boundary_size (port # rest)" by (simp add: this_port)
    finally show ?case .
  qed
  then show ?thesis by simp
qed

fun diagonal_table_row ::
  "(nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow>
    nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<times> 'a list" where
  "diagonal_table_row gate p w [] = (w, [])"
| "diagonal_table_row gate p w (s # south) =
    (let (e, n) = gate p w s;
         (last_e, north) = diagonal_table_row gate (Suc p) e south
     in (last_e, n # north))"

fun diagonal_table_rect ::
  "(nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow>
    nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "diagonal_table_rect gate p [] south = ([], south)"
| "diagonal_table_rect gate p (w # west) south =
    (let (e, n) = diagonal_table_row gate p w south;
         (east, north) = diagonal_table_rect gate (Suc p) west n
     in (e # east, north))"

lemma diagonal_table_row_zero:
  "diagonal_table_row (diagonal_table_cell m) p 0 (replicate width 0) =
    (0, replicate width 0)"
  by (induction width arbitrary: p)
    (simp_all add: diagonal_table_cell_def diagonal_table_ports_def Let_def)

lemma diagonal_table_rect_zero:
  "diagonal_table_rect (diagonal_table_cell m) p
      (replicate height 0) (replicate width 0) =
    (replicate height 0, replicate width 0)"
  by (induction height arbitrary: p) (simp_all add: diagonal_table_row_zero)

lemma diagonal_table_row_split:
  "diagonal_table_row gate p w (south @ next) =
    (let (e, n) = diagonal_table_row gate p w south;
         (ee, nn) = diagonal_table_row gate (p + length south) e next
     in (ee, n @ nn))"
  by (induction south arbitrary: p w) (auto simp: Let_def split: prod.splits)

lemma diagonal_table_north_width[simp]:
  "length (snd (diagonal_table_row gate p w south)) = length south"
  by (induction south arbitrary: p w; auto simp: Let_def split: prod.splits; metis snd_conv)

lemma diagonal_table_rect_horizontal:
  "diagonal_table_rect gate p west (south @ right) =
    (let (e, n) = diagonal_table_rect gate p west south;
         (ee, nn) = diagonal_table_rect gate (p + length south) e right
     in (ee, n @ nn))"
proof (induction west arbitrary: p south right)
  case Nil
  then show ?case by simp
next
  case (Cons w rest)
  obtain e n where first: "diagonal_table_row gate p w south = (e, n)"
    by (cases "diagonal_table_row gate p w south") auto
  obtain ee nn where second:
    "diagonal_table_row gate (p + length south) e right = (ee, nn)"
    by (cases "diagonal_table_row gate (p + length south) e right") auto
  have length_n: "length n = length south"
    using diagonal_table_north_width[of gate p w south] by (simp add: first)
  have whole: "diagonal_table_row gate p w (south @ right) = (ee, n @ nn)"
    using diagonal_table_row_split[of gate p w south right] by (simp add: first second)
  show ?case
    using Cons.IH[of "Suc p" n nn]
    by (simp add: whole first second length_n split_beta Let_def)
qed

lemma diagonal_table_rect_vertical:
  "diagonal_table_rect gate p (west @ next) south =
    (let (e, n) = diagonal_table_rect gate p west south;
         (ee, nn) = diagonal_table_rect gate (p + length west) next n
     in (e @ ee, nn))"
  by (induction west arbitrary: p south) (auto simp: Let_def split: prod.splits)

theorem diagonal_table_rect_quarters:
  "diagonal_table_rect gate p (west @ upper) (south @ right) =
    (let (e_sw, n_sw) = diagonal_table_rect gate p west south;
         (e_se, n_se) = diagonal_table_rect gate (p + length south) e_sw right;
         (e_nw, n_nw) = diagonal_table_rect gate (p + length west) upper n_sw;
         (e_ne, n_ne) =
           diagonal_table_rect gate (p + length west + length south) e_nw n_se
     in (e_se @ e_ne, n_nw @ n_ne))"
proof -
  have length_n:
    "length (snd (diagonal_table_rect gate p west south)) = length south"
    by (induction west arbitrary: p south; auto simp: Let_def split: prod.splits;
      metis diagonal_table_north_width snd_conv)
  obtain e_sw n_sw where sw: "diagonal_table_rect gate p west south = (e_sw, n_sw)"
    by (cases "diagonal_table_rect gate p west south") auto
  obtain e_se n_se where se:
    "diagonal_table_rect gate (p + length south) e_sw right = (e_se, n_se)"
    by (cases "diagonal_table_rect gate (p + length south) e_sw right") auto
  obtain e_nw n_nw where nw:
    "diagonal_table_rect gate (p + length west) upper n_sw = (e_nw, n_nw)"
    by (cases "diagonal_table_rect gate (p + length west) upper n_sw") auto
  have n_sw_width: "length n_sw = length south" using length_n by (simp add: sw)
  have bottom: "diagonal_table_rect gate p west (south @ right) =
      (e_se, n_sw @ n_se)"
    using diagonal_table_rect_horizontal[of gate p west south right]
    by (simp add: sw se)
  have top: "diagonal_table_rect gate (p + length west) upper (n_sw @ n_se) =
      (let (e_ne, n_ne) =
           diagonal_table_rect gate (p + length west + length south) e_nw n_se
       in (e_ne, n_nw @ n_ne))"
    using diagonal_table_rect_horizontal[of gate "p + length west" upper n_sw n_se]
    by (simp add: nw n_sw_width)
  show ?thesis
    using diagonal_table_rect_vertical[of gate p west upper "south @ right"]
    by (simp add: bottom top sw se nw split_beta Let_def)
qed

lemma diagonal_table_empty_south [simp]:
  "diagonal_table_rect gate p west [] = (west, [])"
  by (induction west arbitrary: p) simp_all

lemma diagonal_table_single_column:
  "diagonal_table_rect (diagonal_table_cell m) p south [w] =
    (let (e, n) = diagonal_table_row (diagonal_table_cell m) (Suc p) w south
     in (n, [e]))"
proof (induction south arbitrary: w p)
  case Nil
  then show ?case by simp
next
  case (Cons s south)
  obtain e n where cell: "diagonal_table_cell m (Suc p) w s = (e, n)"
    by (cases "diagonal_table_cell m (Suc p) w s") simp
  have other: "diagonal_table_cell m p s w = (n, e)"
    using cell diagonal_table_cell_transpose[of m p w s]
    by (cases "diagonal_table_cell m p s w") auto
  obtain ee nn where row:
    "diagonal_table_row (diagonal_table_cell m) (Suc (Suc p)) e south = (ee, nn)"
    by (cases "diagonal_table_row (diagonal_table_cell m) (Suc (Suc p)) e south") simp
  show ?case using Cons.IH[where w=e and p="Suc p"]
    by (simp add: cell other row Let_def)
qed

theorem diagonal_table_receiving_rectangle_transpose:
  "diagonal_table_rect (diagonal_table_cell m) (Suc p) west south =
    prod.swap (diagonal_table_rect (diagonal_table_cell m) p south west)"
proof (induction west arbitrary: p south)
  case Nil
  then show ?case by simp
next
  case (Cons w rest)
  obtain e n where row:
    "diagonal_table_row (diagonal_table_cell m) (Suc p) w south = (e, n)"
    by (cases "diagonal_table_row (diagonal_table_cell m) (Suc p) w south") simp
  have column: "diagonal_table_rect (diagonal_table_cell m) p south [w] = (n,[e])"
    using diagonal_table_single_column[of m p south w] by (simp add: row)
  have split: "diagonal_table_rect (diagonal_table_cell m) p south (w # rest) =
       (let (east,north) = diagonal_table_rect (diagonal_table_cell m) (Suc p) n rest
        in (east, e # north))"
    using diagonal_table_rect_horizontal[of "diagonal_table_cell m" p south "[w]" rest]
    by (simp add: column)
  show ?case using Cons.IH[where p="Suc p" and south=n]
    by (simp add: row split Let_def split: prod.splits)
qed

text \<open>The native table compiler joins southwest, southeast, northwest and
northeast rectangles and packs the ordered east and north output boundaries.
The radix vectors are exact caller-supplied boundary geometry.\<close>

definition diagonal_rank_digits :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "diagonal_rank_digits radices digits = diagonal_boundary_rank (zip radices digits)"

lemma diagonal_rank_digits_join:
  assumes "length r1 = length d1"
  shows "diagonal_rank_digits (r1 @ r2) (d1 @ d2) =
    diagonal_rank_digits r1 d1 + diagonal_boundary_size (zip r1 d1) *
      diagonal_rank_digits r2 d2"
  using assms
  by (simp add: diagonal_rank_digits_def zip_append diagonal_boundary_rank_append)

theorem diagonal_table_ranked_quarters:
  assumes sw: "diagonal_table_rect gate p west south = (e_sw, n_sw)"
    and se: "diagonal_table_rect gate (p + length south) e_sw right = (e_se, n_se)"
    and nw: "diagonal_table_rect gate (p + length west) upper n_sw = (e_nw, n_nw)"
    and ne: "diagonal_table_rect gate (p + length west + length south) e_nw n_se = (e_ne, n_ne)"
    and east_width: "length er1 = length e_se"
    and north_width: "length nr1 = length n_nw"
  shows "(diagonal_rank_digits (er1 @ er2)
      (fst (diagonal_table_rect gate p (west @ upper) (south @ right))),
    diagonal_rank_digits (nr1 @ nr2)
      (snd (diagonal_table_rect gate p (west @ upper) (south @ right)))) =
    (diagonal_rank_digits er1 e_se + diagonal_boundary_size (zip er1 e_se) *
        diagonal_rank_digits er2 e_ne,
     diagonal_rank_digits nr1 n_nw + diagonal_boundary_size (zip nr1 n_nw) *
        diagonal_rank_digits nr2 n_ne)"
  using diagonal_table_rect_quarters[of gate p west upper south right]
    diagonal_rank_digits_join[OF east_width, of er2 e_ne]
    diagonal_rank_digits_join[OF north_width, of nr2 n_ne]
  by (simp add: sw se nw ne Let_def)

text \<open>The packed table payload uses two disjoint 16-bit coordinates.
This arithmetic extraction requires the east rank to fit its lane.\<close>

lemma diagonal_word_payload_extract:
  fixes east north :: nat
  assumes "east < 2 ^ 16"
  shows "(east + 2 ^ 16 * north) mod (2 ^ 16) = east"
    and "(east + 2 ^ 16 * north) div (2 ^ 16) = north"
  using assms by simp_all

text \<open>Each packed table lookup in the four-lane wave carries two
unsigned 16-bit responses. Subtracting from the packed maxima complements
the coordinates independently, including zero and the maximum rank.\<close>

theorem diagonal_packed_complement_response:
  fixes east north east_max north_max packed_max packed_entry :: nat
  assumes east: "east \<le> east_max" "east_max < 2 ^ 16"
    and north: "north \<le> north_max" "north_max < 2 ^ 16"
  defines "packed_max \<equiv> east_max + 2 ^ 16 * north_max"
    and "packed_entry \<equiv> east + 2 ^ 16 * north"
  shows "packed_entry \<le> packed_max" "packed_max < 2 ^ 32"
    "(packed_max - packed_entry) mod (2 ^ 16) = east_max - east"
    "(packed_max - packed_entry) div (2 ^ 16) = north_max - north"
proof -
  have radix: "(2::nat)^16 = 65536" "(2::nat)^32 = 4294967296" by simp_all
  show "packed_entry \<le> packed_max"
    unfolding packed_entry_def packed_max_def
    by (intro add_mono mult_left_mono east north; simp)
  have e_bound: "east_max \<le> 65535" using east(2) by (simp only: radix; arith)
  have n_bound: "north_max \<le> 65535" using north(2) by (simp only: radix; arith)
  show "packed_max < 2 ^ 32"
    using e_bound n_bound unfolding packed_max_def by (simp only: radix; linarith)
  have diff: "packed_max - packed_entry = (east_max - east) + 2 ^ 16 * (north_max - north)"
  proof -
    have "packed_entry + ((east_max - east) + 2 ^ 16 * (north_max - north)) =
        (east + (east_max - east)) + 2 ^ 16 * (north + (north_max - north))"
      unfolding packed_entry_def by (simp add: algebra_simps)
    also have "\<dots> = packed_max" using east(1) north(1) by (simp add: packed_max_def)
    finally have "packed_entry + ((east_max - east) + 2 ^ 16 * (north_max - north)) =
        packed_max" .
    then show ?thesis by arith
  qed
  have low: "east_max - east < 2 ^ 16" using east by arith
  show "(packed_max - packed_entry) mod (2 ^ 16) = east_max - east"
    unfolding diff by (rule diagonal_word_payload_extract(1)[OF low])
  show "(packed_max - packed_entry) div (2 ^ 16) = north_max - north"
    unfolding diff by (rule diagonal_word_payload_extract(2)[OF low])
qed

lemma diagonal_word_payload_overflow_negative:
  "(2 ^ 16 + 2 ^ 16 * north) mod (2 ^ 16::nat) \<noteq> 2 ^ 16"
  by simp

lemma diagonal_rank_order_negative:
  "diagonal_rank_digits [5,5] [1,2] \<noteq> diagonal_rank_digits [5,5] [2,1]"
  by (simp add: diagonal_rank_digits_def)

lemma diagonal_rank_width_negative:
  "diagonal_rank_digits [5] [1,2] \<noteq> diagonal_rank_digits [5,5] [1,2]"
  by (simp add: diagonal_rank_digits_def)

lemma diagonal_fringe_order_two_negative:
  "diagonal_table_rect (diagonal_table_cell 2) 0 [1,0] [0,1,0] \<noteq>
    diagonal_table_rect (diagonal_table_cell 2) 0 [0,1] [0,1,0]"
  by (simp add: diagonal_table_cell_def diagonal_table_ports_def Let_def)

lemma diagonal_fringe_order_five_negative:
  "diagonal_table_rect (diagonal_table_cell 5) 0 [1,0] [0,1,0] \<noteq>
    diagonal_table_rect (diagonal_table_cell 5) 0 [0,1] [0,1,0]"
  by (simp add: diagonal_table_cell_def diagonal_table_ports_def Let_def)

unbundle bit_operations_syntax

lemma diagonal_word_bitwise_or_exact:
  fixes east north :: nat
  assumes "east < 2 ^ 16"
  shows "east OR push_bit 16 north = east + 2 ^ 16 * north"
proof -
  have low: "take_bit 16 east = east" by (rule take_bit_nat_eq_self[OF assms])
  have disjoint: "take_bit 16 east AND push_bit 16 north = 0"
    by (rule bit_eqI) (auto simp: bit_simps)
  have "take_bit 16 east + push_bit 16 north =
      take_bit 16 east OR push_bit 16 north"
    by (rule disjunctive_add_eq_or[OF disjoint])
  then show ?thesis using low by (simp add: push_bit_eq_mult)
qed

lemma diagonal_eval_reflected_half_ix:
  fixes lim ix :: nat
  assumes "0 < lim" "even lim" "ix < lim" "lim div 2 \<le> ix"
  shows "lim - Suc ix < lim div 2"
  using assms by presburger

definition diagonal_eval_component :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "diagonal_eval_component lim cap f ix =
    (if ix < lim div 2 then f ix else cap - Suc (f (lim - Suc ix)))"

theorem diagonal_eval_complement_lookup:
  fixes lim cap ix :: nat
  assumes lim: "0 < lim" "even lim" and ix: "ix < lim"
    and bound: "f ix < cap"
    and complement: "f (lim - Suc ix) = cap - Suc (f ix)"
  shows "diagonal_eval_component lim cap f ix = f ix"
    and "ix \<ge> lim div 2 \<Longrightarrow> lim - Suc ix < lim div 2"
proof -
  show "diagonal_eval_component lim cap f ix = f ix"
    using bound complement by (auto simp: diagonal_eval_component_def; arith)
  show "ix \<ge> lim div 2 \<Longrightarrow> lim - Suc ix < lim div 2"
    using diagonal_eval_reflected_half_ix[OF lim ix] by simp
qed

lemma diagonal_eval_transposed_phase:
  "diagonal_table_rect (diagonal_table_cell m) 1 west south =
    prod.swap (diagonal_table_rect (diagonal_table_cell m) 0 south west)"
  using diagonal_table_receiving_rectangle_transpose[of m 0 west south] by simp

lemma diagonal_eval_half_open_negative:
  "(10::nat) - Suc 10 < 10 div 2 \<and> \<not> (10::nat) < 10"
  by simp

ML \<open>
  val checked = @{thms diagonal_table_cell_transpose diagonal_table_cell_source_step
    diagonal_table_cell_two_complement diagonal_table_cell_five_inverse
    diagonal_table_cell_five_inverse_odd
    diagonal_table_trailing_zero diagonal_boundary_rank_append
    diagonal_boundary_rank_below_size diagonal_boundary_rank_split diagonal_boundary_rank_complement
    diagonal_table_rect_zero diagonal_table_rect_quarters diagonal_table_receiving_rectangle_transpose
    diagonal_rank_digits_join diagonal_table_ranked_quarters
    diagonal_word_payload_extract diagonal_packed_complement_response
    diagonal_word_payload_overflow_negative
    diagonal_rank_order_negative diagonal_rank_width_negative
    diagonal_fringe_order_two_negative diagonal_fringe_order_five_negative
    diagonal_word_bitwise_or_exact
    diagonal_eval_reflected_half_ix diagonal_eval_complement_lookup
    diagonal_eval_transposed_phase diagonal_eval_half_open_negative};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected diagonal table proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected diagonal table proof" else ();
\<close>

end
