theory Reverse_Center11_Controlled_Action
  imports Main
begin

text \<open>The affine center/half action and its accumulator are defined for
explicitly supplied physical ports.  Chronological composition is an algebraic
fact about those ports; source extraction and future-port authority are proved
separately by the source refinement theory.\<close>

record reverse_center11_port =
  reverse_center11_odd_width :: bool
  reverse_center11_growth :: bool
  reverse_center11_coefficient :: nat
  reverse_center11_carry_in :: nat
  reverse_center11_carry_out :: nat

definition reverse_center11_port_admitted :: "reverse_center11_port \<Rightarrow> bool" where
  "reverse_center11_port_admitted port \<longleftrightarrow>
    reverse_center11_coefficient port \<le> 18 \<and>
    reverse_center11_carry_in port \<le> 1 \<and>
    reverse_center11_carry_out port \<le> 1 \<and>
    reverse_center11_carry_out port =
      (reverse_center11_coefficient port + reverse_center11_carry_in port) div 10"

definition reverse_center11_tick ::
    "reverse_center11_port \<Rightarrow> int \<times> int \<times> int \<Rightarrow>
      int \<times> int \<times> int" where
  "reverse_center11_tick port state =
    (let a = fst state;
         b = fst (snd state);
         e = snd (snd state);
         q = int (reverse_center11_coefficient port);
         ci = int (reverse_center11_carry_in port);
         co = int (reverse_center11_carry_out port);
         odd_width = reverse_center11_odd_width port;
         growth = reverse_center11_growth port;
         first = (if growth \<and> odd_width then q-a-b+co else a+b+ci) mod 11;
         second = (if growth \<and> \<not> odd_width then q-a-b+co
                   else if odd_width then a+b+co else a+b+ci) mod 11
     in (first, second, (e + first - second) mod 11))"

fun reverse_center11_run ::
    "reverse_center11_port list \<Rightarrow> int \<times> int \<times> int \<Rightarrow>
      int \<times> int \<times> int" where
  "reverse_center11_run [] state = state"
| "reverse_center11_run (port # ports) state =
    reverse_center11_run ports (reverse_center11_tick port state)"

lemma reverse_center11_run_append:
  "reverse_center11_run (first @ later) state =
    reverse_center11_run later (reverse_center11_run first state)"
  by (induction first arbitrary: state) simp_all

definition reverse_center11_mod11 :: "int \<Rightarrow> int" where
  "reverse_center11_mod11 value = value mod 11"

lemma reverse_center11_mod11_nonnegative [simp]:
  "0 \<le> (value::int) mod 11"
  by (rule pos_mod_sign) simp

lemma reverse_center11_mod11_bounded [simp]:
  "(value::int) mod 11 < 11"
  by (rule pos_mod_bound) simp

definition reverse_center11_first_offset :: "reverse_center11_port \<Rightarrow> int" where
  "reverse_center11_first_offset port =
    (if reverse_center11_growth port \<and> reverse_center11_odd_width port
     then int (reverse_center11_coefficient port +
       reverse_center11_carry_out port)
     else int (reverse_center11_carry_in port))"

definition reverse_center11_second_offset :: "reverse_center11_port \<Rightarrow> int" where
  "reverse_center11_second_offset port =
    (if reverse_center11_growth port \<and> \<not> reverse_center11_odd_width port
     then int (reverse_center11_coefficient port +
       reverse_center11_carry_out port)
     else if reverse_center11_odd_width port
       then int (reverse_center11_carry_out port)
       else int (reverse_center11_carry_in port))"

lemma reverse_center11_mod_accumulator_shift:
  fixes e shift first second :: int
  shows "(((e + shift) mod 11 + first - second) mod 11) =
    (((e + first - second) mod 11 + shift) mod 11)"
proof -
  have left_sum:
    "((e + shift) mod 11 + first) mod 11 =
      (e + shift + first) mod 11"
    by (simp only: mod_add_left_eq)
  have left_diff:
    "(((e + shift) mod 11 + first) - second) mod 11 =
      ((e + shift + first) - second) mod 11"
    by (rule mod_diff_cong[OF left_sum refl])
  have right:
    "((e + first - second) mod 11 + shift) mod 11 =
      (e + first - second + shift) mod 11"
    by (simp only: mod_add_left_eq)
  show ?thesis using left_diff right by (simp add: algebra_simps)
qed

lemma reverse_center11_tick_accumulator_shift:
  "reverse_center11_tick port (a,b,(e + shift) mod 11) =
    (fst (reverse_center11_tick port (a,b,e)),
     fst (snd (reverse_center11_tick port (a,b,e))),
     (snd (snd (reverse_center11_tick port (a,b,e))) + shift) mod 11)"
  by (cases port)
    (auto simp only: reverse_center11_tick_def Let_def fst_conv snd_conv
      reverse_center11_mod_accumulator_shift)

lemma reverse_center11_tick_accumulator_projection:
  "snd (snd (reverse_center11_tick port (a,b,e))) =
    (e + fst (reverse_center11_tick port (a,b,e)) -
      fst (snd (reverse_center11_tick port (a,b,e)))) mod 11"
  by (simp add: reverse_center11_tick_def Let_def fst_conv snd_conv)

lemma reverse_center11_tick_first_projection:
  "fst (reverse_center11_tick port (a,b,e)) =
    (if reverse_center11_growth port \<and> reverse_center11_odd_width port
     then int (reverse_center11_coefficient port) - a - b +
       int (reverse_center11_carry_out port)
     else a + b + int (reverse_center11_carry_in port)) mod 11"
  by (simp add: reverse_center11_tick_def Let_def fst_conv snd_conv)

lemma reverse_center11_tick_second_projection:
  "fst (snd (reverse_center11_tick port (a,b,e))) =
    (if reverse_center11_growth port \<and> \<not> reverse_center11_odd_width port
     then int (reverse_center11_coefficient port) - a - b +
       int (reverse_center11_carry_out port)
     else if reverse_center11_odd_width port
       then a + b + int (reverse_center11_carry_out port)
       else a + b + int (reverse_center11_carry_in port)) mod 11"
  by (simp add: reverse_center11_tick_def Let_def fst_conv snd_conv)

lemma reverse_center11_two_branch_if:
  fixes result selected_value otherwise_value :: int
  assumes selected: "P \<and> Q \<Longrightarrow> result = selected_value mod 11"
      and otherwise: "\<not> (P \<and> Q) \<Longrightarrow> result = otherwise_value mod 11"
  shows "result = (if Q \<and> P then selected_value else otherwise_value) mod 11"
  using selected otherwise by (cases P; cases Q) simp_all

lemma reverse_center11_nat_parity_growth_if:
  fixes n :: nat and result odd_value growth_value stable_value :: int
  assumes odd_case: "odd n \<Longrightarrow> result = odd_value mod 11"
      and even_growth_case: "even n \<and> growth \<Longrightarrow> result = growth_value mod 11"
      and even_stable_case: "even n \<and> \<not> growth \<Longrightarrow> result = stable_value mod 11"
  shows "result = (if growth \<and> \<not> odd n then growth_value
    else if odd n then odd_value else stable_value) mod 11"
  using odd_case even_growth_case even_stable_case
  by (cases "odd n"; cases growth; simp_all)

lemma reverse_center11_half_widths:
  "length source - length source div 2 =
      (length source + 1) div 2 \<and>
    length source - (length source + 1) div 2 =
      length source div 2"
proof -
  let ?n = "length source"
  have decomposition: "?n = 2 * (?n div 2) + ?n mod 2"
    using div_mult_mod_eq[of ?n 2] by arith
  have remainder: "?n mod 2 = 0 \<or> ?n mod 2 = 1" by arith
  show ?thesis using decomposition remainder by presburger
qed

lemma reverse_center11_reflected_pair_prefix_structure:
  fixes source paired :: "nat list"
  assumes pair:
    "paired = map (\<lambda>(a,b). a+b) (zip source (rev source))"
  shows "rev (take ((length source + 1) div 2) paired) =
      map (\<lambda>(a,b). a+b)
        (zip (drop (length source div 2) source)
          (rev (take ((length source + 1) div 2) source)))"
proof -
  let ?h = "length source div 2"
  let ?m = "(length source + 1) div 2"
  have h_m: "length source - ?h = ?m"
    using conjunct1[OF reverse_center11_half_widths[where source=source]] .
  have m_bound: "?m \<le> length source"
    using h_m by arith
  have paired_length: "length paired = length source"
    using pair by simp
  have drop_length: "length (drop ?h source) = ?m"
    using h_m by simp
  have prefix_length: "length (rev (take ?m source)) = ?m"
    using m_bound by simp
  have reflected_pairs:
    "rev (take ?m paired) =
      map (\<lambda>(a,b). a+b) (zip (drop ?h source) (rev (take ?m source)))"
  proof (rule nth_equalityI)
    show "length (rev (take ?m paired)) =
        length (map (\<lambda>(a,b). a+b)
          (zip (drop ?h source) (rev (take ?m source))))"
      using paired_length drop_length prefix_length by simp
    fix i
    assume index: "i < length (rev (take ?m paired))"
    have i_bound: "i < ?m"
      using index paired_length m_bound by simp
    have k_bound: "?m - Suc i < length source"
      using i_bound m_bound by arith
    have source_length: "length source = ?h + ?m"
      using h_m by arith
    have reversed_index:
      "length source - Suc (?m - Suc i) = ?h + i"
      using source_length i_bound by arith
    have paired_nth:
      "paired ! (?m - Suc i) =
        source ! (?m - Suc i) + (rev source) ! (?m - Suc i)"
      using pair k_bound by (simp add: nth_map)
    have reversed_source:
      "(rev source) ! (?m - Suc i) = source ! (?h + i)"
      using rev_nth[OF k_bound] reversed_index by simp
    have source_half_bound: "?h \<le> length source"
      using h_m by arith
    have drop_nth:
      "(drop ?h source) ! i = source ! (?h + i)"
      using source_half_bound by simp
    have reverse_prefix_nth:
      "(rev (take ?m source)) ! i = source ! (?m - Suc i)"
      using i_bound m_bound by (simp add: rev_nth)
    have map2_nth:
      "map (\<lambda>(a,b). a+b) (zip (drop ?h source) (rev (take ?m source))) ! i =
        source ! (?h + i) + source ! (?m - Suc i)"
      using drop_length prefix_length i_bound drop_nth reverse_prefix_nth
      by (simp add: nth_map nth_zip)
    have reversed_pair_nth:
      "(rev (take ?m paired)) ! i = paired ! (?m - Suc i)"
      using i_bound m_bound paired_length by (simp add: rev_nth)
    show "(rev (take ?m paired)) ! i =
        map (\<lambda>(a,b). a+b) (zip (drop ?h source) (rev (take ?m source))) ! i"
      using reversed_pair_nth paired_nth reversed_source map2_nth
      by (simp add: add.commute)
  qed
  show ?thesis using reflected_pairs by simp
qed

lemma reverse_center11_run_accumulator_shift:
  "reverse_center11_run ports (a,b,(e + shift) mod 11) =
    (fst (reverse_center11_run ports (a,b,e)),
     fst (snd (reverse_center11_run ports (a,b,e))),
     (snd (snd (reverse_center11_run ports (a,b,e))) + shift) mod 11)"
proof (induction ports arbitrary: a b e shift)
  case Nil
  then show ?case by simp
next
  case (Cons port ports)
  let ?base = "reverse_center11_tick port (a,b,e)"
  obtain x y total where base: "?base = (x,y,total)"
    by (cases ?base) auto
  have shifted:
    "reverse_center11_tick port (a,b,(e + shift) mod 11) =
      (x,y,(total + shift) mod 11)"
    using reverse_center11_tick_accumulator_shift[of port a b e shift] base
    by simp
  have later:
    "reverse_center11_run ports (x,y,(total + shift) mod 11) =
      (fst (reverse_center11_run ports (x,y,total)),
       fst (snd (reverse_center11_run ports (x,y,total))),
       (snd (snd (reverse_center11_run ports (x,y,total))) + shift) mod 11)"
    by (rule Cons.IH)
  show ?case using base shifted later by simp
qed

type_synonym reverse_center11_matrix = "int \<times> int \<times> int \<times> int"

definition reverse_center11_matrix_apply ::
    "reverse_center11_matrix \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "reverse_center11_matrix_apply matrix state =
    (case matrix of (a,b,c,d) \<Rightarrow>
      case state of (x,y) \<Rightarrow>
        ((a*x+b*y) mod 11, (c*x+d*y) mod 11))"

definition reverse_center11_matrix_mult ::
    "reverse_center11_matrix \<Rightarrow> reverse_center11_matrix \<Rightarrow>
      reverse_center11_matrix" where
  "reverse_center11_matrix_mult left right =
    (case left of (a,b,c,d) \<Rightarrow>
      case right of (e,f,g,h) \<Rightarrow>
        ((a*e+b*g) mod 11, (a*f+b*h) mod 11,
         (c*e+d*g) mod 11, (c*f+d*h) mod 11))"

definition reverse_center11_homogeneous ::
    "reverse_center11_port \<Rightarrow> reverse_center11_matrix" where
  "reverse_center11_homogeneous port =
    (if \<not> reverse_center11_growth port then (1,1,1,1)
     else if reverse_center11_odd_width port then (10,10,1,1)
     else (1,1,10,10))"

lemma reverse_center11_mod11_negated_pair:
  fixes a b q co :: int
  shows "(10*a + 10*b + (q + co)) mod 11 =
    (q - a - b + co) mod 11"
proof -
  have rearrange:
    "10*a + 10*b + (q + co) = (q - a - b + co) + (a + b)*11"
    by (simp add: algebra_simps)
  show ?thesis
    by (simp only: rearrange mod_mult_self1)
qed

lemma reverse_center11_half_affine_form:
  "fst (reverse_center11_tick port (a,b,e)) =
      (fst (reverse_center11_matrix_apply
      (reverse_center11_homogeneous port) (a,b)) +
      reverse_center11_first_offset port) mod 11 \<and>
    fst (snd (reverse_center11_tick port (a,b,e))) =
      (snd (reverse_center11_matrix_apply
      (reverse_center11_homogeneous port) (a,b)) +
      reverse_center11_second_offset port) mod 11"
proof (cases "reverse_center11_growth port")
  case False
  then show ?thesis
    by (simp add: reverse_center11_tick_def
        Let_def fst_conv snd_conv
        reverse_center11_first_offset_def reverse_center11_second_offset_def
        reverse_center11_homogeneous_def reverse_center11_matrix_apply_def
        mod_add_left_eq)
next
  case True
  then have growth_true: "reverse_center11_growth port" .
  show ?thesis
  proof (cases "reverse_center11_odd_width port")
    case True
    then show ?thesis
      using growth_true
      by (simp add: reverse_center11_tick_def
          Let_def fst_conv snd_conv
          reverse_center11_first_offset_def reverse_center11_second_offset_def
          reverse_center11_homogeneous_def reverse_center11_matrix_apply_def
          reverse_center11_mod11_negated_pair mod_add_left_eq)
  next
    case False
    then show ?thesis
      using growth_true
      by (simp add: reverse_center11_tick_def
          Let_def fst_conv snd_conv
          reverse_center11_first_offset_def reverse_center11_second_offset_def
          reverse_center11_homogeneous_def reverse_center11_matrix_apply_def
          reverse_center11_mod11_negated_pair mod_add_left_eq)
  qed
qed

lemma reverse_center11_growth_left_annihilates:
  assumes growth: "reverse_center11_growth first"
  shows "reverse_center11_matrix_mult
      (reverse_center11_homogeneous later)
      (reverse_center11_homogeneous first) = (0,0,0,0)"
  using growth
  by (cases first; cases later)
    (simp_all add: reverse_center11_homogeneous_def
      reverse_center11_matrix_mult_def)

ML \<open>
val checked = @{thms reverse_center11_run_append
  reverse_center11_mod_accumulator_shift
  reverse_center11_tick_accumulator_shift
  reverse_center11_tick_accumulator_projection
  reverse_center11_tick_first_projection
  reverse_center11_tick_second_projection
  reverse_center11_two_branch_if
  reverse_center11_nat_parity_growth_if
  reverse_center11_half_widths
  reverse_center11_reflected_pair_prefix_structure
  reverse_center11_run_accumulator_shift
  reverse_center11_half_affine_form
  reverse_center11_growth_left_annihilates};
val _ = if null (Thm_Deps.all_oracles checked) then ()
  else error "Reverse Center11 controlled action depends on an oracle";
val _ = if Thm_Deps.has_skip_proof checked
  then error "Skipped Reverse Center11 controlled action proof" else ();
\<close>

end
