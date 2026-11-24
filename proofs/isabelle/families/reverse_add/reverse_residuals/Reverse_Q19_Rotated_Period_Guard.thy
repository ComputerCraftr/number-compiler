theory Reverse_Q19_Rotated_Period_Guard
  imports Reverse_Punctured_T2_Coefficients
    "Shared_Carry_Dynamics.Ordered_Matrix_Program_Algebra"
begin

text \<open>The Q19 word stores the left half of a symmetric physical pair
field. The same all-phase periodic matcher is valid for both intervals when
the reflected word and the original word have the same ordered rotation.\<close>

definition reverse_q19_reflected_period :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "reverse_q19_reflected_period pattern width =
    map (\<lambda>j. pattern ! ((width - Suc j) mod length pattern))
      [0..<length pattern]"

lemma reverse_q19_rotated_period_value:
  fixes pattern canonical :: "nat list" and offset index :: nat
  assumes nonempty: "pattern \<noteq> []"
    and rotated: "canonical = rotate offset pattern"
  shows "canonical ! (((length pattern - offset mod length pattern) + index) mod
      length pattern) = pattern ! (index mod length pattern)"
proof -
  let ?p = "length pattern"
  let ?phase = "(?p - offset mod ?p) mod ?p"
  have index: "index mod ?p < ?p" using nonempty by simp
  have phase_entry: "canonical ! ((?phase + index mod ?p) mod ?p) =
      pattern ! (index mod ?p)"
    using ordered_rotation_entry_nth[where word=pattern and rotation=offset
        and index="index mod ?p", OF nonempty index]
    by (simp only: rotated)
  show ?thesis using phase_entry by (simp only: mod_add_right_eq mod_add_left_eq)
qed

lemma reverse_q19_reflection_coordinate:
  fixes width index period :: nat
  assumes index: "index < width" and positive: "0 < period"
  shows "(width - Suc ((width - Suc index) mod period)) mod period = index mod period"
proof -
  let ?a = "width - Suc index"
  let ?q = "?a div period"
  let ?r = "?a mod period"
  have split: "period * ?q + ?r = ?a"
    using div_mult_mod_eq[of ?a period] by (simp add: mult.commute)
  have sum: "width - Suc ?r = index + period * ?q"
    using index split mod_le_divisor[OF positive, of ?a] by arith
  show ?thesis by (simp only: sum mod_mult_self2)
qed

theorem reverse_q19_reflected_rotation_transport:
  fixes pattern canonical :: "nat list" and width index offset phase :: nat
  defines "mirror \<equiv> reverse_q19_reflected_period pattern width"
  assumes nonempty: "pattern \<noteq> []"
    and width: "length pattern \<le> width"
    and index: "index < width"
    and rotation: "canonical = rotate offset mirror"
    and phase: "phase = (length mirror - offset mod length mirror) mod length mirror"
  shows "canonical ! (((width - Suc index) + phase) mod length canonical) =
    pattern ! (index mod length pattern)"
proof -
  let ?p = "length pattern"
  let ?r = "width - Suc index"
  have mirror_length: "length mirror = ?p"
    by (simp add: mirror_def reverse_q19_reflected_period_def)
  have mirror_nonempty: "mirror \<noteq> []" using nonempty mirror_length by auto
  have limb: "mirror ! (?r mod ?p) = pattern ! (index mod ?p)"
    using width nonempty reverse_q19_reflection_coordinate[OF index, of ?p]
    by (simp add: mirror_def reverse_q19_reflected_period_def nth_map)
  have transport: "canonical ! (((length mirror - offset mod length mirror) + ?r)
        mod length mirror) = mirror ! (?r mod length mirror)"
    by (rule reverse_q19_rotated_period_value[OF mirror_nonempty rotation])
  have shift: "(?r + phase) mod length canonical =
      ((length mirror - offset mod length mirror) + ?r) mod length mirror"
    by (simp only: rotation phase length_rotate mod_add_right_eq add.commute)
  show ?thesis using transport limb by (simp only: shift mirror_length)
qed

definition reverse_q19_physical_pair_word :: "nat list \<Rightarrow> nat list" where
  "reverse_q19_physical_pair_word source_digits =
    map (\<lambda>i. source_digits ! i + source_digits ! (length source_digits - Suc i))
      [0..<length source_digits]"

theorem reverse_q19_issued_reflected_guard:
  fixes source_at :: "nat \<Rightarrow> nat list" and pattern canonical :: "nat list"
    and generation width index offset phase :: nat
  defines "mirror \<equiv> reverse_q19_reflected_period pattern width"
  assumes source_width: "length (source_at generation) = width"
    and nonempty: "pattern \<noteq> []" and period_width: "length pattern \<le> width"
    and index: "index < width"
    and rotation: "canonical = rotate offset mirror"
    and phase: "phase = (length mirror - offset mod length mirror) mod length mirror"
    and checked: "(source_at generation ! index +
        source_at generation ! (width-Suc index)) =
      canonical ! (((width-Suc index)+phase) mod length canonical)"
  shows "reverse_q19_physical_pair_word (source_at generation) ! index =
    pattern ! (index mod length pattern)"
proof -
  have exact: "canonical ! (((width-Suc index)+phase) mod length canonical) =
      pattern ! (index mod length pattern)"
    by (rule reverse_q19_reflected_rotation_transport[
      where offset=offset, OF nonempty period_width index
        rotation[unfolded mirror_def] phase[unfolded mirror_def]])
  show ?thesis using checked exact source_width index
    by (simp add: reverse_q19_physical_pair_word_def)
qed

ML \<open>
  val checked = @{thms reverse_q19_rotated_period_value
    reverse_q19_reflection_coordinate reverse_q19_reflected_rotation_transport
    reverse_q19_issued_reflected_guard};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse Q19 rotated guard depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Reverse Q19 rotated guard has a skipped proof" else ();
\<close>

end
