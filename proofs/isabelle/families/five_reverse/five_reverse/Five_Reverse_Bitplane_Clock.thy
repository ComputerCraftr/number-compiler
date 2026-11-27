theory Five_Reverse_Bitplane_Clock
  imports Five_Reverse_Bitplane_Lanes Five_Reverse_Packed_Word_Consumer
begin

text \<open>The clock transport is parameterized by the encoding and by the two
sheet refinements.  An instance must prove these representation laws for its
actual bitplane operations before using the clock as production authority.\<close>

locale five_plane_clock =
  fixes encode :: "nat \<Rightarrow> 'word"
    and decode :: "'word \<Rightarrow> nat"
    and reflected :: "'word \<Rightarrow> 'word"
    and normalize :: "'word \<Rightarrow> 'word"
    and multiply :: "'word \<Rightarrow> 'word"
  assumes source: "\<And>seed. decode (encode seed) = seed"
    and reflected_sheet: "\<And>word. decode (reflected word) = five_reflected_E (decode word)"
    and normalization: "\<And>word. decode (normalize word) = five_reflected_normalize (decode word)"
    and multiply_sheet: "\<And>word. decode (multiply word) = 5 * decode word"
begin

fun plane_pairs :: "nat \<Rightarrow> 'word \<Rightarrow> 'word" where
  "plane_pairs 0 word = word"
| "plane_pairs (Suc n) word = multiply (normalize (reflected (plane_pairs n word)))"

lemma plane_pair_physical:
  "decode (multiply (normalize (reflected word))) =
    five_reverse_step (five_reverse_step (decode word))"
  using five_reflected_physical_two_step[of "decode word"]
  by (simp only: reflected_sheet normalization multiply_sheet)

lemma plane_pairs_physical:
  "decode (plane_pairs n (encode seed)) = five_reverse_orbit (2*n) seed"
proof (induction n)
  case 0
  then show ?case by (simp add: source)
next
  case (Suc n)
  have two_more: "2 * Suc n = Suc (Suc (2*n))" by simp
  show ?case using plane_pair_physical[of "plane_pairs n (encode seed)"] Suc.IH
    by (simp only: plane_pairs.simps two_more five_reverse_orbit.simps)
qed

theorem plane_clock_selected_output:
  shows even: "decode (plane_pairs n (encode seed)) = five_reverse_orbit (2*n) seed"
    and odd: "five_reverse_step (decode (plane_pairs n (encode seed))) =
      five_reverse_orbit (Suc (2*n)) seed"
  by (simp_all only: plane_pairs_physical five_reverse_orbit.simps)

end

ML \<open>
  val checked = @{thms five_plane_clock.plane_pair_physical
    five_plane_clock.plane_pairs_physical five_plane_clock.plane_clock_selected_output};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Bitplane clock theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped bitplane clock proof" else ();
\<close>

end
