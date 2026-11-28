theory Comma_Symbolic_Adjacent_Sectors
  imports Comma_Symbolic_First_Sector_Writer
begin

text \<open>The first completed sector supplies the exact Entry source for the
second. The requested cut is selected directly in the second source action;
no intermediate event list is used as writer authority.\<close>

theorem comma_symbolic_adjacent_sector_cut:
  fixes f g p delta delta' offset offset' elapsed elapsed' t t' j :: nat
    and event :: comma_finite_move
  assumes first_sector: "1 \<le> f" "f \<le> 9"
    and second_sector: "1 \<le> g" "g \<le> 9"
    and exponent: "5 \<le> p"
    and first_offset: "offset \<le> 98"
    and second_offset: "offset' \<le> 98"
    and first_packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Next (Comma_Entry g delta' offset'))"
    and second_packet: "comma_c1_first_sector g p delta' offset' =
      (elapsed',t',event)"
    and cut: "j \<le> elapsed'"
  shows "comma_literal_path (Suc elapsed+j)
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_writer_point (comma_first_sector_writer g p delta' offset' elapsed' t') False j)"
    and "comma_literal_path (elapsed'-j)
      (comma_writer_point (comma_first_sector_writer g p delta' offset' elapsed' t') False j)
      (comma_chart_value p (Comma_Near g delta' t'))"
    and "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) =
      [comma_chart_value p (Comma_Entry g delta' offset')]"
proof -
  have first: "comma_literal_path (Suc elapsed)
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Entry g delta' offset'))"
    and ordered: "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) =
      [comma_chart_value p (Comma_Entry g delta' offset')]"
    using comma_c1_first_sector_next[OF first_sector exponent first_offset first_packet] by blast+
  note second = comma_first_sector_writer_selected_cut[OF second_sector exponent second_offset second_packet cut]
  show "comma_literal_path (Suc elapsed+j)
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_writer_point (comma_first_sector_writer g p delta' offset' elapsed' t') False j)"
    by (rule comma_literal_path_append[OF first second(1)])
  show "comma_literal_path (elapsed'-j)
      (comma_writer_point (comma_first_sector_writer g p delta' offset' elapsed' t') False j)
      (comma_chart_value p (Comma_Near g delta' t'))" by (rule second(2))
  show "comma_large_children f (p+delta)
      (comma_chart_value p (Comma_Near f delta t)) =
      [comma_chart_value p (Comma_Entry g delta' offset')]" by (rule ordered)
qed

ML \<open>
  val checked = @{thms comma_symbolic_adjacent_sector_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Adjacent sector action used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Adjacent sector action contains skipped proofs" else ();
\<close>
end
