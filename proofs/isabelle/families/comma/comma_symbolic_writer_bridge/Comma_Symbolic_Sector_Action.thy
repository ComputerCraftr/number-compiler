theory Comma_Symbolic_Sector_Action
  imports Comma_Symbolic_Boundary_Source
begin

text \<open>One source-issued sector action covers both Entry and Near. Its
point operation selects only the requested physical cut, and its duration is
physical elapsed time, not a traversal budget.\<close>

fun comma_symbolic_sector_duration :: "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat" where
  "comma_symbolic_sector_duration p (Comma_Entry f delta offset) =
    fst (comma_c1_first_sector f p delta offset)"
| "comma_symbolic_sector_duration p (Comma_Near f delta h) =
    fst (comma_near_closed_germ f h)"

fun comma_symbolic_sector_point ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_symbolic_sector_point p (Comma_Entry f delta offset) j =
    comma_first_sector_writer_point f p delta offset j"
| "comma_symbolic_sector_point p (Comma_Near f delta h) j =
    comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h j))"

theorem comma_symbolic_sector_cut_exact:
  assumes source: "comma_round_admitted source" and exponent: "5 \<le> p"
    and cut: "j \<le> comma_symbolic_sector_duration p source"
  shows "comma_literal_path j (comma_chart_value p source)
      (comma_symbolic_sector_point p source j) \<and>
    comma_literal_path (comma_symbolic_sector_duration p source-j)
      (comma_symbolic_sector_point p source j)
      (comma_chart_value p (comma_decisive_sector_target (p mod 924) source))"
proof (cases source)
  case (Comma_Entry f delta offset)
  have sector: "1 \<le> f" "f \<le> 9" and offset: "offset \<le> 98"
    using source by (simp_all add: Comma_Entry)
  obtain elapsed t event where packet:
      "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
    by (cases "comma_c1_first_sector f p delta offset") auto
  have bound: "j \<le> elapsed" using cut packet by (simp add: Comma_Entry)
  note exact = comma_symbolic_decisive_entry_packet[OF sector exponent offset packet bound]
  have target: "comma_decisive_sector_target (p mod 924) (Comma_Entry f delta offset) =
      Comma_Near f delta t"
    using exact(1) by (simp add: comma_decisive_endpoint_packet_def Let_def split: prod.splits)
  show ?thesis
    using exact(2,3) packet target
    by (simp add: Comma_Entry comma_first_sector_writer_def)

next
  case (Comma_Near f delta h)
  have sector: "1 \<le> f" "f \<le> 9" and headroom: "1 \<le> h" "h \<le> 540"
    using source by (simp_all add: Comma_Near)
  obtain n t where packet: "comma_near_closed_germ f h = (n,t)"
    by (cases "comma_near_closed_germ f h") auto
  have prefix: "comma_near_prefix n f h t"
    using comma_near_closed_refines(1)[OF sector headroom packet] .
  have bound: "j \<le> n" using cut packet by (simp add: Comma_Near)
  note exact = comma_symbolic_near_cut_exact[OF sector exponent headroom prefix bound, where delta=delta]
  show ?thesis
    using exact(1,2) packet
    by (simp add: Comma_Near comma_decisive_sector_target.simps)

qed

ML \<open>
  val checked = @{thms comma_symbolic_sector_cut_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Sector action used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Sector action contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Sector action excludes legacy authority"
    ["comma_round_close", "comma_finite_macro", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
