theory Comma_Sector_Mask_Instance
  imports Comma_Sector_Mask_Audit.Comma_Sector_Mask_Constructor
    Comma_Sparse_Core.Comma_Sector_Base_Masks
begin

text \<open>First complete decade row through the shared short-sector DAG.
This positive construction check does not certify the other 45 source fibers,
temporal all-stop coverage, or future branch safety.\<close>

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Mask_Constructor.make lthy
        {max_rows=900, max_clauses=8192, max_guard_nodes=8192, max_operations=100000}
      val result = #word engine 1 0
      val _ = Comma_Fast_Kernel.report (#report engine ())
      val (_, lthy') = Local_Theory.note
        ((Binding.name "comma_sector_first_decade_mask", []), [#theorem result]) lthy
    in lthy' end
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_sector_first_decade_mask}) then ()
    else error "Concrete decade mask depends on an oracle";
\<close>
end
