theory Comma_Selected_Block_Smoke
  imports Comma_Selected_Return_Blocks
begin

text \<open>Executable regression checks for the proof builder and imported
boundary facts. This theory is built with its owner but is not an import of
the concrete period checker, so testing is not replayed on that hot path.\<close>

ML_file "selected_block_smoke.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_selected_block_then_certified comma_selected_block_choice_path})
    then () else error "Selected-block regression depends on an oracle";
\<close>
end
