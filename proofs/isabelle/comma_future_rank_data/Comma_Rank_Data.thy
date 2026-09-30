theory Comma_Rank_Data
  imports Comma_Rank_Data_N Comma_Rank_Data_Z
begin

text \<open>Both side tables are untrusted candidate definitions.
The checked instance must compare every rank with complete children
computed from the executable HOL transition.\<close>

definition comma_rank_code_at :: "nat \<Rightarrow> nat" where
  "comma_rank_code_at i =
    (let codes = (if i < 8*924 then comma_rank_codes_N else comma_rank_codes_Z);
         j = i mod (8*924)
     in codes ! (j div 4096) ! ((j div 256) mod 16) !
       ((j div 16) mod 16) ! (j mod 16))"

definition comma_rank_candidate :: "comma_boundary_state \<Rightarrow> nat option" where
  "comma_rank_candidate q =
    (case q of (kind,a,r) \<Rightarrow>
      let index = (if kind = Comma_Z then 8 * 924 else 0) +
        (a - 2) * 924 + r; code = comma_rank_code_at index
      in if code = 0 then None else Some (code - 1))"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_rank_code_at_def comma_rank_candidate_def})
    then () else error "Comma rank lookup depends on an oracle";
\<close>

end
