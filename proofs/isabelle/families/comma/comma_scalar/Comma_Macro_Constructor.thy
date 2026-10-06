theory Comma_Macro_Constructor
  imports Comma_Arithmetic.Comma_Boundary_Primitives
begin

text \<open>The bounded scalar macro remains a reference. Boundary states and
literal child arithmetic are owned by the neutral arithmetic theory.\<close>

text \<open>A result at a fork contains both children in numerical
order; a landmine contains none.  Fuel exhaustion is represented by
None and never counts as a certified macro.\<close>

type_synonym comma_macro_result = "nat \<times> nat \<times> nat \<times> nat \<times> nat list"

fun comma_macro_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    comma_macro_result option" where
  "comma_macro_run 0 f p k w = None"
| "comma_macro_run (Suc fuel) f p k w =
    (let children = comma_large_children f p k in
      if length children \<noteq> 1 then Some (f,p,k,w,children)
      else
        (let L = comma_cycle_length f;
             P = comma_period_displacement f (k mod 10) L;
             G = comma_phase_max_guard f (k mod 10) L;
             H = comma_headroom f p k;
             c = comma_safe_cycle_count H G P (H + 1)
         in if c > 0 then comma_macro_run fuel f p (k + c * P) (w + c * L)
            else
              (let next = hd children;
                   same = (if f < 9 then
                     H > 10 * (k mod 10) + f + 1
                     else H > 10 * (k mod 10) + 9);
                   f' = (if same then f else if f < 9 then f + 1 else 1);
                   p' = (if same \<or> f < 9 then p else Suc p)
               in comma_macro_run fuel f' p' next (Suc w))))"

definition comma_boundary_macro ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> comma_macro_result option" where
  "comma_boundary_macro fuel q =
    (case q of (kind,a,r) \<Rightarrow>
      let p = comma_boundary_sample_exponent q;
          k = comma_boundary_value q p;
          f = (if kind = Comma_N then a - 1 else a)
      in comma_macro_run fuel f p k 0)"

definition comma_boundary_children ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> comma_boundary_state list option" where
  "comma_boundary_children fuel q =
    (case comma_boundary_macro fuel q of None \<Rightarrow> None
      | Some (f,p,endpoint,w,children) \<Rightarrow>
          if length children = 2 then
            Some [(Comma_N,f+1,p mod 924),(Comma_Z,f+1,p mod 924)]
          else Some [])"

definition comma_boundary_exponent_gain ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> nat option" where
  "comma_boundary_exponent_gain fuel q =
    (case comma_boundary_macro fuel q of None \<Rightarrow> None
      | Some (f,p,endpoint,w,children) \<Rightarrow>
          Some (p - comma_boundary_sample_exponent q))"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_boundary_states_set comma_boundary_states_card
      comma_boundary_sample_admitted comma_near_boundary_sector
      comma_zero_boundary_sector comma_boundary_source_sector
      comma_large_children_complete
      comma_large_children_fork comma_large_children_landmine})
    then () else error "Comma macro constructor proof depends on an oracle";
\<close>
end
