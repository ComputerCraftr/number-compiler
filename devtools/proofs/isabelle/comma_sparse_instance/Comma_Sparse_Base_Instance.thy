theory Comma_Sparse_Base_Instance
  imports Comma_Decade_Masks.Comma_Sparse_Checked_Algebra
    Comma_Decade_Masks.Comma_Sector_Mask_Smoke
begin

text \<open>The one shared short-sector constructor supplies all forty-six
base words. Every raw-offset row retains its complete response certificate;
projection is admitted only after its crossing and terminal fields are checked.
No scalar decade graph, rank candidate or finite-run fuel is read here.\<close>

ML \<open>
structure Comma_Sparse_Base_Data = Theory_Data
(
  type T = Comma_Sector_Mask_Constructor.row list option
  val empty = NONE
  fun merge (NONE, right) = right
    | merge (left, NONE) = left
    | merge (SOME left, SOME right) =
        if eq_list (op aconv)
            (map (Thm.prop_of o #theorem) left, map (Thm.prop_of o #theorem) right)
          then SOME left else error "Conflicting sparse base theory publications"
)
\<close>

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Mask_Constructor.make lthy
        {max_rows=900, max_clauses=8192, max_guard_nodes=8192, max_operations=100000}
      val _ = Comma_Fast_Kernel.report "sparse_base_words_start"
      val attempt = Exn.capture
        (Timeout.apply (Time.fromSeconds 40) (fn () => #base_words engine ())) ()
      val _ = Comma_Fast_Kernel.report ("sparse_base_instance " ^ #report engine ())
      val words = Exn.release attempt
      val _ = if length words=46 then () else error "Sparse base requires exactly forty-six words"
      (* Each payload is named and checked once. The aggregate certificate
         contains constants and indices; it never unfolds the forty-six rows. *)
      fun publish (i, (row: Comma_Sector_Mask_Constructor.row)) (entries, context) =
        let
          val name = "comma_sparse_base_row_" ^ Int.toString i
          val ((constant, (_, definition)), next) = Local_Theory.define
            ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"), []), #rows row)) context
          val fold_row = Conv.rewr_conv (Thm.symmetric (Local_Defs.meta_rewrite_rule next definition))
          val fold_scope = Conv.rewr_conv (Thm.symmetric (#full_mask engine))
          val exact = Conv.fconv_rule
            (Conv.arg_conv (Conv.combination_conv (Conv.arg_conv fold_scope) fold_row))
            (#theorem row)
          val admission = Goal.prove next [] []
            (HOLogic.mk_Trueprop (@{term
              "list_all (\<lambda>(out,bits). comma_sector_base_admitted out)"} $ constant))
            (fn {context,...} => simp_tac
              (Comma_Entry_Arithmetic.natural_context context addsimps
                [definition] addsimps @{thms list_all_Nil_iff list_all_Cons_iff
                  comma_sector_base_admitted.simps}) 1)
          val proposition = @{term comma_sparse_base_row_checked} $
            HOLogic.mk_number @{typ nat} i $ constant
          val checked = Goal.prove next [] [] (HOLogic.mk_Trueprop proposition)
            (fn {context,...} => simp_tac
              (Comma_Entry_Arithmetic.natural_context context addsimps [exact, admission]
                addsimps @{thms comma_sparse_base_row_checked_def
                  comma_offset_representatives_def nth_Cons'}) 1)
        in ((constant, checked)::entries, next) end
      val (reversed, rows_context) = fold publish (map_index I words) ([], lthy)
      val entries = rev reversed
      val body = HOLogic.mk_list @{typ comma_sector_rows} (map fst entries)
      val ((table, (_, definition)), next) = Local_Theory.define
        ((Binding.name "comma_sparse_base_row_table", NoSyn),
          ((Binding.name "comma_sparse_base_row_table_def", []), body)) rows_context
      val literal = fold_rev (fn (_, fact) => fn tail =>
        @{thm comma_sparse_base_table_cons} OF [fact, tail]) entries
        @{thm comma_sparse_base_table_nil}
      val proposition = @{term
        "list_all2 comma_sparse_base_row_checked [0..<46]"} $ table
      val theorem = Goal.prove next [] [] (HOLogic.mk_Trueprop proposition)
        (fn {context,...} => simp_tac
          (Comma_Entry_Arithmetic.natural_context context addsimps [definition, literal]
            addsimps @{thms upt_rec}) 1)
      val _ = if null (Thm_Deps.all_oracles [theorem]) then ()
        else error "Concrete sparse base rows depend on an oracle"
      val (_, final) = Local_Theory.note
        ((Binding.name "comma_sparse_base_rows_checked", []), [theorem]) next
      val _ = if is_none (Comma_Sparse_Base_Data.get (Proof_Context.theory_of final))
        then () else error "Sparse base rows were already published in this theory"
    in Local_Theory.background_theory (Comma_Sparse_Base_Data.put (SOME words)) final end
\<close>

definition comma_sparse_base_rows :: "nat \<Rightarrow> comma_sector_rows" where
  "comma_sparse_base_rows i=comma_sparse_base_row_table!i"

lemma comma_sparse_base_rows_refine:
  assumes "i<46"
  shows "comma_sector_rows_refine
    (comma_sector_mask_value 1 (comma_offset_representatives!i))
    (mask 924) (comma_sparse_base_rows i)"
  using comma_sparse_base_table_nth[OF comma_sparse_base_rows_checked assms]
  by (simp add: comma_sparse_base_row_checked_def comma_sparse_base_rows_def)

lemma comma_sparse_base_rows_admitted:
  assumes "i<46" "(out,bits)\<in>set (comma_sparse_base_rows i)"
  shows "comma_sector_base_admitted out"
  using comma_sparse_base_table_nth[OF comma_sparse_base_rows_checked assms(1)] assms(2)
  by (auto simp: comma_sparse_base_row_checked_def list_all_iff comma_sparse_base_rows_def)

definition comma_checked_sparse_base :: "nat \<Rightarrow> comma_sparse_word" where
  "comma_checked_sparse_base i=comma_sparse_sector_base comma_sparse_base_rows i"

lemma comma_checked_sparse_base_refines:
  assumes "i<46"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (comma_checked_sparse_base i)"
  unfolding comma_checked_sparse_base_def
  by (rule comma_sparse_sector_base_refines[OF comma_sparse_base_rows_refine _ assms])
    (use comma_sparse_base_rows_admitted in blast)

theorem comma_checked_sparse_power_refines:
  "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_power (comma_sparse_admit comma_checked_sparse_base) k i)"
  by (rule comma_sparse_power_refines) (rule comma_checked_sparse_base_refines, assumption)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_base_rows_checked comma_sparse_base_rows_refine
      comma_sparse_base_rows_admitted comma_checked_sparse_base_refines
      comma_checked_sparse_power_refines}) then ()
    else error "Sparse base instance depends on an oracle";
\<close>
end
