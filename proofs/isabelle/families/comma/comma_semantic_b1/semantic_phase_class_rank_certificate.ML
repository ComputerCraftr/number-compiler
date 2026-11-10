(* Terminal kernel boundary for a source-bound phase-class rank certificate.
   The relation proof and exact source-action proof must be produced by the
   shallow joint-node compiler.  This module never synthesizes either one
   from a boolean result, a phase table, or a source orbit. *)
structure Comma_Semantic_Phase_Class_Rank_Certificate =
struct
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  fun require_checked ctxt label theorem =
    Transport.checked_closed ctxt ("Phase-class " ^ label)
      (Thm.prop_of theorem) theorem

  (* Inputs are closed HOL-universal certificates. Rulification occurs only
     after context/provenance validation, so no open meta-premise is accepted
     as a purported complete source certificate. *)
  fun certify ctxt {relations,rank_shapes,exact_action} =
    let
      val relations = require_checked ctxt "joint relations" relations
      val rank_shapes = require_checked ctxt "rank shapes" rank_shapes
      val exact_action = require_checked ctxt "exact source action" exact_action
      val result = @{thm comma_crt_rank_relations_sound(1)}
        OF [Object_Logic.rulify ctxt relations,
          Object_Logic.rulify ctxt rank_shapes,
          Object_Logic.rulify ctxt exact_action]
    in require_checked ctxt "rank" result end

  fun certify_B32 ctxt {relations,rank_shapes,exact_action,admitted} =
    let
      val relations = require_checked ctxt "joint relations" relations
      val rank_shapes = require_checked ctxt "rank shapes" rank_shapes
      val exact_action = require_checked ctxt "exact source action" exact_action
      val admitted = require_checked ctxt "source admission" admitted
      val result = @{thm comma_crt_rank_relations_B32}
        OF [Object_Logic.rulify ctxt relations,
          Object_Logic.rulify ctxt rank_shapes,
          Object_Logic.rulify ctxt exact_action,admitted]
    in require_checked ctxt "B32 exact summary" result end
end
