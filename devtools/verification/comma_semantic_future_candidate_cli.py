"""Command-line interface for the semantic FutureCID candidate producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import devtools.verification.comma_semantic_future_artifact as future_artifact
import devtools.verification.comma_semantic_future_candidate as candidate_module


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate an untrusted source-derived semantic FutureCID candidate"
    )
    parser.add_argument(
        "--output", type=Path, required=True, help="fresh candidate output path"
    )
    parser.add_argument(
        "--from-isabelle-data", type=Path, help="export authored tables"
    )
    parser.add_argument(
        "--from-native-export",
        type=Path,
        help="copy canonical candidate bytes exported by the checked Isabelle session",
    )
    parser.add_argument("--occurrence-output", type=Path, help="C1/weight audit output")
    parser.add_argument("--runtime-output", type=Path, help="canonical v2 output")
    parser.add_argument("--reencode-input", type=Path, help="existing v1 candidate")
    parser.add_argument("--isabelle-data-output", type=Path, help="generated HOL data")
    parser.add_argument("--checked-isabelle-data", type=Path, help="authored HOL data")
    args = parser.parse_args()
    if args.from_native_export is not None:
        if any(
            (
                args.from_isabelle_data,
                args.occurrence_output,
                args.runtime_output,
                args.reencode_input,
                args.isabelle_data_output,
                args.checked_isabelle_data,
            )
        ):
            raise ValueError(
                "native candidate export cannot be combined with other modes"
            )
        result = future_artifact.write_runtime_candidate_from_native_export(
            args.from_native_export, args.output
        )
        print(json.dumps(result, sort_keys=True))
        return
    if args.from_isabelle_data is not None:
        if any(
            (
                args.occurrence_output,
                args.runtime_output,
                args.reencode_input,
                args.isabelle_data_output,
                args.checked_isabelle_data,
            )
        ):
            raise ValueError("HOL data export cannot be combined with other modes")
        result = future_artifact.write_runtime_candidate_from_isabelle_data(
            args.from_isabelle_data, args.output
        )
        print(json.dumps(result, sort_keys=True))
        return
    if args.reencode_input is not None:
        if args.runtime_output is not None:
            raise ValueError("re-encoding already writes the v2 runtime candidate")
        occurrence_output = args.occurrence_output or args.output.with_name(
            args.output.stem + ".occurrence.json"
        )
        print(
            json.dumps(
                candidate_module.reencode_candidate(
                    args.reencode_input,
                    args.output,
                    occurrence_output,
                    args.isabelle_data_output,
                    args.checked_isabelle_data,
                ),
                sort_keys=True,
            )
        )
        return
    candidate = candidate_module.build_semantic_future_candidate()
    occurrence_output = args.occurrence_output or args.output.with_name(
        args.output.stem + ".occurrence.json"
    )
    future_artifact.validate_output_paths(
        args.output, occurrence_output, args.runtime_output, args.isabelle_data_output
    )
    output_paths = {
        path.resolve()
        for path in (
            args.output,
            occurrence_output,
            args.runtime_output,
            args.isabelle_data_output,
        )
        if path is not None
    }
    if (
        args.checked_isabelle_data is not None
        and args.checked_isabelle_data.resolve() in output_paths
    ):
        raise ValueError("checked Isabelle data must be distinct from outputs")
    checked_runtime_sha256 = (
        None
        if args.checked_isabelle_data is None
        else candidate_module.verify_runtime_candidate_hol_data_binding(
            candidate.runtime_candidate_record(), args.checked_isabelle_data
        )
    )
    candidate_module.write_new(
        args.output,
        future_artifact.canonical_candidate_bytes(
            candidate.certificate_record()
        ).decode("ascii"),
    )
    candidate_module.write_new(
        occurrence_output,
        json.dumps(
            candidate.occurrence_payload_record(),
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n",
    )
    if args.runtime_output is not None:
        candidate_module.write_new(
            args.runtime_output,
            candidate.runtime_candidate_bytes().decode("ascii"),
        )
    if args.isabelle_data_output is not None:
        candidate_module.write_new(
            args.isabelle_data_output, candidate.isabelle_candidate_data()
        )
    print(
        json.dumps(
            {
                "output": str(args.output),
                "states": len(candidate.states),
                "classes": len(candidate.class_controls),
                "ranked_classes": sum(
                    rank is not None for rank in candidate.class_ranks
                ),
                "refinement_rounds": candidate.refinement_rounds,
                "collision_witnesses": len(candidate.refinement_collisions),
                "seam_projected_from_cid": candidate.seam_is_projected_from_cid,
                "occurrence_output": str(occurrence_output),
                "runtime_output": (
                    None if args.runtime_output is None else str(args.runtime_output)
                ),
                "runtime_sha256": (
                    None
                    if args.runtime_output is None
                    else candidate.runtime_candidate_sha256()
                ),
                "isabelle_data_output": (
                    None
                    if args.isabelle_data_output is None
                    else str(args.isabelle_data_output)
                ),
                "checked_isabelle_data": (
                    None
                    if args.checked_isabelle_data is None
                    else str(args.checked_isabelle_data)
                ),
                "checked_runtime_sha256": checked_runtime_sha256,
            },
            sort_keys=True,
        )
    )
