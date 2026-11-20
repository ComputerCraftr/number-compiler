"""Command-line interface for the untrusted semantic FutureCID candidate."""

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
        "--from-native-export", type=Path, help="copy canonical native export"
    )
    parser.add_argument(
        "--from-m204-source", type=Path, help="literal compact source MDD proposal"
    )
    parser.add_argument(
        "--from-m204-graph", type=Path, help="literal compact class graph proposal"
    )
    parser.add_argument("--occurrence-output", type=Path, help="C1/weight audit output")
    parser.add_argument(
        "--runtime-output", type=Path, help="canonical compact runtime output"
    )
    parser.add_argument("--reencode-input", type=Path, help="existing raw v1 candidate")
    args = parser.parse_args()
    if args.from_native_export is not None:
        if any(
            (
                args.from_m204_source,
                args.from_m204_graph,
                args.occurrence_output,
                args.runtime_output,
                args.reencode_input,
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
    if args.from_m204_source is not None or args.from_m204_graph is not None:
        if args.from_m204_source is None or args.from_m204_graph is None:
            raise ValueError("both M204 proposal files are required")
        if any((args.occurrence_output, args.runtime_output, args.reencode_input)):
            raise ValueError("M204 proposal export cannot be combined with other modes")
        if args.output.resolve() in {
            args.from_m204_source.resolve(),
            args.from_m204_graph.resolve(),
        }:
            raise ValueError("candidate inputs and output must have distinct paths")
        record = future_artifact.runtime_candidate_record_from_m204_data(
            args.from_m204_source.read_text(encoding="utf-8"),
            args.from_m204_graph.read_text(encoding="utf-8"),
        )
        candidate_module.write_new(
            args.output,
            future_artifact.canonical_candidate_bytes(record).decode("ascii"),
        )
        print(
            json.dumps(
                {"output": str(args.output), "authority": record["authority"]},
                sort_keys=True,
            )
        )
        return
    occurrence_output = args.occurrence_output or args.output.with_name(
        args.output.stem + ".occurrence.json"
    )
    if args.reencode_input is not None:
        if args.runtime_output is not None:
            raise ValueError("re-encoding already writes the runtime candidate")
        print(
            json.dumps(
                candidate_module.reencode_candidate(
                    args.reencode_input, args.output, occurrence_output
                ),
                sort_keys=True,
            )
        )
        return
    future_artifact.validate_output_paths(
        args.output, occurrence_output, args.runtime_output
    )
    candidate = candidate_module.build_semantic_future_candidate()
    candidate_module.write_new(
        args.output,
        future_artifact.canonical_candidate_bytes(
            candidate.certificate_record()
        ).decode("ascii"),
    )
    candidate_module.write_new(
        occurrence_output,
        json.dumps(
            candidate.occurrence_payload_record(), sort_keys=True, separators=(",", ":")
        )
        + "\n",
    )
    if args.runtime_output is not None:
        candidate_module.write_new(
            args.runtime_output, candidate.runtime_candidate_bytes().decode("ascii")
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
                "runtime_output": None
                if args.runtime_output is None
                else str(args.runtime_output),
                "runtime_sha256": None
                if args.runtime_output is None
                else candidate.runtime_candidate_sha256(),
            },
            sort_keys=True,
        )
    )
