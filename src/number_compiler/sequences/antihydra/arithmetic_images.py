"""Antihydra's return law and physical projection of shared dyadic images.

Source admission, precision transport, composition, and failure descent belong
to the shared scheduler engine.  This adapter only supplies the arithmetic law
and converts demanded bounded leaves to the existing guarded roof consumer.
"""

from __future__ import annotations

from collections.abc import Iterator

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.blocks import ArithmeticCylinder

ANTIHYDRA_ARITHMETIC_LAW = DyadicReturnLaw(
    family="antihydra-arithmetic-source-image",
    semantic_version="antihydra-arithmetic-source-image-v2-dyadic",
    gains=(3, 3),
    offsets=(0, -1),
    weights=(2, -1),
)


class AntihydraArithmeticImageWorkspace(DyadicReturnImageWorkspace):
    """Pinned blank-tape arithmetic source; physical roofs remain demanded."""

    def __init__(self, ledger: ResourceLedger, returns: int) -> None:
        super().__init__(ledger, 8, returns, ANTIHYDRA_ARITHMETIC_LAW)

    @property
    def returns(self) -> int:
        return self.steps

    def validate(self) -> None:
        try:
            super().validate()
            if self.seed != 8 or self.law != ANTIHYDRA_ARITHMETIC_LAW:
                raise ValueError("another source law")
        except (ValueError, TypeError, AttributeError) as error:
            raise ValueError("Antihydra arithmetic source image was changed") from error

    def segments(self) -> Iterator[tuple[int, ArithmeticCylinder]]:
        for start, summary, word in self.leaf_summaries():
            transfer = summary.transfer
            numerator = transfer.upper * summary.residue + transfer.offset
            output, remainder = divmod(numerator, transfer.lower)
            if remainder:
                raise ArithmeticError("Antihydra arithmetic leaf is not integral")
            yield (
                start,
                ArithmeticCylinder(
                    summary.width,
                    summary.residue,
                    output,
                    summary.delta,
                    summary.minimum,
                    word,
                ),
            )


AntihydraArithmeticActionID = DyadicReturnActionID
AntihydraArithmeticImageID = DyadicReturnImageID
AntihydraArithmeticSourceID = DyadicReturnSourceID
AntihydraArithmeticSupportID = DyadicReturnSupportID
ArithmeticImageSummary = DyadicImageSummary

__all__ = [
    "ANTIHYDRA_ARITHMETIC_LAW",
    "AntihydraArithmeticActionID",
    "AntihydraArithmeticImageID",
    "AntihydraArithmeticImageWorkspace",
    "AntihydraArithmeticSourceID",
    "AntihydraArithmeticSupportID",
    "ArithmeticImageSummary",
]
