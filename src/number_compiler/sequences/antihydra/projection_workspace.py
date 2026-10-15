"""One reusable, charged, empty-between-queries section-image workspace."""

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.stores import LedgerDict

Image = tuple[tuple[int, ...], ...]


class SectionImageWorkspace:
    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            "antihydra.spacetime.images", "demanded_projection"
        )
        self.images: LedgerDict[tuple[int, int], Image] = ledger.make_dict(self.owner)
        self.area = 0
        self.active = False
        ledger.register_container(
            self.owner,
            self.images,
            node_count=lambda: 12 * self.area * len(self.images),
            payloads=self.images.items,
        )
        ledger.register_execution_root(self)
        from number_compiler.sequences.antihydra.payload_audit import (
            register_antihydra_payload_contract,
        )

        register_antihydra_payload_contract(self)

    def start(self, area: int) -> None:
        if type(area) is not int or not 1 <= area <= 4096:
            raise ValueError("section-image area must be 1..4096")
        if self.active or self.images:
            raise RuntimeError("section-image workspace is already active")
        self.area, self.active = area, True

    def put(self, key: tuple[int, int], image: Image, capacity: int) -> None:
        if not self.active or not 1 <= capacity <= 32:
            raise RuntimeError(
                "section-image insertion requires an active bounded query"
            )
        if key in self.images:
            raise ValueError("section-image insertion requires a missing key")
        if len(self.images) >= capacity:
            del self.images[next(iter(self.images))]
            self.ledger.release(self.owner, entries=1, nodes=12 * self.area)
            self.ledger.bump(_antihydra_keys.SPACETIME_SECTION_IMAGE_EVICTIONS)
        self.ledger.reserve(self.owner, entries=1, nodes=12 * self.area)
        try:
            self.images[key] = image
        except BaseException:
            self.ledger.release(self.owner, entries=1, nodes=12 * self.area)
            raise

    def clear(self) -> None:
        count = len(self.images)
        self.images.clear()
        self.ledger.release(self.owner, entries=count, nodes=12 * self.area * count)
        self.area, self.active = 0, False
