"""Proof oracle for the obsolete stage-only radix image representation."""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.proof_payload_admission import (
    register_proof_opaque_types,
    register_proof_payload_auditor,
)


@dataclass(frozen=True, slots=True)
class RadixDivisionInterfaceID(ArenaHandle):
    """Scoped identity of a source-independent bounded division interface."""


@dataclass(frozen=True, slots=True)
class RadixDivisionImageID(ArenaHandle):
    """Scoped identity of one reference quotient stage."""


@dataclass(frozen=True, slots=True)
class RadixDivisionInterface:
    radix: int
    remainder_bits: int

    def __post_init__(self) -> None:
        if type(self.radix) is not int or not 2 <= self.radix <= 1 << 63:
            raise ValueError("division interface requires a bounded exact radix")
        if type(self.remainder_bits) is not int or self.remainder_bits != max(
            1,
            (self.radix - 1).bit_length(),
        ):
            raise ValueError("division interface has an invalid remainder port")


@dataclass(frozen=True, slots=True)
class RadixDivisionImage:
    parent: RadixDivisionImageID | None
    interface: RadixDivisionInterfaceID
    stage: int
    width: int
    active: bool

    def __post_init__(self) -> None:
        if type(self.stage) is not int or self.stage < 0:
            raise ValueError("division image stage must be nonnegative")
        if type(self.width) is not int or self.width < 0:
            raise ValueError("division image width must be nonnegative")
        if type(self.active) is not bool or self.active != bool(self.width):
            raise ValueError("division image activity disagrees with its extent")
        if self.stage == 0 and self.parent is not None:
            raise ValueError("source division image cannot have a parent")
        if self.stage > 0 and type(self.parent) is not RadixDivisionImageID:
            raise ValueError("derived division image requires a scoped parent")


@dataclass(frozen=True, slots=True)
class RadixDivisionImageAuditSnapshot:
    """Detached state for checking the registered image stores and identities."""

    ledger: ResourceLedger
    interface_owner: int
    image_owner: int
    key_owner: int
    interface_store: object
    image_store: object
    key_store: object
    interfaces: tuple[RadixDivisionInterface, ...]
    images: tuple[RadixDivisionImage, ...]
    key_rows: tuple[tuple[object, object], ...]
    interface: RadixDivisionInterfaceID
    source: RadixDivisionImageID


class RadixDivisionImageArena:
    """Reference-only stage identities retained for differential tests."""

    _INTERFACE_KIND = "radix-division-interface"
    _IMAGE_KIND = "radix-division-image"

    def __init__(self, ledger: ResourceLedger, radix: int, source_width: int) -> None:
        if type(radix) is not int or not 2 <= radix <= 1 << 63:
            raise ValueError("division images require a bounded exact radix")
        if type(source_width) is not int or source_width < 1:
            raise ValueError("division images require a positive source extent")
        self.ledger = ledger
        self.token = ArenaToken("radix-division-images")
        prefix = f"radix-{radix}-division-images-{len(ledger.inventory())}"
        self._interface_owner = ledger.register(
            prefix + "-interfaces", "local_interface"
        )
        self._image_owner = ledger.register(prefix + "-nodes", "field_image")
        self._key_owner = ledger.register(prefix + "-interner", "field_image_interner")
        self._interfaces: MutableSequence[RadixDivisionInterface] = ledger.make_list(
            self._interface_owner,
        )
        self._images: MutableSequence[RadixDivisionImage] = ledger.make_list(
            self._image_owner,
        )
        self._keys: MutableMapping[RadixDivisionImage, int] = ledger.make_dict(
            self._key_owner,
        )
        ledger.register_container(
            self._interface_owner,
            self._interfaces,
            node_count=lambda: len(self._interfaces),
            payloads=lambda: self._interfaces,
        )
        ledger.register_container(
            self._image_owner,
            self._images,
            node_count=lambda: len(self._images),
            payloads=lambda: self._images,
        )
        ledger.register_container(
            self._key_owner, self._keys, payloads=self._keys.items
        )
        ledger.register_execution_root(self)
        interface = RadixDivisionInterface(radix, max(1, (radix - 1).bit_length()))
        ledger.reserve_many(
            (
                (self._interface_owner, 1, 1),
                (self._image_owner, 1, 1),
                (self._key_owner, 1, 0),
            )
        )
        self._interfaces.append(interface)
        self.interface = RadixDivisionInterfaceID(self.token, self._INTERFACE_KIND, 0)
        source = RadixDivisionImage(None, self.interface, 0, source_width, True)
        self._images.append(source)
        self._keys[source] = 0
        self.source = RadixDivisionImageID(self.token, self._IMAGE_KIND, 0)

    def resolve_interface(
        self,
        reference: RadixDivisionInterfaceID,
    ) -> RadixDivisionInterface:
        if type(reference) is not RadixDivisionInterfaceID:
            raise TypeError("expected a radix division interface ID")
        reference.validate(self.token, self._INTERFACE_KIND, size=len(self._interfaces))
        return self._interfaces[reference.local_id]

    def resolve(self, reference: RadixDivisionImageID) -> RadixDivisionImage:
        if type(reference) is not RadixDivisionImageID:
            raise TypeError("expected a radix division image ID")
        reference.validate(self.token, self._IMAGE_KIND, size=len(self._images))
        return self._images[reference.local_id]

    def image_id(self, local_id: int) -> RadixDivisionImageID:
        return RadixDivisionImageID(self.token, self._IMAGE_KIND, local_id)

    def audit_snapshot(self) -> RadixDivisionImageAuditSnapshot:
        """Capture exact registered stores and immutable rows for the auditor."""
        return RadixDivisionImageAuditSnapshot(
            self.ledger,
            self._interface_owner,
            self._image_owner,
            self._key_owner,
            self._interfaces,
            self._images,
            self._keys,
            tuple(self._interfaces),
            tuple(self._images),
            tuple(
                (cast(object, image), cast(object, index))
                for image, index in self._keys.items()
            ),
            self.interface,
            self.source,
        )

    def advance(
        self,
        parent: RadixDivisionImageID,
        width: int,
    ) -> RadixDivisionImageID:
        previous = self.resolve(parent)
        self.resolve_interface(previous.interface)
        if type(width) is not int or width < 0:
            raise ValueError("division image extent must be nonnegative")
        record = RadixDivisionImage(
            parent,
            self.interface,
            previous.stage + 1,
            width,
            bool(width),
        )
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump("radix_division_image_intern_hits")
            return self.image_id(found)
        self.ledger.reserve_many(
            ((self._image_owner, 1, 1), (self._key_owner, 1, 0)),
        )
        found = len(self._images)
        self._images.append(record)
        self._keys[record] = found
        self.ledger.bump("radix_division_image_publications")
        return self.image_id(found)


def _audit_radix_stage_images(ledger: ResourceLedger) -> set[tuple[int, int]]:
    """Validate only explicitly loaded proof-stage image arenas."""
    containers: dict[int, object] = dict(ledger.iter_containers())
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not RadixDivisionImageArena:
            continue
        snapshot = root.audit_snapshot()
        stores = (
            (snapshot.interface_owner, snapshot.interface_store),
            (snapshot.image_owner, snapshot.image_store),
            (snapshot.key_owner, snapshot.key_store),
        )
        valid_root = snapshot.ledger is ledger and all(
            containers.get(owner) is store for owner, store in stores
        )
        for index, interface in enumerate(snapshot.interfaces):
            try:
                valid = valid_root and type(interface) is RadixDivisionInterface
                interface.__post_init__()
                valid &= (
                    index == 0
                    and root.resolve_interface(snapshot.interface) is interface
                )
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            if not valid:
                invalid.add((snapshot.interface_owner, id(interface)))
        for index, image in enumerate(snapshot.images):
            try:
                valid = valid_root and type(image) is RadixDivisionImage
                image.__post_init__()
                handle = snapshot.source if index == 0 else root.image_id(index)
                valid &= (
                    root.resolve(handle) is image
                    and dict(snapshot.key_rows).get(image) == index
                )
                root.resolve_interface(image.interface)
                if image.parent is None:
                    valid &= index == 0 and image.stage == 0
                else:
                    valid &= root.resolve(image.parent).stage + 1 == image.stage
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            if not valid:
                invalid.add((snapshot.image_owner, id(image)))
        for key_image, key_index in snapshot.key_rows:
            if not (
                valid_root
                and type(key_image) is RadixDivisionImage
                and type(key_index) is int
                and 0 <= key_index < len(snapshot.images)
                and snapshot.images[key_index] is key_image
            ):
                invalid.add((snapshot.key_owner, id(key_image)))
    return invalid


register_proof_opaque_types(
    RadixDivisionInterfaceID,
    RadixDivisionImageID,
    RadixDivisionInterface,
    RadixDivisionImage,
)
register_proof_payload_auditor(_audit_radix_stage_images)


__all__ = [
    "RadixDivisionImageAuditSnapshot",
    "RadixDivisionImage",
    "RadixDivisionImageArena",
    "RadixDivisionImageID",
    "RadixDivisionInterface",
    "RadixDivisionInterfaceID",
]
