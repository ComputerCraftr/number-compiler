"""Store-free quiescent admission operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
)
from number_compiler.hashlife.behavior.future_behavior import (
    QUIESCENT_COCYCLE_SCHEMA,
    QUIESCENT_GEOMETRY_SCHEMA,
    QUIESCENT_LAW,
    QUIESCENT_OBSERVATIONS,
    QUIESCENT_PROFILE_VERSION,
    FutureBehaviorClass,
    FutureBehaviorClassID,
    FutureBehaviorProfile,
    FutureBehaviorProfileID,
    FutureBehaviorWork,
    _identity_validation_scope,
    certify_quiescent_blank,
)
from number_compiler.hashlife.interfaces.primitive_behavior import (
    PrimitiveBehaviorQuotient,
)
from number_compiler.resources.metric_keys import (
    hashlife_behavior as _behavior_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )


def admit_quiescent_blank(
    self: DiamondQuotientArena,
    quotient: PrimitiveBehaviorQuotient,
) -> tuple[FutureBehaviorProfileID, FutureBehaviorClassID]:
    """Atomically admit one primitive all-blank successor fixed point."""
    admitted = self.lookup_quiescent_blank(quotient)
    if admitted is not None:
        self.ledger.bump(_behavior_keys.FUTURE_BEHAVIOR_PROFILE_EARLY_HITS)
        return admitted
    workspace_entries = 4 * quotient.left_count
    work = FutureBehaviorWork()
    with _identity_validation_scope():
        self.ledger.reserve(self._future_work_owner, entries=workspace_entries)
        try:
            certificate = certify_quiescent_blank(quotient, work=work)
        finally:
            self.ledger.bump(
                _behavior_keys.FUTURE_BEHAVIOR_REFINEMENT_OBSERVATION_CHECKS,
                work.observation_checks,
            )
            self.ledger.bump(
                _behavior_keys.FUTURE_BEHAVIOR_REFINEMENT_SUCCESSOR_CHECKS,
                work.successor_checks,
            )
            self.ledger.bump(
                _behavior_keys.FUTURE_BEHAVIOR_CLASSIFICATION_WORK,
                work.refinement_rounds,
            )
            self.ledger.release(self._future_work_owner, entries=workspace_entries)
        profile = FutureBehaviorProfile(
            certificate.kernel,
            certificate.continuation,
            certificate.alphabet_size,
            certificate.blank,
            QUIESCENT_OBSERVATIONS,
            certificate.safe_blank_left_states,
            QUIESCENT_GEOMETRY_SCHEMA,
            QUIESCENT_COCYCLE_SCHEMA,
            QUIESCENT_PROFILE_VERSION,
            certificate.semantic_digest,
        )
    # The private scope finishes here, before canonical key lookup, reservation,
    # or publication; its validator is reset rather than retained by the arena.
    found_profile = self._future_profile_keys.get(profile)
    if found_profile is not None:
        self.resolve_future_profile(found_profile)
        prospective_profile = found_profile
    else:
        prospective_profile = FutureBehaviorProfileID(
            self.owner,
            "future-behavior-profile",
            self._next_future_profile,
        )
    behavior = FutureBehaviorClass(
        prospective_profile,
        QUIESCENT_LAW,
        certificate.blank,
        False,
        True,
        certificate.blank,
    )
    found_class = self._future_class_keys.get(behavior)
    if found_class is not None:
        self.resolve_future_behavior(found_class)
        if found_profile is None:
            raise ValueError("future class exists without its semantic profile")
        admission_reservations = (
            (self._future_certificate_owner, 1, 0),
            (self._future_admission_owner, 1, 0),
            (self._future_snapshot_owner, 1, 0),
        )
        self.ledger.reserve_many(admission_reservations)
        result = (found_profile, found_class)
        certificate_added = False
        admission_added = False
        try:
            self._future_certificates[found_profile] = certificate
            certificate_added = True
            self._future_snapshots[("certificate", found_profile.local_id)] = (
                self._certificate_snapshot(certificate)
            )
            self._future_admissions[quotient.semantic_identity.digest] = (
                self._quotient_snapshot(quotient),
                *result,
            )
            admission_added = True
        except BaseException:
            if admission_added:
                self._future_admissions.pop(quotient.semantic_identity.digest, None)
            if certificate_added:
                self._future_certificates.pop(found_profile, None)
                self._future_snapshots.pop(
                    ("certificate", found_profile.local_id),
                    None,
                )
            for owner, entries, nodes in reversed(admission_reservations):
                self.ledger.release(owner, entries=entries, nodes=nodes)
            raise
        self.ledger.bump(_behavior_keys.FUTURE_BEHAVIOR_PROFILE_EARLY_HITS)
        return result
    reservations: list[tuple[int, int, int]] = []
    if found_profile is None:
        reservations.extend(
            (
                (self._future_profile_owner, 1, 1),
                (self._future_profile_key_owner, 1, 0),
            )
        )
    reservations.extend(
        (
            (self._future_class_owner, 1, 1),
            (self._future_class_key_owner, 1, 0),
            (self._future_certificate_owner, 1, 0),
            (self._future_admission_owner, 1, 0),
            (self._future_snapshot_owner, 2 + int(found_profile is None), 0),
        )
    )
    self.ledger.reserve_many(reservations)
    added_profile_node = False
    added_profile_key = False
    added_class_node = False
    added_class_key = False
    added_certificate = False
    added_admission = False
    added_snapshots: list[tuple[str, int]] = []
    certificate_profile = prospective_profile
    try:
        if found_profile is None:
            found_profile = prospective_profile
            self._next_future_profile += 1
            self._future_profiles[found_profile.local_id] = profile
            added_profile_node = True
            profile_snapshot_key = ("profile", found_profile.local_id)
            self._future_snapshots[profile_snapshot_key] = self._profile_snapshot(
                profile
            )
            added_snapshots.append(profile_snapshot_key)
            self._future_profile_keys[profile] = found_profile
            added_profile_key = True
        certificate_profile = found_profile
        found_class = FutureBehaviorClassID(
            self.owner,
            "future-behavior-class",
            self._next_future_class,
        )
        self._next_future_class += 1
        self._future_classes[found_class.local_id] = behavior
        added_class_node = True
        class_snapshot_key = ("class", found_class.local_id)
        self._future_snapshots[class_snapshot_key] = self._class_snapshot(behavior)
        added_snapshots.append(class_snapshot_key)
        self._future_class_keys[behavior] = found_class
        added_class_key = True
        self._future_certificates[certificate_profile] = certificate
        added_certificate = True
        certificate_snapshot_key = ("certificate", certificate_profile.local_id)
        self._future_snapshots[certificate_snapshot_key] = self._certificate_snapshot(
            certificate
        )
        added_snapshots.append(certificate_snapshot_key)
        result = (found_profile, found_class)
        self._future_admissions[quotient.semantic_identity.digest] = (
            self._quotient_snapshot(quotient),
            *result,
        )
        added_admission = True
    except BaseException:
        for snapshot_key in reversed(added_snapshots):
            self._future_snapshots.pop(snapshot_key, None)
        if added_admission:
            self._future_admissions.pop(quotient.semantic_identity.digest, None)
        if added_certificate:
            self._future_certificates.pop(certificate_profile, None)
        if added_class_key:
            self._future_class_keys.pop(behavior, None)
        if added_class_node:
            self._future_classes.pop(self._next_future_class - 1, None)
        if added_profile_key:
            self._future_profile_keys.pop(profile, None)
        if added_profile_node:
            self._future_profiles.pop(prospective_profile.local_id, None)
        for owner, entries, nodes in reversed(reservations):
            self.ledger.release(owner, entries=entries, nodes=nodes)
        raise
    self.ledger.bump(_behavior_keys.FUTURE_BEHAVIOR_NEW_CLASSES)
    return result


def lookup_quiescent_blank(
    self: DiamondQuotientArena,
    quotient: PrimitiveBehaviorQuotient,
) -> tuple[FutureBehaviorProfileID, FutureBehaviorClassID] | None:
    """Probe an admitted primitive profile without refinement or accounting."""
    if type(quotient) is not PrimitiveBehaviorQuotient:
        raise TypeError("quiescent admission requires a primitive behavior quotient")
    if type(quotient.semantic_identity) is not SemanticIdentity:
        raise TypeError("primitive behavior requires a semantic identity")
    admitted = self._future_admissions.get(quotient.semantic_identity.digest)
    if admitted is not None:
        authority, admitted_profile, admitted_behavior = admitted
        if not self._quotient_matches(quotient, authority):
            raise ValueError(
                "primitive behavior identity conflicts with its admitted authority"
            )
        self.resolve_future_profile(admitted_profile)
        self.resolve_future_behavior(admitted_behavior)
        self.future_certificate(admitted_profile)
        return admitted_profile, admitted_behavior
    return None


def rollback_quiescent_blank_admission(
    self: DiamondQuotientArena,
    quotient: PrimitiveBehaviorQuotient,
    profile: FutureBehaviorProfileID,
    behavior: FutureBehaviorClassID,
) -> None:
    """Undo one newly admitted profile after cross-arena publication fails.

    Callers may use this only when their read-only admission probe missed.
    Consumed profile and class integers deliberately remain consumed.
    """
    if type(quotient) is not PrimitiveBehaviorQuotient:
        raise TypeError("quiescent rollback requires a primitive behavior quotient")
    if type(profile) is not FutureBehaviorProfileID:
        raise TypeError("quiescent rollback requires a future behavior profile ID")
    if type(behavior) is not FutureBehaviorClassID:
        raise TypeError("quiescent rollback requires a future behavior class ID")
    current = self._future_admissions.get(quotient.semantic_identity.digest)
    if current is None or current[1:] != (profile, behavior):
        raise ValueError("future behavior admission changed before rollback")
    if not self._quotient_matches(quotient, current[0]):
        raise ValueError("future behavior admission authority changed before rollback")
    profile_record = self.resolve_future_profile(profile)
    behavior_record = self.resolve_future_behavior(behavior)
    self._future_admissions.pop(quotient.semantic_identity.digest)
    self.ledger.release(self._future_admission_owner, entries=1)
    remaining = tuple(self._future_admissions.values())
    if not any(item[2] == behavior for item in remaining):
        self._future_class_keys.pop(behavior_record)
        self._future_classes.pop(behavior.local_id)
        self._future_snapshots.pop(("class", behavior.local_id))
        self.ledger.release(self._future_class_key_owner, entries=1)
        self.ledger.release(self._future_class_owner, entries=1, nodes=1)
        self.ledger.release(self._future_snapshot_owner, entries=1)
    profile_is_used = any(item[1] == profile for item in remaining) or any(
        record.profile == profile for record in self._future_classes.values()
    )
    if not profile_is_used:
        self._future_certificates.pop(profile)
        self._future_snapshots.pop(("certificate", profile.local_id))
        self._future_profile_keys.pop(profile_record)
        self._future_profiles.pop(profile.local_id)
        self._future_snapshots.pop(("profile", profile.local_id))
        self.ledger.release(self._future_certificate_owner, entries=1)
        self.ledger.release(self._future_profile_key_owner, entries=1)
        self.ledger.release(self._future_profile_owner, entries=1, nodes=1)
        self.ledger.release(self._future_snapshot_owner, entries=2)
