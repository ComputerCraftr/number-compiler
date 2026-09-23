"""An exact sequence request exceeds its checked mathematical boundary."""


class UnresolvedSequenceTerm(Exception):
    def __init__(
        self,
        index: int,
        certified_max_index: int,
        certificate_id: str,
        reason: str,
    ) -> None:
        self.index = index
        self.certified_max_index = certified_max_index
        self.certificate_id = certificate_id
        self.reason = reason
        super().__init__(reason)

    def diagnostic(self) -> dict[str, object]:
        return {
            "code": "unresolved_sequence_boundary",
            "requested_index": self.index,
            "certified_max_index": self.certified_max_index,
            "certificate_id": self.certificate_id,
            "reason": self.reason,
        }
