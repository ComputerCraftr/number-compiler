from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


def test_root_image_audits_and_owns_the_requested_innovation_tape() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(
        ledger,
        1,
        1002,
        retain_chronology=False,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    try:
        observation = workspace.innovation_observation
        assert observation is not None and observation.producer_issued
        assert observation.modulus == 49

        core = workspace.scheduler._source_image_core()
        view = core.view(workspace.root_image)
        innovation_ports = tuple(
            port
            for port in view.binding.boundary_ports
            if type(port) is tuple
            and len(port) == 3
            and port[0] == "collatz-global-signed-tape-v1"
        )
        assert len(innovation_ports) == 1
        port = innovation_ports[0]
        assert port[1] == view.payload
        assert port[2] == 49
        approved = workspace.audit_image_binding(view.binding, view.payload, None)
        assert approved == (port,)
        assert approved[0] is port

        identity_image = workspace.scheduler.source_image(
            workspace, workspace.root_source, workspace.identity
        )
        identity_view = core.view(identity_image)
        assert identity_view.binding.action == workspace.identity
        assert (
            workspace.audit_image_binding(
                identity_view.binding, identity_view.payload, None
            )
            == ()
        )

        wrong_modulus = (port[0], port[1], 51)
        forged_ports = tuple(
            wrong_modulus if candidate is port else candidate
            for candidate in view.binding.boundary_ports
        )
        with pytest.raises(ValueError, match="innovation"):
            workspace.audit_image_binding(
                replace(view.binding, boundary_ports=forged_ports),
                view.payload,
                None,
            )
    finally:
        workspace.dispose()
