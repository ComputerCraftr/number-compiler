from number_compiler.arithmetic.automata.action_power import ActionPowerArena
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)


def test_action_power_composes_noncommuting_functions_in_chronological_order() -> None:
    mappings: list[tuple[int, ...]] = [(0, 1), (1, 0), (0, 0), (1, 1)]
    owner = ArenaToken("test-transformations")
    actions = tuple(
        ActionProgramID(owner, "test-program", i) for i in range(len(mappings))
    )

    def validate(action: ActionProgramID) -> int:
        return action.validate(owner, "test-program", size=len(mappings)).local_id

    def compose(before: ActionProgramID, after: ActionProgramID) -> ActionProgramID:
        return actions[
            mappings.index(
                tuple(mappings[validate(after)][x] for x in mappings[validate(before)])
            )
        ]

    arena = ActionPowerArena(actions[0], compose, validate=validate)
    assert arena.compose(actions[1], actions[2]) == actions[2]
    assert arena.compose(actions[2], actions[1]) == actions[3]
    assert arena.power(actions[1], 2**100) == actions[0]
    assert arena.power(actions[1], 2**100 + 1) == actions[1]
    assert arena.power(actions[2], 2**100) == actions[2]
    before = arena.metrics()
    assert arena.power(actions[1], 2**100) == actions[0]
    after = arena.metrics()
    assert after.power_hits == before.power_hits + 1
    assert after.composition_requests == before.composition_requests
    assert all(type(value) is int for key in arena._compositions for value in key)
