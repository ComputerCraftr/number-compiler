from number_compiler.sequences.collatz.pair import CollatzValuationState


def test_collatz_valuation_state_is_exact_action_and_shift_phase() -> None:
    for value in range(1, 4096, 2):
        state = CollatzValuationState.from_odd_value(value)
        target = (3 * value + 1) >> state.valuation
        assert state.apply(value) == target
        assert state.increases == (target > value)
        for order in (1, 2, 3, 4, 5, 8, 13):
            assert state.shift_phase(order) == state.valuation % order
        assert state.projection.odd_steps == 1
        assert state.projection.valuation_sum == state.valuation


def test_collatz_valuation_state_is_not_mislabeled_closed() -> None:
    # k=1 occurs at both sources, but the next accelerated valuation differs.
    found: dict[tuple[object, ...], tuple[object, ...]] = {}
    conflict = None
    for value in range(1, 20000, 2):
        current = CollatzValuationState.from_odd_value(value)
        nxt_value = current.apply(value)
        nxt = CollatzValuationState.from_odd_value(nxt_value)
        old = found.get(current.canonical_key)
        if old is not None and old != nxt.canonical_key:
            conflict = (value, current, nxt)
            break
        found[current.canonical_key] = nxt.canonical_key
    assert conflict is not None
