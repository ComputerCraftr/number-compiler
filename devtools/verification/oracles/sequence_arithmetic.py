"""Bounded literal sequence oracles, independent of compiled production actions."""


def reference_successor(full: tuple[int, ...], base: int = 10) -> tuple[int, ...]:
    d = len(full)
    carry = [0] * (d + 1)
    for i, value in enumerate(full):
        carry[i + 1] = int(value + carry[i] >= base)
    reverse = [carry[d - i] for i in range(d + 1)]
    if not carry[d]:
        return tuple(
            2 * full[i] + carry[i] + reverse[i + 1] - base * (carry[i + 1] + reverse[i])
            for i in range(d)
        )
    out = [0] * (d + 1)
    out[0] = full[0] + 1 - base * carry[1]
    out[d] = out[0]
    for i in range(1, d):
        out[i] = (
            full[i]
            + full[i - 1]
            + carry[i]
            + reverse[i]
            - base * (carry[i + 1] + reverse[i - 1])
        )
    return tuple(out)


def collatz_literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = 3 * value + 1 if value & 1 else value // 2
    return value


def reverse_add_literal(seed: int, steps: int) -> int:
    """Compute a bounded decimal reverse/add prefix without production code."""
    value = seed
    for _ in range(steps):
        value += int(str(value)[::-1])
    return value
