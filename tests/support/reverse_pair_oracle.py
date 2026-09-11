"""Exact scalar reverse-pair oracle shared by independent tests."""


def reference_successor(full: tuple[int, ...], base: int) -> tuple[int, ...]:
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
