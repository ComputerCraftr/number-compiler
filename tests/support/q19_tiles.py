"""Physical decimal sources with ordered Q19 U/V tiles and exact collars."""

_A = (1, 9, 5, 9, 1, 3, 7, 3)
_B = (1, 9, 5, 9, 5, 9, 1, 3, 7, 3)
U, V = _A + _A + _B + _A, _A + _B + _A + _A


def physical_seed(word: tuple[int, ...]) -> str:
    half = (17,) + word + (11,)
    low = [max(0, s - 9) for s in half]
    high = [s - d for s, d in zip(half, low, strict=True)]
    low[0], high[0] = 8, 9
    return "".join(map(str, low + high[::-1]))
