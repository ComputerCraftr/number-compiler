from number_compiler.hashlife.actions.jump import StrictBinaryRootBuilder


class JumpBackend:
    def seed_root(self) -> int:
        return 0

    def jump_bit(self, prefix_index: int, root: int, bit: int) -> int:
        return 2 * root + bit


def test_binary_driver_has_no_scale_backend() -> None:
    builder = StrictBinaryRootBuilder(JumpBackend())
    assert set(builder.__slots__) == {"jump_backend"}
    for n in (0, 1, 2, 3, 7, 255, 1025):
        got = builder.root_at(n)
        assert got.root == n
        assert got.jump_calls == (0 if n == 0 else n.bit_length())
        assert got.audit.clean
