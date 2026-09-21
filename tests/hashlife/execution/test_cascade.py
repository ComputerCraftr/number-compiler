from devtools.experiments.reverse_add.cascade import DependencyCascadeArena


def test_dependency_cascade_is_exact_and_hash_cons_suffixes() -> None:
    arena = DependencyCascadeArena(3)
    rows = {(0, 0, 1), (0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 0, 2)}
    a = arena.encode(rows)
    b = arena.encode(reversed(tuple(rows)))
    assert a.root == b.root
    assert set(arena.iter_tuples(a)) == rows
    for row in rows:
        assert arena.contains(a, row)
    assert not arena.contains(a, (1, 1, 2))
    m = arena.metrics()
    assert m.dependency_nodes < len(rows) * 3
    assert m.relations == 1


def test_grouped_dependency_cascade_merges_equal_child_fibers() -> None:
    from devtools.experiments.reverse_add.cascade import GroupedDependencyCascadeArena

    rows = {(x, 0, 1) for x in range(32)} | {(x, 1, 2) for x in range(32)}
    a = GroupedDependencyCascadeArena(3)
    r = a.encode(rows)
    assert set(a.iter_tuples(r)) == rows
    m = a.metrics()
    # A value-by-value trie needs >=64 first two-level edges; grouping equal
    # suffix dependencies should be materially smaller.
    assert m.dependency_edges < 20


def test_grouped_cascade_boxes_are_exact_without_cartesian_expansion() -> None:
    from devtools.experiments.reverse_add.cascade import GroupedDependencyCascadeArena

    a = GroupedDependencyCascadeArena(3)
    # {0..63} x {2,3} x {7..10} is 512 tuples but one dependency box.
    box = ((1 << 64) - 1, (1 << 2) | (1 << 3), sum(1 << i for i in range(7, 11)))
    r = a.encode_boxes((box,))
    assert r.cardinality == 64 * 2 * 4
    boxes = list(a.iter_boxes(r))
    assert len(boxes) == 1 and boxes[0] == box
    m = a.metrics()
    assert m.dependency_edges <= 3
