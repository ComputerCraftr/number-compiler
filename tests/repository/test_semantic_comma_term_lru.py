"""Bounded completed-proof cache integration regressions."""

from devtools.paths import isabelle_root, repository_root


def test_occurrence_cache_replaces_completed_facts_within_shared_bound() -> None:
    """Capacity exhaustion must not permanently freeze completed proof reuse."""
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    cache = (root / "semantic_b1_term_lru.ML").read_text(encoding="utf-8")
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    publication = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text(
        encoding="utf-8"
    )
    assert publication.index('ML_file "semantic_b1_term_lru.ML"') < publication.index(
        'ML_file "semantic_b1_occurrence_check_cache.ML"'
    )
    assert "val memo_capacity = 8192" in checker
    assert "Term_LRU.insert_completed memo request theorem" in checker
    assert "Term_LRU.lookup memo request" in checker
    assert "Term_LRU.clear memo" in checker
    dispatch = checker.split("fun memo_proc context ct =", 1)[1].split("val proc =", 1)[
        0
    ]
    assert dispatch.index(
        "#lookup_equation certificate_store request"
    ) < dispatch.index("Term_LRU.contains_partial memo request")
    assert "memo_evictions=" in checker
    assert "Synchronized.change_result" in cache
    assert "Termtab.size (#values old1) + Termtab.size partials1" in cache
    assert "else evict_state old1" in cache
    assert "Termtab.delete_safe key (#partials old)" in cache
    assert "touch_state key old" in cache
    # Load-time fixtures exercise the actual helper, including refreshed LRU
    # order, missing keys, shared negative capacity and negative-to-positive reuse.
    assert "val _ = Comma_Semantic_B1_Term_LRU.check_fixture ()" in cache
    for check in (
        "lookup cache b = NONE",
        "lookup cache a = NONE",
        "completed_size cache = 2",
        "evictions cache = 2",
        "not (remember_partial partial_only c)",
        "not (contains_partial partial_only a)",
        "partial_size partial_only = 1",
    ):
        assert check in cache
