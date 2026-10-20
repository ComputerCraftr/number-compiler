"""Typed access to private fixtures at deliberate test inspection boundaries."""

from typing import cast


def private_test_attribute(owner: object, name: str) -> object:
    """Retain normal descriptor binding when inspecting a private test hook."""
    return cast(object, getattr(owner, name))


def set_private_test_attribute(owner: object, name: str, value: object) -> None:
    """Exercise the owner's normal attribute-assignment checks in a test."""
    setattr(owner, name, value)
