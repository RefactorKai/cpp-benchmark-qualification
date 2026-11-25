"""Minimal stdlib registration validator imported by pinned predict.py CLI."""

from __future__ import annotations

from typing import Any


def validate_committed_draw(registration: dict[str, Any]) -> None:
    """Validate required top-level fields of a committed draw registration."""
    if not isinstance(registration, dict):
        raise ValueError("registration must be a JSON object")
    for field in ("phase", "pins", "cases"):
        if field not in registration:
            raise ValueError(f"registration missing required field: {field}")
    if not isinstance(registration["pins"], dict) or "methods" not in registration["pins"]:
        raise ValueError("registration.pins must include 'methods'")
    if not isinstance(registration["cases"], list) or not registration["cases"]:
        raise ValueError("registration.cases must be a non-empty list")
