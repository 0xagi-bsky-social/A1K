#!/usr/bin/env python3
"""Check the archived Lean source inventory without invoking Lean.

The CSV is an unsigned content commitment. This checks consistency with that
commitment; it does not authenticate the publisher or verify any proof.
"""

from pathlib import Path
import csv
import hashlib
import json
import re
import sys


def fail(message: str) -> None:
    raise ValueError(message)


def repository_file(repo: Path, relative: str) -> Path:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        fail(f"Unsafe inventory path: {relative}")
    if not path.parts or path.parts[0] != "erdos_20":
        fail(f"Source outside erdos_20: {relative}")
    target = repo / path
    if target.is_symlink() or not target.is_file():
        fail(f"Missing or symbolic source: {relative}")
    if not target.resolve().is_relative_to(repo.resolve()):
        fail(f"Source escapes repository: {relative}")
    return target


def main() -> None:
    repo = Path(__file__).resolve().parents[2]
    index = repo / "erdos_20/indexes/lean-source-files.csv"
    with index.open(newline="", encoding="utf-8") as source:
        rows = list(csv.DictReader(source))
    if len(rows) != 348:
        fail(f"Expected 348 shipped source instances; found {len(rows)}")

    expected = set()
    for row in rows:
        relative = row["repository_path"]
        if relative in expected:
            fail(f"Duplicate inventory entry: {relative}")
        expected.add(relative)
        path = repository_file(repo, relative)
        data = path.read_bytes()
        if len(data) != int(row["size_bytes"]):
            fail(f"Size mismatch: {relative}")
        if hashlib.sha256(data).hexdigest() != row["sha256"]:
            fail(f"SHA-256 mismatch: {relative}")

    actual = {str(path.relative_to(repo)) for path in
              (repo / "erdos_20").rglob("*.lean")}
    if actual != expected:
        fail(f"Inventory mismatch: missing {sorted(expected - actual)}; "
             f"extra {sorted(actual - expected)}")

    reference_index = repo / "erdos_20/indexes/reference-links.csv"
    with reference_index.open(newline="", encoding="utf-8") as source:
        references = list(csv.DictReader(source))
    if len(references) != 21:
        fail(f"Expected 21 linked references; found {len(references)}")
    original_paths = {row["original_relative_path"] for row in rows}
    reference_paths = set()
    for row in references:
        original = row["original_relative_path"]
        if original in original_paths or original in reference_paths:
            fail(f"Duplicate original source entry: {original}")
        reference_paths.add(original)
        if row["role"] != "external-author-reference":
            fail(f"Unexpected reference role: {original}")
        commit = row["upstream_commit"]
        upstream_path = Path(row["upstream_path"])
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            fail(f"Invalid pinned upstream revision: {original}")
        if upstream_path.is_absolute() or ".." in upstream_path.parts:
            fail(f"Unsafe upstream reference path: {original}")
        expected_url = ("https://github.com/bogdan27182/sunflower-paper/blob/"
                        f"{commit}/{upstream_path}")
        if row["url"] != expected_url or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"]):
            fail(f"Malformed upstream reference commitment: {original}")
        if (repo / row["former_repository_path"]).exists():
            fail(f"Upstream reference was unexpectedly copied: {original}")
    if len(original_paths | reference_paths) != 369:
        fail("The shipped and linked inventories do not account for all 369 original sources")

    # The original protected v13 manifest also binds five non-source inputs.
    project = repo / "erdos_20/v13/lean"
    manifest = json.loads((project / "source_manifest.json").read_text())
    for relative, digest in manifest.items():
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts:
            fail(f"Unsafe protected-manifest path: {relative}")
        target = project / path
        if not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest() != digest:
            fail(f"Protected v13 input mismatch: {relative}")

    production = sum(row["role"] == "latest-production" for row in rows)
    if production != 155:
        fail(f"Expected 155 production modules; found {production}")
    print(f"Verified {len(rows)} Lean source files, including {production} v13 modules.")
    print(f"Checked {len(references)} pinned reference links; all 369 original sources are accounted for.")
    print(f"Verified {len(manifest)} original protected v13 inputs.")
    print("Lean compilation, proof verification and remote reference retrieval were not run.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"Inventory verification failed: {error}", file=sys.stderr)
        sys.exit(1)
