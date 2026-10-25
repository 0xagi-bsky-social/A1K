#!/usr/bin/env python3
"""Preservation replay of the round-5 Git tree check.

Written after the round-5 vote; this is reconstructed executable documentation
of the recorded algorithm, not a claim that the original transient code or fresh
nonrecursive network response was recovered. No network or object-database writes.
"""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "h27-tree-tool-result.original.json"


def git_tree_payload(entries):
    def sort_key(entry):
        name = entry["path"].rsplit("/", 1)[-1].encode()
        return name + (b"/" if entry["type"] == "tree" else b"")

    result = bytearray()
    for entry in sorted(entries, key=sort_key):
        mode = entry["mode"].lstrip("0")
        name = entry["path"].rsplit("/", 1)[-1]
        result.extend((mode + " " + name).encode() + b"\0")
        result.extend(bytes.fromhex(entry["sha"]))
    return bytes(result)


def object_sha(payload):
    header = b"tree " + str(len(payload)).encode() + b"\0"
    return hashlib.sha1(header + payload).hexdigest()


def main():
    original = SOURCE.read_bytes()
    wrapper = json.loads(original)
    response = json.loads(wrapper["value"]["result"]["structuredContent"]["content"])
    entries = response["tree"]
    directories = {"": response["sha"]}
    directories.update({e["path"]: e["sha"] for e in entries if e["type"] == "tree"})
    results = []
    root_payload = None
    for directory, declared_sha in directories.items():
        children = [e for e in entries if e["path"].rpartition("/")[0] == directory]
        payload = git_tree_payload(children)
        computed_sha = object_sha(payload)
        results.append({
            "path": directory or ".", "direct_children": len(children),
            "declared_sha1": declared_sha, "computed_sha1": computed_sha,
            "matches": declared_sha == computed_sha, "payload_bytes": len(payload),
        })
        if directory == "":
            root_payload = payload
    git_sha = subprocess.run(
        ["git", "hash-object", "-t", "tree", "--stdin"], input=root_payload,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    ).stdout.decode().strip()
    result = {
        "kind": "preservation_replay_after_round_5_vote",
        "source_sha256": hashlib.sha256(original).hexdigest(),
        "listed_entries": len(entries), "truncated": response.get("truncated"),
        "provenance_path_matches": [e["path"] for e in entries if "provenance" in e["path"].lower()],
        "trees": results,
        "root_git_hash_object_sha1": git_sha,
        "root_python_matches_git": results[0]["computed_sha1"] == git_sha,
        "nonroot_match_count": sum(r["matches"] for r in results[1:]),
        "nonroot_tree_count": len(results) - 1,
        "fresh_nonrecursive_response_preserved": False,
        "limitation": "Original fresh nonrecursive response and original transient reconstruction code were not recoverable after context transition. This result replays the recorded algorithm on the already-preserved recursive response; it is not a new network observation or review vote.",
    }
    (HERE / "root_tree_payload.bin").write_bytes(root_payload)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
