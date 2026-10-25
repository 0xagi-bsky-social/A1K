#!/usr/bin/env python3
"""Bounded exact normalized-token overlap; no global originality inference."""
import argparse
import hashlib
import json
import re
import unicodedata
from pathlib import Path

def digest(data):
    return hashlib.sha256(data).hexdigest()

def tokens(text):
    text = re.sub(r"\ue200.*?\ue201", " ", text, flags=re.S)
    text = re.sub(r"https?://[^\s)]+", " ", text)
    return re.findall(r"\w+", unicodedata.normalize("NFKC", text).casefold())

def numbered_segments(text):
    # Keep only returned page lines; do not join across omitted line ranges.
    parts = re.split(r"L(\d+):", text)
    segments, current, first, last = [], [], None, None
    for i in range(1, len(parts), 2):
        n = int(parts[i])
        body = parts[i + 1].split("\n--------------------------------------------------------------------------------")[0]
        if last is not None and n != last + 1:
            segments.append((first, last, tokens(" ".join(current))))
            current, first = [], None
        if first is None:
            first = n
        current.append(body)
        last = n
    if current:
        segments.append((first, last, tokens(" ".join(current))))
    return segments

def matches(a, b, threshold):
    index = {}
    for j in range(len(b) - threshold + 1):
        index.setdefault(tuple(b[j:j + threshold]), []).append(j)
    output = []
    for i in range(len(a) - threshold + 1):
        for j in index.get(tuple(a[i:i + threshold]), []):
            if i > 0 and j > 0 and a[i - 1] == b[j - 1]:
                continue
            size = threshold
            while i + size < len(a) and j + size < len(b) and a[i + size] == b[j + size]:
                size += 1
            output.append({"manuscript_token_start": i, "source_token_start": j,
                           "token_count": size, "normalized_match": " ".join(a[i:i + size])})
    return output

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("snapshot")
    parser.add_argument("output")
    args = parser.parse_args()
    snapshot_path = Path(args.snapshot)
    wrapper = json.loads(snapshot_path.read_text())
    snapshot = wrapper["snapshot"]
    canonical = json.dumps(snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    assert digest(canonical) == wrapper["snapshot_sha256"]
    manuscript_path = snapshot_path.with_name("manuscript.md")
    manuscript_bytes = manuscript_path.read_bytes()
    assert digest(manuscript_bytes) == snapshot["manuscript_sha256"]
    manuscript_tokens = tokens(manuscript_bytes.decode())
    results = []
    for item in snapshot["evidence"]:
        if item["id"] not in {"F16", "F17"}:
            continue
        raw = Path(item["locator"]).read_bytes()
        assert digest(raw) == item["content_sha256"]
        payload = json.loads(raw)
        assert isinstance(payload, str)
        segments = numbered_segments(payload)
        found = []
        for segment_index, (start, end, words) in enumerate(segments):
            for match in matches(manuscript_tokens, words, 8):
                match.update(segment_index=segment_index, source_line_range=[start, end])
                found.append(match)
        unique = sorted({m["normalized_match"] for m in found}, key=lambda x: (-len(x.split()), x))
        results.append({"evidence_id": item["id"], "locator": item["locator"],
                        "sha256": digest(raw), "source_segments": len(segments),
                        "source_tokens_including_repeated_excerpts": sum(len(x[2]) for x in segments),
                        "maximal_match_occurrences": len(found), "unique_matched_passages": unique,
                        "matches": found})
    result = {"manuscript_sha256": digest(manuscript_bytes),
              "snapshot_sha256": wrapper["snapshot_sha256"],
              "script_sha256": digest(Path(__file__).read_bytes()),
              "method": "NFKC casefolded word tokens; remove citation artifacts and URLs; exact maximal contiguous matches of at least eight tokens; primary excerpt line ranges are not joined across gaps; duplicate excerpts remain separately counted.",
              "corpus": "Only frozen F16 and F17 returned arXiv/A1K primary-source excerpts; no web-wide, semantic-paraphrase, or global originality test.",
              "manuscript_tokens": len(manuscript_tokens), "results": results}
    Path(args.output).write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"manuscript_sha256": result["manuscript_sha256"],
                      "results": [{k: r[k] for k in ("evidence_id", "source_segments", "source_tokens_including_repeated_excerpts", "maximal_match_occurrences", "unique_matched_passages")} for r in results]}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()
