"""Verify published bytes and compare all final PDF pages to reviewed images."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys

BASE = Path(__file__).resolve().parent
OUTPUT = BASE.parents[1] / "outputs/frontier20261020"
sys.path.insert(0, "/home/user/.codex/skills/superresearch-x2/scripts")
from native_research import load_json, validate_review_bundle


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reports = OUTPUT / "research-report"
    receipt = load_json(OUTPUT / "research-report.publication.json")
    manuscript = (reports / "report.md").read_bytes()
    validation = validate_review_bundle(
        load_json(OUTPUT / "review/review-bundle.json"), manuscript)
    assert validation["valid"] and validation["publication_eligible"]
    assert receipt["status"] == "published"
    assert receipt["manuscript_sha256"] == hashlib.sha256(manuscript).hexdigest()
    assert receipt["review_bundle_sha256"] == validation["bundle_sha256"]
    assert receipt["contract_sha256"] == validation["contract_sha256"]
    assert {p.name for p in reports.iterdir()} == {"report.md", "report.html", "report.pdf"}
    for name, record in receipt["artifacts"].items():
        assert sha(reports / name) == record["sha256"]
        assert (reports / name).stat().st_size == record["bytes"]
    assert manuscript == (BASE / "manuscript/research-draft.md").read_bytes()
    images = BASE / "final-visual-qa"
    images.mkdir(exist_ok=False)
    subprocess.run(["pdftoppm", "-scale-to", "1500", "-png",
                    str(reports / "report.pdf"), str(images / "page")],
                   check=True, timeout=60)
    preview = BASE / "preview" / receipt["manuscript_sha256"][:12]
    expected = receipt["renderer"]["validation"]["page_count"]
    actual = sorted(images.glob("page-*.png"))
    assert len(actual) == expected
    pages = [{"page": n, "png_sha256": sha(images / f"page-{n}.png"),
              "identical_to_visually_inspected_preview":
                  (preview / f"page-{n}.png").is_file()
                  and sha(images / f"page-{n}.png") == sha(preview / f"page-{n}.png")}
             for n in range(1, expected + 1)]
    result = {
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "publication": "all three artifact hashes and exact manuscript bytes match",
        "review_validation": validation,
        "pages": pages,
        "visual_status": ("all final page images byte-identical to previously inspected preview"
                          if all(p["identical_to_visually_inspected_preview"] for p in pages)
                          else "actual final page inspection required"),
        "limitations": ["Local byte and visual checks do not establish independent human certification."]
    }
    (OUTPUT / "delivery-verification.json").write_text(json.dumps(result, indent=2) + "\n")
    manifest = [{"path": str(p.relative_to(OUTPUT)), "bytes": p.stat().st_size, "sha256": sha(p)}
                for p in sorted(OUTPUT.rglob("*"))
                if p.is_file() and p != OUTPUT / "file-manifest.json"]
    (OUTPUT / "file-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
