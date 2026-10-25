"""Publish only the actually accepted manuscript and its preserved evidence."""
from pathlib import Path
import hashlib
import json
import shutil
import sys

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
sys.path.insert(0, "/home/user/.codex/skills/superresearch-x2/scripts")
from native_research import load_json, validate_review_bundle
from native_publication import publish_local
from render_report import renderer


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def main():
    research_status = BASE / "research-status.json"
    if research_status.exists():
        status = load_json(research_status)
        if status.get("status") != "research-target-met-publication-gate-open":
            raise RuntimeError("Research admission is closed: " + status["status"])
    manuscript = (BASE / "manuscript/research-draft.md").read_bytes()
    bundle = load_json(BASE / "review/review-bundle.json")
    validation = validate_review_bundle(bundle, manuscript)
    if not validation.get("valid") or not validation.get("publication_eligible"):
        raise RuntimeError("Actual final review is not publication eligible: " + str(validation))
    destination = ROOT / "outputs/frontier20261020"
    destination.mkdir(exist_ok=False)
    shutil.copytree(BASE / "release-formal", destination / "formal")
    shutil.copytree(BASE / "review", destination / "review")
    evidence = destination / "evidence"
    evidence.mkdir()
    for name in ["contract.json", "review-admission.json",
                 "primary-source-check-20261020.json", "amendment-two-star.json",
                 "render_report.py", "render_custom_preview.py",
                 "prepare_formal_bundle.py", "rebuild_closure.py"]:
        shutil.copy2(BASE / name, evidence / name)
    for branch in ["formal", "theory", "compute", "root_proofs"]:
        if (BASE / branch / "receipts").is_dir():
            shutil.copytree(BASE / branch / "receipts", evidence / f"{branch}-receipts")
    diagnostics = evidence / "exploratory-diagnostics"
    diagnostics.mkdir()
    for relative in [
        "compute/universal_two_star.py", "compute/universal_two_star.json",
        "compute/universal_two_star.stdout", "compute/universal45-coverage-notes.md",
        "compute/sharp45_witness.json", "compute/encoding.json",
        "compute/cadical-relax.log", "b_universal_check.cpp",
        "b_universal_check.json", "b_universal_data.py", "b_universal_data.txt",
        "root_proofs/Sharp45.lean", "root_proofs/ComponentCertificate.lean",
        "formal/two-star-incidence-research.md",
        "formal/two-star-incidence-diagnostics.json",
    ]:
        source = BASE / relative
        target = diagnostics / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    digest = hashlib.sha256(manuscript).hexdigest()
    preview = BASE / "preview" / digest[:12]
    for name in ["custom-rendering.json", "visual-review-root.json", "visual-review.json"]:
        if (preview / name).is_file():
            shutil.copy2(preview / name, evidence / ("accepted-preview-" + name))
    receipt = publish_local(bundle, manuscript, destination, "research-report", renderer=renderer)
    if receipt["status"] != "published":
        dump(destination / "publication-delivery-status.json", receipt)
        raise RuntimeError("Publication requires attention: " + receipt["status"])
    for name, record in receipt["artifacts"].items():
        data = (destination / "research-report" / name).read_bytes()
        assert hashlib.sha256(data).hexdigest() == record["sha256"]
        assert len(data) == record["bytes"]
    assert (destination / "research-report/report.md").read_bytes() == manuscript
    readme = f"""# Rank-four sunflower research: upper eighty endpoint

The accepted report is in `research-report/`: Markdown, HTML and PDF.
Manuscript SHA256: `{digest}`.

The formal conclusion is I(27) implies G(80). The two formerly open actual
81-member boundary profiles are excluded. An additional unconditional
structural theorem bounds families with two distinct noncooccurring
degree-twenty points by 80, on unrestricted finite supports.

The ordinary corollary 54 <= f(4,3) <= 80 applies the explicitly external
computer-assisted I(27) theorem in arXiv:2609.06175v1. That external
enumeration is not locally kernel checked. The general sunflower
conjecture, global priority and an unconditional local Lean G(80) theorem
are not claimed.

`formal/` contains 161 source modules, source hashes, the actual build
and axiom receipts, and a pinned rebuild recipe. Assurance: axiom-audited;
63 modules freshly compiled and 98 source-matched prior successful
rebuilds reused. This is not independent reproduction.

`review/` preserves the actual twelve specialist contexts' ten rounds,
separate final Chief/Alpha/Beta audits and the native review validation.
These are autonomous agent reviews in one orchestration environment,
not independent human certification.

`evidence/` retains search provenance, original proof receipts, rendering
checks and explicitly exploratory computations including failed attempts.
Diagnostic cap 45 is not an established theorem.

`research-report.publication.json` binds the reviewed manuscript, review
bundle, contract and the three actual output files by SHA256. Local
publication does not upload this work to any external service.
"""
    (destination / "README.md").write_text(readme)
    manifest = []
    for path in sorted(destination.rglob("*")):
        if path.is_file():
            content = path.read_bytes()
            manifest.append({"path": str(path.relative_to(destination)),
                             "bytes": len(content),
                             "sha256": hashlib.sha256(content).hexdigest()})
    dump(destination / "file-manifest.json", manifest)
    print(json.dumps({"status": receipt["status"],
                      "directory": str(destination),
                      "manuscript_sha256": digest,
                      "review": validation,
                      "artifact_count": len(receipt["artifacts"])}, indent=2))


if __name__ == "__main__":
    main()
