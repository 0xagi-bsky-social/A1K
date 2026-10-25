"""Reproduce the exact top-three-star numerical leaf.

This script is a diagnostic.  SupportGrid.lean independently checks the
universal 20^3 finite grid by ordinary kernel-reduced `decide`.
"""
import hashlib
import json
from pathlib import Path

rows = []
for a in range(20):
    for b in range(20):
        for c in range(20):
            if not (1 <= c <= b <= a <= 19 and a+b <= 34 and a+b+c <= 46):
                continue
            ell = max(0, a+b+c-28)
            envelope = 55*c + (a-c)*(a-1) + (b-c)*(b-1)
            score = 3*envelope - ell*ell + 3*ell
            rows.append((score, a, b, c, ell, envelope))
maximum = max(row[0] for row in rows)
report = {
    "assurance": "certificate-diagnostic",
    "grid_size_before_hypotheses": 20**3,
    "admissible_grid_points": len(rows),
    "maximum": maximum,
    "maximizers": [dict(zip(["score", "a", "b", "c", "ell", "envelope"], row))
                   for row in rows if row[0] == maximum],
    "contradiction_requires_at_least": 2262,
    "margin": 2262-maximum,
    "claim_limit": "Finite numerical leaf, not by itself a family-support theorem.",
}
print(json.dumps(report, indent=2))
