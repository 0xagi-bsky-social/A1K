# H27 computational-source scope: corrected inspection boundary

24 October 2026. This additive source-audit note supersedes the archive-authentication wording in the H27 section of `highdegree/EXTERNAL-H27-JIN-SCOPE.md`. The frozen earlier note remains intact. It does not change the statement of Proposition 6.7, its ordinary mathematical use, or the distinction between H27 and the new local predicates.

## Actual retrieved material

During round-four review, the literature reviewer fetched the authors' H27 supplement. The parent independently retrieved the same README and shell-script blobs and the complete tracked repository tree through the GitHub connector at approximately 10:00 UTC. Three ordinary web opens had failed with a cache miss; they did not establish file contents. The connector returned:

- README Git blob `db9b1966f961156b0c7e4b8b158f9e171cddd33b`.
- `check_archived_run.sh` Git blob `d3b4ae7f1a2abce5561c3d033bd5e0a04744c17a`.
- Untruncated Git tree `d4d5723267c662291efdadfa6e7061d919e76fa9`, with 117 entries.
- HTTP 404 for the README's named `PROVENANCE.md` path. No case-insensitive provenance path appears among those tracked tree entries.

Both retrieved text contents independently reproduce their Git blob SHA1 commitments. Their SHA256 hashes, actual tool results and the tree result are preserved in `review67/research-r4/h27-source-inspection-manifest.json`. These are local integrity comparisons, not proof of a source-to-historical-execution relationship. Compressed archive contents and other historical repository states were not inspected in this source check; no absence within such material is inferred.

Primary locations: [README](https://github.com/bogdan27182/sunflower-paper/blob/main/artifacts/f43_upper_83/intersecting_27/README.md), [shell audit script](https://github.com/bogdan27182/sunflower-paper/blob/main/artifacts/f43_upper_83/intersecting_27/check_archived_run.sh), and [unavailable provenance pointer](https://github.com/bogdan27182/sunflower-paper/blob/main/artifacts/f43_upper_83/intersecting_27/PROVENANCE.md). The blob and tree identifiers above pin the material actually inspected rather than treating the moving main branch as immutable.

## Corrected distinction

The README says its procedure checks three frozen archive hashes and directs readers to the unavailable provenance file for the source-to-run trust boundary. The inspected top-level script does not explicitly compare hashes of those three compressed archives. It extracts the archives, invokes a C run-record verifier, compares two assembled frontier hashes with a specified value, invokes small independent controls, compiles a current source executable and runs small historical/current executable controls. This is source inspection of visible operations; none of those programs was executed for the present check, and it is not an audit of every invoked C predicate.

Accordingly, the earlier phrase that the checker authenticates archives is too broad and is withdrawn. The inspected materials support a description of intended frontier/run-record and small-control checking, with an unresolved source-to-historical-run provenance inspection gap. They do not support a claim that this project authenticated the original compressed archives, matched the whole historical execution to reviewed source, or reran the target-28 exhaustion. The external upper-bound computation is a historical exhaustive-search ledger, not a compact locally checked unsatisfiability certificate.

H27 remains the explicitly cited external computer-assisted theorem of Axante et al., Proposition 6.7. The present work does not independently re-establish it. The new degree-case and coefficient checks do not supply the missing external provenance. No counterexample to H27 or error in its mathematical statement has been established by this inspection. Publication and assurance wording must retain both the ordinary theorem dependency and the specific access/inspection limitation.

## Timing and sensitivity

This is a source-audit update obtained during review, after the literature novelty-search cutoff of 07:57:31 UTC. It does not retroactively enlarge that search or assert a later exhaustive priority check. The new information is exposed prospectively to the following complete review round.

The imported numerical value matters: with an intersecting cap h, the common neighbourhood lower bound at 68 becomes 68-h. In the direct A3 argument, the same deficit calculation gives a[i] at least 136-5h. Thus h=27 supplies neighbourhood 41 and positive fibres, while h=28 supplies only 40 and a lower bound -4. The existing argument cannot simply replace H27 by a weaker cap; no such robustness is claimed.
