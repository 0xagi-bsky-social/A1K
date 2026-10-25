# Degree-20 working proof check

23 October 2026. This is a bounded check of a research leaf, not a final review
or publication step. Inspected `internal-proof.md`, `stage2-proof.md`,
`check_stage2_certificates.py`, and `stage2-certificates.json`, with the cited
frozen trace-foundations and D20 sources. No heavy computation was rerun.

## Current finding

No invalid projection, lost multiplicity, missing marker orbit, actual-anchor
failure, sunflower-distinctness failure, hidden neighbourhood threshold, or
circular use of the large-singleton `k=5` conclusion was found in the stage-two
argument. The prospective theorem remains conditional on the imported universal
structure and H27. The upstream finite classification is not independently
re-proved by this check, and the finite coefficient covers are not Lean replay.

The existing `local51-geometry-check.md` identifies one citation precision issue
in the internal-member stage: the degree-18 part of `s≤7 ⇒ d≤17` needs the
paper's universal `lem:r16maximal` (`paper/main.tex:612–636`), not just section E
of `TRACE_FOUNDATIONS.md`, which expressly discusses degrees at least 19.
That named high-link lemma supplies the needed mathematical premise. This is
not a new mu hypothesis.

## Projection, multiplicity, and distinctness

For markers without an exterior point, the projected universe is all twelve
link points. For the other three marker types it also includes their actual
exterior point 12. Thus it contains the entire marker and every link block;
the omitted distinguished cone point x is absent from every residual.
Consequently all expressions `Q∩M`, `Q∩T`, exact anchor traces, point/pair/triple
incidences, and residual degrees occurring in the certificates are determined
by the projection. Additional exterior points cannot alter a coefficient or
the three intersections used for a blocking sunflower.

The covering inequality is summed over actual residual members, retaining
multiplicities of proper projected traces. It requires no injectivity of the
projection. A trace of size four denotes exactly one possible residual by
four-uniformity and simplicity. In particular the marked residual contributes
its bonus `q(M)-L` once. There is no assumption that every admissible trace is
realized or realizable.

A blocking cone is distinct from the two residuals because it contains x.
If the residual is M itself, the test would require `T∩M=M`, impossible for a
three-element T and four-element M. Thus the checker never excludes M by a
degenerate sunflower. Internal exclusions remove only four-element subsets of
one whole component, after the internal-member lemma has been established.

## Actual anchors and local inequalities

Every ordinary exact-trace row has an anchor in the fixed cone list or equal
to the marked residual. Its exact trace is a proper subset of that actual
anchor. The standard capacities 10,3,1 therefore apply: removing the trace
leaves an intersecting sunflower-free residual family, because two disjoint
residual sets would form a sunflower with the anchor. Fixed-cone contributions
are subtracted in the ordinary row list. Local exact pair/triple rows use
weaker unsubtracted bounds, which remain valid.

The singleton-at-most-seven rows are used only on central anchors. For any
index y involved, the marker meets that anchor in a pair or triple through y;
this is explicitly checked in the certificate reader. The marker therefore
adds a member to K_y, rather than to the disjoint singleton part of the link.
It is distinct from the five prescribed members because it avoids x.

There is no circularity in `large singleton ⇒ k=5`. Before these rows are used,
the independent internal-member stage has eliminated every internal four-set
from a putative family of size at least 68. B4 then makes K_y intersecting.
It contains the five prescribed triples `{x}∪E`, where E runs over the C5
edges in the component of y. Any further triple containing x would enlarge
the already complete degree-20 link of x, which is impossible. A further
triple avoiding x must meet every edge E. Since C5 has vertex-cover number
three, all three points of that triple belong to the five cycle vertices;
adjoining y gives an internal four-set, already excluded. Hence K_y consists
of exactly the five prescribed triples. The marker would give a sixth, so its
presence forces the singleton class below eight.

The E04 mixed-sign row follows directly from `a≥1` and
`a+c+e+s≤10`: `c+s-9(a+e)≤10-10(a+e)≤0`. The first condition comes from the
actual marker; the second is the post-internal-removal residual degree bound
at point 7. No local signature or neighbourhood bound enters.

## Symmetry and the ordinary endgame

The component signature minimizes over the full P10 automorphism group.
Independent signatures in Y and Z, sorted to allow component interchange,
therefore classify exactly the relevant product-group orbits. An exterior
point needs no further signature: any one such point can be renamed 12 while
renaming the complete family. The six counts 120,20,120,20,225,180 sum to
`C(12,4)-2 C(6,4)+C(12,3)=685`; these are precisely the noninternal four-sets
with three or four link points and at most one marked exterior point.
The proof uses this only to normalize an existing marker, and never assumes
that a completion is symmetric.

An independent set-based direct check completed in 0.065 seconds, within the
one-second allowance. It did not import or execute either certificate checker
and wrote no certificate files. It represented each projected trace as an
actual four-set completed by fresh exterior labels, compared literal set
intersections with all actual cones and M, and evaluated the supplied integer
row weights. The resulting minima and integer caps were:

| Case | traces | excluded | minimum q | q(M) | H | integer cap on r |
|---|---:|---:|---:|---:|---:|---:|
| E00 | 794 | 460 | 2 | 3 | 81 | 40 |
| E01 | 1,093 | 604 | 2 | 3 | 91 | 45 |
| E02 | 794 | 439 | 2 | 3 | 80 | 39 |
| E03 | 1,093 | 562 | 3 | 4 | 141 | 46 |
| E04 | 794 | 469 | 10 | 10 | 430 | 43 |
| E05 | 1,093 | 596 | 1 | 2 | 48 | 47 |

The same small check obtained all 60 component automorphisms, reproduced the
six orbit counts above, and confirmed that the orbit of the internal marker
0123 contains all 15 four-subsets of a component. This is an additional finite
diagnostic, not a substitute for the geometric row proofs or a Lean check.

The mixed-pair covering argument uses only the already established bound of
two link points per residual, and the literal P10 degree/codegree counts 5,2.
Every selected cone is distinct from the residuals, and Q differs from M
because Q is assumed to avoid M's two exterior points. The three categories
have upper bounds 6,20,20; subtracting two for M's triple membership is valid
regardless of further overlaps.

Once mixed pairs are absent, each residual meets at most eight cones and is
disjoint from at least twelve. For each fixed cone, all members disjoint from
it are intersecting, by the empty-core sunflower prohibition. H27 therefore
applies to that actual family, and `12r≤20·27` is a multiplicity-preserving
double count of cone–residual pairs. This supplies the stated contradiction
for `r≥48` without any support bound or positive-degree assumption.

## Assurance boundary

The internal stage uses the universal C5 inequality `d(y)-I_y≤15` before
internal exclusion, with I_y retained. Stage two uses `d(y)≤15` only afterward.
The frozen source's mu42 model and bounded-support numerical setup are not
inherited by this argument: the specific imported geometric statements used
here precede those model restrictions or have separately universal statements.
Their validity remains an explicit structural dependency.

No change to the source proof files, no global bound67 conclusion, and no
opening of a final-review/publication gate follows from this check.
