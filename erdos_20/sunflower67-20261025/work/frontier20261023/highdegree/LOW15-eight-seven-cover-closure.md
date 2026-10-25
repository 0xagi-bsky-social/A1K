# The classified 8+7 degree15 links fail the cap15 A3 interface

24 October 2026. New ordinary transfer of a bounded exact diagnostic.
This is not a Lean theorem, an independent replay of the imported I7
classification, or a final review. The single standard-library census
was authorized and completed in0.171 seconds; it used no LP solver.

Assume F is a simple SF4 family of size68 with maximum point degree15,
and invoke the ordinary NO44 conclusion, H27 and Jin as in
`LOW15-A3-star-fibre-reduction.md`. Suppose an actual degree15 point x
has rho(L_x)=8. An actual link triple has eight disjoint triples H;
H is intersecting and B4 makes the other seven triples K intersecting.
Use the imported I8 classification, arbitrary-support I7 catalogue,
and P8/Q8 isolation.

## Why the finite models cover arbitrary support

The I7 catalogue consists of the eight literal templates H0,...,H7
in the frozen paper's universal R16 proof, reproduced in the new
source. Its support-at-most7 argument is an ordinary theorem about
arbitrary support, rather than a chosen ambient cutoff. The finite
classification itself remains an explicitly imported dependency.

For P8, isolation makes its entire six-point support disjoint from K.
The two P8 types are obtained by deleting two P10 blocks intersecting
in one or two points. Pairing these with each of the eight I7
templates gives16 labelled models. No relative-support choices remain.

For Q8, its five-point core avoids the whole support of K. Its two
distinct leaves are either both fresh, exactly one is a K point, or
both are distinct K points. A leaf swap removes their order. For an
I7 support of size n this gives1+n+binom(n,2) labelled gluings.
The seven six-point templates and one seven-point template give183
gluings. Literal SF3 testing rejects170 and retains13. Rejection uses
only an actual triple sunflower in the displayed link; an allowed
gluing is never rejected merely for failing an unproved assumption.
Thus there are29 valid 8+7 models in this slightly enlarged domain.

## Covers retain every exterior completion

For every model L and each prescribed deletion D of size d<=2, at
least13 link triples remain. The universal SF3 point-degree bound6
implies that two points meet at most12, so an ambient four-cover of
L minus D contains at least three points of W=supp(L).

Let C3 be all three-subsets of W covering L minus D. Let P4 be all
four-subsets of W covering it which contain no C3. Every actual
x-avoider covering L minus D either equals a P4 or contains a C3.
Simplicity and global triple codegree2 therefore give

    number of actual covers <= |P4|+2|C3|.              (1)

This is a union bound; overlapping C3 completions are harmless.
Exterior points are not assigned labels or bounded in number.

The source constructs all support triples and four-sets and records
which link members they miss. A support set is a cover for precisely
the deletion sets containing this missed-member set. Distributing
each support set to all such deletions reconstructs the full relation.
There are1+15+105=121 deletions per model and3509 8+7 cases.

The source optionally tightens (1) by two universal incidence bounds.
If all cover generators contain a pair P, the actual cover count is
at most6 minus the number of prescribed x-cones containing P. If
C3 is empty and every P4 contains z, delete z; each resulting actual
triple uses three pairs, and each such pair has remaining capacity
at most2 from the ambient triple-codegree bound. Prescribed x-cones
already containing that ambient triple subtract one capacity unit.
These are valid upper bounds even if the candidate sets are not
jointly realizable. In particular they handle the P8-i1 raw12 cases.
The current cap15 domain independently excludes P8-i1, so those
additional cases are not needed for the conclusion.

The completed maxima are:

| I8 side | Valid models | d=0 | d=1 | d=2 |
|---|---:|---:|---:|---:|
| P8, omitted blocks meet1 |8|0|4|10|
| P8, omitted blocks meet2 |8|2|4|10|
| Q8, including every valid leaf gluing |13|2|4|8|

For the P8-i1 two-deletion cases the raw maximum in (1) is12 and
the stated incidence reduction gives10. Every other displayed entry
already follows from the raw bound. The diagnostic also examined
R16-minus-one models, but its unresolved R15 rows are not used here.

## Transfer back to the A3 graph

An independent degree15 star support supplies at least10 actual full
covers, contradicting the first column (or the earlier ordinary
full-cover bound4). A nonindependent degree15 star support has the
four-index form proved in `LOW15-A3-star-fibre-reduction.md`: its two
endpoint weights are1 or2. An endpoint of weight1 supplies at least11
actual covers after deleting one prescribed link member, exceeding4.
An endpoint of weight2 supplies at least12 covers after deleting its
two prescribed members, exceeding10. All cases contradict the table.

Therefore, conditional on the stated ordinary and imported finite
premises and this exact diagnostic, no degree15 point can have a
complete 8+7 link. This excludes rho=8 at a degree15 point. It neither
classifies nor excludes rho<=6. The separate rho7 ordinary route is
not needed for this particular implication.

## Frozen evidence from this run

* Source `LOW15_classified_cover_probe.py`:
  `8a0dd2733dafb365a51c26b3512394bb6b7c88399ef5674589e8872ba9c199c3`.
* Receipt `LOW15-classified-cover-probe.json`:
  `2c13e66d1aa9f8dc1c4319b60c89684b000e571acfa08edc2d33966b14fd271d`.
* Imported paper `work/frontier20261020/prior-art68/repository/paper/main.tex`:
  `4aa36c9d56af5a8e3bdb44749107820549a73e0d3405e6c700104fa4c30e5c21`.

The receipt records all literal model triples, support labels, maxima,
rejected gluings and a digest of the complete reconstructed covering
relation. Its status remains a conditional discovery census. A future
independent reconstruction would be a distinct assurance step.
