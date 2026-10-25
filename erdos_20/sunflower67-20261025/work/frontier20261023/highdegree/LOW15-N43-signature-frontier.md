# N43: proved subcases and a necessary signature frontier

24 October 2026. Ordinary research checkpoint, not a final audit or a
global exclusion. All support in the underlying four-set family remains
arbitrary. The only execution here was a standard-library scalar/signature
census, under a ten-second timeout; its final run took about0.14 seconds.

The NO44 composition is checked separately in
`LOW15-NO44-composition-check.md`. It does not require rho<=6 classification.
The following additional N43 subcases are now excluded ordinarily:

* All four singleton pools8, T=0: `LOW15-N43-all-eight-no-triples.md`.
* T=4: `LOW15-N43-four-triples-exclusion.md`.
* All four singleton pools8, T=3, and one further mixed-singleton T3
  profile: `LOW15-N43-three-triples-all-eight.md`.

The last two proofs use the explicit near-point matching lemma: if a
point-link inside the near component has two disjoint edges, a far Q8
leaf at that point would add a third edge disjoint from the near support.
This excludes only the particular leaf occurrence justified by the
matching, rather than treating the whole Q8 support as isolated.

## Exact scope of the small census

`LOW15_N43_signature_census.py`, SHA256
`75f0d7dccfa9a2d8ba7f5c42ad83cb1a33994a93113255b909cf31b5d3b4898a`,
produced `LOW15-N43-signature-census.json`, SHA256
`451428ca6162338868c663352494f272444536a89f4040779c1339e09fabfccf`.
The receipt includes hashes of its ordinary proof dependencies.

It enumerates bounded integer p in{0,1,2,3}^6, t in{0,1}^4, s in{0,...,8}^4,
with N=43 and global degree cap15. It imposes the displayed elementary
pair-capacity, B4 pair-row and triple-star constraints. At a degree15
root with s>=7 it checks necessary anchored signatures from all known
complete-link alternatives:

1. Every literal P8 obtained by deleting two P10 blocks meeting in two
   points, plus each imported I7 type on disjoint support (120 families).
2. Q8 plus each I7 type, with either of Q8's two distinct leaves matched
   to distinct I7 points or left fresh. Its five-point core is disjoint
   from I7 by B4. There are358 tested gluings, of which18 are SF3.
3. R16 minus a hub triple, using the exact-rho7 theorem and the separate
   complete outer-deletion exclusion. The later hub-deletion exclusion
   is not imported in this frozen census.

This normalization is exhaustive for the B4 8+7 alternative because
only the two Q8 leaves can overlap the other component; it is not an
assumed ambient support cutoff. The I7 list and its arbitrary-support
classification remain imported finite facts. The anchored signature
records, at each of the three anchor points j, the number of triples
meeting the anchor in{j} and in its complementary pair. Those become
the original root's p_ij and omitted-index t_j.

The census deliberately imposes no such local classification on a
degree15 root with s<=6. Hence the unresolved rho<=6 domain is retained.
No admitted scalar signature is asserted to have a global realization.

The remaining geometric filters are already proved necessities. Good
singleton8 roots with row>=5 have one exterior triangle; categories
of size>=2 identify triangles. A singleton7 degree15 root at T=0 must
be the shared-Q8-leaf exception: its row is(1,3,3), the size3 categories
have a common triangle and its size1 edge avoids that triangle. The
rho7 deletion types cannot have its distinguished triple with all
point degrees<=4. These triangles may propagate through size3 categories
as well. An exceptional size1 edge cannot simultaneously lie on a
good partner's identical triangle. Reciprocal exceptions give an actual
anchor of neighbourhood<=40, as proved in the N44 reduction. Finally,
the explicitly named closed T0/T3/T4 subcases are removed.

There are2561 initial sorted-singleton rows,1110 after elementary cuts,
669 after degree15 signatures, and191 oriented rows after the stated
ordinary exclusions. Canonicalization under all24 root permutations
leaves41 necessary scalar orbits. The complete representatives are in
the JSON; the class counts are:

| Sorted singleton counts | T | Remaining orbits |
|---|---:|---:|
|6,6,8,8|0|2|
|6,7,8,8|0|4|
|6,7,8,8|1|1|
|6,8,8,8|0|2|
|6,8,8,8|1|1|
|6,8,8,8|2|2|
|7,7,8,8|0|8|
|7,7,8,8|2|1|
|7,8,8,8|0|6|
|7,8,8,8|1|3|
|7,8,8,8|2|4|
|7,8,8,8|3|1|
|8,8,8,8|1|2|
|8,8,8,8|2|4|

## A precise low-rho target

At a degree15, singleton6, T=0 root the row is8, hence its three pair
counts are(2,3,3). The actual link anchor has point degrees(3,4,4),
with all three pair codegrees1. No rho7 R15 deletion or complete B4
8+7 anchored signature has these data. Thus this situation forces
rho at most6 in the complete link. In the degree3 point-link, the
anchor edge has two degree-one endpoints and is isolated; the other
two edges form a path, since two further disjoint edges would create
a three-matching. This is a concrete target for the separate rho6 work.

The one surviving mixed-singleton T3 profile is
p=(1,1,2,2,1,1), t=(0,1,1,1), s=(7,8,8,8), with all four degrees15.
The other T3 cases are already covered by the ordinary note above.

Further N43 casework was paused in favour of independently checking
the new rho<=6 finite reduction. The41 rows are a documented necessary
frontier, not a claim that41 geometries exist or that N43 is excluded.
