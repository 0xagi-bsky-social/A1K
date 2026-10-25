# Independent preparation for the eight-model deletion-cover bound

23 October 2026. Ordinary proof development. The new source
`replay_d16_i8_deletion_covers.py` was written and inspected only: it was
not imported or executed, and no case count is reported here as a new
successful replay. No old file was edited. There is no LP, support cutoff,
Lean claim, or final scholarly review in this task.

## Exact target and separation of evidence

The target is the following conditional geometric theorem. Let L be the
complete16-member link of an actual point x, split into two intersecting
eight-triple components. Assume the established P8/Q8 classification and
isolation: a P8 support is disjoint from the other component, and the two
five-point Q8 cores avoid the opposite full support, with shared leaves
allowed. If D is any prescribed set of d<=3 link triples, the number of
actual x-avoiders meeting every triple of L minus D is at most

    c_d = (1,2,4,10)_d.

The frozen Oct20 diagnostic reports this claim for5576 deletion cases,
including six raw-count exceptions corrected by pair incidence. That
report is evidence to reconstruct, not an imported successful new run.
The new source imports none of the old producer functions and uses only
the Python standard library. Its explicit checks remain active under
Python optimization; it uses no `assert` statements.

## Why exactly eight literal models suffice

The ten literal P10 blocks are

    012,015,023,034,045,124,134,135,235,245.

A P8 deletes two of them. Their intersection size is1 or2. The new source
reconstructs the entire P10 automorphism group from all six-point
permutations and checks that its two omission orbits equal, as sets, the
complete30- and15-element domains. Representatives are

    P0=P10 minus {034,135},
    P1=P10 minus {012,015}.

The Q8 model has hubs0,1, triad2,3,4 and leaves5,6:

    023,024,034,123,124,134,015,016.

The six unordered pairs from P0,P1,Q on disjoint supports, together with
Q/Q sharing exactly one or two leaves, cover every permitted geometry.
The two components' leaf swaps identify all choices with the same number
of shared leaves. No Q8 core point is identified with the opposite
support. In the current cap16 branch the separately proved no-P8-without-
two-cover theorem removes the three models involving P0; retaining them
here checks a larger universal domain and avoids relying on that theorem
for the deletion-cover bound.

For every literal model, the source checks cardinality16, both component
cardinalities8 and intersection, sunflower-freeness, and maximum used
point degree at most5. The automorphism equality proves omission-orbit
coverage, rather than inferring it from equal orbit counts.

## Arbitrary exterior points are retained

Put W=supp(L). Deleting at most3 triples leaves at least13. Any two
points of W meet at most10 link triples, since each used point has link
degree at most5. Therefore every ambient four-cover of L minus D has at
least three points in W. It may have a fourth point anywhere outside W.

Let C3 be all triples of W covering L minus D, C4 all four-subsets of W
covering it, and P4 those members of C4 containing no C3. Every actual
four-cover belongs to P4 or contains at least one member of C3. An actual
cover with an exterior point has exactly three W points, which form such
a C3. By simplicity a particular P4 occurs at most once. By global
triple codegree2, each C3 is contained in at most two actual four-sets,
regardless of their exterior points. Thus

    number of actual covers <= |P4| + 2|C3|.

The right side is a union upper bound: counting an internal four-set
through several C3 more than once is harmless. It is not an assumption
that those exterior completions are jointly realizable.

The new enumeration runs support-first. For every support triple or
four-set S, it computes the set M of link triples missed by S. If
|M|<=3, S is distributed to every deletion set D containing M and of
size at most3. This reconstructs the whole covering relation by upward
closure. The deletion domain is independently formed from all16-bit
masks of weight at most3 and checked to have sizes1,16,120,560. Every
one of the8*697 cases contributes its complete C3,C4,P4 lists and bounds
to one deterministic SHA256 digest.

## The raw12 cases have an actual-family bound10

If the union bound exceeds the target10 at d=3, the replayer requires,
rather than assumes, that C3 is empty, C4 has exactly12 members, those
members have a common point z, and their union U has at most seven points.
No exterior completion remains because C3 is empty. Every actual cover
is therefore one of these internal four-sets and contains z.

Delete z from each actual cover. The resulting distinct triples are on
U minus z, which has at most six points. Each triple contains three pairs.
For any fixed pair ab, at most two residual triples can contain it:
their original four-sets contain the fixed ambient triple {z,a,b}, whose
global codegree is at most2. Counting incidences gives

    3 * number of actual covers
      <= 2 * binom(|U minus z|,2)
      <= 2 * binom(6,2) =30.

Hence at most10 covers are actual. This does not use an intersecting
family bound, a maximum independent set computation, or an assumption
that all12 candidates form a sunflower-free family. The source checks
this pair budget explicitly and independently rebuilds the exception
records before comparing them with the frozen six records.

## Transfer to fibre inequalities

Let t_i be the number of the16 actual x-cones in image fibre i. For any
image index i, let D_i be the actual set of x-cones in fibres adjacent
to i, so q_i=|D_i| is the sum of the corresponding t_j. Every actual
x-avoider in fibre j meets all x-cones outside D_j: a disjoint pair
would require an image edge between their fibres.

If D_j is a subset of D_i, that x-avoider therefore meets every cone
outside D_i as well. Distinct fibres contain disjoint sets of vertices
of the disjointness graph, so these are distinct ambient four-sets.
Whenever q_i<=3 the cover theorem gives the down-set inequality

    sum_(j with D_j subset D_i) (a_j-t_j) <= c_(q_i).

The membership test uses the actual occupied-neighbour subsets. Since
each occupied fibre contains at least one star member, inclusion of
these index subsets is equivalent to inclusion of the corresponding
actual cone sets. It is not a comparison of the cardinalities q_i,q_j
alone. No assumption about the presence of all permitted graph edges
is involved.

This is the intended interface to stability_notes' independent fibre
reconstruction. Successful cover and fibre runs would still need their
ordinary classification, graph-homomorphism and degree16-existence
premises composed explicitly; this source preparation makes no such
completed global claim.

## Frozen provenance

Relative to `work/frontier20261020/prior-art68/analysis/`:

* `prior68_cover_probe.py`:
  `13c5468d86b8033cf2ef03811845108f9da7a95d31196590a5cef5bd57c4de37`.
* `prior68_cover_probe.json`:
  `66b23589dd87a39a5b2e68d2f71a685b97c46a2fb9f7d992398772916e9bf592`.
* `prior68-research.md`:
  `92caa67b0215e80b64b19f25b3d2ba8873f489fb9edc5d389ab3a23d79a9f912`.

These bytes are checked before and after any future replay. The JSON's
status string is not trusted as proof; all models, covers, exceptions,
maxima and case counts are reconstructed before comparison.
