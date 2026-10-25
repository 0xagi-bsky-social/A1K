# Independent preparation of the order68 fibre reconstruction

23 October 2026. Substantive proof development and source preparation, not
final review or publication. The new C++ program has not been compiled or
executed. The Python driver passed AST syntax only. No solver is involved.

## Current ordinary interface and its exact scope

The new cap16 chain proves singleton<=8 and N<=44; see
`D16-NO45-ordinary.md` and its independent scalar/ordinary check. If an
actual point of degree16 exists, its complete link is either R16 or a
B4-separated I8+I8 family. Imported R61 excludes R16 at cardinality68,
mu>=41 and Delta<=18. I8 classification and reciprocal core isolation
leave the eight old P8/Q8 models (the newly excluded P8 type may safely
be retained as an overcover in this reconstruction).

The existence of a degree16 point is an explicit extra premise. The
argument does not close families whose maximum degree is at most15.

The disjointness graph has68 vertices, is triangle-free, has independence
number<=27, and has minimum degree24. The imported Jin theorem with k6
applies since24*20>7*68. Reducing empty fibres by the ordinary cyclic
map v -> v-1-[v>=k]-[v>=2k] yields a surjective A_k image, k=3,4,5,6.
The images A1,A2 contradict respectively68<=54 and136<=135.
For cyclic differences k through2k-1, write a_i for fibre masses and
b_i for adjacent mass. Then24<=b_i<=27. With r_i=b_i-24,

    0<=r_i<=3, sum r_i=24-4k,
    a_i=4+r_i+r_(i+k)+r_(i+2k-1).

For an actual degree16 star let t_i be its fibre masses and
q_i=sum_(j adjacent i)t_j. Then sum t_i=16,0<=t_i<=a_i, and
q_i<=r_i whenever t_i>0. These bounds allow all missing inter-fibre
edges; no complete-blowup assumption is used.

If the positive support of t is independent, it lies in a cyclic
k-window. That window has mass>=24 and supplies at least8 actual
four-transversals outside the star. Every separated I8+I8 has at most
one full four-transversal: each P8 requires its unique two-cover when
one exists; two Q8 cores each require two points, leaving no room for
leaves, so their four points must be the two hub pairs. Thus independent
star support is impossible. In particular A6 is already excluded
ordinarily because r=0. The implementation also checks the finite
window property for every independent support but does not enumerate
all its star mass vectors.

## Exact down-set inequality

Let D_i be the actual star members in fibres adjacent to i. Then
|D_i|=q_i. Every nonstar member in fibre j with D_j subset D_i meets
all star members outside D_i. These are distinct actual four-sets,
so the deletion-cover capacities c=(1,2,4,10) imply, for q_i<=3,

    sum_(j: D_j subset D_i)(a_j-t_j)<=c[q_i].

Since different fibres partition the star, D_j subset D_i is exactly
inclusion of their occupied-neighbour coordinate masks. Weighted
coordinates are not treated as one member: q_i sums their full masses.
The independent cover reconstruction in
`replay_d16_i8_deletion_covers.py` checks all5576 deletion cases and the
ordinary arbitrary-support transfer separately. Its successful receipt
is required by the new fibre driver; a prepared checker alone is not
accepted as a verified cover input.

## Different star enumeration

`d16_fibre_reconstruction.cpp` does not reuse or execute the Oct20
producer. It generates the complete bounded r-composition domain and
quotients only by rotations/reflections. Each nonindependent star vector
has one lexicographically first occupied graph edge. The new search
partitions vectors by that edge, forces its two endpoints positive, and
assigns integer coordinate values directly. A positive coordinate is
rejected if it creates an earlier occupied edge or exceeds any already
occupied neighbour's remaining q budget. Future ceilings also use
those necessary conditions and the total16 requirement.

Every valid nonindependent vector has exactly one such first edge.
For that seed its successive true coordinate values obey every pruning
inequality, so no valid vector is removed; a completed vector is checked
again from scratch. At every completed vector all applicable down-set
cover inequalities are checked directly. The old B/near shortcuts and
its independence-number test are not used. The old saved output reports
zero alpha exclusions in each image, so omitting that test should not
change the expected counts.

For each profile the program emits r,a, star count, unresolved count and
one unresolved witness if any; it also emits aggregate exclusions by
capacity. Full-image counts are required to match

    profiles: 543,1541,103,1;
    stars:    33912,87790,2621,0.

These expected values are cross-checks, never a substitute for generating
and classifying every vector. Any mismatch, unresolved vector, invalid
integer identity or deadline expiration fails closed. Optional profile
slices are labelled partial and cannot certify the complete image.

## Pins, intended invocation and evidence boundary

New C++ source SHA256:
`fa29e7cd616b68a3df3d2252397e30ebc3e6593c5c3d66f2720874d2c9002991`.
New driver `replay_d16_fibres.py` SHA256:
`37becdceb4ce6313ecf904d8eeb1f0e39e338350df691db0a75018c72252a674`.
The driver pins the C++ source, the independent cover checker and bridge,
and the old diagnostic files. It accepts one k and a total deadline at
most60 seconds, compiles only the new source in a temporary directory,
and binds the compiled binary and cover receipt in its output. No command
has been run. A future scheduled invocation has the form

    python3 replay_d16_fibres.py --k 3 --cover-receipt COVER.json \
        --output NEW_FIBRE_K3.json --seconds 30

The existing Oct20 files have been read and current hashes recorded in
`D16-fibre-preparation-integrity.json`. Their saved counts and proof
interfaces agree with this task. That byte-integrity inspection is not
a replay of their original execution, and their output does not itself
supply a cryptographic binding to the compiler/source used in that old
run. It can presently be cited as a frozen exact diagnostic, while the
independent reconstruction remains prepared and unexecuted. A future
successful run would provide independent finite arithmetic evidence,
conditional on the stated ordinary/imported theorem chain, not Lean or
an unconditional global67 conclusion.
