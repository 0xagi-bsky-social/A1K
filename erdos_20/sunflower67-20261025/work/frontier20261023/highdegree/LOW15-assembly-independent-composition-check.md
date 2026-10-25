# Independent composition check of the cap15 assembly

24 October 2026. Ordinary research checkpoint. I found no substantive
composition gap in `LOW15-complete-argument.md` under its explicit
universal imports and named finite predicates. This check does not
compose the higher-degree branches, assert a global67 theorem, or
upgrade executable finite evidence to Lean verification.

## Dependency order and domain guards

The upstream order is acyclic: H27 gives mu41; the cap15 cone argument
excludes P10; the large-singleton arguments give N<=44; that bound
excludes P9 and yields exact-singleton cap8. The four N44 profiles
then force a complete size15 link with rho exactly7 and one of two
impossible actual-triple degree patterns in R16 minus one triple.
This step uses the rho7 theorem, not the later rho<=6 exhaustion or
the later exclusion of complete R15 links. My earlier
`LOW15-NO44-composition-check.md` records this guard in detail.

The existing cap14 exclusion supplies an actual degree15 point x in
the remaining cap15 branch. For its complete link L_x, each disjoint
companion family of an actual triple is an exact singleton family in
F. Therefore rho(L_x)<=8. The three domains rho<=6, rho=7, rho=8 are
exhaustive. In particular the assembly does not assume that rho>=7
before completing the new rho<=6 finite argument.

For rho<=6, the eleven-point domain is derived from the ordinary
degree-two reduction and moment inequality. It is not an assumed
ambient-support cutoff. My independent degree-two reconstruction
checked the91 and78 normalized motif domains, the fresh-point guards,
and the full completion obstruction. The three subsequent proof-tree
replays are separate completed finite evidence supplied by the parent
task. I inspected their bound identities and reported results; I did
not rerun those trees or independently reinspect their full replayer
implementation in this composition pass.

For rho7, the two complete R15 deletion types are excluded using
actual hub anchors. My separate independent note checks both their
arithmetic and the complete-P5/B4 equality guard. Neither depends on
the A3 step or a numerical feasibility claim. The p0i category retained
in the hub-deletion proof is essential and is retained in the assembly.

## A3 does not require a complete blowup

From N<=43, the disjointness graph G on68 members has minimum degree
at least25; H27 bounds its independence number by27. Jin's k=4 strict
threshold is satisfied since350>340. The recorded empty-fibre reduction
and elementary mass bounds leave A3: A1 and A2 contradict68>54 and
136>135, and A4 would require275 neighbouring-fibre incidences while
their exact sum is272.

For A3, indices modulo8 have adjacency differences3,4,5. The adjacent
fibre masses satisfy25<=b_i<=27. Writing r_i=b_i-25 gives

    r_i in {0,1,2}, sum r_i=4,
    a_i=7+r_i+r_(i+3)+r_(i+5).

For the degree15 star, let t_i be its mass and S its occupied indices.
A star member cannot be disjoint from another star member. Its degree
is therefore at most b_i minus the star mass in adjacent image fibres.
Thus q_i=sum_(j adjacent i)t_j<=r_i on S, and

    sum_(i in S) t_i*deg_(A3[S])(i)<=4.

The small induced-support argument in the fibre note is valid: two
disjoint edges have all four weights1 and cannot support the star;
a two-edge path exhausts the r budget and has at most one isolated
fibre of mass7; a chord with one isolated fibre has total mass at most11.
The remaining nonindependent support is four consecutive indices,
with only their endpoint pair adjacent and endpoint weights1 or2.

If S is independent, its cyclic three-index window has mass at least25,
so at least10 nonstar members meet every prescribed star cone. In the
nonindependent case, deleting the t_3 cones at one endpoint leaves
at least10+t_3+r_5 nonstar members in the other three fibres. Their
images are nonadjacent to every retained star image. The contrapositive
of the graph-homomorphism property makes these actual members meet
every retained cone. This needs only the absence of image edges;
it never assumes all permitted image edges occur in G.

All these nonstar members avoid x, so meeting an x-cone is exactly
meeting its underlying link triple. The result is at least10 actual
full four-covers, or at least11/12 actual covers after deleting one/two
specified cones. Deleted cones remain actual members of F; the chosen
raw cover bound does not subtract any of their capacities.

## The rho8 gluing domain and ambient cover transfer are complete

Choose an actual link triple A with eight disjoint companions H.
H is intersecting, and B4 makes the remaining K of size7 intersecting.
Universal I8/I7 classification applies to these actual components.

P8 isolation gives fully disjoint supports here: a deleted P10 block
is supported in H and therefore avoids A, so it cannot lie in K.
The already excluded P8 omission-intersection1 type is not retained in
the closing domain. For Q8, only its core is forced disjoint from K;
the two leaves may be shared. The proof does retain such gluings.
The hub-plus-two-leaves isolation exceptions also avoid A and cannot
belong to K. Thus no unsupported full Q8 support isolation is used.

A shared Q8 leaf v is permitted exactly when no two K triples
intersect in precisely {v}, equivalently its K point-link is intersecting.
Pairs of Q8 triples have a core point in common, so cannot make a mixed
sunflower with K. A core-only Q8 triple avoids K, and K is intersecting.
The only remaining mixed possibility is one Q8 leaf triple with two
K triples, giving exactly the stated single-leaf criterion. Both leaves
can be tested separately; a three-member sunflower cannot contain two
distinct leaf triples and a K triple because their common hub pair is
absent from K.

The allowed shared vertices are none for H0,H1,H3,H4,H5, vertex0 for
H2,H6, and vertices5,6 for H7. This yields13 Q8 gluings, plus8 separated
P8-i2 models. Keeping symmetric duplicates is harmless. This finite
domain derives from arbitrary-support component classification and
the exact gluing criterion, not a guessed size of the ambient set.

For any one of these21 links, after at most two deletions at least13
triples remain. Every support point occurs in at most6 link triples,
so two points cannot cover the retained link. Every ambient four-cover
therefore uses at least three support points. If it contains a support
three-cover C, global triple codegree2 permits at most two actual
foursets per C. Otherwise it is a support four-cover containing no
such C and simplicity permits it at most once. Consequently

    actual four-covers <=2*|C3|+|P4|.

This is a union bound; repeated counting of a fourset with several C3
subsets only weakens it. Arbitrary exterior completions and coincidences
are included. There is no assumption that every actual cover lies
wholly in the displayed support.

## Finite evidence inspected and closing comparison

I inspected the independent deletion-first source
`replay_low15_eight_seven_covers.py` and its saved receipt. The source
builds the analytical21-model domain, imports no producer, and tests
all121 deletion sets per model by literal set incidence. It checks
the sunflower-free and point-degree conditions, forms C3 and P4, and
uses the raw bound above. The saved PASS receipt has2541 cases and
maxima(2,4,10), strictly below the required(10,11,12). No incidence
refinement or R15 model enters this selected closing domain. I did
not rerun this successful finite job during this composition check.

The older A3 note's open-interface language describes its writing-time
state. The independent finite receipt and complete assembly explicitly
discharge that interface; the final argument does not rely on an
unfinished N43 profile census.

All15 SHA256 entries in the assembly's byte-identity table match the
current files. The principal inspected identities are:

| Input | SHA256 |
|---|---|
| LOW15-complete-argument.md | 6c3438b2ae2f8438b3c761019e3d1e711d13cf92679c082a7f33c8a762167b68 |
| LOW15-A3-star-fibre-reduction.md | 0b088edeecd0a486f19050422b446d871e31b87fc4098994f5aa1241f665455c |
| LOW15-A3-cover-independent-bridge.md | 43a8e28c18d135437ff97f4012f3d49b7015152a538c2d02b1cb12616968c17b |
| replay_low15_eight_seven_covers.py | ebc5c607ab5f88b1427b01757e55c4567e2982af81b920cbcb0b7be120755296 |
| LOW15-eight-seven-cover-independent-replay.json | a0f011d3f75df225f386fe8c1b0c266cc199b0d0861f9d2a05d009e613821b10 |

The external universal inputs remain H27, B4/isolation, I8/I7
classification, the named HP15/crowding scope, and Jin. This note
checks their composition and the stated finite interfaces; it does
not claim to reprove that entire prior chain.
