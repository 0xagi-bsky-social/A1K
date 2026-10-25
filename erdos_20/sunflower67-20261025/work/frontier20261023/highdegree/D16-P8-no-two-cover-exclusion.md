# Cap16 exclusion of a P8 component with no two-cover

23 October 2026. Ordinary research proof development, not a final audit.
No solver, enumeration or Lean process was used. Exterior support is
arbitrary. This is a conditional reduction after the global no-P9 and
NO46 results; it does not exclude the other P8 type or Q8.

Let F be a simple SF4 family with68 members and global degree at most16.
Assume the established cap16 no-P9 result and N(Q)<=45 for every actual
Q. H27 gives mu>=41. Use the universal capacities, isolation, P10
incidences, and guarded actual cross-star bound HP15.

Suppose L_x contains H=P10 minus {B_1,B_2} on W, where the two deleted
blocks meet in exactly one point. Then H has no two-point cover: the
two P10 blocks avoiding a support pair intersect in two points, so
they cannot both be these deleted blocks. Every pair is therefore
avoided by an H block. Its three-point transversals are precisely

    H union {B_1,B_2,C_1,C_2},       C_i=W minus B_i.

No-P9 excludes any missing block from the complete L_x. Isolation
therefore gives L_x=H union K with every K triple disjoint from W.

## Any actual outside member has a small disjoint complement

Take actual Q disjoint from {x} union W and put I=D(Q). It is an
intersecting SF4 family. Its complete x-link is H union K', with
k=|K'| and every K' triple outside W.

If k=0, every x-avoider in I has either a three-point W trace which
is a transversal of H, or is an internal four-subset of W. Each
internal four-set contains at least one H block: a four-set contains
exactly two P10 blocks, and B_1 union B_2 has size5, so it cannot
contain both deleted blocks. Global triple-capacity2, after the eight
x-cones, therefore bounds the combined number of internal four-sets
and H-block completions by8. For each complementary exceptional pair
B_i,C_i, intersection of I bounds its two completion classes together
by2: if both occur, their exterior points must all agree, leaving one
member of each trace; otherwise one trace has capacity2. Thus

    |I|<=8+8+4=20.                                        (1)

For k>0, an x-avoider must meet H using at least three W points and
must meet every K' cone outside W. It has exactly three W points and
one exterior centre lying in the common intersection of K'. There
are no internal four-sets. Eight H-block completions and at most four
exceptional completions give

    |I|<=8+k+12=20+k.                                     (2)

This is at most22 when k=1 or2.

For k>=3, the common intersection of K' has size at most1 by global
triple-codegree2. If empty, I has no x-avoiders and |I|<=d(x)<=16.
Otherwise the common point is z and every x-avoider is z plus one
of the twelve listed transversals. Both B_i and C_i cannot occur:
their z-lifts together with any surviving xK' cone would be a
sunflower with core {z}. Hence at most one member of each complementary
pair of exceptional traces is present.

All other pairs among the four exceptional triples intersect. Indeed,
|B_1 intersect B_2|=|C_1 intersect C_2|=1 and
|B_1 intersect C_2|=|B_2 intersect C_1|=2. Every exceptional triple
also meets every H block because it is a transversal. Thus the entire
family of actual z-tails is intersecting and cross-intersecting with
the eight actual x-tails H. It is SF3, since all its z-lifts are
actual, and both centres lie outside W. HP15 bounds its size by7.
As k<=6 by pair-codegree of x,z,

    |I|<=8+k+7=15+k<=21.                                  (3)

Equations (1)--(3) give |D(Q)|<=22 in every case. But NO46 gives
|D(Q)|=68-N(Q)>=23, contradiction. Therefore no actual Q avoids
{x} union W.

## Whole-support contradiction

All n=68-d(x)>=52 members avoiding x now meet W. Their exact-one-W
subfamily is intersecting because an H block avoids any two support
points; otherwise a disjoint pair and such an x-cone form an empty
sunflower. H27 bounds that subfamily by27. The total residual
W-incidence is at most6*16-3*8=72. Consequently

    104<=2n<=72+27=99,

a contradiction. No point-link contains this P8 type.

## Dependency boundary

The global no-P9 result is `D16-P9-global-ordinary-exclusion.md`.
The N<=45 premise is the subsequent ordinary NO46 deduction; this
proof is not used to derive that premise. Canonical P10/P8 models,
isolation, universal codegrees, H27 and guarded cross-star retain
the prior source boundary in the frozen repository
`work/frontier20261020/prior-art68/repository`, especially
`paper/main.tex:188--231,272--350,1001--1024`.

The P8 type with deleted blocks meeting in two points has a unique
two-cover. Its x-avoiders may have only two W points, so the complement
proof above does not apply. No I7/I8 catalogue, old mu42 premise,
ambient support bound or global67 conclusion is used.
