# Cap16: ordinary closure of the N45 signatures

23 October 2026. Research proof development with a small exact arithmetic
case check, not a final audit or Lean formalization. No LP, numerical
model, large support enumeration or Lean process was run. Exterior
support is unrestricted.

**Conclusion.** Under the named prior/imported results and the preceding
ordinary cap16 reductions, every actual member of a size68 SF4 family
with global degree cap16 has neighbourhood at most44. The final two
necessary arithmetic signatures are excluded by explicit sunflower,
codegree and cross-star arguments.

## Acyclic premises

Let F be simple, four-uniform and three-sunflower-free, including empty
core; assume |F|=68 and Delta<=16. The preceding steps are:

1. `D16-P10-ordinary-exclusion.md`: no P10 point-link.
2. `D16-NO47-ordinary.md`: N<=46.
3. `D16-P9-root16-ordinary-exclusion.md` and
   `D16-P9-global-ordinary-exclusion.md`: no P9 point-link, hence every
   exact singleton count is at most8.
4. `D16-NO46-ordinary.md`: N<=45.
5. `D16-P8-no-two-cover-exclusion.md`: no P8 component whose two
   deleted P10 blocks intersect in one point. Its proof uses N<=45,
   not the N<=44 conclusion proved here.

We also retain H27, the universal exact-trace bounds and codegrees,
B4, I8 classification and isolation, the universal R16 theorem, and
the imported guarded actual cross-star theorem HP15. H27 gives mu>=41.
The imported R61 result excludes a complete R16 link at cardinality68
under mu>=41 and Delta<=18; its guard holds here. These are conditional
ordinary/source-backed inputs, not a new replay of the whole external
theorem chain.

## Complete degree16 local signatures

Every remaining complete point-link of size16 has a B4 partition into
two intersecting eight-triple families. Indeed, R16 is excluded; B4
gives two intersecting parts of total16, and no-P9 prevents either
part from having nine or ten triples. Each part is either Q8 or a P8
whose deleted P10 blocks intersect in two points. P8 isolation gives
disjoint supports when a P-type occurs. In Q8/Q8 only leaves may be
shared; the two cores each avoid the entire opposite support, as
justified again below.

Fix an actual anchor R={0,1,2,3}. For a degree16 root i, the triple
A=R minus i is in one eight-part. If it is a P8 block or a Q8 core
triple, its exact singleton count s_i is8. A Q8 leaf triple also gives
s_i=8 unless that leaf is shared with the opposite Q8; in that case
exactly one opposite triple meets it and s_i=7.

For the s_i=8 cases, list the three pairs (p_ij,t_j), j!=i. Here p_ij
is the exact pair count at R and t_j is the exact triple count omitting
j. Up to reordering the three partners, the complete list is

    ((0,1),(2,1),(2,1)),
    ((1,1),(1,1),(2,1)),
    ((1,1),(2,0),(2,1)),
    ((0,1),(3,0),(3,0)).                                  (1)

These counts are obtained directly by intersecting each of the other
seven triples of the near P8/Q8 with A. The small checker constructs
all P8 families obtained by deleting any intersecting-two-point pair
from the ten literal P10 blocks, and the literal Q8; thus it does not
assume a numerical orbit count for this signature list.

For s_i=7, write A={h,k,l}, a Q8 leaf triple with shared leaf l.
The other leaf triple gives t_l=1, the three edges of the triad give
p_ih=p_ik=3, and the unique opposite leaf triple through l gives
p_il=1. No other triple through i has a larger R intersection. Thus
the only shared-leaf signature is

    ((1,1),(3,0),(3,0)).                                  (2)

In particular, no other singleton count is possible at degree16.
Every signature (1),(2) has a triple trace through i. Consequently
an anchor with T=0 has no degree16 root. If it had N45, all four
degrees would then be at most15, and the degree identity would force
S=32, all singleton counts8 and all pair rows6. The common-triangle
HP15 obstruction would exclude it. The checker retains T0 anyway.

## Necessary arithmetic coverage

Let S=sum s_i, T=sum t_i, r_i=sum_(j!=i)p_ij. The exact identities at
a hypothetical N45 anchor are

    1+S+sum p_ij+T=45,
    d(i)=1+s_i+r_i+T-t_i<=16,
    sum d(i)=92-S+T,
    S>=28+T,          0<=s_i<=8, 0<=p_ij<=3, 0<=t_i<=1.

The script `D16_NO45_signature_check.py` exhausts this bounded integer
domain. It sorts s only, loops over all pair and triple assignments,
and canonicalizes surviving whole (p,t,s) rows under S4. Sorting s
loses no case because every actual anchor can be relabelled to have
sorted singleton counts; the other coordinates remain unrestricted.
It also imposes the following previously proved necessary conditions:

* global pair codegree `1+p_ij+T-t_i-t_j<=6`;
* B4 pair-row bound r_i<=6 at s_i=8;
* a triple exterior point cannot cover a three-edge pair triangle,
  giving p_ij<=2 when t_i=1 and s_j=8, or reciprocally;
* the omitted triple-member bound r_i<=4 when t_i=1 and every other
  singleton count is8;
* the common-triangle contradiction when every s_i=8 and every r_i>=5;
* the literal complete degree16 signatures (1),(2).

The local row facts and their proofs are in
`LOW15-large-singleton-core.md`; they apply here at cap16 in the stated
guards. The signature check leaves exactly two necessary S4 orbits:

| Case | p in order 01,02,03,12,13,23 | t | s |
|---|---|---|---|
| A | (0,2,2,2,2,0) | (1,1,1,1) | (8,8,8,8) |
| B | (1,1,2,2,1,1) | (1,1,1,1) | (8,8,8,8) |

Both have all four degrees16 and all pair rows4. The diagnostic counts
are2054 base rows with sorted singletons,164 after elementary guards,
six oriented survivors in that sorted-singleton convention, and two
S4 orbits. This is arithmetic coverage of necessary signatures, not a
claim that every signature corresponds to actual exterior geometry.

Frozen files for this bounded check:

    D16_NO45_signature_check.py
    c2e197eccab1238d36e95a4f9453211e2095a92a802e2b736867c513846ee611

    D16-NO45-signature-check.json
    dbf2504ded7c889c9d72f0a4cc6d9b462085250d27c6b133568e5b33d2c1fed2

The script uses only Python standard-library integer/set operations
and imports no numerical model, solver or external catalogue.

## Relating the four actual triple members

For either surviving case, write the actual exact triple member as

    Q_l=(R minus l) union {z_l},       z_l outside R.

If {i,j} union e is an actual pair-trace member, B4 in L_j forces its
near triple {i} union e to intersect Q_i minus j. The only possible
intersection is z_i, so z_i lies in e. Similarly z_j lies in e.
Therefore

    p_ij=2 implies z_i=z_j,                                (3)

since otherwise the only possible exterior two-set would be {z_i,z_j},
and the two actual members of that category would coincide.

If all four z_l agree with z, every one of the four pair members
through a fixed root i contains z, as do the three exact triple
members through i. This gives at least seven members containing
{i,z}, contrary to global pair-codegree6. Thus all-equal z is impossible.

In Case A, the p=2 graph is the connected graph K2,2. Equation (3)
forces all z_l equal, giving the contradiction immediately.

## The matching case forces isolated Q8 cores

In Case B, the p=2 edges are03 and12. Equation (3) gives

    z_0=z_3=a,             z_1=z_2=b.

The all-equal contradiction gives a!=b. Every cross-pair category
01,02,13,23 has its unique exterior edge {a,b}. The category03 has
two distinct edges {a,u},{a,v}; u,v are distinct, outside R, and
different from a. Neither is b: at root0 the two cross-pair members
01ab,02ab already consume both units of triple-codegree on {0,a,b}.
Likewise the category12 consists of {b,w},{b,z} with distinct leaves
outside R union {a,b}.

For example, the eight near triples in L_0 are exactly

    123, 23b, 13b, 12a, 1ab, 2ab, 3au, 3av.

This is the literal Q8 with hubs3,a, triad{1,2,b}, and leavesu,v.
Similarly, at each of the other three original roots the complete
near family is Q8 and its five-point core contains both a and b.
There are exactly eight other link triples, the actual singleton
tail family of size8, supported outside R.

The far family avoids the whole near Q8 core. Here is the full
isolation guard, including possible shared leaves:

* If the far family is P8, its support is disjoint from the near
  support. A near triple touching it could only be a deleted P10
  block; that block also avoids the actual anchor A=R minus i and
  would belong to the far class instead, impossible.
* If the far family is Q8, its core avoids the whole near support.
  A possible near triple meeting that core would be a far hub plus
  both far leaves; it avoids A and cannot be near. For the reciprocal
  direction, a far triple meeting the near core could only be a near
  hub plus both near leaves, wholly inside the near support. But
  every far Q8 triple contains a point of the far core, which was
  just shown disjoint from the near support. Thus this is impossible.

Only Q8 leaves can overlap; no full-support isolation is assumed.
In particular all four far singleton families avoid both a,b and
all of R. Each is an actual intersecting SF3 family of size8.

The actual member 01ab is therefore disjoint from centres2,3 and
from every tail in their two far families. If a tail from the first
and a tail from the second were disjoint, their lifted members and
01ab would form an empty-core sunflower. Those two tail families
are consequently cross-intersecting. Their distinct centres2,3
are outside both supports, and all lifts are actual. HP15 now gives

    16=8+8<=15,

a contradiction. This excludes Case B and finishes NO45.

## Scope and source boundary

The preceding N<=45 bound and the exclusion of its equality case give
N<=44. All exterior identifications used in the final argument were
forced by actual members, B4 or literal codegrees. The only finite
computation here is the small necessary integer-signature coverage.

The prior source repository is
`work/frontier20261020/prior-art68/repository`, pinned commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`. The relevant paper sections
are188--231 and272--350 for the canonical families, isolation, B4 and
capacities;443--462 for universal R16;968--1024 for crowding/cross-star;
and the following R61 theorem for its cardinality guard. All additional
ordinary dependencies are listed above. No old mu42 or minimum-degree
premise, numerical branch LP, or final global67 conclusion is claimed.
