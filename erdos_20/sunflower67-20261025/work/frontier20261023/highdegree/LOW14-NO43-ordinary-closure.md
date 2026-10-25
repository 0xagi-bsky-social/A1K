# Ordinary exclusion of the cap14 N43 cores

23 October 2026. New substantive proof, not a final review. This note leaves
the previously hashed files unchanged. It uses H27, the ordinary intersecting
I8 classification and isolation/B4 lemmas, and the imported cross-star
theorem in its already established mu>=41, Delta<=18 scope. Jin's graph
theorem is additionally needed for the global cap14 consequence.

## Premises already obtained

Suppose F is a finite simple SF4 family with 68 members, global point-degree
cap14 and no empty-core sunflower. H27 gives mu>=41. The ordinary P9
cone-average argument in `LOW15-mu41-research.md` excludes P9 in every
point-link, so all exact singleton counts are at most eight. At every actual
anchor, N<=43 follows from its degree-sum identity and S<=32.

The arbitrary-support reduction in `LOW14-Wagner-research.md` proves that
any actual root R={0,1,2,3} with N=43 has the following complete core:

* every root degree is14, all four singleton counts are8, and all exact
  root triple counts vanish;
* there are ten exact pair-trace members and R itself;
* every pair member is {i,j} union e, where e is an edge of one common
  exterior triangle T, disjoint from R;
* the opposite root-pair counts agree and their three values are one of
  (0,2,3), (1,1,3), (1,2,2).

Thus the complete core has eleven actual members on V=R union T. Its
seven-point support was derived by the B4 near-link and elementary edge
arguments; it was not assumed. The finite nine-orbit census is consistent
with this ordinary reduction but is not needed for the exclusion below.

## The near link has a two-edge matching at every triangle point

Fix i in R. In the complete triple link L_i, let A=R\{i}, let D_i be the
eight triples disjoint from A, and let K_i be the triples meeting A.
The near family K_i consists of A and exactly five triples j union e,
where j lies in R\{i} and e is an edge of T. By B4 it is intersecting.

For an edge e of T, at most two of these five triples use e. Otherwise
the three original four-sets would contain the same triple {i} union e,
contradicting the universal triple-codegree cap two. Since T has exactly
three edges, their multiplicities are therefore (2,2,1), in some order.
It follows that every t in T occurs in three or four triples of K_i.

The point-link of t inside K_i is a **simple bipartite graph** with parts
R\{i} and T\{t}: its edges are the pairs {j,u} from triples {j,t,u}.
Its maximum degree is at most two, by the same original triple-codegree
bound on {i,t,j} or {i,t,u}. It has at least three edges. Such a graph has
a matching of size two. Indeed, three pairwise intersecting distinct edges
would form a three-edge star or a triangle; the first violates maximum
degree two and the second violates bipartiteness.

Consequently, for every t in T there are two actual near triples

    {t,j1,u1}, {t,j2,u2}

whose pairs {j1,u1} and {j2,u2} are disjoint. This is a literal matching
statement about actual members, not a degree-histogram inference.

## All eight singleton tails are completely outside V

The family D_i is intersecting SF3 of size eight, so it is P8 or Q8.
Every point of its support avoids R: all its triples avoid A and, being
members of L_i, avoid i.

If D_i is P8, isolation says that a triple of K_i meeting its support must
be one of its two missing P10 blocks. But those blocks also avoid A, so
an actual occurrence would belong to D_i rather than K_i. Hence K_i
avoids the whole support of D_i. Since K_i uses every point of V\{i},
the entire P8 support avoids V.

If D_i is Q(h,k;U;a,b), isolation says that a triple of K_i meeting its
five-point core {h,k} union U must be one of {h,a,b},{k,a,b}. Both of
these triples lie on the support of D_i, so avoid A and cannot belong
to K_i. Thus the Q8 core is outside V. Its leaves already avoid R.

Suppose one leaf were t in T. Its actual Q8 leaf triple is {h,k,t}.
Choose the two near triples furnished by the preceding matching lemma.
The hubs h,k lie outside V, while the matching edges lie inside V\{i,t}.
The three link triples

    {t,j1,u1}, {t,j2,u2}, {t,h,k}

have all three pairwise intersections equal to {t}. They are distinct,
so they form a sunflower in L_i, equivalently a sunflower with core
{i,t} in F. This is impossible. Neither leaf lies in T.

Therefore in both cases every triple of D_i is disjoint from V. This
argument specifically resolves the possible Q8 leaf overlap; core isolation
alone would not have been sufficient.

## Cross-star contradiction

There is at least one positive root-pair count, say p_kl>0. Let i,j be
the other two root points and choose an actual core member B={k,l} union e.
Its support lies in V and it avoids i,j.

Take any U in D_i and W in D_j. If the triple tails U,W were disjoint,
the actual four-sets {i} union U, {j} union W, and B would be pairwise
disjoint: both tails avoid V, and their distinct centres also avoid B.
That would be an empty-core sunflower. Thus D_i,D_j are cross-intersecting.

They are intersecting SF3 families of sizes8 and8, and both centres i,j
are outside both tail supports. All their lifts are actual members of the
same F. These are exactly the guards of the imported cross-star theorem.
It supplies an actual member C with

    |N[C]| <= d(i)+d(j)-d(i,j)+4 <= 14+14-1+4 =31,

contradicting mu>=41. Equivalently one can use the weaker imported HP15
consequence directly: 8+8<=15 is impossible.

This excludes every N43 core, including all nine finite representatives,
without a residual trace LP and without bounding the exterior support.
The minimum-degree and support20 refinements are not needed for this proof.

## Independent graph step: N43 must exist under cap14

For completeness, suppose instead that every neighbourhood were at most42.
The disjointness graph G has68 vertices, is triangle-free, has alpha<=27
by H27, and minimum degree at least26. Jin with k=3 applies because
26*11>4*68 and gives a homomorphism to cyclic A3 on eight indices, with
edge differences3,4,5. Empty fibres are allowed initially.

Let a_i be fibre sizes and b_i=a_(i+3)+a_(i+4)+a_(i+5). The adjacent
fibres form an independent set, so b_i<=27. Put e_i=27-b_i. Then

    sum e_i=8*27-3*68=12.

The elementary circulant incidence identity gives

    a_i=b_i+b_(i+3)+b_(i+5)-68
       =13-e_i-e_(i+3)-e_(i+5) >=1.

One can check the identity by expanding the three b terms: every a_j
occurs once and a_i occurs once more. Therefore every fibre is occupied.
A vertex in fibre i has neighbours only in adjacent fibres and at least
26 neighbours, so b_i>=26. This contradicts

    8*26 <= sum b_i =3*68=204.

This proves that an N43 anchor exists whenever all neighbourhoods are at
most43. Multiplication of cyclic labels by3 modulo8 carries differences
3,4,5 to1,4,7, so this is exactly the Wagner labelling used in the older
proof, with no graph-convention mismatch. No finite fibre census is needed.

Combining this existence argument with the ordinary N43 exclusion above
rules out the entire Delta<=14 branch at cardinality68, conditional on
the explicitly named H27, classification, cross-star and Jin imports.
It does not exclude Delta15 or prove the global bound67.

## Frozen-note wording correction

In the r_i=0 paragraph of `LOW14-Wagner-research.md`, the words
"all a_i possible neighbours" should read "all b_i possible neighbours".
The formula b_i=25 and the conclusion N=43 there are unchanged. This
separate correction preserves the earlier note and census hashes.

The cross-star source and successful prior replay provenance are recorded
in `PRIOR_DELTA18_UNLOCK.md` and `prior-delta18-unlock.json`; the ordinary
I8/B4/isolation statements are in the frozen prior paper's canonical and
isolation sections. Their use here is conditional mathematical composition,
not a new replay, independent reconstruction of those certificates, or Lean.
