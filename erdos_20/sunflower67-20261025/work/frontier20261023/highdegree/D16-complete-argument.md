# Exclusion of maximum point degree sixteen at cardinality sixty-eight

24 October 2026. Ordinary conditional proof with independently reconstructed
finite integer checks. This is research development, not final scholarly review,
not an end-to-end Lean theorem, and not a global bound of sixty-seven.

## Literal statement and dependencies

Let F be a finite simple family of four-element sets, containing no three distinct
members with equal pairwise intersections, including the empty intersection.
Assume |F|=68 and maximum used point degree exactly16. Under the following named
external/prior theorem inputs and local ordinary lemmas, a contradiction follows.

The external/prior inputs are H27 (intersecting SF4 maximum27), B4, the I8 and
I9/I10 classifications and isolation lemmas, the universal R16 classification,
the guarded actual cross-star HP15 result, R61 under mu>=41 and Delta<=18,
and Jin's strict triangle-free graph-homomorphism theorem for k<=9. Their exact
source is the pinned Oct9 companion 90c03c79bcf44eb8f61dff1b86091b822cc4cd3c
and the earlier recorded imports. This proof does not silently discharge their
external computations or promote them to local Lean theorems.

The acyclic cap16 local chain is:

1. D16-P10-ordinary-exclusion.md and D16-NO47-ordinary.md give no P10 and N<=46.
2. D16-P9-root16-ordinary-exclusion.md and D16-P9-global-ordinary-exclusion.md
   exclude every P9 component; all exact singleton counts are at most8.
3. D16-NO46-ordinary.md gives N<=45.
4. D16-P8-no-two-cover-exclusion.md excludes the P8 type with transversal number3.
5. D16-NO45-ordinary.md, including its independently reconstructed small integer
   signature domain, excludes equality45 and gives N<=44.

H27 gives mu>=68-27=41 throughout, so the stated guards hold. Fix an actual point
x of degree16. R61 excludes its complete R16 link. B4 and the singleton bound
then partition its full link into I8+I8; isolation yields the eight literal
P8/Q8 models, allowing shared Q8 leaves. Retaining the already excluded P8 type
in the finite cover census is a safe enlargement of the domain.

## Graph representation

The disjointness graph G on F is triangle-free, has alpha(G)<=27 and minimum
degree at least24. Jin applies with k=6 because 24*20>7*68. Deleting empty image
fibres by the stated cyclic homomorphism gives a surjective Andrasfai image A_k.
Images A1 and A2 contradict the independence bound, leaving k=3,4,5,6.
No completeness of permitted inter-fibre edges is assumed.

Let a_i>0 be fibre masses and b_i the sum on adjacent image fibres, with indices
modulo 3k-1 and adjacency differences k,...,2k-1. Then 24<=b_i<=27. Put r_i=b_i-24.
The cyclic inverse identities are

    0<=r_i<=3,  sum r_i=24-4k,
    a_i=4+r_i+r_(i+k)+r_(i+2k-1),  sum a_i=68.

Let t_i count the sixteen x-star members in fibre i and q_i the sum of t_j in
adjacent fibres. Then sum t_i=16, 0<=t_i<=a_i, and t_i>0 implies q_i<=r_i:
those q_i star vertices are forced non-neighbours of any star vertex in fibre i.

Independent occupied star support lies in a cyclic k-window, of mass at least24.
Every vertex in that window meets every star member, so at least eight distinct
nonstar members would be full four-transversals. The ordinary proof in
D16-I8-full-quasi-transversals.md bounds such members by one. Independent support
is therefore impossible, including the entire A6 case where r=0.

## Arbitrary-support cover capacities and nonindependent stars

For every deletion set of d<=3 prescribed star members, the number of actual
nonstar members meeting all undeleted star members is at most c_d=(1,2,4,10).
D16-I8-deletion-cover-reconstruction.md proves the arbitrary-support transfer:
every such four-cover uses at least three link-support points; support triples
have at most two completions by triple-codegree. Six raw12 exceptions have an
actual-family upper bound10 by a separate pair-incidence count on six residual
points. No ambient support cutoff is imposed.

The new standard-library reconstruction verified all eight models and all
8*(1+16+120+560)=5576 deletion sets, including all six exceptions. Its receipt is
D16-I8-cover-independent-replay.json, status PASS, source and inputs unchanged.

Let D_i be the actual star members in image fibres adjacent to i. Whenever
|D_i|=q_i<=3, every nonstar vertex in any fibre j with D_j subset D_i meets all
star members outside D_i. Distinct fibres give distinct actual sets. Thus

    sum_(j: D_j subset D_i)(a_j-t_j) <= c_(q_i).

Subset inclusion is checked on occupied-neighbour masks; q_i still counts the
full star multiplicities. It is not merely a comparison of q_i and q_j.

The new C++ reconstruction partitions every nonindependent t by its first
occupied image edge and generates all integer assignments satisfying the above
necessary conditions. It directly checks every completed vector against the
cover inequalities. It does not execute or import the old Oct20 producer.

| k | Complete dihedral r profiles | Nonindependent star vectors | Unresolved |
|---|---:|---:|---:|
|3|543|33912|0|
|4|1541|87790|0|
|5|103|2621|0|
|6|1|0|0|

All four fresh driver receipts have status PASS and complete_conditional_k_exclusion
true: D16-fibre-k3-independent.json through D16-fibre-k6-independent.json.
They bind the independent source, compiler, binary, actual cover receipt and
ordinary bridge. Total:2188 profiles and124323 nonindependent star vectors.
Every such vector violates a necessary inequality; independent support was
excluded ordinarily. This is the desired contradiction.

## Exact claim boundary

The entire case Delta=16 is excluded conditional on the named imported and
ordinary prerequisites. Families with Delta<=15 do not supply a sixteen-member
star and are not covered. Delta=17 is a separate open branch. Combining this
with earlier Delta>=18 and Delta<=14 exclusions leaves exactly15 and17 as
possible maximum degrees in the current hypothetical68-member family reduction.
The finite calculations are certificate-diagnostic under the SuperMath grading;
independent algorithms improve evidential redundancy but do not make them Lean
kernel checks or independent human certification. Final review and publication
remain closed until the user's substantive frontier criterion is actually met.
