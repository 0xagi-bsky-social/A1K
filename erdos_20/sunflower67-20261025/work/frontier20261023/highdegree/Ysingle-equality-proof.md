# The singleton Y internal pattern: equality is impossible

23 October 2026. This is a targeted ordinary proof for one degree-19 leaf, conditional on the imported universal SF3 structure and H27, together with the exact trace-cover check identified below. It is not an end-to-end Lean result, an independent rerun of the complete degree-19 search, or a final scholarly review.

Assume F is a finite simple four-uniform three-sunflower-free family of size 68. Let x have complete link

    P10(Y) ⊔ P9(Z),

where Y={0,1,2,3,4,5}, Z={6,7,8,9,10,11}, and the supports are disjoint. The P10 model is

    012,015,023,034,045,124,134,135,235,245.

On Z use the same model shifted by six and delete 678. Suppose M={0,1,2,3} is the only member of F contained in Y, and no member is contained in Z. There are r=68−19=49 members avoiding x. We show these assumptions are contradictory.

## Exact trace cover and its equality consequence

For each residual member Q avoiding x, let S=Q∩(Y∪Z). Thus |S|≤4, with no assumption about Q's remaining points. Let n(S) count members with this trace. An incidence row for U counts residual Q with U⊆Q. An exact row (A,U) counts residual Q with Q∩A=U, where A is an actual central member x∪T. We display x symbolically even though residual Q avoids it.

The following seventeen necessary inequalities each enter with weight one:

| Type | Set or exact row (A,U) | Residual upper bound |
|---|---|---:|
| Incidence | U=678 | 2 |
| Incidence | U=6,9,10 | 1 |
| Incidence | U=7,9,10 | 1 |
| Incidence | U=7,9,11 | 1 |
| Incidence | U=8,9,11 | 1 |
| Incidence | U=8,10,11 | 1 |
| Exact | (x012,{1}) | 10 |
| Exact | (x045,{0,5}) | 3 |
| Exact | (x235,{2,5}) | 3 |
| Exact | (x245,{2,4}) | 3 |
| C5 | Residual non-internal members through 3 | 10 |
| Exact | (x023,{0,2}) | 3 |
| Exact | (x034,{0,4}) | 3 |
| Exact | (x{6,7,11},{6,7,11}) | 1 |
| Exact | (x{6,8,9},{6,8,9}) | 1 |
| Exact | (x{7,8,10},{7,8,10}) | 1 |
| Exact | (x{8,10,11},{10,11}) | 3 |

Their right-hand sides sum to 48. Incidence bounds use triple codegree at most two, subtracting an existing central member when appropriate. The exact singleton, pair and triple bounds are respectively 10,3,1; these are the universal intersecting-residue bounds. The C5 row is d(3)−5−I_3≤10, where I_3=1, using the universal complete-C5 deduction d(3)−I_3≤15 from `C5-internal-compatibility.md`. Thus its left side is d(3)−6.

Let q(S) be the sum of the seventeen row coefficients of trace S. The complete twelve-point trace domain has 794 subsets of size at most four. Exclude (i) every four-point internal trace except M, and (ii) any trace S for which

    S∩T=S∩M=T∩M

for a prescribed link block T. The second exclusion is precisely the sunflower obstruction from Q,M,x∪T; every actual residual member passes it. The checker `check_Ysingle_equality.py` evaluates this explicit integer function without a solver, projection-model import, or local-signature catalogue. The saved receipt reports 400 admissible traces, 394 excluded traces, and

    q(M)=0,   q(S)≥1 for every other admissible S.

Because n(M)=1, summing over the actual residual family gives

    r−1 ≤ ∑_S q(S)n(S) ≤48.

Hence r≤49. If r=49, every inequality in the weighted sum is tight: each has nonnegative slack and positive unit weight. In particular the C5 row is tight, so

    d(3)−6=10,   d(3)=16.

This uses an exact sum of integer row inequalities; it does not infer geometric equality from a floating-point optimizer.

## Transport forces d(1)=16

The permutation π=(1 3)(4 5), fixing 0,2, is an automorphism of P10 and preserves M setwise. In tuple form it is

    (0,3,2,1,5,4).

Its block images, in the model order above, are

    023,034,012,015,045,235,135,134,124,245.

Extend π by the identity on x, Z, and all other ambient points. The relabelled family satisfies exactly the same hypotheses. Applying the preceding equality consequence to that relabelled family gives d_F(1)=16. No symmetry of the unknown family itself is assumed.

## Complete C5 links force synchronized P10 tails

The complete-C5 structure lemma in `C5-internal-compatibility.md` states that a sunflower-free triple family of size at least sixteen with a point of degree exactly five whose complete point-link is C5 splits into disjoint-support intersecting parts. The part containing that point consists of its five star triples and its internal cycle covers. Its proof checks the R16 exception explicitly (R16 has only degrees four and six), handles the arbitrary opposite six-member component in the 10+6 case by P10 isolation, and treats the Q8/Q8 shared-leaf possibility without assuming all Q8 supports are isolated.

Apply that lemma in the links of 1 and 3, where the distinguished point is x. M supplies the sole internal member through either point, and its residual triple is a C5 cover in both cases. Since both degrees equal sixteen, each near part has precisely six members: five prescribed central members and M. Each far part has ten members and is a P10, with support outside {x}∪Y.

Write H_i={T⊆V(F)∖({x}∪Y):|T|=3, {i}∪T∈F} for i=1,3. We have |H_1|=|H_3|=10, with each an intersecting sunflower-free P10.

There is a prescribed P10(Y) block C avoiding both 1 and 3; in fact exactly two exist since 10−5−5+2=2. If T∈H_1 and U∈H_3 were disjoint, {1}∪T, {3}∪U and {x}∪C would form an empty-core sunflower. Therefore H_1 and H_3 are cross-intersecting.

A P10 has no transversal with at most two points, since some block avoids any chosen support pair. Its three-point transversals are exactly its ten blocks: such a transversal must be wholly on its six-point support, and the intersecting P10 contains exactly one member of each complementary pair of three-subsets. Thus any three-subset outside P10 has its complement in P10 and misses that block. Every member of H_3 is therefore a member of H_1. Their equal size yields

    H_1=H_3=:P,

a common P10 on a six-point support H outside {x}∪Y.

## Doubled-P10 counting gives the contradiction

The twenty members {1}∪T,{3}∪T for T∈P meet the hypotheses of `doubled-P10.md`. Its ordinary proof shows that every other member avoids H and that

    |F|≤27+d(1)+d(3)−d(1,3).

The pair {1,3} occurs in exactly three members. Two are prescribed central members, x134 and x135; the third is M. There are no others: the link decomposition at 1 consists of its five central members, M, and far members whose tails avoid Y. Therefore

    |F|≤27+16+16−3=56,

contradicting |F|=68. This excludes the singleton-M leaf whenever its complete central link and stated internal assignment occur.

## Exact receipt identity and assurance

The original dual is `degree19/Ypattern01-Z.json`, associated with frozen generator `degree19_projection_v4.py`, whose SHA-256 is

    fd29f91c8423f9b8be6a727ca52651b86521437f51f90b21f1eb03d666131b97.

The current mutable generator is not asserted to have this hash. The dual scale is 10^10. All eleven selected inequality weights are exactly 10^10. After division by that scale, the twelve equality weights, indexed as stored, are

    16:3, 17:1, 24:3, 26:1, 80:1, 84:1,
    88:1, 92:1, 112:1, 116:1, 144:3, 147:1.

Each pair is eliminated into one of the final six exact rows in the table. In particular, the row at index 112 concerns the block {7,8,10}, not {7,9,10}. The original scaled H is 480000000000, the correction is 10000000000, and the upper bound is 490000000000.

The independent checker receipt is `degree19/Ysingle-equality-check.json`, with result PASS. It records source-receipt SHA-256

    848706ad3687959f42f7c6e73fc7822fdacf3a5c35a400b2af479d31d257b00c

and checker SHA-256

    94ad81ea118f99718ef6c3fef76e64386ab9c8e5adbc91708e2f339da56373e7.

This note independently interprets the exact weights, source identity, stabilizer, and ordinary equality geometry. It reuses that saved 794-trace checker receipt rather than claiming a new replay. The numerical leaf bound, equality forcing, universal structural assumptions, and H27 are distinct dependencies. The doubled-P10 isolation proof itself needs no trace certificate.

Frozen structural locators, relative to `../../frontier20261020/prior-art68/repository/`, are `paper/main.tex:206–231` (P10 and intersecting triple classification), `272–331` (isolation and B4), `333–376` (degree/codegree and trace capacities), `443–462` (R16), and `612–636` (high-link classification). The detailed size-sixteen support argument and source boundary are in `C5-internal-compatibility.md`; H27's source boundary is recorded in `doubled-P10.md`.
