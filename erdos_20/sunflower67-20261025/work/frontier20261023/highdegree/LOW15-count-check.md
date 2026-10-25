# Independent LOW15 cone-count and scalar check

23 October 2026. Bounded ordinary proof development, not final review or a global extremal claim. Inspected `LOW15-mu41-research.md`, SHA-256 `3cd423debfe7b966924369d69f2b88d03fd99cc119cfedd4d534733b69bff547`, without editing it. This check covers its P10/cap15 and P9/cap14 arguments; it does not check the subsequent Jin/graph argument.

**Finding:** the scalar179 bound, the cone-average weights with arbitrary internal members, and the related P9 inequality are valid under their stated imported premises. The P10 argument has the exact stronger identity

    3W=10D+5H+2B−3E_bad−10I,

so internal four-sets improve the contradiction. The P9 argument gives `2W≤45Δ−155`, excluding a P9 subfamily in any point-link when Δ≤14. At Δ≤15 it gives only the necessary root degree at least13.

## Actual-family definitions and imported premises

F is finite, simple, four-uniform, and three-sunflower-free, including empty cores. Every actual member has closed neighbourhood at least41; H27 and |F|≥68 suffice for this. The global degree cap is15 for the P10 conclusion,14 for the P9 conclusion. All tail and trace counts below count actual members with multiplicity of exterior completions. No bound is placed on the exterior support.

The needed imported inputs are H27, the universal SF2/SF3 capacities and intersecting SF3 bound/classification, and the guarded prior cross-star theorem. The latter assumes two distinct centres outside both tail supports, actual intersecting SF3 tails which are cross-intersecting, and all their lifts in F. At μ≥41, Δ≤18, it gives a pairwise tail-sum bound15. Its finite-certificate dependency is explicit in `PRIOR_DELTA18_UNLOCK.md` and the frozen source `paper/main.tex:1001–1024`; it is not re-proved by the scalar enumeration here. The pair/singleton resource argument is also written in `D18-P10-internals.md` §7 and the frozen `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md`.

The two counting arguments do not use minimum used degree7, the support≤23 consequence, μ42, a classification of I7, or a high-degree point-link decomposition. They require only the prescribed nine or ten actual cones; completeness of that collection as the entire point-link is unnecessary.

## P10 cone counting, retaining every internal member

Prescribe all ten cones `{x}∪T`, with T in the literal P10 on Y={0,…,5}. Let m=d(x), and R be all members avoiding x. For U⊆Y, let n_U count members Q∈R with Q∩Y=U. Define

    H=Σ_(|U|=1)n_U=Σ_y h_y,
    P=Σ_(|U|=2)n_U,       b_y=Σ_(|U|=2,y∈U)n_U,
    B=Σ_y b_y=2P,
    E=Σ_(|U|=3)n_U,       I=Σ_(|U|=4)n_U,
    D=Σ_Q∈R |Q∩Y|=H+2P+3E+4I.

D is the actual residual incidence, equivalently `Σ_y(d(y)−d(x,y))`. The prescribed cones consume thirty incidences, so at cap15,

    D≤6·15−30=60,       h_y+b_y≤15−5=10.

Other members through x can only strengthen these bounds. Arbitrary internal four-sets are still present in D and in every incidence count.

Let W sum, over the ten cones A, the number of residual members meeting A. Every one of the m members through x meets every cone, so the exact identity at each cone is `|N[A]|=m+|{Q∈R:Q∩A≠∅}|`. Thus `W≥10(41−m)≥260`.

The meeting multiplicity of a trace U is5 for |U|=1,8 for |U|=2,10 for a P10 block U,9 for a nonblock triple U, and10 for |U|=4. For triples, P10 contains exactly one member from each complementary pair on six points, because its ten triples are intersecting. Therefore a nonblock has exactly one disjoint block, its complement. Let E_bad count residual members whose three-point Y-trace is a nonblock. This proves exactly

    W=5H+8P+10E−E_bad+10I,
    3W=10D+5H+2B−3E_bad−10I.

There is no estimate hiding the internal contribution: the coefficient of an internal member in3W is30, whereas its contribution in10D is40. Dropping the two nonpositive corrections is valid even before any internal exclusion.

## The scalar domain really applies to these pools

All residuals with a singleton Y-trace form an intersecting SF4 subfamily. Members with the same centre meet there. If members at different centres y,z were disjoint, a P10 block avoiding y,z would give a cone disjoint from both. Such a block exists: exactly `10−(5+5−2)=2` P10 blocks avoid a given pair. H27 gives H≤27.

Deleting each singleton's centre produces its actual triple-tail family. Within one pool, two disjoint tails with a cone through the centre would give a singleton-core sunflower. Between pools, disjoint tails again give an empty-core sunflower using a cone avoiding both centres. Thus every pool is intersecting SF3, different pools are cross-intersecting, and all tails avoid Y∪{x}. The distinct centres are outside both supports, exactly the cross-star guard. Hence `h_y+h_z≤15` and `0≤h_y≤10`.

For the complete pair pool at a C5 point y, write a member as `{y,j}∪e`, where e is an exterior edge. If two partner points differ, a C5 edge avoiding them supplies the sunflower witness when their exterior edges are disjoint; if the partners coincide, use a prescribed cone through that partner. Every singleton tail meets every exterior edge by the corresponding avoided-partner witness. Each exterior edge has multiplicity≤2 by global triple-codegree2. Its distinct-edge family is a star or a triangle.

The usual star/triangle resource argument therefore yields

| b | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| upper bound on h | 10 | 10 | 8 | 5 | 4 | 2 | 1 |

All witnesses use prescribed cones and the selected singleton/pair members, never absence of an internal four-set. Additional internal members can consume capacity but cannot invalidate these upper bounds. The separate condition h+b≤10 already follows from the global cap and the five prescribed incidences at y.

## Exact scalar maximum179

For integer h,b in the table with h≤7, one has `2h+3b≤20`, hence `5h+2b≤(11h+40)/3`. If all six h's are≤7, summing with H≤27 gives179.

Otherwise HP15 permits exactly one h≥8. For h=10, h+b≤10 gives b=0 and the other five h's sum≤17; their score is≤129, giving total≤179. For h=9, b≤1 and the remaining score is≤floor(398/3)=132, again giving≤179. For h=8, b≤2. A remaining h-sum≤18 gives total≤176. A remaining sum19 gives score≤floor(409/3)=136, but that score is odd because it equals5·19+2B′; it is therefore≤135, giving total≤179. This verifies the source's parity step.

The bound is sharp for this scalar domain. For example,

    h=(4,4,4,4,4,7),       b=(4,4,4,4,4,2)

has H=27, B=22, score179, and satisfies every scalar constraint. This is a scalar witness, not a constructed SF4 family.

Consequently the P10 cones force

    780≤3W≤10·60+179=779,

a contradiction. Under μ≥41 and global Δ≤15, no point-link contains P10. An exact singleton class of size10 would be an intersecting ten-triple P10 in its centre's point-link, so every exact singleton is≤9 under the same premises.

## P9 analogue and the cap14 conclusion

Let P9=P10∖{A}, C=Y∖A, and prescribe its nine cones. Put H_A=Σ_(y∈A)h_y and H_C=Σ_(y∈C)h_y. The prescribed incidences are4 at each A point and5 at each C point. For a global cap d,

    D≤6d−27,
    h_y+b_y≤d−4 for y∈A,    h_y+b_y≤d−5 for y∈C.

If P_CC counts residual pairs wholly in C, the exact meeting weights are4/5 for A/C singletons,8 for C pairs and7 for other pairs, and at most9 for triples and four-sets. Therefore

    9(41−m)≤W≤3D+H_A+2H_C+P+P_CC.

More precisely, with E_bad counting nontransversal triples, the independent literal check gives

    3W=9D+3H_A+6H_C+3P+3P_CC−3E_bad−9I.

Write B_A=Σ_A b_y and B_C=Σ_C b_y. The pair-incidence comparison `P+P_CC≤B_A/2+B_C` has slack one half of the mixed A/C pair count. Hence

    H_A+2H_C+P+P_CC
      ≤Σ_A(h_y+b_y/2)+Σ_C(2h_y+b_y)
      ≤(3/2)(d−4)+3(d−5)+(H_A+2H_C)/2.

P9 still has a block avoiding every pair, since P10 has two and only one block was deleted. Thus H_A+H_C≤27 and all HP15 pair bounds remain valid. Summing the three pair bounds within C gives2H_C≤45; integrality gives H_C≤22. Substitution yields

    W≤18d−81+(9d−42+49)/2=(45d−155)/2.

At d=14, m≤14 gives2W≥486 while2W≤475, a contradiction. Thus no point-link contains P9 at cap14, and every exact singleton has size≤8. At cap15 the same inequality only gives `9(41−m)≤260`, hence m≥13. No P9 exclusion at cap15 follows from this average alone.

This calculation uses actual prescribed occurrence counts and degree capacities, without applying the C5 pair table to any P5 point. Its internal-four-set contribution is again favourable and retained.

## Small independent checker

`check_LOW15_count.py`, SHA-256 `baf099440529ef80f791e9cd5e64f4f9f9d7eee885afb1427933e5f8579f2775`, imports only the Python standard library. It uses the literal ten-block P10, not a numerical producer. It was run as

    python3 work/frontier20261023/highdegree/check_LOW15_count.py

and returned PASS. It checks all57 subsets of Y of size≤4 against each exact P10 and P9 contribution identity, including all15 internal four-sets without sunflower filtering. For the scalar maximum it constructs all46 admissible (h,b) pairs. Since all cross-coordinate constraints involve only h and the score increases in b, it chooses the maximum permitted b at each h. Symmetry then reduces to nondecreasing six-tuples of h. All2446 feasible sorted tuples are checked; the maximum is179, with19 maximizing tuples. Removing HP15 raises the maximum to183, which confirms that the guarded cross-star input is substantive for this scalar proof.

The checker is an exact bounded diagnostic. The written proofs above establish the family-to-count implications and the scalar bound ordinarily; neither this diagnostic nor the note is a Lean formalization, independent certification of the imported cross-star package, or a global exclusion of68.
