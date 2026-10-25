# Degree 18 with a P10 component: nonempty internals are excluded

23 October 2026. All twelve nonempty P10 internal-orbit certificates pass exact integer replay against the frozen size-68 component model. Together with the ordinary family-to-model bridge below and its explicit imported premises, they exclude a nonempty internal family on the P10 support. This is a proof-development result for this branch. It does not exclude the empty P10 state, the P9+P9 degree-18 branch, or every degree-18 point, and it is not a Lean proof or final review.

The replay used no solver and no SciPy matrix construction. It rebuilt the small internal catalogue and necessary local-state domains through the hash-matched producer's `catalog` and `build`, then independently recomputed the weighted row sums and box minimum with Python integers. This is shared-producer model reconstruction and exact arithmetic replay, not an independent implementation of the model.

## 1. Exact scope and mathematical conclusion

Let F be a finite simple four-uniform family without a three-sunflower, including an empty core. Assume:

1. `|F|>=68`, every point degree is at most 18, and x has degree 18.
2. The complete link of x is a P10 on `S={0,...,5}` and an intersecting eight-triple family on support disjoint from S. Thus exactly ten members through x meet S; they are the prescribed P10 cones. No form or support-size bound for the opposite eight-triple family is imposed by this component model.
3. H27 holds for intersecting four-uniform sunflower-free families.
4. The imported universal SF2/SF3 capacities, I8/I9/I10 classification, isolation, B4, R16/high-link structure, and universal rooted trace margins and extension-point compatibility hold. The complete-C5 degree-16 deduction in `C5-internal-compatibility.md` is used as an ordinary consequence of these premises.

Then no member of F is contained in S.

The complete degree-18 decomposition with a P10 component is supplied by the universal high-link theorem when this branch occurs. The **global** point cap 18 is a separate premise, supplied in the intended application only after higher-degree branches have been excluded. The displayed degree of x alone does not imply it.

H27 gives `|N_F[R]|>=|F|-27>=41` for every actual member R. The model uses this threshold 41; no threshold 42, minimum positive degree four, pair-degree sum 20, anchor-degree sum 52, or singleton bootstrap seven is imported. A family satisfying the corresponding local assumptions `mu>=41` and the H27 singleton-pool bound also maps into the model without referring separately to its size.

## 2. Replayed files and exact results

The twelve receipts are `degree18/P10_001.json` through `degree18/P10_012.json`. Every one selected the frozen source `degree18_component_v1.py`, SHA-256

    3463c85f1e22de41d1c41ce4e43b6d2ab3e2ccfe7b6aa870c3e200ef87964c02

and matched imported `local43.py`, SHA-256

    258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b.

The replayer is `replay_component18.py`, SHA-256

    23f7a2bbd98374761de07da5e98c52cf5d3ed901499bd1c546f769df68cb038e.

For `A z<=b`, `E z=f`, `l<=z<=u`, it reads nonnegative stored integer weights in the producer's order `A,E,-E`, computes q and H, and verifies

    minimum = sum_j min(l_j*q_j, u_j*q_j),
    G = H-minimum < 0.

Every original column, including each degree and anchor selector, contributes to the box minimum. The artificial phase-one slack column is absent. A hypothetical feasible vector would imply `minimum<=q.z<=H`, a contradiction. The scale `10^10` is recorded; no numerical tolerance or floating-point phase-one minimum enters the conclusion.

The complete nonempty-orbit table is:

| Case | Complete internal representative | Orbit size | Columns | Replayed H | Replayed minimum | Exact G | Result |
|---|---|---:|---:|---:|---:|---:|---|
| P10_001 | 0123 | 15 | 3209 | -370370376 | -59 | -370370317 | PASS |
| P10_002 | 0123, 0134 | 30 | 446 | -10000000000 | 0 | -10000000000 | PASS |
| P10_003 | 0123, 0145 | 30 | 1523 | -1875000000 | 0 | -1875000000 | PASS |
| P10_004 | 0123, 0245 | 15 | 293 | -10000000000 | 0 | -10000000000 | PASS |
| P10_005 | 0123, 0134, 0145 | 30 | 243 | -10588235294 | -6 | -10588235288 | PASS |
| P10_006 | 0123, 0134, 0245 | 60 | 113 | -20000000000 | 0 | -20000000000 | PASS |
| P10_007 | 0123, 0134, 1245 | 30 | 230 | -10666666667 | -9 | -10666666658 | PASS |
| P10_008 | 0123, 0145, 2345 | 10 | 753 | -10000000000 | 0 | -10000000000 | PASS |
| P10_009 | 0123, 0245, 1345 | 5 | 107 | -10000000000 | 0 | -10000000000 | PASS |
| P10_010 | 0123, 0134, 0145, 1235 | 30 | 118 | -20000000000 | 0 | -20000000000 | PASS |
| P10_011 | 0123, 0134, 0145, 2345 | 30 | 109 | -20000000000 | 0 | -20000000000 | PASS |
| P10_012 | 0123, 0134, 0145, 1235, 1245 | 6 | 105 | -20000000000 | 0 | -20000000000 | PASS |

All twelve were run serially, with a 20-second process alarm per case. Observed individual times were 1.66–2.55 seconds; the serial batch took 28.43 seconds. No deadline was exceeded. `P10_000` was not replayed in this task.

The compact batch receipt is `degree18-replay/P10-nonempty-summary.json`. The twelve detailed receipts are `degree18-replay/P10_001-replay.json` through `P10_012-replay.json`. Each binds its input receipt, source, imported local43, catalogue, complete integer rows and boxes, replayed q, and arithmetic. Each also stores the weighted row names and their A/E/-E signs.

The standalone entry accepts one receipt and selects either the frozen v1 source or the current producer by exact SHA-256; `--source v1` or `--source current` can restrict that selection. It refuses a source mismatch. All current twelve successes concern v1. The current producer read during this task had SHA-256

    8300c77fb1bf46c35f0028debf91b41a6ed07b035d9d324fb1239b98cc5bc557;

it adds whole-component singleton-pool rows, which were not used in these twelve v1 replays. Support for selecting that source is not a claim that a current-source receipt was replayed here.

## 3. Catalogue coverage: all nonempty internals occur in the table

Use the fixed P10 model

    012 015 023 034 045 124 134 135 235 245.

The internal family is the **complete** assignment `I=F intersect binom(S,4)`, including absences of every other internal four-set. There are fifteen possible four-sets. The recursive `catalog(10)` starts with the ten fixed cones, visits every increasing sequence of the fifteen four-set indices, and permits a new member precisely when it forms no sunflower with two existing fixed or selected members.

Every actual internal assignment is reached: each of its prefixes is sunflower-free, so none of its successive additions is rejected. Conversely a generated assignment has no forbidden triple, since a forbidden triple would be detected when its last selected member was inserted; the initial P10 cone family is already sunflower-free. This proves the recursion's necessary-domain coverage without imposing properties on exterior completions.

The automorphism loop considers all 720 permutations of S and retains exactly those preserving the P10 block set. These form its full automorphism group. Its action on the fifteen four-sets preserves compatibility with the fixed cones. The representative loop takes one previously unseen assignment and marks its whole orbit; the final `seen==set(all_int)` check verifies the covered assignment list exactly.

The replayed output has 292 compatible assignments, 60 automorphisms, and 13 orbits. The twelve orbit sizes above sum to 291; the thirteenth orbit is the unique empty assignment. The size histogram for internal sizes zero through five is `1,15,75,135,60,6`. The canonical JSON digest of the rebuilt catalogue is

    37168963641376910c922ef83f2c6af1aebaed7c9335b5b04d059741f3308a05.

These are executed finite checks by the source-hashed Python producer, with a source-inspected completeness argument; they are not a Lean-verified classification. Under any component automorphism, relabel the entire hypothetical F, fixing x and all exterior points. This sends its internal assignment to the listed representative without assuming the unknown completion itself is symmetric. Thus the twelve contradictions cover all nonempty actual internal assignments.

## 4. Exact proper traces and all box restrictions

The label of x in this component constructor is 6. For each nonempty `U subset S` of size at most three define

    n_U = #{Q in F : x notin Q and Q intersect S = U}.

There are 41 coordinates: 6 singleton, 15 pair, and 20 triple traces. They are multiplicities of actual members, not binary existence flags. Arbitrarily many distinct ambient exterior labels may be used. Actual internals I are counted separately as fixed members. The other eight members through x avoid S and therefore contribute to none of these coordinates. Members with empty S-trace are omitted because they contribute to none of the modeled neighbor statistics; their number is not artificially bounded.

Let B be the ten prescribed P10 cones together with all members of I. Every member of B is an actual member, and every point of B is in `S union {x}`. The implemented boxes are

    0 <= n_U <= cap(|U|) - #{Q in B : U subset Q},
    cap(1)=18, cap(2)=6, cap(3)=2.

The exact trace class is a subset of the incidence class through U, so subtracting fixed incidences is valid. The box may be weaker than the full joint incidence constraint; this causes no problem. The three capacities are respectively the assumed global point cap and the universal pair/triple codegree bounds.

If two distinct fixed members A,B satisfy

    A intersect B = A intersect U = B intersect U,

the coordinate n_U is set to zero. For any actual Q counted by it, its intersections with A and B depend only on U: Q avoids x, and both fixed members lie on `S union {x}`. Q is distinct from a fixed cone because it avoids x, and from a fixed internal because its trace has size at most three. Thus this test forbids a literal sunflower for every exterior completion of U.

The complete assignment is required. Treating the listed internals as only selected presences would invalidate the fixed offsets and the confinement filter below.

## 5. `raw_rows`: threshold 41, degree cap 18, and zero bootstrap

For a central anchor `R={x} union T`, order its points `(x,a,b,c)` by the sorted triple T. The first six entries of a row are exact pair counts in order `xa,xb,xc,ab,ac,bc`; the next four are triple counts indexed by the omitted anchor point; the last four are singleton counts in the same point order. Write them as p,t,s. Then

    k_i = 1 + sum_{j != i} p_ij + sum_j t_j - t_i,
    d_i = s_i+k_i.

The complete centre link fixes the three x-pair counts and three x-containing triple counts from the P10 model. It fixes `s_x=8`, because the opposite eight members have disjoint support, while all P10 blocks intersect T. Hence `k_x=10` and `d_x=18` at every central anchor.

The loop considers every free pair count in 0,...,3, every free triple count in 0,1, and every neighbor singleton count in 0,...,10 that passes `local_s_candidates(...,17,0,0)`. The universal capacities prove those ranges. The zero final parameters remove the old singleton bootstrap; the lower degree test is only the unavoidable `d>=1` for an anchor point.

The helper's remaining filters have the following universal meanings, as detailed in `D19-model-bridge.md`, §4:

* At degree 17 or 18, the singleton/near sizes are the two parts of the universal disjoint-support high-link decomposition.
* When `s>=8`, B4 gives an intersecting near family with `k<=10`; D6 gives incident pair mass at most six, D8 bounds pairs facing an occupied complementary triple by two, and D7 gives all incident pair counts at most two when `k>=9`.
* For near sizes 8,9,10, the signature builder includes every anchor and every ordering in every size-k P10 subfamily, and Q8 at size eight. This is complete under the imported I8/I9/I10 classification, independently of the ambient support.
* The extension consistency test only rejects conflicts between forced equality and forced distinction of actual extension points. Equality is propagated transitively; it is not inferred from two equal counts.

The caller caps all four degrees by 18, imposes `1+sum p+sum t+sum s>=41`, and imposes degree sum at least 19 for every pair of anchor points. The last condition follows directly from the size-41 neighborhood: members in it avoiding a chosen anchor pair lie in two singleton classes and one pair class, at most `10+10+3=23`. The union of the two point stars therefore has size at least 18; their common actual anchor adds at least one back in the degree sum.

The five margin bounds `(12,14,17,19,22)` for `sum p+sum t`, according to the number of singleton classes below eight, are the universal `TRACE_FOUNDATIONS` D.3–D.5 results. The “at most two degrees >=19” filter is vacuous under this caller's cap 18. No old mu42 row enumeration or ordering of the unknown neighbor degrees is copied into `raw_rows`.

Thus the actual fourteen-trace row appears before the additional assignment-specific filtering. Sorted deduplication only merges identical count vectors.

## 6. Shared six-point support proves the `clean` and `esc` filters

This is the central structural step; an arbitrary seven-member intersecting family is never classified as P8 or Q8.

Fix a point y of the component, a central anchor through it, and the complete triple link L_y. Its distinguished point x has the complete prescribed C5 star in the P10 case. For the P9 version of the same constructor, it has a C5 or a four-edge P5 star. Put

    V = {x} union (S minus {y}).

The star triples collectively cover all six points of V. Let A be the link-anchor triple, let D be the triples disjoint from A, and let K be those meeting A, with sizes s,k. Every star triple is in K because A contains x. The list `links[y]` is the star plus **all** assigned internal triples through y. Its cardinality is `fy[y]+iy[y]`.

The code activates confinement when

    s>=8, or d(y)>=17, or (the star is C5 and d(y)>=16).

In each of these regimes K is intersecting and every assigned internal triple belongs to K:

1. If `s>=8`, B4 makes K intersecting, and D is itself an intersecting SF3 family. If D is P8/P9/P10, its entire support avoids A. P-type isolation forces every member of K to avoid that support: a deleted P10 block would also avoid A and thus belong to D. As K contains the star spanning V, D's support is disjoint from V, so no internal triple can be in D.
2. If D is Q8, use only its five-point core. The entire Q8 support avoids A. Its two possible additional triples meeting the core also avoid A and hence cannot occur in K. Core isolation therefore makes K avoid the Q8 core. The star spanning V implies this core is disjoint from V. Every Q8 member contains at least two core points, so no member of D is an internal triple on S. This argument allows shared leaves.
3. At `d(y)>=17`, the universal high-link decomposition gives two intersecting components on disjoint supports. The one containing x contains the full star and therefore V. It is exactly K; the other is D and avoids V. Every internal triple lies in K.
4. In the extra C5 regime `d(y)=16`, the complete-C5 structure lemma gives the same conclusion. Its proof excludes R16 because its points have only degrees four and six, handles the P10+I6 and P9+I7 possibilities by P-type isolation, and excludes Q8+Q8 using its core point-links and leaf degrees. It does not assume an arbitrary sixteen-triple family splits.

It follows that all members in `links[y]` lie in the same intersecting K. If `clean[y]` is false, two of them are disjoint, so the candidate row is impossible. Otherwise `k>=len(links[y])` is necessary.

For C5, any other member of K avoids x and must meet every cycle edge. Covering C5 requires at least three of its five vertices. A triple covering it is therefore wholly on `S minus {y}`, hence is an assigned internal already in `links[y]`. Thus

    k = len(links[y])

in every activated C5 regime. This proves the P10 implementation, where `esc[y]=0` for all six points.

For completeness, the P5 code in the shared constructor is also safe. Any extra triple of K not already in `links[y]` must use the unique two-vertex cover C of the path plus a point outside V. There can be at most two such triples by the pair codegree bound, with internal occupation of C already counted in `links[y]`. The `covers` computation requires C to meet every member of `links[y]`, so it also enforces compatibility with the assigned internals.

The `esc` test tries one or two triples `C union {7}`, `C union {8}`, requiring both intersection and absence of a three-sunflower with the fixed link. These two labels are fresh relative to `V={0,...,6} minus {y}`. If an actual set of one or two exterior additions exists, their distinct actual exterior points can be renamed to 7,8 while fixing V; every intersection in this test is preserved. Thus `esc` is an upper bound for the number of actual additions. It is not an exterior-support cutoff. No existence of a globally realizable completion is inferred from a successful test.

Finally, whenever activated K has `k>=8`, I8/I9/I10 applies. It cannot be Q8: no Q8 point-link contains the full prescribed C5 or four-edge P5. It is consequently P8/P9/P10 on six points. Its support already contains all six points of V, so it is **exactly V**. Every non-star triple is internal and already assigned, and exterior escape is impossible. This justifies the conditional upper limit

    k <= len(links[y]) + (esc[y] if k<8 else 0).

At `k=7` the proof uses only intersection, the unique P5 two-cover, and the pair codegree bound. There is no I7 classification hidden in this inequality.

The degree cap `caps[y]=min(18,15+I_y)` for a C5 point follows from deleting its internal triples and applying the complete-C5 obstruction. For P5, the universal high-link decomposition forces `I_y>=1` at degree 17 and `I_y>=4` at degree 18, by the same path-cover argument; when k>=8 the six-point support gives `I_y=k-4`. The cap loop only applies these proved necessary lower bounds. All six points in the twelve P10 cases are C5 points.

## 7. Exact equations, common degrees, and remaining upper rows

For each point y the model chooses exactly one integer degree in the range from its fixed incidence count `fy[y]+iy[y]` to `caps[y]`. Its degree-tie equation is

    sum_{U contains y} n_U - sum_d d * delta_{y,d}
      = -fy[y]-iy[y].

This is the exact degree decomposition: the only omitted members either avoid S or are the fixed members already subtracted.

At each central anchor the model chooses one surviving fourteen-trace row. The seven exact trace classes avoiding x are the three singleton classes, three pair classes, and full component block T. For each such feature W its equation is

    sum_{U : U intersect T = W} n_U - sum_r lambda_r * row_feature(r)
      = -#{Q in I : Q intersect T = W}.

Fixed cones cannot contribute to a trace avoiding x; assigned internals contribute exactly the displayed offset. The code's feature positions 11–13, 3–5, and 6 are respectively the neighbor singletons, free pair counts, and triple omitting x in the row layout of §5. The bucket upper/lower pruning retains an actual row because actual trace coordinates lie in their boxes. The anchor-degree equations identify the chosen degree at every anchor with the same point's common selector. Every actual family sets its actual point-degree and anchor-row selectors to one and the others to zero, satisfying all these equations simultaneously.

The remaining thirteen v1 upper rows for P10 are six copies of each of

    b_y<=6,    5*h_y+9*b_y<=59,

and the single row

    sum_y h_y<=27.

Here `h_y=n_{ {y} }` counts the complete exterior singleton family at y, and `b_y=sum_{j!=y} n_{ {y,j} }` counts all pair-trace members through y in the P10 case. These are component traces, not exact traces at one smaller anchor.

For the pair bounds, write a pair member as `{y,j} union E`, with E an exterior edge. The exterior edges are pairwise intersecting: for different partners j,k, a C5 star edge avoiding both exists; a disjoint E,E' together with its cone gives a sunflower with core y. For equal partners use a cone through y,j. Every singleton tail meets every such edge by a cone through y avoiding j. An edge occurs at most twice by the triple codegree of `{y} union E`.

An intersecting simple edge family is a star or triangle. In a triangle, multiplicity two gives `b<=6`; every singleton tail covers the triangle, and the three triple-codegree capacities give `b+h<=6`. In a star, the pair codegree through its centre gives `b<=6`. With two distinct leaves, at most two singleton tails avoid the centre and at most `6-b` contain it, giving `h<=8-b`. For b>=5, at least three distinct leaves force at most one centre-avoiding tail, giving `h<=7-b`. With only one distinct edge, `b<=2` and summing the two endpoint pair capacities gives `h+2b<=12`. Together with `h<=10`, the resulting necessary bounds for b=0,...,6 are

    h <= 10,10,8,5,4,2,1.

Every entry satisfies the two displayed affine rows. For a P5 point in the shared constructor, the same argument must be applied separately after excluding each endpoint of its unique two-cover from the partner choices; `pair_constraints` does exactly that. It does not apply the argument to the unrestricted P5 pair family.

For the singleton-pool row, all actual four-sets with exactly one S point form an intersecting family. Two with the same point meet there. For distinct points y,z, a P10 block avoiding y,z exists; if the two members were disjoint, its cone would be disjoint from both. H27 therefore bounds this actual pool by 27. This includes arbitrary exterior completions and does not assume internal emptiness.

The current producer's extra `whole-pool` rows require lower bounds on h_y from the central singleton size s_y. The separate proof in `D18-structural-tools.md` gives h_y=s_y in the high-degree separation regimes, h_y=s_y at s_y=9,10 by P-type isolation, and h_y>=6 at s_y=8 using Q8 core isolation if necessary. These rows are absent from frozen v1 and are not needed for the present twelve contradictions.

## 8. Replay checks and conclusion boundary

The replayer checks the exact case fields, `outside=18-component`, `r10=r9=0`, canonical interior four-sets, and equality with the identified complete orbit representative. It matches both source hashes before rebuilding, validates every model coefficient, right-hand side, and finite box as a Python integer, checks dimensions and local catalogue sizes against the original receipt, and checks the stored zero objective/target convention. It rejects duplicate or out-of-range weight indices and negative source weights. Its exact arithmetic includes all original rows and columns and compares H, minimum, G, and the negative-gap flag with the stored values. It verifies source, dependency, and input-receipt stability at the end.

The mathematical bridge above maps any hypothetical family with a nonempty assigned P10 internal into its corresponding model. The complete 292-assignment catalogue and 60-element symmetry action reduce every nonempty assignment to one of the twelve table rows. Each row has a strictly negative exact gap. Hence the P10 internal family must be empty under §1's premises.

This result retains imported universal structure and H27 as ordinary mathematical dependencies. It neither copies the old mu42 certificates nor claims a Lean check of the new Python models. The empty P10 case and the rest of degree 18 remain separate research obligations.

Sources inspected: the frozen Oct20 `paper/main.tex:188–231,272–376,443–462,612–636`; `companion/upstream/MU42/TRACE_FOUNDATIONS.md`, D.1–D.5; `companion/upstream/MU42/scripts/local43.py`; `companion/upstream/D18_P10/PROOF.md`, §§1–3,8.2; `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md`, pair/singleton and complete exterior-family arguments. October 23 bridges used: `D19-model-bridge.md`, `C5-internal-compatibility.md`, `D19-singleton-I04.md`, and `D18-structural-tools.md`.
