# The upstream bootstrap at neighborhood threshold 41

Date: 2026-10-20. Task mode: substantive exploratory mathematical research.
Source: Oleksiy Babanskyy's *An upper bound for three-sunflower-free families
of four-element sets*, repository pinned at
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.

This note studies a hypothetical simple SF4 family of size 68, with empty
sunflower kernel forbidden. H27 would give minimum closed neighborhood
`μ ≥ 41`. The objective is to identify usable premises for excluding 68,
not to certify the reported exclusion of 69. No final review process was
run. No external source file or frozen Lean file was changed.

The principal useful finding is an existing result in the external companion:
**under μ ≥ 41 and Δ ≤ 18, its crowding argument already supplies minimum
used degree 7 and, at cardinality 68, support at most 23.** These are not
new results claimed by this note. Below is a written reconstruction of the
short counting and private-vertex arguments needed to use those conclusions.
This avoids trying to transfer the whole μ42 bootstrap.

The new probes here are `certificate-diagnostic`; the ordinary derivations
are not Lean formalizations. The selected unchanged external finite suites
were separately replayed by the coordinating agent in normal and optimized
Python. Their receipt is
[`../../replay-selected-20261020/RECEIPT.json`](../../replay-selected-20261020/RECEIPT.json).
It records a selected-four-suite partial pass, not a full companion replay,
not a formalization of the written reductions, and not independent human
validation.

## 1. Conventions and μ-independent premises

For an actual ordered anchor `R={0,1,2,3}`, write

```
p = (p01,p02,p03,p12,p13,p23)
t = (t0,t1,t2,t3), with ti the trace omitting i
s = (s0,s1,s2,s3)
P = Σp, T = Σt, S = Σs
ki = 1 + Σj≠i pij + T − ti
di = ki + si
N = |N[R]| = 1 + S + P + T
D = Σi di = 4 + S + 2P + 3T = N + 3 + P + 2T.
```

All counts concern actual distinct members. Empty traces are not artificially
bounded. The following source ingredients do not depend on μ42:

* Global point/pair/triple capacities 20/6/2.
* Exact trace capacities `si≤10`, `pij≤3`, `ti≤1`.
* B4: `si≥8` makes the neighboring part of the point-link intersecting.
* The rooted I8/I9/I10 signatures, universal R16 classification and maximality,
  and degree-17 through degree-20 link decompositions.
* The five margins `P+T≤(12,14,17,19,22)[q]`, where `q` counts `si<8`.
* The actual equality/distinction constraints for triple-extension points.
* At most two points of degree at least 19 in one anchor.
* The separate C5 obstruction, P5/C5 confinement, and the external-family
  constraints `Σ|Hy|≤20` in the P10 case and `≤22` in the P9 case.

The last statements are geometric or local finite premises; dropping μ by
one does not alter their hypotheses. Their sources are
[`../../repository/companion/upstream/MU42/TRACE_FOUNDATIONS.md`](../../repository/companion/upstream/MU42/TRACE_FOUNDATIONS.md),
[`../../repository/companion/upstream/MU42/C5_PROOF.md`](../../repository/companion/upstream/MU42/C5_PROOF.md),
and
[`../../repository/companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md`](../../repository/companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md).

There is a simple unconditional replacement for the old co-occurring
degree-sum bound. For `x,y∈R`, with complementary points `z,w`,

```
N = d(x)+d(y)−d(x,y)+sz+sw+pzw
  ≤ d(x)+d(y)−1+10+10+3.
```

Thus **μ41 implies `d(x)+d(y)≥19`** for every co-occurring pair.
The corresponding value at μ42 is 20.

Also `D≥N+3≥44`. This is the correct elementary member-sum bound before
further structural restrictions.

## 2. Precisely what fails in the old μ42 bootstrap

The old proposition asserts singleton 9 or 10 requires `k≥7`, minimum degree
4, pair sum 20, member sum 52, and a support charge at most `17/50`.
These cannot be transferred by replacing the symbol 42 with 41.

The one-constructor bounded raw-domain probe
[`probe_domain41.py`](probe_domain41.py) imports the source's arbitrary-μ
constructor without editing it. Its full output is
[`domain41-diagnostic.json`](domain41-diagnostic.json).

| Necessary conditions imposed | Rows | Degree profiles | Min degree | Min pair sum | Min member sum |
|---|---:|---:|---:|---:|---:|
| Universal μ41 domain | 1,451,334 | 1,447 | 1 | 19 | 44 |
| Additionally assume `r9=r10≥6` | 808,547 | 1,259 | 1 | 19 | 50 |
| Additionally assume `r9=r10≥7` | 460,453 | 1,161 | 1 | 19 | 50 |
| Additionally assume `r9=r10≥7`, degree≥4 | 460,429 | 1,149 | 4 | 19 | 50 |

The last three lines are conditional diagnostics. The singleton assumptions
have not been proved at μ41. These rows are numerical necessary states, not
constructed SF4 families.

Explicit boundary states make the lost units visible:

1. Degree 1 is admitted by
   `p=(0,0,0,3,3,3)`, `t=(1,0,0,0)`,
   `s=(0,10,10,10)`, giving `d=(1,18,18,18)` and `N=41`.
   At μ42 this row is removed solely by its neighborhood size.
2. The all-singleton row `p=t=0`, `s=(10,10,10,10)` has
   `N=41`, `d=(11,11,11,11)`, and member sum 44.
3. Even after imposing the old singleton `k≥7` rule, the row
   `p=(0,0,0,0,3,3)`, `t=0`, `s=(8,8,8,10)`
   has `k=(1,4,4,7)`, `d=(9,12,12,17)`, `N=41`,
   and member sum **50**. It also satisfies crowding26.
   See [`member50-witness.json`](member50-witness.json).

The raw μ41 domain has one degree-1 row, four degree-2 rows, and 25 degree-3
rows. Unlike at μ42, not every degree-3 row has singleton count 2 at that
point. Consequently the old argument “all three link triples are pairwise
disjoint” does not cover the new degree-3 domain. The old special degree-2
lemma assumes all six neighbors have degree 18; new degree-2 rows include
neighbor triples `(17,17,17)`, `(17,17,18)`, and `(17,18,18)`.

The old star charge also fails at μ41. Even under the conditional
`r9=r10≥7` and minimum-degree-4 restrictions, 56 rows violate it. The largest
corrected charge is `23099/61200`, exceeding `17/50` by `2291/61200`.
One witness is

```
p=(2,0,0,3,3,3), t=(1,0,0,0), s=(1,7,10,10)
d=(4,17,18,18), k=(3,10,8,8), N=41.
```

Its old correction weight is 425. This particular obstruction has top-three
singleton sum 27 and is removed by the existing crowding26 theorem once
`Δ≤18` has been established. It is not evidence against that theorem.

There are also important implementation traps. The source
`component42.base_rows` hardcodes minimum degree 2 and used-pair sum 20;
`component_projection42.raw_rows` additionally hardcodes member sum 46 and
neighborhood 42. Its degree-selector interval begins at 2. These are
μ42-derived restrictions, not universal geometry. Passing a new μ parameter
without changing those premises would silently delete legitimate μ41 states.

## 3. The usable existing μ41 theorem after Δ≤18

The source paper's crowding lemma explicitly assumes **μ≥41 and Δ≤18** and
concludes that the three largest singleton counts at any anchor sum to at
most 26. The companion's crowding certificate additionally declares

```
minimum_used_degree = 7
support_at_cardinality_68 = 23
global_67_proved = false.
```

These conclusions occur in
[`../../repository/companion/terminal/crowding/code/verify.py`](../../repository/companion/terminal/crowding/code/verify.py),
in `mathematical_replay` and `local_and_global_checks`. They are existing
external results. The following reconstruction explains their mathematical
bridge in full.

Fix `R={x,a,b,c}`, let `m=d(x)`, put `Sx=sa+sb+sc`, let `Px` sum the three
pair traces within `{a,b,c}`, and write `u=tx` for the triple trace omitting x.
Then exactly

```
N = m + Sx + Px + u.
```

Crowding26 gives `Sx≤26`; trace capacities give `Px≤9`, `u≤1`.
Thus `41≤m+36`, so every used degree is at least 5.

### Eliminating degrees 5 and 6

If `m=5`, then necessarily `Sx=26`, `Px=9`, `u=1`, hence the three opposite
pair traces are `(3,3,3)`.

If `m=6`, then `Sx≥25`. When `Sx=25`, again `(Px,u)=(9,1)`.
When `Sx=26`, the only opposite configurations are

```
(pab,pac,pbc;u) = (3,3,3;0), (3,3,3;1),
                  or a permutation of (2,3,3;1).
```

In every case at least two among `sa,sb,sc` are at least 8: otherwise their
sum is at most `10+7+7=24`.

Choose such a point y. B4 makes the part `Ky` of `Ly` meeting `R\{y}`
intersecting, and

```
|Ky| = d(x,y) + pyz + pyw + u,
```

where `{z,w}={a,b,c}\{y}`. For an intersecting triple family of size 8, 9,
or 10, inspect its root `R\{y}` and record

```
(family size, degree of x, singleton trace at z,
 singleton trace at w, pair trace zw).
```

Among the 17 rooted projections of P8/Q8/P9/P10, the pattern `(3,3,1)` in
the last three coordinates occurs only as `(8,1,3,3,1)`. Patterns
`(3,3,0)` and `(2,3,1)` never occur. Therefore:

* For `(pyz,pyw,u)=(3,3,1)`, necessarily `d(x,y)=1`.
* For `(3,3,0)` or `(2,3,1)`, a codegree at least 2 would make `|Ky|≥8`
  and give a forbidden projection. Again `d(x,y)=1`.

Thus every member of `Lx` has at least two private vertices, meaning vertices
of degree 1 in that complete link.

An SF3 family with at least two private vertices in each triple has at most
four triples. Indeed, any nonisolated triple can intersect others only in
its unique nonprivate point. Each connected intersection component is
therefore a star. It has at most two triples, since three would form a
sunflower with that center. There are at most two components, since a triple
from each of three components would give an empty-kernel sunflower.
Hence `|Lx|≤4`, contradicting `m∈{5,6}`.

This proves the conditional **minimum used degree at least 7** from the
crowding lemma and the ordinary I8/I9/I10 classifications.

The narrow local check was rerun separately here. It reconstructed 17 rooted
projections and 45/339 relaxed degree-5/degree-6 states, all having the required
private-point property. Its receipt is
[`crowding-local-diagnostic.json`](crowding-local-diagnostic.json).
This run did not itself replay the crowding certificate; the coordinating
agent's selected-suite receipt does record that separate replay.

### Member sums and support

Crowding also gives `S≤34`. To see this, sort the four singleton counts:
the smallest is at most 8, while the other three sum to at most 26.
Therefore `P+T=N−1−S≥N−35`, and

```
Σv∈R d(v) = N+3+P+2T ≥ 2N−32 ≥ 50.
```

This is a direct member-sum replacement that does not require any new
singleton-forcing bootstrap.

A stronger asymmetric inequality is useful. Put
`q_y=d(x,y)` for `y∈{a,b,c}`, and `Q=qa+qb+qc≥3`. Exact counting gives

```
d(a)+d(b)+d(c) = Sx + 2Px + 3u + Q
               = 2(N−m) − Sx + u + Q
               ≥ 59−2m.
```

Choose x of minimum degree in the anchor. Every sorted anchor degree tuple
`(m,d2,d3,d4)` consequently satisfies

```
7 ≤ m ≤ d2 ≤ d3 ≤ d4 ≤ 18,
m+d2 ≥ 19,
d2+d3+d4 ≥ 59−2m.
```

The existing source's exact 664-tuple check gives

```
Σv∈R 1/d(v) ≤ 439/1260,
```

with maximizing relaxed tuple `(7,12,15,18)`. Summing over all 68 members,
each support point contributes exactly one, so

```
|supp F| ≤ floor(68 · 439/1260)
         = floor(7463/315)
         = 23.
```

The degree cap gives the lower bound
`|supp F|≥ceil(272/18)=16`. Thus the usable existing interval is
**16≤|supp F|≤23**, conditional on μ41 and Δ18.

For clarity, this support result needs neither the old `r9=r10≥7` bootstrap
nor the μ42 star-charge certificate.

## 4. Bounded singleton-component probes

Two exploratory copies were created in this directory, with the exact changes
recorded in [`component-probe-adaptations.json`](component-probe-adaptations.json).
The μ42 assumptions were replaced by positivity and the ordinary pair-sum
bound 19. The probes additionally impose Δ18 and crowding26; no old singleton
lower bound was used. The upstream files remain unchanged.

The source's `k≤5` reduction increases the central singleton count to 5.
This is still a permissible relaxation here: the center then has degree at
most 15; its singleton remains below 8; and inserting a singleton of size at
most 5 into the three-largest sum can contribute at most `10+10+5=25`.
Thus this increase cannot create a new crowding26 violation.

Both probes use every compatible complete internal family on the isolated
six-point component, then the shared six global neighbor degrees, and finally
all 256 admissible correlated external lower-bound vectors. They are necessary
relaxations only; no external support bound is imposed.

| Component, `k≤5`, μ41, Δ18, crowding26 | Internal assignments | Central rows | Scalar survivors | Correlated survivors |
|---|---:|---:|---:|---:|
| P10 | 292 | 60,640 | 8,780 | 8,473 |
| P9 | 373 | 40,473 | 3,310 | 3,012 |

Results:
[`component-P10-k5-cap18-crowding1.json`](component-P10-k5-cap18-crowding1.json)
and
[`component-P9-k5-cap18-crowding1.json`](component-P9-k5-cap18-crowding1.json).

At μ42 the source's corresponding correlated check leaves zero states.
At μ41 the weaker domain retains many states even after the available
crowding restriction. Therefore this method has **not proved even `k≥6`**
for singleton sizes 9/10 at the new threshold.

The surviving P10 states occur in 291 internal assignments; P9 in 363.
Neither has a survivor with empty internal family. For example:

* P10 internal mask 256, neighbor degrees `(14,15,16,15,16,16)`, retains
  104 external lower-bound vectors.
* P9 internal mask 512, neighbor degrees `(14,14,14,16,16,16)`, retains
  one vector.

Those are diagnostic obstructions to this relaxation, not realized families.
An improved probe should couple the same 41 nonempty six-point trace
variables across anchors, rather than only their degrees and external lower
bounds. It must also incorporate internal presence and absence in the same
way as the source projection builder. The μ42 projection's row, pair-sum,
member-sum and degree-selector assumptions must all be changed explicitly.
No broad projection suite was run in this task.

## 5. Remaining obligations and research priority

The best reusable branch is:

```
|F|=68 + H27
    ⇒ μ≥41
    ⇒ universal capacities and trace geometry

μ≥41 + Δ≤18 + existing crowding26
    ⇒ minimum used degree≥7
    ⇒ member sum≥50 and pair sum≥19
    ⇒ 16≤support≤23 at cardinality68.
```

The first essential new global step is still to handle **Δ=20 and Δ=19 at
cardinality 68 and μ41**. The crowding theorem's degree-18 hypothesis cannot
be used in those branches. Although the source D20/D19 proofs contain
μ-independent geometric endgames, their reductions into those endgames use
μ42-derived trace domains and the R42/N42 singleton bounds. Their old
certificates cannot be transferred merely because the final contradiction
has numerical slack.

After Δ≤18 is established, use the direct existing crowding support theorem
above to investigate **Δ=18 and Δ=17** with the corrected μ41 domains.
This avoids making recovery of the full μ42 bootstrap a prerequisite.

If the route later reaches Δ16, the source's local R61 theorem already has
the required μ41/Δ18 scope. Thus a complete R16 link would contradict
cardinality 68. What is still missing is an argument forcing such a link,
or a different exclusion of the remaining separated-link alternatives.
The source's maximum-degree-at-most-15 exclusion and its graph/fiber
transition were organized at 69; neither is inherited automatically.
The terminal A_k census is being studied separately.

An orthogonal route is to study equality in H27 at a root with `N=41`,
since its disjoint complement would have size 27. The cited H27 bound alone
does not supply a classification of every extremal intersecting family;
uniqueness of the displayed classical example must not be assumed.

Nothing in this note excludes 68, validates the entire reported theorem68,
or establishes worldwide novelty. Its contribution is the exact separation
of transferable premises, failed inequalities, an explicit written recovery
of the existing μ41 support package, and reproducible small probes identifying
where a stronger singleton argument is still needed.
