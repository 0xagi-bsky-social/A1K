# R99 I02: exact equality forces a doubled P10

23 October 2026. Ordinary research proof for the marked I02 leaf, not a final audit or Lean result. No solver, model construction, local-catalogue enumeration, or large search was run. A bounded check of the794 possible core traces was performed with explicit integer coefficients; its complete recipe is recorded below.

Let F be a finite simple SF4 family with |F|≥68 and Δ(F)≤18. Let x have complete link P9(Y)⊔P9(Z), with Y={0,…,5}, Z={6,…,11}; each P9 is the model

    015,023,034,045,124,134,135,235,245

on its six labels, with the second shifted by six. Assume the actual member M={6,7,9,10} is present. Other internal members are allowed. Write R={Q∈F:x∉Q}, r=|R|≥50.

The leaf is impossible. Its old exact bound50 has an equality obstruction: two positively weighted singleton capacities must both be tight at10. Their actual exterior pools are then a doubled P10, contradicting the global size. Moreover, its numerical local-catalogue row can be replaced by an ordinary degree-pair lemma, leaving a small explicit trace-cover certificate.

## 1. Source identity and the old certificate

The inspected receipt is `degree18_r99/I02-none.json`, SHA-256

    e666ae331fe40dd91e4f13d6d50dc317db5430b5a3791b77906b8e86d506dadc.

It records generator hash

    c8ce671c0ee1138b747c566b0c9322e6c69ba3e21c518b288ad64d53881b0322,

which matches `degree18_r99_projection_v1.py`, not the subsequently edited current generator. Its imported local43 hash is

    258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b.

The old certificate has scale10^10, H=495000000000, correction5000000000, and upper numerator500000000000. Two selected inequalities have weight5000000000:

* exact trace {6} on the actual anchor x∪{6,9,10}, cap10;
* exact trace {7} on the actual anchor x∪{7,9,10}, cap10.

These are actual singleton classes of four-sets. The prescribed central cones contribute zero to them because those cones contain x. At objective50, equality in the full exact upper bound forces every positively weighted inequality tight; the box correction cannot hide positive slack in either of these rows.

The conclusion from that old certificate remains conditional on its necessary-domain embedding and exact coefficient check. The following replacement removes its local-catalogue dependency.

## 2. A universal adjacent-P5 degree-pair bound

For the two P5 neighbours6,7 of the same complete P9 component,

    d(6)+d(7)≤34.                                          (PP34)

This uses Δ≤18 and the universal separated size17/18 link classification, but no μ41 or marked-member hypothesis.

Suppose d(6)=18. In L_6, the distinguished point x has complete point-link

    7—11—10—9—8.

The size18 decomposition is P10⊔P8/Q8 or P9⊔P9 on disjoint supports. The component containing x has point-degree4 at x. It cannot be P10, whose point degrees are5. Nor can it be Q8: its degree4 point-link is C4, not this complete four-edge path. Thus the near component is P8 or P9, on exactly the six points {x,7,8,9,10,11}. Its P10 completion adds the missing endpoint edge78 at x. The five non-x triples of that completion are exactly the five three-point covers of the completed C5. In F they correspond to

    {6,8,10,11}, {6,8,9,11}, {6,7,9,11},
    {6,7,9,10}, {6,7,8,10}.

At least four of these five members must be present: a P8 near component has four non-x triples, and a P9 near component has five.

If d(7)≥17, the separated high-link theorem makes every internal member through7 lie in the intersecting component containing x. Hence its residual triple must cover the complete point7 path

    6—11—9—10—8.

But {6,7,9,11} leaves edge{8,10} uncovered at7, while {6,7,8,10} leaves edge{9,11} uncovered. Both would be forbidden, leaving only three of the five required possibilities. This contradiction proves

    d(6)=18 ⇒ d(7)≤16.

The symmetric assertion follows in literal labels by using the five possible non-x members at7:

    {7,8,10,11}, {7,8,9,11}, {6,7,10,11},
    {6,7,9,10}, {6,7,8,9}.

The third and fifth are noncovers of the point6 path, respectively missing edges{8,9} and{10,11}. Thus d(7)=18 implies d(6)≤16. If neither degree is18, both are at most17. This proves(PP34).

In the old dual, the last eight-row anchor group is the anchor x∪{6,7,11}. Its coefficients reduce to

    (d(6)+d(7)−e)/4≤34/4,

where e is the exact triple class {6,7,11} at that anchor. Replacing this by (PP34)/4 increases every affected trace coefficient and keeps the same right side. This replacement is valid independently of the original catalogue.

## 3. Explicit integer cover, with no local selectors

Let S=Q∩(Y∪Z) for Q∈R. There are794 subsets of the twelve-point core of size at most four. For an actual central member A, E(A,U) denotes the number of residual members with exact trace U on A. Let b_v count residual members whose trace on Z is a pair containing v. Let I_v count internal members contained in Z through v, and J_v the ones containing the unique two-cover C_v of its P5, with

    C_6={9,11},   C_7={10,11}.

Use the following necessary rows with integer weights. All degrees in the displayed degree rows have their fixed central contribution removed when defining the trace coefficient.

| Row | Residual cap | Weight |
|---|---:|---:|
| Incidence of {8,9} | 4 | 2 |
| Incidence of {8,10} | 4 | 2 |
| Incidence of {9,11} | 4 | 2 |
| Incidence of {10,11} | 4 | 2 |
| Incidence of {0,1,2} | 2 | 4 |
| E(x245,{4,5}) | 3 | 4 |
| E(x{6,9,10},{6}) | 10 | 2 |
| E(x{7,9,10},{7}) | 10 | 2 |
| b_9 | 6 | 2 |
| b_10 | 6 | 2 |
| d(6)−4−I_6+J_6 | 12 | 1 |
| d(7)−4−I_7+J_7 | 12 | 1 |
| Incidence of each T∈{015,023,034,124,134,135,235,245} | 1 each | 4 each |
| d(6)+d(7)−8 | 26 | 1 |

The weighted right-hand side is198. The pair/triple incidence caps follow from global codegrees6 and2, subtracting the fixed central cones. Exact trace caps10 and3 are universal intersecting-residue bounds. The pair-pool bound6 applies at the C5 neighbours9,10. The refined P5 deletion inequalities are proved in `D19-singleton-I04.md`; the final row is(PP34).

Define q(S) as the weighted sum of these21 row coefficients. The only traces excluded in the cover check are those satisfying

    S∩T=S∩M=T∩M

for some prescribed link triple T. Such a trace would make Q,M,x∪T a sunflower. This leaves432 traces, excluding362. Other internal members are not set to zero. Direct integer evaluation gives

    q(M)=2,   q(S)≥4 for all other admitted traces.           (COVER)

Since M is an actual four-set, its trace has multiplicity exactly1. Thus

    4r−2 ≤ Σ_(Q∈R) q(Q∩(Y∪Z)) ≤198,

and r≤50.

At r=50, equality holds throughout. In particular both weight2 exact-singleton rows in the table are tight, each with value10.

### Bounded check recipe

The following self-contained Python computes(COVER) using no solver, model import, signature catalogue, or exterior-point cutoff. It is the bounded integer check executed during preparation of this note; it checks794 traces, not actual families.

```python
from itertools import combinations
mask = lambda vs: sum(1 << v for v in vs)
D = [mask(map(int,t)) for t in
     '012 015 023 034 045 124 134 135 235 245'.split()]
L = D[1:] + [T << 6 for T in D[1:]]
X, Z, M = 1 << 13, 63 << 6, mask((6,7,9,10))
C = {6:mask((9,11)), 7:mask((10,11))}
pairs = [mask(t) for t in ((8,9),(8,10),(9,11),(10,11))]
triples = [D[i] for i in (1,2,3,5,6,7,8,9)]
def q(S):
    z = 2*sum((S & U) == U for U in pairs)
    z += 4*int((S & 7) == 7)
    z += 4*int((S & (X|mask((2,4,5)))) == mask((4,5)))
    z += 2*int((S & (X|mask((6,9,10)))) == (1<<6))
    z += 2*int((S & (X|mask((7,9,10)))) == (1<<7))
    z += 2*sum(bool(S & (1<<v)) and (S&Z).bit_count()==2
               for v in (9,10))
    for v in (6,7):
        removable = (S.bit_count()==4 and (S&Z)==S
                     and (S&C[v]) != C[v])
        z += int(bool(S & (1<<v)) and not removable)
    z += 4*sum((S&T)==T for T in triples)
    z += int(bool(S & (1<<6))) + int(bool(S & (1<<7)))
    return z
admitted = []
for k in range(5):
    for vs in combinations(range(12),k):
        S = mask(vs)
        if any((S&T)==(S&M)==(T&M) for T in L):
            continue
        admitted.append(S)
        assert q(S) >= (2 if S==M else 4), (vs,q(S))
assert len(admitted)==432 and q(M)==2
assert 4*(2*4)+4*2+4*3+2*(2*10)+2*(2*6)+2*12+8*4+26==198
```

## 4. Tight singleton classes produce a doubled P10

The singleton class at anchor x∪{6,9,10}, trace{6}, is an intersecting SF3 family of ten triple residues in L_6, hence a P10. P10 isolation forces the complementary part of L_6 to avoid its support. That part contains the four prescribed x-star triples, whose union is {x}∪(Z∖{6}). Therefore every singleton tail avoids {x}∪Z, and this class is exactly the complete exterior pool H_6. The same argument at anchor x∪{7,9,10} gives H_7 of size10.

A prescribed P9(Z) block avoids6 and7. Consequently H_6 and H_7 are cross-intersecting: disjoint tails together with that central cone would be an empty-core sunflower. The three-point transversals of P10 are exactly its ten blocks, so the two size-ten families coincide on a common six-point support H outside {x}∪Z.

The twenty actual members {6}∪T,{7}∪T for T in that common P10 satisfy `doubled-P10.md`. Hence

    |F|≤27+d(6)+d(7)−d(6,7)≤63,

already contradicting |F|≥68. In fact(PP34) gives the stronger upper bound61−d(6,7). Equivalently, the previously proved HP16 pool inequality would say20≤16.

Thus r=50 is impossible; the marked I02 leaf is excluded by ordinary geometry plus the explicit bounded trace cover. No complete internal assignment, fractional degree interpretation, or symmetry assumption on the completion was used.

## Imported premises and remaining assurance boundary

The frozen source root is `../../frontier20261020/prior-art68/repository/`.

* `paper/main.tex:206–231`: P10 model, degrees, C5 links, and intersecting SF3 classification.
* `paper/main.tex:272–305,612–636`: isolation and disjoint-support size17/18 decompositions.
* `paper/main.tex:333–376`: universal codegrees and exact residue capacities.
* `companion/upstream/D18_P10/PROOF.md:62–97`: the C5 pair-pool cap6 without μ42 or support restrictions.
* `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–152`: cross-intersecting exterior pools and exact identification of singleton classes of size9/10.

H27 remains an imported intersecting SF4 theorem. The bounded trace check is an executable integer certificate diagnostic, not Lean kernel verification. The source-backed classification and the refined P5 deletion lemma remain ordinary mathematical dependencies. The full D18 branch is not claimed closed by this leaf proof.
