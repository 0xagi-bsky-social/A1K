# A complete C4 point-link forces an internal completion at degree17

24 October 2026. Ordinary development using the already imported universal
degree17 link classification and explicit I7/I8 templates. No LP, coefficient
replay, ambient-support search or Lean job is used.

## General local statement

Let F be a simple SF4 family with maximum point degree at most17. Let t,x
be distinct used points such that their complete pair-link is a four-cycle
C4 on a four-point set W, disjoint from x,t. If no actual member of F is
of the form {t} union T for T in choose(W,3), then d_F(t)<=16.

Assume instead d_F(t)=17 and consider the complete triple link L_t.
Its complete point-link at x is precisely the stated C4. The universal
high-link theorem gives one of the separated-support forms

    P10 plus I7,       or       P9 plus I8.

These are the same eleven root possibilities used by the frozen D17
projection; the ordinary/import boundary is recorded in
`D17-I7-classification-route.md`. Their supports are disjoint, so all
four triples through x belong to a single component. A P10 point has
degree5 and complete point-link C5. A degree4 P9 point has point-link
P5, obtained by deleting one edge from C5. Therefore x belongs to the
I7 or I8 component.

The explicit I7 catalogue has exactly the following C4 points. The
last column exhibits a component triple avoiding the listed point
and lying entirely on its four C4 neighbours.

| I7 type | Point | Four neighbours | Actual contained triple |
|---|---:|---|---|
| H1 |5|1,2,3,4|234|
| H2 |3|1,2,4,5|145 (also245)|
| H2 |4|1,2,3,5|135 (also235)|
| H2 |5|1,2,3,4|134 (also234)|
| H7 |4|0,1,2,3|023|

The entries use the literal templates in `D17-I7-classification-route.md`.
This small point-link inspection is exhaustive within the eight imported
templates: four edges forming C4 have exactly four nonisolated vertices,
each of degree2. All other degree4 point-links in those templates fail
that literal degree pattern.

For I8, a P8 point of degree4 has point-link P5: its original P10
five-cycle has lost exactly one incident block. Thus only Q8 is possible.
Write Q8 as the six core triples h+choose(U,2), k+choose(U,2), and
the two leaf triples hk+l,hk+m. Its degree4 points are the triad
points. If x is one of them, W={h,k} union (U minus x), and both
h+(U minus x) and k+(U minus x) are actual triples contained in W.

Every possible component therefore contains an actual triple T subset W.
In L_t this lifts to the actual member {t} union T of F, contradicting
the hypothesis. This proves the local statement. The proof uses a
complete pair-link; an arbitrary four-cycle subgraph would not suffice.

## Application to the current P9-Q8 branches

The fixed root x has complete link P9 on Y={0,...,5} and Q8 on
Z={6,...,12}, with Q8 hubs6,7, triad U={8,9,10}, and leaves11,12.
For each t in U its complete pair-link with x is C4 on

    W={6,7} union (U minus t).

Every possible completion {t} union T from the lemma is a four-set
wholly in Z. Therefore the explicitly justified `empty_z` premise
implies d_F(t)<=16 for all three triad points. This premise is already
available in the exterior Q8 stage. It is independent of which E4
representative is selected and independent of any optional exterior
support or degree16 no-P9 conclusion.

Each triad point occurs in exactly four prescribed root cones. In a
residual trace model the resulting rows are simply

    sum_(trace s containing t) n_s <=12,   t=8,9,10.

The bound is on the full actual degree, so every exterior completion
through t is counted. Equivalent local-state pruning may discard d=17
states at these three points, but it is not necessary for row validity.
The frozen graph-template filter checks isomorphism of the point-link;
it does not alone require the additional actual completion just used.

The original E4_56 and E4_57 v9 saved primals both have degree17 at
their represented triad point8 and degrees15 at the other two triad
points. Thus this row cuts both saved primals. That is discovery evidence,
not a claim about the optimum after adding the row. No model was edited
or run while writing this note.

## Explicit imported boundary

The high-link17 decomposition and I7/I8 classification are imported
universal theorems with the scope stated above. The eight I7 templates
were independently covered by `D17_i7_coverage.py` and its saved receipt;
this note neither reruns nor upgrades that finite assurance. Its new
step is the literal completion consequence and the degree16 row.
