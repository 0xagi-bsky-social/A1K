# F68 terminal research: deletion-robust transversals

Status: **draft mathematical reduction with certificate-diagnostic exact checks**.
This is substantive research, not a final review or publication approval. No Lean
elaboration or kernel verification is claimed. None of the prior paper's written
reductions is certified by the new computations.

Source: `paper/main.tex` in the frozen prior-art repository, commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`. Relevant named results are B4 separation,
the intersecting triple classification, isolation, the definition/classification
of R16, and R61. The main numerical theorem remains the prior claimed upper bound
68. The work below does **not** establish the global upper bound 67.

## Concrete result

The terminal fibre argument can be extended to cardinality **68**, conditional on
the three upstream conclusions

1. maximum point degree 16;
2. every exact singleton at every actual anchor has size at most 8;
3. every closed neighbourhood has size at most 44.

Together with H27 and the prior ordinary/finite local inputs, these assumptions
contradict the existence of an SF4 family of size 68. The new ingredient is a
deletion-robust cover bound, with capacities **1, 2, 4, 10** after deleting
respectively 0, 1, 2, 3 prescribed triples from a separated 8+8 link.

The global bound 67 remains conditional because at size 68 H27 gives only
`mu >= 41`; the paper's upstream degree, singleton and neighbourhood reductions
are proved on `mu >= 42` domains. They cannot simply be imported unchanged.

## 1. The exact graph domain at 68

Let G be the disjointness graph. It has order 68, is triangle-free, and has
independence number at most 27 by H27. The neighbourhood upper bound 44 gives
minimum graph degree at least 24.

Jin's theorem as stated in the prior paper applies with `k=6`, since
`24*20 = 480 > 7*68 = 476`. With `k=5` the inequality is equality
`24*17 = 6*68 = 408`, so that version cannot be used.

Use the paper's cyclic convention: A_k has vertices modulo `3k-1` and edges at
cyclic differences `k,...,2k-1`. To reduce an empty fibre, the following general
map sends A_k minus vertex 0 to A_(k-1):

`f(v) = v - 1 - [v >= k] - [v >= 2k]`, for `1 <= v <= 3k-2`.

For k=5 its images are
`(0,1,2,3,3,4,5,6,7,7,8,9,10)`;
for k=6 they are
`(0,1,2,3,4,4,5,6,7,8,9,9,10,11,12,13)`.
For an edge with ordinary difference d in `[k,2k-1]`, the map subtracts the
number of thresholds k and 2k crossed. A difference k crosses exactly one,
a difference 2k-1 crosses both, and the intermediate differences remain in
`[k-1,2k-3]`. Rotation handles any deleted vertex. This also supplies the missing
k=5,6 maps that were not listed in the original paper.

After deleting empty fibres repeatedly the image is surjective. The images
A_1 and A_2 are impossible: respectively `68 <= 2*27` and `2*68 <= 5*27`.
Hence k belongs to `{3,4,5,6}`.

Let `a_i` be fibre masses and `b_i=sum_{j~i} a_j`. Every A_k neighbourhood is
independent, so `b_i<=27`. Surjectivity gives `b_i>=24`. Set `r_i=b_i-24`.
The inverse incidence identity is

```
r_i in {0,1,2,3}
sum_i r_i = 24 - 4*k
a_i = 4 + r_i + r_(i+k) + r_(i+2*k-1).
```

This follows from the circulant identity `NC=CN=J+Id`, where N is the adjacency
matrix and C is the sum of shifts 0,k,2k-1: `Cr = a + 68 - 72 = a - 4`.
The probe independently checks every reconstructed sum and neighbourhood sum.
In particular all these candidate fibre masses are positive.

For a degree-16 point x, let `t_i` count its star members in fibre i. Put
`q_i=sum_{j~i}t_j`, and let I be the support of t. Necessary conditions are

```
sum_i t_i = 16,  0 <= t_i <= a_i,
q_i <= r_i for each i with t_i>0.
```

The last inequality accounts for the star-star edges missing at every actual
star vertex. It is not a matching assumption.

If I is independent, it is contained in a cyclic window W of k consecutive
indices. The C++ reconstruction checks this property for every independent
support of each A_3,...,A_6. Such a window is a neighbourhood of some image
vertex, hence has mass at least 24. All its members outside the x-star meet the
entire star, giving at least `24-16=8` full four-transversals. This contradicts
the capacity 1 below.

## 2. Why a non-R16 sixteen-link has exactly the required form

At the anchor `R={x} union A`, the exact singleton class at x corresponds
precisely to triples of L_x disjoint from A. Thus the assumed singleton bound
gives `rho(L_x)<=8`. R16 was defined in the prior source as an SF3 family of
size 16 with rho at most 7.

If L_x is not R16, choose A with eight disjoint triples. The part
`H=D_L(A)` has size eight and is intersecting because three disjoint triples
are forbidden. Its complementary part `K=N_L[A]` also has size eight and is
intersecting by B4 separation. Thus H and K are both P8 or Q8. This uses no
classification of an arbitrary I7.

Isolation from the prior paper gives disjoint supports when either part is P8.
For Q8/Q8, the two five-point cores are disjoint and avoid the other entire
support, while the two sets of leaves can overlap in zero, one, or two points.
These are exactly the prior paper's overlap conventions, not full support
isolation for Q8.

There are two P8 types. They delete two P10 triples whose intersection has size
one or two. The exact automorphism check finds the P10 group of order 60 and
complete omission orbits of sizes 30 and 15. Representatives are

```
P0 = P10 minus {034,135};  P1 = P10 minus {012,015}.
Q  = {023,024,034,123,124,134,015,016}.
```

Unordered pairs of P0,P1,Q give six disjoint-support models. Adding Q/Q with
one or two shared leaves gives eight models in total. These cover all cases
under the preceding structural reduction.

## 3. Cover lemma, including arbitrary exterior points

Let L be one of these separated 8+8 links, embedded as the complete x-link of
an SF4 family. Delete a prescribed subset D of d triples, with `0<=d<=3`.
Let C be any collection of actual members of the ambient family avoiding x
and meeting every triple in `L minus D`. Then

`|C| <= c_d`, where `(c_0,c_1,c_2,c_3)=(1,2,4,10)`.

Here is the finite reduction, which does not silently bound exterior labels.
Every point of L occurs in at most five of its triples (a shared Q leaf
occurs only twice). Two support points meet at most ten triples. A cover of
at least thirteen triples must therefore use at least three support points.
It has at most one point outside `supp(L)`.

Enumerate support triples C3 meeting `L minus D` and support four-sets C4
meeting `L minus D`. Let P4 consist of those C4 containing no C3. Every actual
cover either is a member of P4 or contains some C3. A fixed C3 belongs to at
most two ambient members by the global triple-codegree cap. Therefore

`|C| <= |P4| + 2*|C3|`.

This is an upper bound by a union count; a set containing multiple C3 may be
counted several times, which preserves the inequality. It includes every
possible exterior completion through its three-point support trace.

For d=0,1,2 the eight-model enumeration gives bounds 1,2,4. For d=3 the raw
bound is at most 12. There are exactly six normalized omission cases where
the raw bound exceeds 10. In each, C3 is empty, the twelve C4 share one point,
and their union has seven points. Thus every actual cover is on those seven
points, and deleting the common point gives triples on six points. Each pair
of these residual triples has codegree at most two because the corresponding
global triple has codegree at most two. Counting pair incidences gives

`3*|C| <= 2*binom(6,2)=30`.

This proves the claimed bound 10 in those cases too. The JSON output records
the omitted triples, shared point and seven-point support for all six cases.
The complete exact support census has `8*(1+16+120+560)=5576` omission cases.

## 4. Applying the new cover lemma to the entire fibre census

For each fibre i, let D_i be the union of star members in adjacent fibres;
it has size q_i. Every member of fibre i avoiding x covers `L minus D_i`.
More strongly, every member outside the star in a fibre j with
`D_j subset D_i` also covers that same remaining link. These are distinct
ambient four-sets. Consequently, whenever `q_i<=3`,

`sum_{j: D_j subset D_i} (a_j-t_j) <= c_(q_i)`.

The probe represents D_i by occupied-neighbour coordinate masks. Since each
coordinate contributes its entire star class, coordinate inclusion is exactly
inclusion of these actual sets of star members; it does not compare unrelated
external labels.

Every nonisolated positive t-coordinate is bounded by the minimum r-value of
its occupied neighbours, hence at most three. Isolated positive coordinates
retain their full range up to a_i. The DFS enumerates all such vectors of
sum 16, checking every missing-edge constraint. It quotients fibre profiles
only by dihedral symmetry; star vectors themselves are counted with labels.

| Image | Dihedral r-profiles | Nonindependent star vectors | Remaining |
| --- | ---: | ---: | ---: |
| A3 | 543 | 33,912 | 0 |
| A4 | 1,541 | 87,790 | 0 |
| A5 | 103 | 2,621 | 0 |
| A6 | 1 | 0 | 0 |

Thus a non-R16 degree-16 link is excluded throughout this F68 domain.
A maximum-degree-16 point exists by the assumed degree conclusion; its link
is R16. H27 supplies `mu>=41`, while `Delta=16<=18`, so prior R61 applies and
gives `68<=61`, a contradiction.

## 5. Why the original B>=1 extrapolation is false

Before the stronger cover inequalities, 149 vectors survive the full and
single-deletion cover constraints: 14 for A3, 134 for A4, and one for A5.
All have B=0, where B counts forced complete transversals.

The A5 witness is

```
r = (0,0,0,0,0,0,0,2,0,0,0,0,0,2)
a = (4,4,6,4,6,4,4,6,6,4,4,4,6,6)
t = (0,0,0,0,0,0,0,2,0,4,4,4,0,2).
```

It satisfies all fibre and star inequalities. The maximal blowup with all
star-star edges removed is triangle-free, has minimum degree 24 and
independence number 26. So adding the abstract graph independence bound 27
does not repair the old argument. This is an abstract graph/domain witness,
not a realized sunflower-free set family.

In this witness two fibres together supply ten actual candidate covers after
omitting the same two star triples. Capacity 4 rules it out. The d<=2 bounds
and raw d=3 bound 12 reduce all 149 cases to eleven A4 vectors; bound 10
eliminates those final eleven.

## 6. Reproduction and remaining obligations

Files in this analysis directory:

- `prior68_cover_probe.py`: eight-model omission census and P8 orbit check.
- `prior68_cover_probe.json`: exact output, including six exceptional structures.
- `prior68_fibre_probe.cpp`: full r-domain and star-vector census; independent
  support/window check; exact fibre algebra; fail-closed final census checks.
- `prior68_fibre_probe.txt`: exact census output.
- `prior68_graph_helpers.py` / `.json`: verified deletion maps through k=6
  and a reconstruction of the abstract A5 counterexample to the old interface.

Commands:

```
python3 prior68_cover_probe.py > prior68_cover_probe.json
g++ -std=c++17 -O3 prior68_fibre_probe.cpp -o prior68_fibre_probe
./prior68_fibre_probe > prior68_fibre_probe.txt
python3 prior68_graph_helpers.py > prior68_graph_helpers.json
```

Observed checks are exact-integer diagnostics, not imported source proof
verification, independent reproduction, or Lean certificates. No 42-suite
rerun was performed by this research agent. No frozen Lean, manuscript, or
review source was changed.

Open work for a global improvement:

1. Establish F68/`mu>=41` analogues of the preliminary degree exclusions,
   singleton<=8, and closed-neighbourhood<=44 conclusions.
2. Turn this draft structural bridge into the assurance grade required by
   the parent task; in particular formalize or independently reproduce the
   new model reduction, support-cover checks, and star census.
3. Keep H27 and all prior source-only dependencies explicit. New diagnostics
   cannot upgrade their evidence status.

The useful new mathematical interface is the deletion-cover capacity vector
`(1,2,4,10)` and its demonstrated sufficiency for the F68 terminal domain.
