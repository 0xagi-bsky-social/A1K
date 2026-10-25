# Independent check of the cap16 NO45 development

23 October 2026. Ordinary proof-development check, not a final review.
No LP, model construction, heavy enumeration or Lean process was run.
The independent scalar calculation below completed in about0.08 seconds.

Checked `D16-NO45-ordinary.md`, SHA256
`37f54fcc17c537cff444861e0d2bbc3d8862fd0c70fc83bb7500d847def32cab`.
No gap was found under its named prior/imported and preceding ordinary
premises. In particular its P8-no-two-cover exclusion uses only N<=45,
so the proof of the stronger N<=44 conclusion is acyclic.

## Scalar coverage and local signatures

The whole N45 scalar domain is exactly bounded by s_i in0..8, p_ij in0..3,
t_i in0..1, 1+S+P+T=45 and d_i=1+s_i+r_i+T-t_i<=16. The degree sum gives
S>=28+T. Sorting only s loses no actual anchor because all pair and triple
coordinates are then enumerated without restriction. The necessary
pair-degree, pair-row, triangle/triple, omitted-row and common-triangle
filters used in the producer each have the stated B4/codegree guards.
In particular none applies the omitted-row4 bound with a missing high
neighbour, or assumes the common-triangle theorem for a singleton7 pool.

A complete degree16 link has an8+8 B4 partition after no-P9 and R61.
The allowed P8 type has deleted blocks meeting in two points. Direct
intersection with a P8 block or Q8 core/leaf block gives the four listed
s8 signatures. A shared Q8 leaf gives exactly one additional opposite
near triple, changing s8 to s7 and p_leaf0 to1; its only signature is
((1,1),(3,0),(3,0)). No other degree16 singleton is possible. All Q8
core points avoid the opposite whole support; leaves alone may overlap.
The signature filter therefore retains every actual degree16 root.

I independently reconstructed the scalar domain in
`D16_NO45_independent_check.py`. This reverse enumeration starts with
(p,t), derives each singleton ceiling from its degree bound, and enumerates
only deficits from those ceilings; it does not import or execute the
original checker. It reproduced counts2054,164,6 and exactly the same
two S4 orbits. Its source SHA256 is
`27cbe7889ebddf51521752c9d642944792aa34c0b20d6b8c740d5fffb9213d00`.
The successful output is `D16-NO45-independent-scalar.json`.
This is independent finite arithmetic verification of necessary scalar
coverage, not an enumeration of exterior realizations or a Lean proof.

## Both ordinary geometric closures are valid

For the two remaining all-s8/all-t1 signatures, each actual pair residue
E_ij contains z_i and z_j by B4 in the opposite root links. Two distinct
residues in one category therefore force z_i=z_j. If all four coincide,
the four pair members and three triple members through any root give
seven distinct actual members on its pair with z, exceeding pair cap6.
Thus the connected p2 graph in CaseA closes directly.

In CaseB, p2 is the matching03,12 and hence z0=z3=a,z1=z2=b with a!=b.
The cross categories have the forced edge ab. Triple capacity on0ab
excludes b from either03 residue's second point; similarly at12. The
near L0 triples displayed in the proof are exactly Q8 with hubs3,a,
triad1,2,b and two distinct leaves. The other roots have the stated
analogous Q8 near families, all with a,b in their core.

The reciprocal isolation argument is sound. Starting with the far
family and actual anchor A, a P8 deleted block or Q8 hub-plus-both-leaves
exception cannot be near because its support avoids A. Thus a far Q8
core avoids the near support. Conversely a far triple touching the
near core could only be a near exceptional hub-plus-both-leaves triple,
wholly on the near support; every far Q8 triple contains a far-core
point, contradicting the already established direction of isolation.
This proves core separation in both directions without treating the
Q8 leaves as isolated.

Every far singleton tail consequently avoids R union {a,b}. The fixed
actual member01ab is disjoint from the lifted centres2,3 and from their
tail supports. Two disjoint tails would give an actual empty-core
sunflower with01ab. Hence these two actual intersecting eight-tail
families are cross-intersecting, with both centres outside both supports.
The HP15 import applies exactly and contradicts8+8=16.

Combining the independently checked finite scalar coverage with these
ordinary closures gives N<=44 under cap16, conditional on the explicit
prior and preceding ordinary inputs. It does not create a point of
degree16 when the actual maximum is at most15, nor close the whole
remaining fibre argument by itself.
