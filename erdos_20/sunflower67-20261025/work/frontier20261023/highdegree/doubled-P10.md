# Doubled P10 isolation and counting

23 October 2026. Ordinary proof on an arbitrary ambient ground set. This note is conditional on the imported intersecting SF4 bound H27 and the universal SF3 degree bound when those numerical bounds are invoked. It is not a Lean formalization or a final scholarly audit. No finite-trace enumeration is needed for the isolation proof.

Let F be a finite simple four-uniform family with no three distinct members whose pairwise intersections are all equal; empty cores are included. Let H be a six-point set supporting a P10 family P. Let a,b be distinct points outside H, and assume all twenty members

    {a}∪A, {b}∪A  (A∈P)

belong to F. Then every other member of F is disjoint from H. Moreover,

    |F| ≤ d_F(a)+d_F(b)−d_F(a,b)+27.

Consequently, the universal point-degree bound twenty gives |F|≤67. If d_F(a)=d_F(b)=16 and d_F(a,b)=3, the bound is 56.

## Elementary P10 facts

Use the canonical model

    P={012,015,023,034,045,124,134,135,235,245}.

It is intersecting, has ten blocks, every point has degree five, every pair has codegree two, and every point-link is a five-cycle. In particular, exactly two blocks avoid any given pair of support points: 10−5−5+2=2.

Every nonempty S⊆H of size at most four admits A,B∈P, allowing A=B, such that

    A∩B=A∩S=B∩S.

Here is a complete proof by size of S.

* If S={v}, take two disjoint edges in the five-cycle point-link at v. The corresponding blocks meet exactly in v.
* If |S|=2, take the two blocks containing S. Their third points differ, so all three intersections equal S.
* If |S|=3 and S is a block, take A=B=S. Otherwise take any pair C⊂S and the two blocks containing C. Neither third point lies in S, since that would make S a block, so all three intersections equal C.
* If |S|=4, its complement in H is a pair. A block A avoiding that pair exists (indeed two exist); take B=A⊆S.

This covers all possible nonempty traces of a four-set on H without limiting the number or identity of points outside H.

## Isolation of every extra member

First recall the elementary P10 isolation argument for triples. In a sunflower-free triple family containing P, a new triple meeting H in at least two points is impossible: a pair on H already belongs to two blocks, and the new triple would make three triples with that pair as their common intersection. If a new triple meets H in exactly one point v, two disjoint edges of the C5 point-link at v and the new residual edge form a matching of size three. The corresponding triples are a sunflower. Thus every additional triple avoids H.

Now let Q∈F be outside the prescribed twenty members.

If a∈Q, the triple Q∖{a} belongs to the sunflower-free link of a, which contains P. It is not one of P's blocks. P10 isolation therefore gives Q∩H=∅. The same argument applies if b∈Q, including when Q contains both centres.

Otherwise Q avoids both a and b. Suppose S=Q∩H is nonempty. Choose A,B as in the preceding four cases. The three members {a}∪A, {b}∪B, Q are distinct, even when A=B, and have pairwise intersections

    A∩B, A∩S, B∩S.

These are equal, a contradiction. Hence again Q∩H=∅.

## Counting the remainder

Let G={Q∈F:a∉Q and b∉Q}. Every member of G is outside the prescribed twenty, and hence avoids H. If two members of G were disjoint, they and any prescribed member {a}∪A would be a sunflower with empty core. Thus G is intersecting. It remains a four-uniform sunflower-free family, so H27 gives |G|≤27.

Inclusion-exclusion on the two centre stars now gives

    |F|=|G|+d_F(a)+d_F(b)−d_F(a,b)
        ≤27+d_F(a)+d_F(b)−d_F(a,b).

There is no hidden subtraction of the twenty prescribed members: they are already counted once each in the two centre degrees. Equivalently, the additional centre-containing members number d_F(a)+d_F(b)−d_F(a,b)−20.

## Source boundary

Frozen source root: `../../frontier20261020/prior-art68/repository/`.

* `paper/main.tex:206–231` specifies P10 and the degree, codegree and point-link facts.
* `paper/main.tex:272–305` states and proves the P10 isolation lemma. Its P10 case is reproduced above.
* `paper/main.tex:333–350` supplies the universal SF3 bound twenty, and hence the point-degree bound twenty in SF4.
* `paper/main.tex:104–109` identifies H27 as the imported intersecting four-uniform bound, rather than a bound for general triple families.

The new deduction here is the doubled-centre isolation and its counting consequence. The four-case trace proof is ordinary finite combinatorics, not a numerical-certificate or bounded-support surrogate.
