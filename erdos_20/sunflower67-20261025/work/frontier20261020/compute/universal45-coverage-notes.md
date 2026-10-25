# Universal two-star diagnostic: coverage and remaining proof obligations

This is a research note, not an accepted report or Lean theorem.

Candidate theorem: every finite 4-uniform 3-sunflower-free family with distinct
points x,y of degree20 and no member containing both has at most45 members.
The bound is attained by the explicit45-member family in sharp45_witness.json.

## Reduction to finite relative geometries

1. The existing extremal20 classification plus CanonicalTwenty.high_link_two_canonical_designs gives each link as two canonical ten-designs on disjoint six-point supports. The no-joint-member premise ensures both centers are absent from both links.
2. Fix a bijection of the first link support to0..11, with its two canonical designs on0..5 and6..11. The second link support has12points, so the union of both links has at most24points. Extend the fixed bijection injectively into0..23.
3. The relative supports of the second components are encoded by three colors (absent, componentA, componentB) on the first two six-blocks. Each first-block automorphism group has60elements. Enumerating all729 colorings and taking the minimum under all60 automorphisms is complete, even if redundant. The second block is treated independently. Outside the first support, arbitrary permutations leave the first link unchanged; therefore only the counts assigned to the two second components matter. Canonicalize these outside colors and sort the unordered second support pair. This gives1090 representative support partitions; no assumption of transitivity beyond the explicitly enumerated60 automorphisms is made.
4. On every selected six-support all intersecting2-(6,3,2) designs are enumerated independently by the1024 one-from-each-complementary-triple-pair choices with each pair occurring twice. Exactly12 survive. This is exhaustive because an intersecting ten-triple family on six points chooses exactly one of each of the ten complementary pairs. Thus1090×12×12=156960 relative geometries cover all possible link pairs.
5. A residual member R avoiding x,y has four points. Once the pair of links has been embedded in0..23, embed any points of this one R outside their union into24..27. Inspect all20475 four-subsets ofFin28. A candidate is allowed iff, for every t in the first link and s in the second, the three full members {x}∪t,{y}∪s,R do not have all pairwise intersections equal. Since R and links avoid x,y, this test is exactly not(t&s == t&R == s&R).
6. The exact Python result is156938 geometries with no allowed residual, ten with three, ten with one, two with five. Every allowed residual in all22 nonempty geometries lies inside the actual union of the two link supports. This last fact is essential: the embedding of the links is fixed once and for all; every residual member, considered separately, is forced inside that fixed union. Therefore all residual members simultaneously belong to the same at-most-five list. One must not silently normalize distinct residual members with unrelated maps and then count them as one list.
7. The two center stars are disjoint families of20members each. The family decomposes into these40members plus residual members, so the finite property implies cardinality≤45.

## Observed evidence and limits

- universal_two_star.py/json/stdout: exact Python integer/NumPy bit-set diagnostic, runtime≈5seconds.
- verify_b_geometry.py/json: independent fixed17-support implementation and exhaustive210210 labeled support-partition coverage; reproduces all46224 fixed-support cases.
- sharp45_witness.json:45distinct four-sets on15points; all14190 triples checked and no sunflower; centers13,14 have degree20 and never cooccur.
- row_components.cpp/jsonl: a different residual-row parameterization overFin22, classifying11 row orbits; only3-design+outsider and4-in-one-block admit disjoint pairs of good second-design components.
- No Lean theorem currently discharges the relative-orbit completeness, evaluator soundness, finite tables, or ambient representation bridges for the universal45claim.
- These diagnostics do not establish originality, independent certification, or a new all-rank sunflower bound.

## Failed approaches retained

The1.775million-clause ProfileA relaxation was generated in4.4seconds; CaDiCaL returned UNKNOWN at120seconds. The totalizer encoding passed4096 independent Z3 truth-table cases, but this is not a proof of the target CNF.
An attempted shortcut asserting every compatible second-design component lies inside first-link support∪R is false as an isolated component statement; fresh_link_vertex.json preserves counterdiagnostic cycles. The global requirement of two disjoint components is essential.
