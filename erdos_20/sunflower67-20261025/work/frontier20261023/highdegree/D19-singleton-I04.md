# The singleton I04 state and the P5 cover-capacity refinement

23 October 2026. Ordinary structural deduction, not a final review or Lean formalization. No solver, catalogue, or certificate replay was run. Only the existing equality receipt was read and its displayed trace degrees summed. Universal SF3 high-link decomposition and B4 are retained as imported structural results.

## Main conclusion

Let the complete link of x be P10(Y)⊔P9(Z), where P9(Z) omits B={6,7,8}. Suppose the only internal member contained in Z is

    M={6,9,10,11}.

Then **d(6)≤16**, not merely d(6)≤17. This is the missing one-unit improvement in the old singleton equality relaxation. More generally, two useful inequalities hold for every P5 neighbor y∈{6,7,8}.

Write C_y for the unique two-vertex cover of the four-edge path that is the complete link of the pair {x,y}. Define

    I_y = #{Q∈F : y∈Q⊆Z},
    J_y = #{Q∈F : {y}∪C_y ⊆ Q ⊆ Z}.

Thus J_y counts only internal members, and 0≤J_y≤I_y. The three covers are

| y | C_y | Triple consuming capacity |
|---|---|---|
| 6 | {9,11} | {6,9,11} |
| 7 | {10,11} | {7,10,11} |
| 8 | {9,10} | {8,9,10} |

The strengthened central-anchor inequality is

    s_y≥8  ⇒  k_y≤6+I_y−J_y.                         (P5-cover)

There is also an unconditional whole-degree bound

    d(y)−I_y+J_y≤16.                                  (P5-delete-cover)

These are valid before assigning all internal members or assuming they are absent. They do not require μ≥41, μ≥42, H27, a fixed cardinality, or a support cutoff. They do require the stated complete P5 pair-link; merely prescribing four path cones while allowing more members through {x,y} is insufficient.

## Proof of the conditional central-anchor inequality

Fix an actual central anchor R containing x and y. Its link anchor A=R∖{y} contains x. Let K_y be the members of L_y meeting A, and let s_y be the number disjoint from A. If s_y≥8, B4 makes K_y intersecting.

1. **Exactly four members of L_y contain x.** The complete link of x is the prescribed P10⊔P9. A P5 neighbor y belongs to exactly four P9 blocks, so d_F(x,y)=4. Consequently every x-containing member of L_y is one of the four prescribed path-star triples. There is no uncounted non-central extra containing x. All four belong to K_y because A contains x.

2. **Every other member of K_y covers the path.** It avoids x and must meet each of the four x-star triples, since K_y is intersecting. The meeting points lie on their path edges. If it is contained in Z∖{y}, it corresponds to one of the I_y internal members. The number of such members in K_y is at most I_y; equality is not needed for this proof.

3. **An exterior member must use C_y.** A three-element set avoiding x and not contained in Z∖{y} has at most two points on the five-vertex path. Covering all four path edges requires at least two points, and the unique two-point cover is C_y. Hence every exterior extra in K_y is C_y∪{a} for an a outside {x}∪Z. In F, its corresponding member is {y}∪C_y∪{a}.

4. **Internal occupation consumes the same capacity.** The pair C_y in L_y, equivalently the triple {y}∪C_y in F, has codegree at most two. The J_y actual internal members already consume J_y of these two incidences, whether or not they lie in K_y. The pair C_y is not a path edge, so none of the four prescribed star triples consumes it. Thus the number of exterior extras in K_y is at most 2−J_y. Other members using this triple can only reduce that allowance further.

Counting gives

    k_y ≤4+I_y+(2−J_y)=6+I_y−J_y.

This argument deliberately uses “at most I_y internal members in K_y.” It does not need the additional classification fact that all internal members lie on the near side when the opposite singleton is large. The global codegree bound charges J_y correctly in either case.

## Proof of the unconditional deletion inequality

The following triple-level statement suffices. Let L be any SF3 family with a point x of degree exactly four whose complete point-link is a four-edge path on five vertices V. Let I count the members of L contained in V, and J count those members that also contain the unique two-point cover C of that path. Then

    |L|−I+J≤16.

Delete precisely the I−J internal members not containing C. All remaining internal members contain C. If at least seventeen triples remain, choose a seventeen-member subfamily L′ containing the four path-star triples. By the universal size-17 decomposition, L′ is P10⊔I7 or P9⊔I8 on disjoint supports. Therefore the intersecting component containing x has at least seven members and contains all four star triples.

Every non-star member of that component covers the path. If it is internal, it survived deletion and contains C. If it is exterior, the unique-two-cover argument shows that it contains C. The pair codegree cap allows at most two non-star members in total. The component therefore has at most 4+2=6 members, contradicting its size at least seven.

Apply this to L=L_y and V=Z∖{y}. The I and J counts are exactly I_y and J_y. This proves (P5-delete-cover) without imposing a large-singleton hypothesis at a particular anchor.

## The singleton I04 contradiction in literal labels

For y=6, the four prescribed members of L_6 containing x are

    {x,7,11}, {x,8,9}, {x,9,10}, {x,10,11}.

Their point-link at x is the path

    8 — 9 — 10 — 11 — 7,

whose unique two-cover is {9,11}. The sole internal member M contributes {9,10,11} to L_6, so I_6=J_6=1. Thus (P5-delete-cover) immediately gives d(6)≤16.

The same contradiction can be expressed directly in the degree-17 branch. With I_6=1, the previous universal rooted conditions already force (s_6,k_6)=(10,7). The component containing x would require three additions to its four path-star triples. There is only one internal addition, so at least two must be exterior. Both contain {9,11}. Together with the existing internal triple {9,10,11}, these would give pair codegree at least three in L_6. In F this is the explicit three-sunflower

    {6,9,10,11}, {6,9,11,a}, {6,9,11,b},

with common core {6,9,11}, where a and b are distinct exterior points. Simplicity gives a≠b, and neither equals 10. Hence degree 17 is impossible.

The other two P5 points have I_7=I_8=0 and degree at most 16 by the original bound. The C5 points 9,10,11 each have I=1 and degree at most 16 by the C5 deletion bound. Thus all six points of Z have degree at most 16 in this singleton state.

## Relation to the saved equality receipt

The inspected file is `degree19/Zpattern02-none.json`, with assigned Z mask 3648={6,9,10,11}. It records source hash

    91b3bb0b57fbf587cd47b3b1c0b9be3b9ebc4d801bfa45f7a81e1ee033f33abd

and exact-box bound 49: scale 10^10, H=480000000000, correction=10000000000. The saved fractional trace solution has global degrees

    d6=17, d7≈13.67135, d8≈14.5, d9=16, d10≈14, d11=16.

It violates the new d6≤16 inequality. Fractional feasibility was not a realized set family.

The displayed dual has unit positive multiplier on the row labeled `['P5',6]`. In the inspected source `degree19_projection.py:104–105`, that row counts non-internal residual members through 6 and has right-hand side 16−4=12, i.e. d6−I6≤16. In this exact singleton assignment, the new inequality lowers that same right-hand side by one to 11. With the identical old coefficient matrix and bounds, its recorded multiplier would lower the displayed upper bound from 49 to 48; the box correction is unchanged by a right-hand-side change alone. This is an algebraic observation about the saved certificate, not an independently replayed new certificate. Any final receipt must bind the strengthened row and the exact source actually checked.

## Safe model formulation

For projected trace variables, J_y is the sum of n_T over four-point traces T contained in Z and containing {y}∪C_y. These are actual internal members, so their trace variables are binary and no exterior multiplicity is lost.

The unconditional row is

    (sum of residual incidences through y) − I_y + J_y ≤ 16−4=12.

Equivalently, the coefficient is zero on internal members through y not containing C_y and one on all other residual members through y, including J_y. This formulation is linear and independent of an exact internal assignment.

For a convex combination of central-anchor rows, replace the old conditional cost inequality by

    Σ_r λ_r [s_y(r)≥8] max(0,k_y(r)−6) ≤ I_y−J_y.

Because I_y−J_y≥0, (P5-cover) proves this for an actual integral row; convexification gives a necessary relaxation. A source-safe pruning check is `conditional_cost ≤ max_possible(I_y−J_y)`, not the former maximum I_y alone. Degree-specific lower requirements should remain separate unless their own J_y refinements are proved.

## Source dependencies and assurance boundary

The frozen root is `work/frontier20261020/prior-art68/repository/`.

* `paper/main.tex:188–204`: SF2 maximum degree and matching characterization, giving the pair codegree cap two in an SF3 link.
* `paper/main.tex:308–326`: B4 separation for an actual link anchor with at least eight disjoint triples.
* `paper/main.tex:612–636`: size-17 decomposition into disjoint-support intersecting components of sizes 10+7 or 9+8.
* `companion/upstream/D19/PROOF.md:28–45`: complete C5/P5 stars and the earlier weaker central bound k_y≤6+I_y.
* `companion/upstream/D19/PROOF.md:120–126`: the unique-two-cover exceptional triples, including {6,9,11}.

The new ingredient is charging occupied internal members against the same triple capacity as the possible exterior additions. No new finite computation or broad classification is asserted. Neither inequality has been formalized in Lean in this note; their use remains an ordinary-mathematics premise until that bridge is supplied.
