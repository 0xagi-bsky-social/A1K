# Source check of the Local51 geometric premises

23 October 2026. Bounded proof-source inspection, not final scholarly review. No computation, enumeration, certificate replay, or Lean compilation was rerun for this check. The conclusion is conditional on the imported universal SF3 classification, isolation, and separation results in the frozen source. Those results have not been newly formalized or independently re-proved here.

## Finding

The implication `s ≤ 7 ⇒ d ≤ 17` is universal for an actual anchor in a finite simple SF4 family under the imported high-link theorem. It does not use μ42. The two-large-index argument giving `e = 0` and `a ≤ 1` is also valid in the specific prescribed degree-20 P10⊔P10 setting. Its omitted trace identifications can be supplied explicitly below.

There is a citation precision issue, rather than a missing mathematical inference: `TRACE_FOUNDATIONS.md` section E explicitly discusses degree at least **19**, so section E alone does not justify the degree-18 case used at `internal-proof.md:51`. The correct direct citation is the paper's `lem:r16maximal`, `paper/main.tex:612–636`, which covers degrees 17–20. The foundations file points to that lemma at line 5, but the local proof should name it directly.

## Exact source locators

All upstream paths below are relative to the frozen root `work/frontier20261020/prior-art68/repository/`.

| Source locator | Statement used |
|---|---|
| `paper/main.tex:451–462` | Universal R16 classification on arbitrary support; its statement explicitly retains certified finite computation as a dependency. |
| `paper/main.tex:612–621` | `lem:r16maximal`: SF3 families of size 18 have forms P10⊔I8 or P9⊔P9 on disjoint supports; sizes 19 and 20 have P10⊔P9 and P10⊔P10. |
| `paper/main.tex:622–636` | The high-link proof uses maximality, the universal R16 theorem, B4, intersecting size bounds, and isolation. It contains no neighbourhood or SF4 cardinality hypothesis. |
| `paper/main.tex:638–650` | The section introducing the μ≥42 domains starts **after** the universal high-link lemma; bootstrap42 is a later proposition. |
| `proof/DEPENDENCIES.md:5,13–20` | Explicit dependency order: universal foundations → R16/maximality → high-link alternatives → trace foundations → neighbourhood bootstrap. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:3–5` | Universal domain and explicit denial of a neighbourhood threshold/support cutoff; maps historical E17/E18/C1 language to the paper's current high-link theorem. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:21–37` | Complete link, singleton/complement split, degree identity, universal exact-trace capacities. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:63–78` | D7 and the size-10 rooted model: all relevant pair traces are 2 and complementary triple traces are 1. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:80–109` | Definition of extension points, D8, D9, and distinction of occupied extension points in a large index's K with size ≥9. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:252–261` | Section E explicitly gives the root split only for high points of degree ≥19. |
| `companion/upstream/MU42/PROOF.md:14–20` | The μ42 model imposes the already universal degree-17/18/19/20 split constraints; these are input premises, not bootstrap conclusions. |
| `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:149–152` | Historical E17/E18/C1 names are used for separation of complete links into components on disjoint supports. |
| `companion/upstream/D18_P10/PROOF.md:14–16,40–53` | Degree-18 use of the isolated P10/P9 component and high-link separation; this is corroboration, not needed as an independent premise. |

The target proof locations are `work/frontier20261023/highdegree/internal-proof.md:43–61`. No root proof file was edited by this check.

## Why the small-singleton implication is universal

Let R be any actual four-element member, y∈R, and A=R∖{y}, an actual member of the complete SF3 link L_y. Its singleton count s_y(R) is exactly the number of members of L_y disjoint from A, as defined in `TRACE_FOUNDATIONS.md:21–27`.

Suppose d(y)≥18. The universal bound gives d(y)≤20. By `lem:r16maximal`, L_y is the disjoint-support union of two intersecting families, with respective sizes 10+8 or 9+9 at degree 18, 10+9 at degree 19, or 10+10 at degree 20. The actual block A belongs to exactly one component. Every block in that component meets A because the component is intersecting; every block in the opposite component is disjoint from A because the supports are disjoint. Hence s_y(R) is the size of the opposite component, which is at least 8. Taking the contrapositive yields `s_y(R)≤7 ⇒ d(y)≤17`.

This argument applies to every actual anchor, not just the special central anchor or μ42-model rows. It uses neither a support cutoff, H27, a lower bound on |F|, nor any conclusion of the μ42 bootstrap. Degree 17 need not be excluded: its 10+7 split explains why the boundary is 17. No classification of an arbitrary I7 is required.

## Literal trace dictionary at R={x,1,3,5}

The complete link of x is the prescribed P10 on Y and its disjoint P10 on Z. The P10 list is written at `internal-proof.md:18–20`. Since this is the complete degree-20 link, there are no further members containing x. Its first-component cones give the following exact trace data; the ten second-component cones supply s_x=10, while k_x=10.

| Exact class on R | Prescribed first-component link blocks | Count / exterior extension |
|---|---|---|
| pair {x,1} | 012,124 | p_x1=2 |
| pair {x,3} | 023,034 | p_x3=2 |
| pair {x,5} | 045,245 | p_x5=2 |
| triple R∖{1}={x,3,5} | 235 | t_1=1, z_1=2 |
| triple R∖{3}={x,1,5} | 015 | t_3=1, z_3=0 |
| triple R∖{5}={x,1,3} | 134 | t_5=1, z_5=4 |
| R itself | 135 | the actual anchor |

The three extension points 2,0,4 are outside R and pairwise distinct. These facts may therefore be read from the literal P10 construction; the distinction theorem in `TRACE_FOUNDATIONS.md:103–109` gives the same conclusion without fixing labels.

Because a member with trace 13,15,35,135,{1}, or {3} on R necessarily avoids x, the local variables are exactly `a=p_13`, `b=p_15`, `c=p_35`, `e=t_x`, `s=s_1`, and `t=s_3` in the foundations' complete-family notation. Thus there is no residual/full-family mismatch. The five prescribed cones at points 1 and 3 supply the degree identities in the local proof.

## D8/D9 and the both-large case

Assume s_1≥8 and s_3≥8. The central index x is large because s_x=10.

* D8 at index 1, using t_3=t_5=1, gives p_13≤2 and p_15≤2. At index 3, using t_1=t_5=1, it gives p_13≤2 and p_35≤2. All required occupied triple classes are the prescribed classes in the table.
* If e=t_x=1, D9 applies to x and 1: both are large, t_x=t_1=1, and p_x1=2. It gives z_x=z_1. D9 applied to x and 3 likewise gives z_x=z_3. This contradicts z_1=2 and z_3=0. The universal 0/1 capacity for e then gives e=0.
* If a=p_13=2, D9 applies directly to 1 and 3, since both are large and t_1=t_3=1. It gives z_1=z_3, the same contradiction. D8 already gives a≤2, hence a≤1. This second argument does not require e=1 or e=0.

Thus the use of D9 in `internal-proof.md:55–59` satisfies all of D9's hypotheses. The existing prose is compressed, but the explicit identities above fill it without a new assumption.

Finally, if d(1)=20, the universal high-link split gives (s_1,k_1)=(10,10). D7 and its size-10 refinement give a=b=2 and all complementary triple traces occupied, including t_x=e=1. This confirms the separate `d1=20 or d2=20 ⇒ a=2 and e=1` premise; the point-3 case is symmetric.

## Remaining assurance boundary

No local logical gap was found in these geometric deductions **conditional on the imported universal structural results**. This inspection does not validate all finite computation inside the upstream universal R16 classification, and does not prove that classification in Lean. The new `Local51.lean` remains an axiom-audited arithmetic implication with the geometric statements as hypotheses. Connecting concrete set families to those hypotheses is an outstanding Lean representation/geometry obligation. This note is a targeted source check, not a final scholarly review or an independent reproduction of the upstream proof.
