# A triangle forced by the I06 equality case

23 October 2026. Ordinary structural research, not a final audit or Lean proof. No LP, numerical-model import, or enumeration was run. The saved v5 dual was read, including its integer scalar bound and positive row labels; its entire weighted coefficient sum was not independently replayed here.

The useful conclusion is a universal linear inequality from two actual members. Applied to the remaining singleton I06 assignment, it improves the saved v5 residual upper bound50 to49.5, conditional on that certificate's exact replay. It also shows directly that equality at50 forces a second I06 member. No cross-intersection of the two leaf P10 pools and no transversal-number-three assumption for Q8 is required.

## 1. General two-anchor inequality

Let F be a finite simple SF4 family, including the empty-core prohibition. Suppose the following are actual members, with all six displayed point labels distinct:

    R={x,h,k,m},       M={h,a,l,m}.

Let s be the exact singleton count at m relative to R, and let p be the exact pair count at {k,m} relative to R. Put

    M'={k,a,l,m},       j=1 if M'∈F, and j=0 otherwise.

Then

    s≥8 ⇒ p≤2+j,                                      (1)
    s+p−j≤12.                                         (2)

The only imported structural input beyond the usual exact trace capacities is B4 in the complete triple link at m.

To prove (1), consider the link anchor R∖{m}={x,h,k}. If s≥8, B4 says that its near family is intersecting. The actual member M contributes the near triple {h,a,l}.

The universal exact-pair cap gives p≤3, so it suffices to consider p=3. Write its three actual members as

    {k,m}∪U1, {k,m}∪U2, {k,m}∪U3,

where the distinct two-sets Ui avoid R. Any two Ui intersect: if they were disjoint, their two members together with R would form a sunflower with core {k,m}. The three Ui cannot have a common point, because their three corresponding members would then form a sunflower with core {k,m} together with that point. Three distinct pairwise-intersecting edges without a common point are the three edges of a triangle.

Every triple {k}∪Ui is near the link anchor because it contains k. Near intersection with the known triple {h,a,l} gives

    Ui∩{a,l}≠∅,

since Ui avoids h and k is distinct from h,a,l. A triangle whose every edge meets the two-set {a,l} must contain both a and l as vertices: with at most one of them, the opposite edge would miss the two-set. One of its edges is therefore {a,l}. Its corresponding actual member is M', so j=1. This proves (1).

For (2), if s≥8 use (1) and s≤10. If s≤7, use p≤3 to obtain s+p−j≤10≤12. The inequality is unconditional once the two actual members R,M are fixed. It is on arbitrary support and does not require μ41, a global degree cap, any component classification, or a complete internal assignment.

## 2. Literal application to Q8 I06

Use the complete root-link labels

    x=15, h=6, k=7, a=8, b=9, c=10, l=11, m=12.

The actual marker is M={6,8,11,12}, mask6464. The prescribed leaf root cone is

    R_m={15,6,7,12}, mask37056.

The exchanged member forced by (1) is

    M'={7,8,11,12}, mask6528.

It is another member of the same I06 internal orbit. The inequality is exactly

    s_12(R_m)+p_{7,12}(R_m)−n_6528≤12.                  (3)

All three coordinates have a literal actual-family interpretation in the full core projection. The first two count proper residual traces on R_m; the last is the binary four-core trace of the actual member M'. The fixed root cones contribute zero to those exact singleton and pair classes, so no extra fixed offset is needed. M itself has R_m-trace {h,m}, not {k,m}.

Exchanging l and m gives the additional valid row

    s_11(R_l)+p_{7,11}(R_l)−n_6528≤12,
    R_l={15,6,7,11}.

Both use the presence of M. No free or absent I06 member is treated as present in their hypotheses.

## 3. Consequence of the saved v5 dual

The inspected receipt is

    degree18_p10/Q8-I06-markedB4-d31e05613888.json.

It records source SHA-256

    1c50c4ca52c325b12156389a71b0a491dc27ba8f5645745d6e6d30f882aa2def,

scale10^10, H=500000000000, correction0, and therefore the reported residual bound50. Its positive upper rows include:

| Stored row | Label | Integer multiplier |
|---|---|---:|
| 866 | `['exact-anchor',37056,4096]` | 5000000000 |
| 871 | `['exact-anchor',37056,4224]` | 5000000000 |

These are respectively s_12(R_m)≤10 and p_{7,12}(R_m)≤3, each with normalized weight1/2. Assuming exact replay of the saved certificate, equality at residual50 forces both rows tight. Thus s=10 and p=3. Statement (1) then forces n_6528=1.

Consequently equality50 is impossible in the **complete singleton assignment** whose only Z-internal member is M. It is not enough merely to mark M while leaving other I06 members free: in that larger branch the conclusion is the presence of M', not an immediate contradiction.

There is a stronger direct bound for the singleton assignment. Because n_6528=0, inequality (3) says s+p≤12. In the saved weighted proof, replace the two half-weight rows s≤10 and p≤3 by one half-weight row s+p≤12. The coefficient vector is identical, the right-hand side drops by1/2, and the old box correction is unchanged. Every other constraint remains a necessary constraint for the singleton subcase. The exact residual bound is therefore

    residual≤49.5,

and integrality gives residual≤49. A hypothetical size68 family with root degree18 has residual50, so the singleton assignment is excluded under the replayed v5 certificate and the ordinary B4 argument above.

This replacement does not claim a new numerical run or independently reconstructed dual. It gives a concrete exact certificate transformation for a later replayer. Alternatively, the ordinary equality contradiction suffices if the original upper50 certificate has already been checked.

## 4. Implementation and scope

For a selected actual marker M and central anchor R_m, add the sparse row (3) directly to the trace variables. No local degree selector, conditional big-M constant, P10 support synchronization, or additional orbit enumeration is needed. Its right-hand side is12, with coefficients+1 on the exact-m and exact-km categories and−1 on the exact four-set M'. The negative coefficient on M' is intentional; that member belongs to the exact-km category and accounts for the permitted triangle edge.

The basic proof can be used in other branches whenever two actual members have this two-point overlap and B4 is available. Its use here is conditional only on the two actual anchors, not on the full Q8 internal classification.

The imported B4 source is `../../frontier20261020/prior-art68/repository/paper/main.tex:308–331`. The marked-member context is `D18-marked-B4-row.md`. Exact replay of the old dual, the preceding exclusion of other internal-orbit assignments, and any later H27 clique cuts remain separate evidence. This note does not assert closure of the unassigned I06 branch or of the whole D18 problem.
