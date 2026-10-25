# Independent ordinary check of global no-P9 at cap16

23 October 2026. Narrow proof-development check, not a final review,
model replay or Lean result. No solver or enumeration was run.

Checked `D16-P9-global-ordinary-exclusion.md`, SHA256
`f5159c7c5e9edc89da8117dc0d12969b817f4057577d53437c479da44f531a9c`.
The proof is valid under its named ordinary and imported premises.
All earlier notes pinned by v7 remain unchanged.

The additional exceptional-trace witness is exact: if both B and its
complement C occur in D(Q), intersection forces their exterior centres
to coincide at z. Every surviving outside-link triple U contains z.
Thus z+B,z+C,x+U have all three pairwise intersections exactly {z}.
This forbids their simultaneous occurrence whenever K' is nonempty.
For a singleton common intersection, HP15 consequently bounds the entire
avoider tail family by6, not7. Pair degree6 yields |D(Q)|<=21 when
k>=3; empty common intersection gives only the root star. Therefore
NO47 and complement22 force k2 equality and at least eleven global
three-point W traces, without a degree16-only I7 argument.

For m<=15, the initial O>=10 count retains internal four-sets. An
actual outside Q with a surviving K cone excludes all such internals.
The three complete C5 points have degree at most15, the remaining
three at most16, giving D_W<=66. The cone weights4/5 for singletons,
7/8 for pairs and at most9 for triples are correct. Hence

    369-9m <= W_sum <=5H+8P+9E
           =5D_W-2(P+E)-4E <=248+2m-4E.

With E>=11 and m<=15, the two ends force equality: m15,E11,D_W66,
P15,H3. Equality in the pair weights forces every pair trace inside
C=W minus B. The stated C5 pair-pool argument then contradicts P15.

There is also a shorter check of that last contradiction, avoiding a
separate pair-pool import. The residual incidence on C is at most
3*15-15=30, since the nine prescribed P9 cones already use15 incidences
there. The fifteen C-pair traces alone use30. But equality in one
actual disjoint complement contains the nine forced H-block copies,
which together contribute another15 incidences on C. These are distinct
residual members of trace size3, so the residual C-incidence is at
least45>30. Thus the equality contradiction follows directly from the
same complete-C5 degree bound already used in D_W<=66.

The lower-root argument uses the root16 exclusion only to cover m16
at its conclusion. The root16 proof did not use this global conclusion.
The dependency order is acyclic, and the resulting claim is global
no-P9 and exact-singleton cap8 under global cap16; the remaining
R16 and eight-plus-eight degree16 links are not excluded here.
