# Bridge for the new R99 exterior-pool rows

23 October 2026. Targeted ordinary justification of four added row families, not a final model audit or Lean result. No solver or catalogue job was run. The inspected `degree18_r99_projection.py` has SHA-256

    eaf95c1159c85387c8953eec5cd70c9782485286493640b2df9252584f8e823f.

The row constructions checked are HP16 at line121, pool-affine at123, and whole-pool / pool-conditional at161–168. This note binds those formulas; it does not assert that future edits have the same hash.

Assume a finite simple SF4 family F with |F|≥68, Δ(F)≤18, and complete link P9(Y)⊔P9(Z) at x on disjoint six-point supports. All sunflower cores, including the empty core, are forbidden. H27 and the universal SF3 structure theorems remain imported mathematical premises. No μ42, minimum degree, or support bound is used.

## Shared coordinates represent actual pools

For a component C and v∈C, put

    H_v={T:T∩({x}∪C)=∅, {v}∪T∈F},
    h_v=|H_v|,   P_C=Σ_(v∈C)h_v.

For residual trace counts n_S on the model's core, these are exactly

    h_v=Σ_(S∩C={v})n_S,   P_C=Σ_(|S∩C|=1)n_S.

Exterior points, including points of the other component or a distinguished marked exterior point, remain unrestricted. Each quadruple in a fixed singleton category determines one triple of H_v and conversely. The central cones have component traces of size0 or3, so no fixed central contribution needs subtracting from these coordinates.

Each H_v is intersecting SF3: two disjoint tails and a prescribed cone through v would give a sunflower with core{v}. For v≠w a P9 block avoids both, so disjoint tails from H_v,H_w would give an empty-core sunflower with its cone. Thus the pools are cross-intersecting. A triple lies in at most two pools by the global triple-codegree bound2.

The union of the actual singleton-category quadruples is intersecting. H27 therefore gives P_C≤27. Intersecting SF3 classification gives h_v≤10. If h_v=10, the P10 transversal description and multiplicity2 give P_C≤20; if h_v=9, the P9 description gives P_C≤22.

## HP16

The code row is exactly

    h_v+h_w≤16,   v≠w in the same component.

Its proof is `D18-pool-research.md`, §§2–3. If two pools sum to at least17, one has size10 and the other at least7, or one has size9 and the other at least8. In the first case both lie in the same P10. In the second, the size≥8 pool also lies in the unique P10 completion of the P9: its only possible extra transversal is the complementary triple, whose presence would limit that intersecting SF3 pool to at most7 members.

There are at most three total omitted blocks in the two P10 subfamilies. The near-P10 trace argument gives

    |F|≤27+d(v)+d(w)−d(v,w)+3≤66,

a contradiction. The row genuinely uses the global hypotheses |F|≥68 and Δ≤18. It is not claimed for arbitrary small SF4 families.

The generator coefficient test `(S&comp) in (1<<v,1<<w)` counts the two disjoint singleton categories exactly once each.

## Pool-affine

The row is exactly

    2P_C+7h_v≤110.

For h_v≤8 it follows from 2·27+7·8=110. At h_v=9 the P9 pool bound gives 2·22+7·9=107; at h_v=10 the P10 bound gives 2·20+7·10=110. These exhaust the integral actual values of h_v. Hence this linear row is valid for every actual family and remains valid in the relaxation containing their convex hull.

The code assigns coefficient9 to the v-singleton category and coefficient2 to the other five singleton categories, which is precisely 2P_C+7h_v. HP16 is not needed for this affine row.

## Whole-pool lower bounds at a central anchor

Fix an actual central anchor x∪T through v. In L_v let A=(x∪T)∖{v}, D={B:B∩A=∅}, and K={B:B∩A≠∅}; write s=|D|, k=|K|, d=s+k.

Always H_v⊆D, since its tails avoid the whole central component and x. The lower bound used in the code is

    h_v≥g(s,k,d),

where g=s if d≥17, or if v is C5 and d≥16, or if s≥8 and k≥8. In all other cases g=ell(s), with ell(8)=6, ell(9)=9, ell(10)=10 and ell(s≤7)=0.

Each case has an ordinary structural justification:

* At s=9 or10, D is P9/P10. P-type isolation makes K avoid the whole support of D: any allowed missing P10 block would still avoid A and hence belong to D, a contradiction. The prescribed x-star in K spans {x}∪(C∖{v}), so D is wholly exterior, and H_v=D.
* At s=8, the same proof gives h_v=8 if D is P8. If D is Q8, its five-point core avoids K. An exceptional extra triple meeting that core would use its two leaves and one hub, hence would avoid A and could not lie in K. The six core triples are therefore exterior. The two leaf triples need not be exterior, so only h_v≥6 is asserted in the generic case.
* At d≥17, the universal high-link decomposition gives intersecting parts on disjoint supports. The part containing x contains its complete P5/C5 star, hence all of {x}∪(C∖{v}). As A is a member of that part, its intersecting property makes it exactly K; the opposite part is D and is entirely exterior. Thus h_v=s. This includes the possible arbitrary I7 near part; no I7 classification is being assumed.
* For a C5 neighbour at d=16, the complete-C5 lemma in `C5-internal-compatibility.md` supplies the same disjoint-support conclusion. It explicitly excludes R16 by point degrees4/6 and the Q8/Q8 case by the complete C5 point-link. Thus h_v=s.
* If s≥8 and k≥8, B4 first makes K intersecting. Its I8/I9/I10 classification cannot be Q8, whose complete point-links are not P5 or C5. Hence K is a P-type, with support exactly {x}∪(C∖{v}). Isolation makes D avoid that support: a missing P10 block would meet the actual block A and so would not lie in D. Again h_v=s.

For a local selector row r the generator correctly computes

    k(r)=d_F(x,v)+the two residual exact-pair counts through v
                     +the residual exact-triple count,
    d(r)=k(r)+s(r).

Here d_F(x,v) is4 at a P5 point and5 at a C5 point. The selector feature order uses the same sorted three points as the singleton coordinates. There is no extra constant from a marked member: it already contributes through the shared trace counts.

An actual family chooses a single actual local row. Therefore

    Σ_r λ_r g(r)−h_v≤0

is necessary. The `whole-pool` code assigns precisely these coefficients. In particular it does not infer h_v≥s−2 for s≤7 merely from k≥8; the intersecting-near-part hypothesis is needed and is included in the code's condition.

## Pool-conditional

For one anchor and one neighbour v, the code row is

    P_C+5 Σ_r λ_r[s_v(r)=9]+7 Σ_r λ_r[s_v(r)=10]≤27.

For an actual row, s=9 implies h_v=9 and hence P_C≤22; s=10 implies h_v=10 and P_C≤20. Otherwise P_C≤27 suffices. These three cases prove the inequality. Its coefficients5 and7 are the actual losses from27, not arbitrary numerical penalties.

The proof applies separately to each (anchor,v) row. Adding penalties from different points into one stronger right-side27 row would require another argument; the inspected code does not do that. Sharing the same h_v and P_C between all anchors is necessary, and the generator does so through the common residual trace coordinates.

## Source and assurance boundary

The direct ordinary derivations and pinned locators are recorded in `D18-structural-tools.md`, `D18-pool-research.md`, and `C5-internal-compatibility.md`. Frozen universal sources include `paper/main.tex:206–231,272–350,443–462,612–636` and `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–152`, relative to `../../frontier20261020/prior-art68/repository/`.

All four row families have the required actual-family interpretation. Convex selector relaxation may admit spurious solutions; validity only requires that every actual family map into it. This note checks those four formulas and their mathematical premises, not all row catalogues, staged case coverage, numerical certificates, or the final degree-18 conclusion.
