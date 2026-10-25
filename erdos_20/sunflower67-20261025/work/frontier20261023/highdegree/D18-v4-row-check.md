# Ordinary check of the v4 Q8 hub rows

23 October 2026. Targeted ordinary proof development, not a final audit, source-chain reproof, numerical certificate replay, or Lean result. No LP, numerical-model import, enumeration, or Lean job was run. The hashed research note and v3/v4 model files were read without editing them.

**Conclusion:** the HUB deletion lemma and the three newly added v4 hub restrictions are sound under their stated imported SF3 classification, isolation, B4, and universal R16 premises. In particular, the Q8 overlap argument isolates cores and permits shared leaves; it does not assume the two entire Q8 supports are disjoint. This conclusion concerns the new v4-minus-v3 rows, not every existing v3 row or the whole D18 branch.

The inspected files are:

| File | SHA-256 |
|---|---|
| `D18-Q8-internal-research.md` | `fb6b3918fe2e47cb23f7c4889b9d09bb6195da27bd7ec5572e218cad328887a6` |
| `degree18_p10_projection_v3.py` | `f699b11692532e800ef87c17dc5a3b7baac7cae4c50b0fa01e8ae64c3cee604d` |
| `degree18_p10_projection_v4.py` | `ea937a93ba7fdfdced8287ae832055ee63dc1cc4765437a749cfed436c3ccc7f` |

## 1. The star is complete, and its only intersecting additions are the three completions

Use the note's labels h=6,k=7,a=8,b=9,c=10,l=11,m=12 and x=15. In the complete link L_h, the members through x are exactly

    xab, xac, xbc, xkl, xkm.

Completeness follows from the complete root link L_x=P10(Y)⊔Q8(Z): its members containing h are exactly those five Q8 blocks. No additional four-set through {x,h} is available. This property persists upon deleting completion triples and upon choosing a sixteen-member subfamily containing the five star members.

A triple U avoiding x that meets all five star members must use at least two of a,b,c, to cover the triangle ab,ac,bc. With only one position left, it must use k to meet both disjoint-triad edges kl and km. Thus it is precisely one of kab,kac,kbc. This argument also excludes arbitrary new ambient points. The lifted four-sets are exactly

    {h,k,a,b}, {h,k,a,c}, {h,k,b,c},

with masks960,1472,1728: the entire I00 orbit. At the other hub the same three four-sets occur. Each completion meets every one of the five star members.

## 2. The sixteen-member obstruction

After deleting all present completion triples, suppose at least sixteen members remain. Select L0 of size16 containing the complete five-star. Its distinguished point x has degree exactly5 and the star spans seven points.

If every actual member of L0 has at most seven disjoint companions, the universal R16 theorem applies. In its displayed template, each of four hubs has degree6 and each triad point has degree4. There is no degree5 point. This excludes that case without treating every size16 family as R16.

Otherwise take an actual anchor A with at least eight disjoint members. Let D be its disjoint family and K its closed neighborhood. D is intersecting: two disjoint members of D together with A would form an empty-core sunflower. B4 makes K intersecting. Hence both have size at most10 and their sizes sum to16.

If D is P8, P9, or P10, isolation makes K avoid D's whole support. A deleted-block exception is on D's support, which avoids A, and would belong to D instead of K. If x belonged to this P-type support, all five x-star members would lie there. Their seven-point span cannot fit into a six-point P-type support. Therefore x lies outside it and all five star members lie in K. With the three completions absent, Section1 forces K to consist of just those five members. Then |D|+|K|≤10+5<16, a contradiction.

It remains that D is Q8 and K has size8. The intersecting size8 classification says K is P8 or Q8.

If K is P8, any D member meeting its support must be a deleted P10 block, by isolation. Such a member lies wholly on that six-point support. Since D is intersecting, no other D member may avoid that support; all eight D members would therefore be among at most two deleted blocks, impossible. Thus D and K have disjoint supports. The five-star lies in one part. Its seven-point span excludes the P8 part. In the Q8 part, its complete triangle-plus-path graph identifies x as a hub, k as the other hub, a,b,c as the triad, and l,m as the leaves. The other three Q8 triples are the absent completions, a contradiction.

If both D and K are Q8, first K avoids the core of D. Its only possible exceptional triples are on the support of D, so avoid A and cannot belong to K. Thus supp(K) is disjoint from core(D). Conversely, any D member meeting core(K) would be an exceptional triple on supp(K). Every D member contains at least two core(D) points, contradicting supp(K)∩core(D)=∅. Hence supp(D) also avoids core(K). Their only shared points can be leaves of both Q8 families. Such a shared leaf has total degree2, so the degree5 point x is not shared. All five x-star members lie in one Q8 part and again force the absent completions.

All cases are excluded. The completion-free triple family has size at most15 on arbitrary ambient support.

## 3. Global deletion row and degree cap

Let G be the number of the three I00 four-sets actually present. Deleting their corresponding triples from L_h leaves the same complete five-star and removes all possible completions. Therefore

    d(h)−G≤15,
    d(k)−G≤15.

This deletion proof does not require μ41, global Δ18, minimum used degree7, or any support cutoff. Those remain separate premises of the surrounding model.

In v4 lines511–520, `internal[v]` consists of genuine four-core members contained in Z and containing v. The edge-cover test on their three-point residues selects exactly the three masks above, at each of v=6,7. No proper trace or anonymous exterior multiplicity is being counted as G.

The complete root star contributes fixed_degree[v]=5. The code's row

    sum_(residual incidences through v, excluding I00) n_t ≤15−5

is consequently exactly d(v)−G≤15. Selected markers are counted in the residual variables, so their incidence is neither omitted nor subtracted twice.

Each of the three internal variables is binary with an actual-family upper bound hi[i]. Thus G≤Σhi[i], and the v4 line529 cap

    d(v)≤min(18,15+Σhi[i])

is necessary. After the I00 orbit has been excluded, Σhi=0 and both hub caps become15. The actual degrees still lie in the retained `degree_choices` even when optional distribution selectors are disabled; filtering local degree metadata by those choices is safe. The preexisting v3 minimum7 restriction has its own imported bridge and is not justified anew here.

## 4. Conditional near-size pruning

At a central anchor through h, the link anchor contains x. Its near family K therefore contains all five prescribed x-star members. If its disjoint singleton size s is at least8, B4 makes K intersecting. Section1 then shows that its other members are precisely the present completion triples. Every completion meets this anchor because it meets every star member. Thus

    s≥8 ⇒ |K|=5+G≤5+Σhi[i].

The same holds at k. This validates the v4 lines558–560 predicate

    singleton<8 OR near≤5+Σhi.

The singleton coordinate `cat[:,4+f]` follows the three residual-pair coordinates and one triple coordinate; `data['near'][:,f]` uses the same ordered anchor point. The condition is applied only when v is one of the two Q8 hubs. It does not impose a C5/P5 star assumption on Q8 triad points or leaves, and does not classify arbitrary I7 near families.

The note's additional HUB-K equality at d(v)≥17 follows from the imported universal disjoint-support high-link decomposition, since the part containing x is intersecting and contains the complete star. The v4 local predicate uses only the s≥8 case, so its soundness does not depend on extending that predicate to all high-degree rows.

## 5. Exact imported source boundary

Relative to `../../frontier20261020/prior-art68/repository/`, the required ordinary source statements are:

* `paper/main.tex:273–305`: P-type whole-support isolation and the two Q8 core exceptions.
* `paper/main.tex:308–331`: B4 and the explicit warning that Q8 leaves may be shared.
* `paper/main.tex:443–463`: the precise R16 guard |L|=16, ρ(L)≤7 and its displayed universal template.
* `paper/main.tex:612–636`: maximality and high-link decompositions, used for the separate degree≥17 HUB-K observation.

The R16 theorem is itself supported by the source's stated finite certificates; this check imports that theorem rather than independently proving its entire chain. No newly saved Q8 solver result, exact dual replay, staged orbit closure, or final degree18 conclusion is asserted by this row check.
