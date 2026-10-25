# Degree-18 exterior pools: ordinary structural cuts

23 October 2026. Research note, not a final audit or Lean proof. No solver, classification replay, or Lean job was run. The new statements below use arbitrary ambient ground sets and the imported universal intersecting SF3 classification and H27. They do not use cardinality 69, μ≥42, a minimum degree, or an upper bound on support.

Assume F is finite, simple, four-uniform and three-sunflower-free, including empty cores. In the degree-18 application suppose |F|≥68 and Δ(F)≤18. For a complete central P10 or P9 component S, put

    H_y={T:T∩(S∪{x})=∅, {y}∪T∈F},   h_y=|H_y|,  y∈S.

The principal new usable row is

    h_y+h_z≤16  for every two distinct y,z∈S.                 (HP16)

In particular h_y=10 forces h_z≤6, while h_y=9 forces h_z≤7. This strengthens the old aggregate bounds without asserting that those aggregate bounds alone decrease.

## 1. Scrutiny of the doubled-P10 proof

The argument in `doubled-P10.md` is sound under the stated four-uniform/simple/all-cores convention. In the trace witness, allowing A=B is legitimate because the actual members a∪A and b∪B have distinct centres; they are distinct four-sets. If Q avoids the centres, its exterior points cannot affect intersections with these stars. If Q contains a centre, P10 isolation is applied to that centre's SF3 link. Finally H27 is applied only to the intersecting family avoiding both centres, after its disjointness from the P10 support has been proved.

The resulting bound is

    |F|≤27+d(a)+d(b)−d(a,b).

Under Δ≤18 this is at most 63. Thus a hypothetical |F|≥68 cannot contain a doubled P10 anywhere, independently of the central component under consideration. This is a global prohibition; cross-intersection alone does not assert that two smaller pools are identical.

## 2. Two near-complete P10 stars

Let P be a P10 on six-point support H, let a,b∉H be distinct, and let P_a,P_b⊆P. Suppose all members a∪A for A∈P_a and b∪B for B∈P_b belong to F. Define the total number of omitted blocks, with omissions in the two families counted separately, by

    m=(10−|P_a|)+(10−|P_b|).

If m≤3, then

    |F|≤27+d(a)+d(b)−d(a,b)+m.                               (NP10)

Consequently, under Δ≤18, such two stars force |F|≤63+m≤66 and are impossible in the ≥68 case.

### The trace witness with at most three omissions

Let ∅≠S⊆H, |S|≤4. Unless S is a P10 block absent from at least one of P_a,P_b, there are A∈P_a,B∈P_b such that

    A∩B=A∩S=B∩S.

A useful elementary observation: if two distinct P10 blocks A_1,A_2 have the required common trace on S, failure of both orientations (A_1 in P_a, A_2 in P_b) and (A_2 in P_a, A_1 in P_b) costs at least two membership omissions. The two orientation tests use disjoint membership incidences.

* **|S|=1, S={v}.** Exchange a,b so that P_a omits at most one block; this is possible because m≤3. At least one block B∈P_b contains v, since P_b omits at most three of the five blocks through v. In the C5 point-link, B's residual edge has two disjoint edges. At most one corresponding block is missing from P_a. A surviving choice gives A∩B={v}.
* **|S|=2, S={u,v}.** The two blocks containing S give one candidate pair. A matching of size two in the point-v C5 with vertex u deleted gives another candidate pair, whose common trace on S is {v}. These four blocks are distinct. Failure of both candidate pairs costs at least four omissions, impossible.
* **|S|=3 and S∈P.** If S lies in both families take A=B=S; otherwise this is precisely the permitted exceptional case.
* **|S|=3 and S∉P.** For each of its three pairs C, the two P10 blocks containing C have distinct third points outside S. These six blocks are all distinct: a block containing two different pairs of S would be S itself. Failure of all candidate pairs would cost at least six omissions. Thus one gives the required trace C.
* **|S|=4.** Exactly two P10 blocks T_1,T_2 lie in S, since exactly 10−5−5+2=2 blocks avoid the complementary pair. If one is in both families, use A=B. Otherwise at least two omissions have already occurred. The pair C consisting of the two points in T_1△T_2 lies in neither internal block. Its two P10 blocks therefore have their third points outside S and form a candidate pair. They are distinct from T_1,T_2; blocking both orientations costs two further omissions. Four omissions would be required, impossible.

This argument is on literal traces, without enumeration or a finite exterior universe.

### Counting the exceptions

Let G consist of members avoiding both centres. For Q∈G, a nonempty trace on H not covered by an exceptional P10 block would give a sunflower with the two star members in the witness. Thus any Q∈G meeting H has Q∩H=T for some T∈P. Such Q is T∪{z}, with z∉H∪{a,b}.

The triple T already has 1_{T∈P_a}+1_{T∈P_b} completions at the two centres. Its global codegree is at most two. Hence the total number of these exceptional Q is at most

    Σ_(T∈P) [2−1_{T∈P_a}−1_{T∈P_b}]=m.

Every remaining member of G avoids H. Any two disjoint such members, together with any prescribed a-star member, would be an empty-core sunflower. They form an intersecting SF4 family and have size at most27 by H27. Thus |G|≤27+m; inclusion-exclusion of the two centre stars proves (NP10).

No isolation assertion about additional centre-containing members is needed for this counting proof: all of them are already included in d(a)+d(b)−d(a,b).

## 3. Cross-intersecting large pools satisfy HP16

Each H_y is an intersecting SF3 family: a fixed central cone through y would form a sunflower with two disjoint tails. Hence h_y≤10. For y≠z, a P10 block avoids both points; after one deletion a P9 still has such a block. Its central cone shows that H_y,H_z are cross-intersecting.

If h_y=10, H_y is P10. Its triple transversals are precisely its ten blocks, so H_z⊆H_y. If h_z≥7, the two centre stars omit at most three blocks in total and (NP10) contradicts |F|≥68, Δ≤18. Therefore h_z≤6.

If h_y=9, write H_y=P∖{D} with P a P10 and E=H∖D. The triple transversals of H_y are exactly P∪{E}; there is no two-point transversal. Thus H_z⊆P∪{E}.

If E∈H_z, then D∉H_z because D and E are disjoint and H_z is intersecting. Each of the three pairs of E belongs to two P10 blocks, and these six blocks are distinct because E∉P. Including E in the sunflower-free triple family H_z forces omission of at least one block for each pair, lest its pair codegree become three. Thus H_z omits D and at least three other P10 blocks, so h_z≤6+1=7.

Consequently h_z≥8 implies H_z⊆P. Then the two stars have at most (10−9)+(10−8)=3 omissions, and (NP10) again contradicts the size assumption. Therefore h_z≤7.

If h_y+h_z≥17, one has size at least9. The preceding two cases exclude all possibilities. This proves (HP16).

The argument also applies to two complete exterior triple families obtained in another context whenever they are intersecting and cross-intersecting, their distinct centres avoid both tail supports, and their four-set lifts belong to F. Their origin in a particular central component is only a sufficient way to obtain cross-intersection.

## 4. Another cut: no common P8

Two centres cannot share all eight blocks of a P8 in the ≥68, Δ≤18 setting. For a doubled P8, write it as P10 minus two blocks D_1,D_2. The four trace-size cases from the doubled-P10 proof still exclude every nonempty trace except D_1,D_2:

* Singleton traces have a matching of size two in C5 after at most two edges are removed.
* For a pair {u,v}, use the two blocks through the pair, the two matching blocks through u avoiding v, and the two matching blocks through v avoiding u. These are three disjoint pairs of blocks. Two deleted blocks cannot destroy all three pairs.
* For a triple outside P10, its three pair-based candidate pairs use six distinct blocks, so again two deletions cannot destroy all three. A retained P10 block uses A=B.
* A four-set contains two P10 blocks. If neither survives, they are exactly D_1,D_2; the two blocks through their symmetric-difference pair both survive and give the witness.

Members avoiding the centres and meeting the support therefore extend D_1 or D_2, at most four members by triple codegree2. The rest form an intersecting family, as before. Hence

    |F|≤27+d(a)+d(b)−d(a,b)+4≤67.

This rules out any common P8 subfamily of two pools. It does not rule out a common Q8 by the same proof: Q8's leaves and two-point transversal require a separate argument. It also does not assert that arbitrary two eight-member cross-intersecting pools coincide.

## 5. Which upstream pool inequalities transfer

The following constraints are genuinely universal once the stated central component and actual exterior pools have been defined.

* The pair/singleton table is b=0,…,6 with h≤10,10,8,5,4,2,1, and its weaker linear consequence 5h+9b≤59. For C5 use the whole pair-residual family through y. For P5 apply it separately to pair traces whose other central point avoids each of the two vertices of the unique two-cover. It is not valid to silently use the whole P5 pair family.
* The scalar pool bounds Σh≤36 if one h≥8, Σh≤22 if one h≥9, and Σh≤20 if one h=10 follow from triple-transversal counts and multiplicity at most two. The sharper P8-without-two-cover bound24 also survives.
* H27 applies to the union of all four-set singleton categories, since they are pairwise intersecting. Therefore Σh≤27 holds unconditionally for these six pools. This dominates36 and the generic Q8 bound34; it does not dominate22,20, or24.
* (HP16) is an additional set of fifteen linear inequalities per six-point component, valid after the global ≥68 and Δ≤18 hypotheses are available.

The old total20 bound is not reduced merely by observing that doubled P10 is forbidden. A full pool of ten can share its ten second occurrences among five other centres, two blocks per centre; this has total20 but creates no second large pool. For example, take a degree-18 central link P10(Y)⊔P8(Z) on disjoint supports, one external P10 on H, all ten tails at centre0, and assign each tail once more to one of centres1,…,5 with two tails per centre. This is a sunflower-free local family of38 members with Δ18 and singleton pool total20. Its central cones and tail members cannot make a mixed sunflower because pair intersections of tail members meet H whereas cones avoid H. It is not a ≥68 counterexample; it shows that reducing the aggregate20 needs additional information about the rest of F.

## 6. Translating anchor singleton sizes into actual pool cuts

The shared-pool interpretation is essential. At singleton size9 or10, isolation identifies that anchor singleton exactly with H_y. At size8, a P8 singleton contributes eight exterior triples, while a Q8 singleton contributes at least its six core triples; its leaf triples may fail to be exterior. Thus universally

    h_y≥ℓ(s_y),  ℓ(10)=10, ℓ(9)=9, ℓ(8)=6, ℓ(s≤7)=0.

Combining with HP16 gives ℓ(s_y)+ℓ(s_z)≤16 for two distinct central neighbours. In particular two singleton sizes9/10 are impossible in one component. If one has size10, another size8 can only be Q8, with exactly six exterior triples and both leaf triples non-exterior. If one has size9, another size8 cannot be P8; a Q8 may have six or seven exterior triples.

Whenever the stronger complete-C5 degree≥16 lemma applies, the far component is entirely exterior, so it is safe to use its full size rather than the generic lower bound six for Q8. The imported high-link separation gives the same benefit at degrees17–18. These distinctions avoid treating unrelated scalar anchor rows as independent exterior families.

## 7. Dependencies which cannot be carried over wholesale

`D18_P10/PROOF.md` builds its anchor catalogues at threshold42 (lines55–60), and its empty-P10 forest uses97 rows per anchor and the resulting degree-profile list (lines124–148). Their orbit exclusions and exhausted forest therefore do not transfer to μ41 by citation alone. The same applies to the R99 internal and marked-trace exclusions whose target is residual51: numerical bounds between50 and51 do not exclude residual50.

In contrast, pair/singleton geometry, literal extension identifications, the degree18/codegree6/2 capacities, complete-C5 deductions, the pool inequalities, and the new near-P10 proofs remain available on arbitrary support. The concrete source restrictions, rather than the paper's terminal degree conclusion, are the justification for each row.

## Frozen source locators

All upstream paths are relative to `../../frontier20261020/prior-art68/repository/`.

* `companion/upstream/D18_P10/PROOF.md:62–97`: pair/singleton geometry, table, and explicit independence from H27/μ42/n69/support bounds.
* `companion/upstream/D18_P10/PROOF.md:183–218`: shared exterior pools,8/9/10 transversal bounds, and the old all-degree13 example.
* `companion/upstream/D18_P10/PROOF.md:289–300`: H27 on the union of pure singleton categories, with internal assignments unrestricted.
* `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–123`: cross-intersection, multiplicity two, and P9/P10 transversal descriptions.
* `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:125–152`: actual singleton-to-pool identification and the Q8 leaf caveat.
* `companion/upstream/D18_R99/PROOF.md:70–78,98–117,123–158`: shared pool rows and the original residual51-dependent exclusions.
* `paper/main.tex:206–231,272–350`: P10, intersecting triple classification, isolation, and universal degree/codegree caps.

The new ordinary results proved here are (NP10), (HP16), and the doubled-P8 exclusion under the stated global hypotheses. No entire degree-18 branch is declared closed.

## 8. Terminal P10 plus P8/Q8: residual count at most37

There is a short terminal separation proof which survives the possible two-point transversal of P8 or Q8.

Let the complete central link be P10(Y)⊔J(Z), where J is P8 or Q8 on a disjoint support Z. Write S=Y∪Z, and assume two previously established exclusions:

1. No residual member avoiding x has four points in S.
2. No residual member has a three-point trace on S meeting both Y and Z.

These exclusions are hypotheses here, not conclusions of this note. Thus the permitted core traces have size at most two, or are pure triples in one component. Let R be the family of residual members avoiding x.

If Q,Q′∈R are disjoint, then (Q∪Q′)∩Y must be a transversal of P10(Y), and (Q∪Q′)∩Z must be a transversal of J. Otherwise a central cone avoiding both would give three pairwise disjoint members. The relevant transversal lower bounds are

    τ(P10)=3,     τ(J)≥2.

The second bound is valid for both P8 and Q8: neither has a point common to all its triples. It does not assert τ(J)=3.

Suppose neither Q nor Q′ has a pure Y trace of size three. Their Y traces must nevertheless have union size at least three. At least one then has a pure Y pair: a mixed allowed trace has only one Y point, and two such traces have at most two Y points altogether. The other member has a Y point and hence at most one Z point, since mixed three-point traces are forbidden. The pure Y pair member has no Z point. Thus their Z union has size at most one, contradicting τ(J)≥2.

Therefore one member, say Q, has a pure Y triple trace T. To cover Z, Q′ must have at least two Z points; the allowed-trace hypotheses force it to have a pure Z pair or pure Z triple and no Y points. It follows that T itself is a transversal of P10. Such a triple is one of P10's ten blocks.

Define

    A={Q∈R: Q∩S is a block of P10(Y)}.

Every disjoint pair in R has one member in A. Hence R∖A is intersecting and H27 gives |R∖A|≤27. Each block T of P10 already has the prescribed completion x∪T, so its global triple codegree at most two permits at most one residual completion. Therefore |A|≤10 and

    r=|R|≤27+10=37.                                        (TERM-P10)

In particular residual50 is impossible. No restriction on the number or identities of exterior points is used. A pure Z pair extending the unique two-cover is allowed throughout: it belongs to the opposite side of every possible disjoint residual pair, so it does not enlarge the class A which is removed before applying H27.

The same asymmetric argument explains why it is unnecessary to bound the entire Z-transversal pool or remove its two-cover extensions. It is enough that the opposite P10 has transversal number three and only ten triple transversals, each with one existing central completion. The unresolved work for applying this terminal lemma is the exact exclusion of four-core and mixed-three traces at residual50; the old residual51 certificates cannot supply those exclusions automatically.
