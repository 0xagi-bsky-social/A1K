# Ordinary check of the v5–v7 marked rows

23 October 2026. Targeted proof-development check, not a final audit, full model reconstruction, certificate replay, or Lean result. No LP or numerical producer import was performed. The frozen models and their hashed ordinary notes were read without editing them.

**Conclusion:** the added v5 marked-B4 restrictions, v6 literal H27 trace-clique rows, and v7 triangle-companion rows have valid actual-family interpretations on arbitrary exterior support. The checks below cover these additions to the previously checked v4 model, not every earlier source dependency or the whole D18 branch.

| Frozen model | SHA-256 |
|---|---|
| v5 | `1c50c4ca52c325b12156389a71b0a491dc27ba8f5645745d6e6d30f882aa2def` |
| v6 | `f82581d7034b65a3a890975925d45aa8822e81b6a6e549d43d76b66efbf14b58` |
| v7 | `8d926ede018142db5909da443c55792d51625e4d1b0eaa22e4157aa0098edad7` |

The imported local notes are `D18-marked-B4-row.md` (SHA-256 `a6472d0196e514f9b6396665334993880f080414a9199d42a4f50fc5c1481cfe`), `D18-H27-trace-cliques.md` (`aa2464c8325cd9344ebfd83091ea769a98de700c62a2491c997d0cd2ad4c5bb8`), and `D18-I06-triangle-closure.md` (`3ae4598a645482695649bf484ac906cb14b08129d88310e44d92413f8f5c2c0b`).

## 1. v5: literal disjoint near members force singleton at most7

For an actual anchor A and v∈A, `fixed_near_disjoint` at v7 line360 considers fixed actual members B through v satisfying `(B & A) != {v}`. Since B contains v, this is precisely the condition that B∖{v} meet the link anchor A∖{v}. It then seeks two such B,C with B∩C={v}. Their link triples are disjoint near members.

If the exact-v singleton class at A had at least8 members, B4 would make the near link family intersecting, contradicting this literal pair. Hence the actual singleton cap is7. The function uses only prescribed complete root cones and selected actual markers/assigned members; free variables with positive upper bounds are not treated as actual members. The anchor itself cannot produce a false witness: any near B intersects it in at least two points.

At v7 lines468–470, this cap replaces10 only for singleton traces with the witness. The row subtracts the fixed root-star contribution because the left side counts residual members. Selected markers remain in the residual variables and are not incorrectly subtracted as root cones. At lines603–604 the same witness removes central-selector rows whose corresponding singleton exceeds7. Both uses have the same actual interpretation and use the same ordered point index.

The proof is purely a B4 consequence. No degree cap, finite support, classification of I7, or speculative presence of an unselected member is used by this addition.

## 2. v6: H27 applies to actual trace multiplicities

The represented universe U contains every nonroot point of every fixed root cone and every point of every selected residual member. Residual members avoid root x. Thus, for a fixed actual B, whether a residual member Q meets B is determined exactly by Q∩U together with the known absence of x.

For two trace classes s,t, the code's `forced_meeting` at v7 lines486–487 has two valid witnesses:

1. If s∩t is nonempty, any actual members in the two classes share that represented point.
2. If some fixed actual B is disjoint from s∪t, then B is disjoint from every actual member in either class. Two disjoint actual members from those classes would form an empty-core sunflower together with B, which is impossible.

The test is also applied with s=t. This matters for a proper trace with multiple actual completions, especially the empty trace. A nonempty class is internally intersecting through its represented points; the empty class is internally intersecting because a fixed actual member disjoint from it rules out two disjoint completions. Diagonal checks are therefore part of the proof, not optional graph bookkeeping.

Any collection passing the pairwise and diagonal tests represents an actual intersecting subfamily of F. Its number of members is the sum of the integer trace multiplicities; proper traces are not treated as binary. H27 gives that sum at most27. The family counted is the residual subfamily in these classes, so the uncounted root cones need not be subtracted from27. A selected marker in a counted class is included once through its trace variable.

The fifteen seeds at v7 lines485–491 are enabled only for Q8 with the actual I06 marker. Every seed pair, including diagonals, is checked against the actual `fixed` members before the row is added. Each greedy extension at lines493–496 passes the same diagonal test and meets all existing classes, so the property is preserved by induction. Completeness or maximality of the clique search is unnecessary: any verified clique yields a valid row. Traces with zero upper bound may remain in a seed without changing the inequality; their inclusion is harmless.

A small independent check extracted only the literal seed lists using Python AST parsing, reconstructed the18 root cones and marker6464 literally, and checked all5235 seed pairs/diagonals. All fifteen seeds passed. This did not execute the producer, reconstruct its matrices, or run an LP. The greedy-extension correctness follows from the preceding induction; no claim is made that all possible H27 cliques have been found.

## 3. v7: both triangle-companion rows have the stated coordinates

The ordinary inequality proved in `D18-I06-triangle-closure.md` is

    s_m(R)+p_{km}(R)−1_{M'∈F}≤12,

for actual members R={x,h,k,m}, M={h,a,l,m}, and companion M'={k,a,l,m}. Its proof uses exact caps s≤10,p≤3 and B4: when s≥8, three exact-pair residues form a triangle, whose intersection with the known near member forces the companion. When s≤7 the bound is automatic.

The v7 addition at lines500–515 applies only to selected actual members in the literal I06 orbit. Such a member has one hub h∈{6,7}, one triad point a∈{8,9,10}, and both leaves11,12. The expression `k=13-h` selects the other hub. Replacing h by k gives exactly the companion I06 member. For each leaf, the generated anchor is the actual Q8 root cone containing x, both hubs, and that leaf. All point-distinctness and two-anchor overlap hypotheses hold.

The row first assigns coefficient+1 to the exact-leaf and exact-other-hub/leaf categories, then subtracts one from the companion's actual four-core variable. The companion belongs to the exact-pair category, so its net coefficient is zero. This is precisely the intended subtraction, not an assumption that the companion is absent. The implementation remains valid when the other I06 variables are free, which is essential for the new unassigned marked receipt.

All fixed root cones contain x, which is in the generated anchor, so their contribution to these singleton/pair categories is actually zero. The general subtraction `12-offset` is nevertheless the correct convention. Selected residual members continue to be counted through the variables.

An independent literal check covered all six I06 markers and both leaf choices: all12 anchors were prescribed root cones, every companion remained in I06, and its anchor trace was exactly the asserted other-hub/leaf pair. No model was imported for this check.

The code does not enable these rows for arbitrary unselected I06 variables. It enables them only when the member is listed in `selected`, either as the actual marker or as part of a complete assigned internal pattern. Thus no assumed presence is smuggled into the unassigned surrounding family.

## 4. Current active internal chain and remaining boundary

The independent geometry/stage checker has accepted the active Q8 internal chain in `D18-P10-active-manifest.json`:

* Original v2 receipts exclude I00,I01,I03,I07 without other Z-internal exclusions.
* The v4 HUB receipts exclude I02,I04,I05 using exactly those earlier forbidden orbits.
* `Q8-I06-triangle-255df392c7d3.json` excludes the unassigned marked I06 case with the other seven orbits forbidden. It records v7, scale10^10, H=490000000000, correction5000000000, and strict residual upper49.5.

All eight Q8 internal marker orbits, covering all35 Z-internal four-sets, are represented in this dependency chain. No complete-pattern receipt is active; the optional I06 pattern plan does not supply an assumption to this chain. The checker validates literal geometry, premise dependencies, hashes and saved scalar arithmetic. Exact coefficient replay of the numerical certificate remains separate.

The Q8 mixed-four and mixed-three domains still require their own active receipts before full marker coverage is claimed. H27 itself, B4, the preceding v3/v4 bridge, and the terminal ordinary argument after exclusions are imported or separately documented. This note supplies a soundness check of the new rows, not a new proof of those dependencies or an end-to-end D18 conclusion.
