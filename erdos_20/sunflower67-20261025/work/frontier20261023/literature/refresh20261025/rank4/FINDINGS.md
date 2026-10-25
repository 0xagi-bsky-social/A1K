# Rank-four literature refresh — 25 October 2026

Fresh literature gate only. No specialist review round, proof vote, final audit, manuscript edit, computation replay, or publication was performed.

Cutoff requested: client date 2026-10-25, America/New_York. Retrieval session ended approximately 2026-10-25 13:24 UTC (09:24 EDT); this does not claim coverage of the remainder of the date. Tool outputs include their own crawl dates, which can be older than retrieval. Old local ledgers were read only as source-location leads and were not treated as fresh checks.

## Bounded conclusion

No public primary result establishing ordinary M(4,3) ≤ 67 or a stronger upper bound was identified in the retrieved records. No revised version, withdrawal, or correction affecting the two checked rank-four foundations was observed. The strongest directly inspected rank-four claim remains Babanskyy's upper bound 68; the current project's proposed upper bound 67 would improve that numerical comparison by one if established. This is a bounded search result, not an exhaustive novelty certification, proof validation, or authorization to resume reviews or publish.

The comparison means finite simple families of exactly four-element sets, on arbitrary finite support, with three distinct members forbidden whenever all pairwise intersections agree, including an empty core. It is a maximum-size convention: upper bound 67 is equivalent to forcing a sunflower at 68, and upper bound 68 forces one at 69.

## Primary records freshly checked

| Primary source | Observed version / date | Exact relevant scope and result |
|---|---|---|
| [Oleksiy Babanskyy, aiXiv:2610.01292](https://aixiv.online/abs/2610.01292), [v1 HTML](https://aixiv.online/html/2610.01292v1) | Only v1 displayed, received 2026-10-09 10:55:39 UTC. No correction or withdrawal displayed. | Theorem 1.1 excludes size 69 using imported H27 and the manuscript's classification and finite-exclusion lemmas, hence 54 ≤ M(4,3) ≤ 68. Definitions match the scope above. The paper explicitly does not exclude size 68. Its local cap 61 needs a complete R16 point-link and is not global. |
| [Babanskyy companion](https://github.com/aconsciousfractal/Four-Uniform-Three-Sunflower-Bound) | Fresh commits query returned one commit: 90c03c79bcf44eb8f61dff1b86091b822cc4cd3c, 2026-10-08 23:25:44 UTC. All-state issue query returned []. | README and pinned paper/main.tex still state 68. The README separates exact computational replay from verification of written reductions and external human reproduction. H27 is imported, not re-executed by this companion. |
| [Axante, Budala, Chitic, Dumitru and Nacu, arXiv:2609.06175](https://arxiv.org/abs/2609.06175), [v1 HTML](https://arxiv.org/html/2609.06175v1) | Only v1 displayed, submitted 2026-09-05 16:31:55 UTC. No correction or withdrawal displayed. | Proposition 6.7: every intersecting four-uniform three-sunflower-free family has at most 27 members. Proposition 6.8 supplies equality; Theorem 6.9 gives 54 ≤ f(4,3) ≤ 83. The definitions explicitly allow the empty core and require finite families with distinct members. |
| [Axante author-linked companion](https://github.com/bogdan27182/sunflower-paper) | Fresh commits query returned three September 5 commits, latest d4d5723267c662291efdadfa6e7061d919e76fa9 at 08:11:54 UTC. All-state issue query returned []. | H27 uses 11,720 canonical-augmentation roots and an archived search ledger. The freshly read lean/README.md lists the rank-four lower witnesses and explicitly excludes finite upper-bound enumerations from its formalized scope. No new H27 kernel proof was found here. |
| [Bogdan C. Dumitru's university page](https://cs.unibuc.ro/~bdumitru/) | Page footer says last updated 27 September 2026; retrieved afresh. | Author's sunflower entry still states 54–83 and intersecting maximum 27. Its withdrawal statement concerns a different separating-words paper, not sunflowers. |
| [Babanskyy homepage](https://www.oleksiybabanskyy.com/) | Fresh search representation, crawler age two weeks. | E20-R4 v0.2.0 card states 54–68 / forcing 69. This is a related author source, not independent confirmation. |

The companion heads agree with the heads retained in the older local ledger; that comparison was made after fresh retrieval. Empty issue lists cover those endpoints and do not prove that no discussion or correction exists elsewhere.

H27 remains an ordinary computer-assisted external theorem in this literature check. No large computation or Lean rebuild was run. No inference of falsehood or formal assurance is made from the search ledger, README wording, or absence of a new issue.

## Potentially confusable leads checked or scoped out

- [SproutSeeds/sunflower-lean README](https://github.com/SproutSeeds/sunflower-lean/blob/6b7f3dcc19a111cf772a630092c48567ac1b51d8/README.md) studies intersection-capped M3(l,t). Its M3(l,2) ≤ 3l²−l+2 yields 46 at l=4 only under the extra pairwise-intersection cap 2. The current target allows intersections of size 3.
- [SproutSeeds SmallCases.lean](https://github.com/SproutSeeds/sunflower-lean/blob/6b7f3dcc19a111cf772a630092c48567ac1b51d8/SunflowerLean/SmallCases.lean) says M(4,3)=8, but its literal quantification is over families of subsets of Fin 4, with no uniformity constraint. Here 4 is support size. It cannot replace ordinary rank-four M(4,3).
- [Rynaldo Stoltz manuscript](https://github.com/rynald0cst0ltziam/erdos-sunflower-decay/blob/main/MANUSCRIPT.md), dated 20 February 2026, reports a heuristic 36-member rank-four lower family and empirical spreadness behavior. It supplies no universal upper 67 or better, and its lower36 is below the classical54.
- [Four-Petal Sunflower-Free Triple Extremal Threshold](https://github.com/jfairfaxball-348/Four-Petal-Sunflower-Free-Triple-Extremal-Threshold) concerns f(3,4), a different uniformity/petal pair; its README explicitly reports no stronger bound.
- [DennisKoshta/sunflower3-49a-certificate](https://github.com/DennisKoshta/sunflower3-49a-certificate) reports the Erdős–Szemerédi capacity lower bound μ3 ≥ (64728+√3018723123)^(1/26) ≈ 1.5678599024. Its block has 252,292 sets on28 points. [clavis-systems/c49-sunflower-replay](https://github.com/clavis-systems/c49-sunflower-replay) concerns capacity replays. Neither is a uniformity-four upper bound; neither was executed. This adjacent lead was passed to the parent.
- Turán-number results with a prescribed core size, Frankl-completeness, bounded-VC-dimension estimates, and mixed-size/word-capacity results surfaced in searches. None was promoted into an ordinary rank-four numerical improvement. Secondary VibeMathed, MathWorld, SciRate, ProofAtlas, and similar records were leads only.

## Coverage limits and retrieval failures

1. The fresh arXiv native search URL for sunflower, ordered newest first, returned a representation crawled six days earlier whose newest listed result was September27. It omitted the already known October19 Bucić–He–Lee result. It is therefore demonstrably incomplete for the requested cutoff and was not used to establish absence.
2. aiXiv REST list and paper-record URLs returned tool-access errors. The aiXiv abstract/history page worked, and the versioned HTML initially failed on direct open but succeeded through its observed link. No entire aiXiv corpus was retrieved by this agent.
3. A first URL used aixiv.science/abs/2610.01292 and failed. The relevant archive is aixiv.online. Searching the bare numeric ID also returns an unrelated arXiv high-energy-physics article: aiXiv and arXiv IDs must not be conflated.
4. GitHub /readme endpoints were rejected as unsupported by the connector; the same public files were successfully read through /contents/README.md. Raw failures are retained.
5. GitHub repository search used bounded first pages (up to100), and code search used top30 or100 results. Broad numeric searches returned many homonyms and do not exhaust GitHub. Exact phrases, the known author repositories, and narrower mathematical queries were also used.
6. Search engines often relaxed over-specific numerical queries and returned irrelevant results. No-hit or irrelevant-hit searches were not treated as evidence of mathematical absence. Version histories and author repositories provide positive evidence only for their own displayed states.
7. Search and fetch outputs are preserved verbatim as returned, including old crawl labels and errors, in source-tool-outputs.json and source-tool-outputs-supplement.json. Their call order and exact arguments are retained. No historical raw record was overwritten.

## Actual web queries

1. `"sunflower" "4" "67" Babanskyy`
2. `"2610.01292"`
3. `"2609.06175"`
4. `Babanskyy sunflower 68 aiXiv`
5. `"sunflower" "4" "67" "bound"`
6. `"sunflower" "M(4,3)" "67"`
7. `"sunflower" "f(4,3)" "66"`
8. `"sunflower" "four-element" "65"`
9. `"sunflower" "four-uniform" "64"`
10. `"sunflower" "f(4,3)" "54"`
11. `"sunflower" "forcing threshold" "68"`
12. `"sunflower" "4-uniform" "67"`
13. `"sunflower" "68 sets"`
14. `site:arxiv.org sunflower "4,3" "67"`
15. `site:arxiv.org sunflower "4,3" "66"`
16. `site:aixiv.online sunflower "67"`
17. `site:aixiv.online sunflower "66"`
18. `site:arxiv.org sunflower "4,3" "65"`
19. `site:arxiv.org sunflower "4,3" "64"`
20. `site:aixiv.online sunflower "65"`
21. `site:aixiv.online sunflower "64"`
22. `site:arxiv.org sunflower "4,3" "54"`
23. `site:aixiv.online sunflower "54"`
24. `"three-sunflower-free" "68" "threshold"`
25. `"sunflower" "forcing threshold" "68"`
26. `"2609.06175v2"`
27. `"Babanskyy" "sunflower" correction`
28. `"Axante" "sunflower" correction`
29. `"four-uniform" "sunflower" upper bound` (recency=30 days)
30. `"sunflower-free" "upper bound" "67"`
31. `"sunflower-free" "upper bound" "66"`
32. `"sunflower-free" "upper bound" "65"`
33. `"sunflower-free" "upper bound" "64"`
34. `"sunflower-free" "upper bound" "54"`
35. `"four-element" "sunflower" "at least 68"`
36. `"Babanskyy" sunflower "67"`
37. `"Axante" sunflower revision erratum`

## Actual GitHub search queries

1. github.search_repositories: `sunflower`; topn/per_page=100, page=1.
2. github.search: `sunflower 67`; topn/per_page=30, page=default.
3. github.search: `sunflower 66`; topn/per_page=30, page=default.
4. github.search: `sunflower 65`; topn/per_page=30, page=default.
5. github.search: `sunflower 64`; topn/per_page=30, page=default.
6. github.search_repositories: `sunflower-free`; topn/per_page=100, page=1.
7. github.search_repositories: `sunflower uniform`; topn/per_page=100, page=1.
8. github.search_repositories: `sunflower bound`; topn/per_page=100, page=1.
9. github.search: `"M(4,3)"`; topn/per_page=100, page=default.
10. github.search: `"f(4,3)"`; topn/per_page=100, page=default.
11. github.search: `"three-sunflower-free"`; topn/per_page=100, page=default.
12. github.search: `sunflower "M(4,3)"`; topn/per_page=100, page=default.

The raw files also contain every direct primary open, text find, observed-link click, repository fetch, and its returned output.

