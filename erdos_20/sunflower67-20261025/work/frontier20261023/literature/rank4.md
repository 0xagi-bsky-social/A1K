# Rank-four sunflower literature refresh — 23 October 2026

Research note only. This search applies the evidence and assurance rules of
`superresearch-x2` and `supermath-x2`; it starts no new proof work, final
review round or final report. Earlier files and receipts were not edited.

**Cutoff:** 2026-10-23, America/New_York. The live clock read
2026-10-23 11:18:47 UTC (07:18:47 EDT) during this search. This is a
morning snapshot, not coverage of future publications later that day.

**Result:** the strongest directly comparable numerical claim found and
verified *as a primary-source claim* remains
`54 ≤ M(4,3) ≤ 68`. No eligible source with upper bound below 68, lower
bound above 54, correction overturning the bound, or newer version of the
two principal papers was retrieved. This is a bounded-search finding,
not a guarantee of global completeness, novelty, priority, or mathematical validity.

## Scope and conventions

The target is the maximum cardinality of a finite simple family of sets
of **exactly four elements**, forbidding three **distinct** members with
equal pairwise intersections, including the empty intersection. The
forcing threshold is one greater than this maximum. “Rank four” here
does not mean a mixed family of sets of cardinality at most four.

Searches covered primary arXiv and aiXiv records, the author-linked GitHub
repositories, author homepages, indexed publication/correction searches,
and additional GitHub repositories returned by broader sunflower searches.
The route was prospectively set by the parent task and then extended to
new GitHub leads found during searching. Search-engine mirrors and
AI-result trackers were discovery leads only. Their labels and assertions
were not used to establish a theorem or verification status.

## Verified source status

| Primary source | Version/status observed | Directly relevant claim and limitation |
|---|---|---|
| Oleksiy Babanskyy, *An upper bound for three-sunflower-free families of four-element sets*, [aiXiv record](https://aixiv.online/abs/2610.01292), [versioned text](https://aixiv.online/html/2610.01292v1) | Only v1 displayed; submitted 2026-10-09 10:55:39 UTC. No withdrawal/correction notice observed. | Reports 54 ≤ M(4,3) ≤ 68, with exactly the convention above. Theorem 1.1 explicitly invokes H27 and its classification/finite-exclusion lemmas. |
| [Babanskyy companion](https://github.com/aconsciousfractal/Four-Uniform-Three-Sunflower-Bound) | Latest returned commit `90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`, 2026-10-08 23:25:44 UTC; same as the old foundation. Repository issue query returned an empty list. | README still states 68; finite replay is distinguished from verification of written reductions and external human reproduction. |
| Axante, Budala, Chitic, Dumitru and Nacu, *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*, [arXiv record](https://arxiv.org/abs/2609.06175), [v1 text](https://arxiv.org/html/2609.06175v1) | Only v1 displayed; submitted 2026-09-05 16:31:55 UTC. No journal-reference or correction notice displayed. | Proposition 6.7 reports intersecting maximum ≤27 using 11,720 canonical-augmentation roots; Proposition 6.8 gives equality. Theorem 6.9 reports 54 ≤ f(4,3) ≤ 83. |
| [Axante author-linked repository](https://github.com/bogdan27182/sunflower-paper) | Latest returned commit `d4d5723267c662291efdadfa6e7061d919e76fa9`, 2026-09-05 08:11:54 UTC, followed by two earlier commits that day. Issue query returned an empty list. | No later returned commit. The pinned [Lean README](https://github.com/bogdan27182/sunflower-paper/blob/d4d5723267c662291efdadfa6e7061d919e76fa9/lean/README.md) lists the rank-four lower-bound witnesses; its scope excludes the finite enumerations behind the global upper bounds. |
| [Babanskyy homepage](https://www.oleksiybabanskyy.com/) | Opened directly; indexed sunflower entry E20-R4 v0.2.0 also retrieved. | Still advertises 54–68. The direct extracted homepage omitted dynamically displayed work cards; the card was visible in the search representation. |
| [Bogdan Dumitru's university homepage](https://cs.unibuc.ro/~bdumitru/) | Direct text opened; page states last updated 2026-09-27. | Still lists the 54–83 paper and intersecting extremum 27. No follow-up rank-four manuscript listed in the returned text. |

The September 5 submission timestamp is from the primary arXiv record;
some search mirrors display September 9 as an announcement/index date.
Those dates are not interchangeable.

## Assurance boundary

This run reread primary theorem statements and source/version metadata;
it did not execute a checker, rebuild Lean, audit all written arguments,
rerun H27, or independently reproduce a global upper bound. No new
`elaborated`, `axiom-audited`, `clean-kernel-replayed`, or
`independently-reproduced` receipt is claimed.

The aiXiv author disclosure reports all 42 companion suites run normally
and with Python optimization, while explicitly excluding independent
specialist endorsement and an end-to-end formal proof. Its reproduction
panel currently says no reports. This is author-side reported evidence,
not verification performed by this refresh.

The existing local [foundation ledger](../../frontier20261020/prior-art68/FOUNDATION_LEDGER.md)
separately records six of 42 suites replayed in the October 20 work, with
external H27, Jin and the full written coverage chain still outside that
local replay. Those old checks are retained with their old scope.
The new search neither strengthens nor invalidates them.

Thus 68 remains the appropriate **reported numerical frontier** for a
proposed improvement in this exact finite problem. A genuine bound at
most 67 would need its own full argument; an assumption of H27 must remain
visible unless separately discharged. The local cap 61 for a complete
R16 point-link is conditional on that structure and is not a global
replacement for 68.

## New adjacent leads, excluded from rank-four comparison

The broader GitHub search found fresh primary repositories for
Erdős–Szemerédi **ground-set capacity** lower bounds. Their parameter
counts ambient points, and their base families are not exactly
four-uniform. They do not improve the lower endpoint 54 here.

| Source retrieved | Source-reported bound | Screening decision |
|---|---|---|
| [Aspect5/sunflower-free-capacity](https://github.com/Aspect5/sunflower-free-capacity) README, blob `34b305b7f121ee9b7503378823cd0fc22583d067` | v1.2, 2026-10-17: μ₃ ≥ 1.56477309608283… | Relevant to adjacent capacity problem; no computation run here. |
| [joshua17-create/sunflower-lower-bound](https://github.com/joshua17-create/sunflower-lower-bound) README, blob `8be7da1b309ab2c5c448eb43335a6cdc719379d4` | μ₃ ≥ (1042 + 2√261207)^(1/17) = 1.5666969787… | Uses 75-set and 121-set mixed-size families. Not a rank-four lower-bound witness. |
| [xSyllaa/sunflower-pendant-chain](https://github.com/xSyllaa/sunflower-pendant-chain) README, blob `2dbddf5f267d094caf02492e26d13f1754d303cf` | v2, 2026-10-20: μ₃ ≥ (1127 + √925536)^(1/17) = 1.5678015201… | Newer adjacent lead forwarded to the parent. Source discloses no peer review or human mathematician check; only README claims inspected here. |
| [Four-Petal-Sunflower-Free-Triple-Extremal-Threshold](https://github.com/jfairfaxball-348/Four-Petal-Sunflower-Free-Triple-Extremal-Threshold) README | Work dated 2026-10-14 on f(3,4); explicitly says no stronger bound established. | Different uniformity/petal pair; excluded. |
| [DR-16/sunflower-seeds](https://github.com/DR-16/sunflower-seeds) code-search excerpts | Ai Weiwei art-installation web page. | Unrelated homonym. |
| [Frankl-complete four-set lead](https://github.com/michaeliu4/frankl-complete-four-sets) repository-search result | A different union-closed/Frankl-completeness question. | Not used; no full source proof audit in this scan. |

The parent independently assigned the October 19 arXiv:2610.26686
Erdős–Szemerédi conjecture paper to another agent. This note makes no
new assessment of it and does not conflate that statement with the
fixed-uniformity Erdős–Rado conjecture.

## Actual searches and outcomes

All web queries below were executed on 2026-10-23. They returned the two
principal papers, their mirrors and author listings, adjacent work, and
many irrelevant sunflower/name/number matches. No eligible improvement or
correction was retrieved. The raw results preserve those unwanted hits;
zero eligible hits must not be read as zero search-engine hits.

1. `"Babanskyy" "sunflower" "68"`
2. `"2610.01292" sunflower`
3. `"Axante" "2609.06175"`
4. `"M(4,3)" sunflower 2026`
5. `"sunflower" "four-element" bound 2026 67`
6. `"sunflower" "4-uniform" "68"`
7. `"sunflower" "f(4,3)" "54"`
8. `"sunflower" "M(4,3)" "55"`
9. `site:arxiv.org sunflower "four" "2026"`
10. `site:aixiv.online sunflower bound`
11. `"An upper bound for three-sunflower-free" correction OR erratum OR revision`
12. `"Sunflower-Free Uniform Families" correction OR erratum OR v2`
13. `"sunflower-free" "four" "67"`
14. `"sunflower-free" "four" "55"`
15. `"sunflower-free" "4-uniform" bound 2026 October`
16. `"2609.06175" github`
17. `"three-sunflower" "four-element" -site:vibemathed.com -site:erdosproblems.ai`
18. `"f(4, 3)" "sunflower" 2026`
19. `"M(4, 3)" "sunflower" 2026`
20. `"Babanskyy" "sunflower" correction`
21. `"sunflower-free families" "54" "2026" -site:a1k.ai -site:vibemathed.com -site:erdosproblems.ai`
22. `"sunflower-free" "54" "improved" four`
23. `"f(4,3)" "67" sunflower`
24. `"four-uniform" sunflower new bound October 2026`
25. `"54" "sunflower" "four-element" -site:erdosproblems.ai -site:vibemathed.com -site:a1k.ai`
26. `"sunflower-free" "four-uniform" "bound" -site:erdosproblems.ai -site:vibemathed.com -site:a1k.ai -site:mathworld.wolfram.com`
27. `"2609.06175v2"`
28. `"Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds" journal publication`
29. `"An upper bound for three-sunflower-free families of four-element sets" journal publication`

GitHub operations used the connected GitHub tools:

- Repository search queries: `sunflower` (first 100 results),
  `sunflower combinatorics` (up to 50),
  `sunflower four` (up to 50), and `sunflower bound` (up to 30).
- For each main companion: `search_commits` with empty query,
  repository specified, `sort=committer-date`, `order=desc`, `topn=10`;
  `search_issues` with the exact `repo:owner/name`, updated ordering,
  and `topn=30`.
- Fetched each main root README; fetched Axante's pinned
  `lean/README.md`; fetched the four mathematical adjacent READMEs;
  screened the art repository with code search after its root README was absent.
- Directly opened the two paper records, both versioned HTML texts and
  the two author homepages. Used text-find for “github”, “6.7” and
  “Abbott” in Axante v1.

## Retrieval gaps and provenance

The [raw machine record](rank4.raw.json) saves the actual stored web and
connector responses, including returned snippets and errors. It has 29
actual web query strings. The first four-query response was displayed in
the live transcript but was not saved from the transient tool result;
its relevant primary sources were then reopened and captured. All
subsequent stored responses are preserved as returned, even where the
chat display truncated them.

The aiXiv machine JSON endpoint failed twice (cache miss, then not
accessible via this tool). The readable record and versioned HTML worked.
The DR-16 root README returned 404; its website open gave a cache miss;
code search then resolved it as irrelevant art. These are retrieval
limitations, not evidence of mathematical corrections.

Search-engine indexing and cached page text can lag; repository search
pagination was bounded; issue searches returned no results but cannot
certify absence of private discussions. No subscription MathSciNet or
zbMATH search, full citation graph, complete global repository census,
or unpublished-work access was performed. Exact-title publication
searches returned no new journal version, but no comprehensive
publication-status proof is possible from those searches.

The two source families must remain clustered: an author paper,
repository and homepage are related evidence, and repeated mirrors do
not provide independent mathematical corroboration.

