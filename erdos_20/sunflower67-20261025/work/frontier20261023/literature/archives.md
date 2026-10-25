# Additional-repository sunflower literature refresh

Research cutoff: **2026-10-23, America/New_York**. Retrieval session: 2026-10-23; clock observation near completion: 11:20:05 UTC (07:20:05 EDT). Investigator: subagent `/root/refresh_archives`.

This is a bounded source refresh for the parent frontier freeze, not a publication or final scholarly review. The user explicitly postponed final reviews/publication until a frontier breakthrough. SuperResearch X2 source-routing and evidence distinctions and SuperMath X2 assurance distinctions were followed. No new proof-development branch, formal verification, final-review agent, or publication was started.

## Finding relevant to the frontier

**This sweep found no primary source establishing a rank-four, three-petal upper bound below 68.** That is a search outcome, not a claim of exhaustive absence or a proof that 68 is correct. The arXiv/aiXiv assessment and the October 19 Erdős–Szemerédi paper belong to other assignees. General web searches rediscovered the announced 68 bound and the older 83 bound, without locating a stronger eligible primary result.

Two recent ECCC papers add material methodological context. Neither directly settles the rank-four three-petal extremal problem. A third ECCC paper gives an exact extremal result for a different, weaker forbidden configuration.

## Primary findings

### A-01. Derandomized robust sunflowers

Bruno Pasqualotto Cavalar, Théo Fabris, Partha Mukhopadhyay, Srikanth Srinivasan, Amir Yehudayoff, *Derandomized Sunflowers and Radical Lower Bounds*. ECCC TR26-220; report timestamp September 28, 2026, 17:29; publication timestamp 18:10. [Record](https://eccc.weizmann.ac.il/report/2026/220/); [46-page PDF](https://eccc.weizmann.ac.il/report/2026/220/download).

The primary abstract reports a robust-sunflower derandomization using independence linear in DNF width, replacing a quadratic independence requirement in the earlier DNF-fooling route. The result extends to locally independent, approximately identical marginals. The PDF's Theorem 1.1 (printed p. 2, PDF page 4) gives independence parameter $k=O(w\log(1/\delta))$ and tolerance $\varepsilon=\Omega(1/w)$, for a width-$w$ monotone DNF above its stated size threshold. Definition 2.10 and Corollary 2.11 (printed pp. 19–20) specify the distributional sunflower and precise parameter regime. The proof uses moments; the application separates small arithmetic circuits from powers requiring large monotone circuits. **Disposition:** relevant new structural/methodological literature, no advertised numerical improvement for $f(4,3)$. This refresh inspected statements and scope, not the complete proof or computational reproducibility.

### A-02. A faithful-support slice-rank obstruction

Sankeerth Rao Karingula and Shachar Lovett, *Limitations of the slice rank method in additive combinatorics*. ECCC TR26-205; September 22, 2026, 22:23. [Record](https://eccc.weizmann.ac.il/report/2026/205/); [11-page PDF](https://eccc.weizmann.ac.il/report/2026/205/download).

PDF Theorem 1 (printed p. 3) states that for every field and $k\ge4$, every tensor faithfully realizing the complete $k$-sunflower relation on $(\{0,1\}^n)^k$ has slice rank $2^n$. Corollary 2 gives a lower bound $2^{n-k}$ when the support equivalence is imposed only on pairwise distinct inputs, for $n\ge k$. The word “faithfully” imposes both directions of the nonzero/support equivalence. It does not cover every conceivable reduction, restricted family, or tensor allowed to vanish on some valid relation tuples. Here $k$ counts petals, not set size. **Disposition:** relevant limitation to record beside later polynomial-method developments; no contradiction with every alternative method and no rank-four three-petal bound. Statements source-inspected only; no Lean assurance claimed.

### A-03. Exact moonflower extremal bound

Shachar Lovett, Raghu Meka, Yimeng Wang, ECCC TR26-069. Initial record May 9, 2026; revision 1 July 20, 2026. The record title is *Moonflowers and efficient code sparsification*; the revision PDF title is *Moonflowers and code sparsification*. [Record](https://eccc.weizmann.ac.il/report/2026/069/); [revision 1 PDF](https://eccc.weizmann.ac.il/report/2026/069/revision/1/download).

A moonflower requires each member to have an element absent from all other members. Revision Theorem 1.4 and Lemma 1.5 (printed p. 2) give the exact maximum $\binom{k+w-1}{w}$ for $k$-moonflower-free families of sets of size at most $w$. The revision also develops universe reduction and code-sparsification applications. A moonflower need not be a sunflower, as the paper explains, so excluding three sunflowers cannot be silently replaced by excluding three moonflowers. **Disposition:** useful adjacent extremal structure; does not yield the desired rank-four improvement directly. Statement and definition inspected; proof not audited.

### A-04. Institutional repository: temperate families

Jan Petr and Pavel Turek, *Towards odd-sunflowers: Temperate families and lightnings*, Journal of Combinatorial Theory, Series A 220 (2026), 106133, DOI [10.1016/j.jcta.2025.106133](https://doi.org/10.1016/j.jcta.2025.106133). [Cambridge repository PDF](https://api.repository.cam.ac.uk/server/api/core/bitstreams/06054773-c3d2-40ad-a3be-20daf1900374/content).

The accessible published PDF records acceptance November 17, 2025. It studies temperate families motivated by odd-sunflowers and identifies the maximum-size families using consecutive middle layers; Theorems 1.3–1.6 include extremal classification and an intersecting odd-ground-set case. **Disposition:** adjacent variant, not a new October 2026 rank-four three-petal improvement. Its historical “state of art” wording predates the current cutoff and is not evidence for the current frontier.

## Screened or incomplete leads

### A-05. viXra: rejected as frontier evidence

Cody Shane Mitchell, *Exact Values and Proven Slack in the Erdős–Szemerédi Sunflower Problem: A Comprehensive Analysis with Directions for Future Research*, January 14, 2026; ai.viXra 2601.0054v1. [Accessible PDF](https://www.ai.vixra.org/pdf/2601.0054v1.pdf). The abstract landing URL failed, but the 12-page PDF was readable.

There is an immediate source-level defect: Example 5.1 (printed p. 5) calls a family containing $\{1\},\{2\},\{3\},\{4\}$ sunflower-free. Any three displayed singleton members have the same pairwise intersection, the empty set, under Definition 1.1. The computational domain in §2.1 also excludes the empty set although Definition 1.2 is phrased over all subsets. The paper's tensor is a NOT-sunflower tensor (§4.1), which cannot be identified with another paper's sunflower-support tensor without a bridge. **Disposition:** excluded as support for a frontier change; this is a screening counterexample to a displayed source claim, not a new extremal theorem.

### A-06. SSRN: primary records indexed, direct retrieval denied

Search results from SSRN itself identified:

- Soumi Nandi, Chandrima Kayal, Smiha Samanta, *Sunflower lemma for polynomials over finite fields*, posted July 14, 2026, nine pages, [SSRN 7118656](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7118656). The indexed abstract concerns a polynomial-ring analogue.
- Zijian Zeng, *The Exact Value of a Pairwise-GCD Sunflower-Free Function At 126*, written August 19, posted September 5, 2026, [SSRN 7395458](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7395458). The indexed abstract claims a finite arithmetic value, with a DRAT certificate, not the rank-four set-family maximum.

Both direct abstract-page fetches returned **403 Forbidden**. They remain primary-index metadata/abstract leads, without full-paper verification or certificate replay.

### A-07. Zenodo leads: not promoted from aggregators

Secondary discovery identified *Frankl-complete sunflowers and extremal families of four-sets* (Liu Mingchang; DOI 10.5281/zenodo.22702735) and *On the Erdős-Rado Sunflower Conjecture* (Charles EDOU NZE; DOI records 21992249/21992250). Direct Zenodo records and the first DOI failed through this tool. The former concerns Frankl-completeness and union-closed extensions, a different property; the latter is described as a survey/formalization of classical bounds. No mathematical claim from these unavailable primaries is admitted to the frontier. Their appearance on multiple aggregators does not provide independent corroboration.

## Repository coverage and limits

| Source route | Actual result and limit |
|---|---|
| ECCC | 2026 year index and targeted search; primary records/PDFs for TR26-220, TR26-205, and TR26-069 revision 1. No sub-68 rank-four result located. |
| HAL | Exact phrase search returned no match; broader search returned largely author CV pages. HAL API and direct search-page retrieval were inaccessible. This is incomplete coverage, not proof of zero relevant records. |
| Zenodo | Exact mathematical queries returned mostly irrelevant botanical records; two relevant titles emerged through wider discovery. API and targeted primary records were inaccessible. |
| OSF/Preprints | Domain query returned no results; direct OSF discovery page was inaccessible. |
| Preprints.org | Hits concerned biological sunflowers, phyllotactic Goldbach visualizations, or use of the classical lemma in a P-versus-NP claim. None supplied a rank-four numerical improvement; the unrelated P-versus-NP claim was not evaluated. |
| Research Square | Domain-constrained sunflower-conjecture search returned no results. |
| SSRN | Two mathematical variant leads; direct retrieval returned 403. |
| viXra/ai.viXra | One relevant 2026 PDF inspected and rejected as frontier evidence for the explicit defect above. |
| TechRxiv | Domain-constrained sunflower-conjecture query returned no results. |
| MathOA | Dedicated sunflower query returned no results. |
| Institutional repositories/pages | Cambridge published PDF inspected; University of Bucharest author page surfaced the existing 83-bound work. Targeted search also included Cambridge, LSE, UWA, ISTA, and Penn; LSE reported robots.txt denial. No universal institutional coverage claimed. |
| General rank-four cross-check | Queries included “68”, “67”, “rank-4”, “rank four”, “four-element”, “4-uniform”, and “f(4,3)”. They rediscovered known announcements and secondary trackers, not an eligible stronger primary theorem. |

The search engine sometimes returned loose lexical matches despite quotation marks and domain restrictions. Irrelevant botanical and retail hits were excluded. “No results” means that actual query returned no results through the available tool, not that the repository contains no relevant work. Search caches, incomplete indexing, inaccessible endpoints, unpublished work, and unseen revisions remain limits.

See `archives_evidence_log.jsonl` for the actual queries/retrieval requests, discovered source URLs, and tool-locator IDs. The log preserves request provenance and screening status without claiming raw-byte downloads or exhaustive search. No independent scholarly review, proof validation, or originality certification is claimed.

