# Fresh general-sunflower search, 24 October 2026

Scope: primary-source literature discovery through 24 October 2026, including versions, corrections and public formalization availability for Bucić–He–Lee. This is a search record, not mathematical proof checking, a local Lean replay, or a final review. Rank-four literature and the separate archive search are owned by the parent task. No proof or solver job was run for this refresh.

## Bucić–He–Lee: version and scope

[The arXiv record](https://arxiv.org/abs/2610.26686) lists only v1, submitted 19 October 2026 at 16:32:32 UTC. No v2, withdrawal or correction notice was displayed. Targeted correction/erratum searches found no relevant primary correction; that is a bounded search finding, not a guarantee that none exists.

[The paper](https://arxiv.org/html/2610.26686v1), Theorem 1, gives

\[
|\mathcal F|\le 3\left(2-\frac1{16k^3}\right)^n
\]

for a family in \(2^{[n]}\) without a \(k\)-sunflower, \(k\ge3,n\ge1\). The factor 3 is outside the power. This is the fixed-ground-set Erdős–Szemerédi problem. It does not give an ambient-independent exponential bound for arbitrary uniform families. The paper's AI statement reports Lean 4.35 verification and says release via Palomar is forthcoming. That release wording predates the registry discovery below.

## Public formalization discovered in this refresh

The primary [Palomar recent-results JSON](https://data.palomar-registry.org/recent.json), around its entry beginning at the rendered line 2582, lists:

- ID `PALOMAR-2026-10-22-000016`, version 1; status `registered`.
- Publication timestamp `2026-10-22T08:04:03Z`.
- Source `mbucic4/erdos-szemeredi-sunflowers`, commit `8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7`.
- Declarations `ErdosSzemeredi.vector_bound`, `ErdosSzemeredi.set_bound`, `ErdosSzemeredi.sunflower_conjecture`.
- Preserved repository `PalomarArchive/mbucic4--erdos-szemeredi-sunflowers--2a579c35c2b2`.

The [public source repository](https://github.com/mbucic4/erdos-szemeredi-sunflowers) was accessible. Declaration scope and reported verification limitations are recorded in `general.md`. This session performed no local statement check or replay.

The [versioned human record](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000016&version=1), exact JSON record, version-history endpoint and pinned GitHub tree failed to load through the web tool. The registry API search also failed. The root repository loaded, but individual Challenge and Issues links failed. No failed URL was retried. Accordingly, detailed registry mechanical-report claims cannot be established from this session. The accessible listing supports registration, version and commit metadata.

## General uniform bounds and recent directions

| Primary source | Result and scope found in this refresh |
| --- | --- |
| Bell–Chueluecha–Warnke, [Note on Sunflowers](https://arxiv.org/abs/2009.09327), v2 18 March 2021 | For distinct sets of uniformity \(\ell\), a threshold of the form \((Cr\log\ell)^\ell\) forces an \(r\)-sunflower. This refines Rao's \(O(r\log(r\ell))\) base. The bounded-VC preprint below still identifies this as the best general estimate. For small \(\ell\), use the usual adjusted logarithm convention rather than literally setting \(\log1=0\). |
| Ge–Wang–Xu–Zhao, [Bounded VC-dimension implies the Erdős–Rado sunflower conjecture](https://arxiv.org/html/2609.18995v1) | Theorem 1.1 states that an \(\ell\)-uniform family of VC-dimension at most \(d\) with more than \((50dr)^\ell\) members contains an \(r\)-sunflower. For \(\ell\)-bounded families it gives \(\sum_{j=0}^{\ell}(50dr)^j<2(50dr)^\ell\). This is an additional fixed-VC hypothesis, not the unrestricted conjecture. |
| Cavalar–Fabris–Mukhopadhyay–Srinivasan–Yehudayoff, [Derandomized Sunflowers and Radical Lower Bounds](https://eccc.weizmann.ac.il/report/2026/220/), 28 September 2026 | Derandomizes robust sunflower lemmas to \(O(w)\)-wise independence, also allowing certain locally independent, approximately identically distributed marginals; gives circuit lower-bound applications. It does not state an improved unrestricted uniform-family cardinality threshold. |
| Axante–Budala–Chitic–Dumitru–Nacu, [Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds](https://arxiv.org/abs/2609.06175), 5 September 2026 | Recursive constructions give a general lower bound on exponential growth; the paper also gives a general upper bound in uniformity three with at least four petals. Its small-rank bounds are referred to the parent's rank-four search. |
| Karingula–Lovett, [Limitations of the slice rank method in additive combinatorics](https://arxiv.org/abs/2609.27044), 22 September 2026; [ECCC TR26-205](https://eccc.weizmann.ac.il/report/2026/205/) | For at least four petals, exact-support tensors for the set-sunflower relation have maximal slice rank, with a related distinct-input obstruction. This constrains that method; it is not a counterexample to a sunflower bound. Bucić–He–Lee explicitly distinguish their vector tester from this set-relation obstruction. |

The [bounded-VC arXiv abstract record](https://arxiv.org/abs/2609.18995) displays v1 submitted 17 July 2026, despite the `2609` identifier; the full HTML also displays July. Preserve that observed metadata discrepancy rather than silently assigning a September submission date. This search did not establish its cause.

The primary sources located still leave the unrestricted Erdős–Rado uniform conjecture open. No later improvement of the general \((Cr\log\ell)^\ell\) upper-bound form was located by the recorded searches through the cutoff. This is a literature-search conclusion, not an exhaustive database theorem.

## Search limitations and cache discrepancies

- Searches and direct opens worked; the earlier usage-limit failure did not recur.
- Several individual endpoints returned inaccessible/cache-miss errors, as itemized above.
- An ECOPRO search snippet displayed an October 23 update, but the opened institutional page was an older June listing. It was not used to infer a manuscript revision.
- Secondary sites included both stale release-status claims and an incorrect alternative formula for Theorem 1. The displayed theorem above comes from the primary manuscript; formal-release status comes from the primary registry and public repository.
- No software from the new repository was downloaded, installed, imported or executed. No new proof review was performed.

Queries, consulted URLs and endpoint failures are recorded separately in `general-search-log.json`.
