# General sunflower literature: 24 October refresh

The fresh search located a public formalization release for Bucić–He–Lee. The primary [Palomar listing](https://data.palomar-registry.org/recent.json) records `PALOMAR-2026-10-22-000016` v1, published `2026-10-22T08:04:03Z`, source commit `8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7` of `mbucic4/erdos-szemeredi-sunflowers`. The [repository](https://github.com/mbucic4/erdos-szemeredi-sunflowers) is public. Earlier claims that no public artifact had been located are now outdated.

The [arXiv record](https://arxiv.org/abs/2610.26686) still displays only v1, 19 October 2026. No primary correction or erratum was found in the recorded searches. The theorem concerns subsets of an n-element ground set; it does not resolve the unrestricted uniform Erdős–Rado conjecture.

Full scope, queries, consulted literature and cache limitations are in [general-sunflower-refresh.md](general-sunflower-refresh.md) and [general-search-log.json](general-search-log.json). They include the recent bounded-VC theorem `(50dr)^ell`, robust-sunflower derandomization, recursive constructions and the set-relation slice-rank obstruction. The best unrestricted uniform upper-bound form located remains `(Cr log ell)^ell`.

## Exact scope reported by the public repository

This table records the accessible README's descriptions, not a fresh inspection of Lean theorem headers.

| Declaration | Reported scope |
| --- | --- |
| `ErdosSzemeredi.vector_bound` | `k >= 3`, `D >= 1`, `n >= 0`; vector-sunflower-free `V` in `[D]^n` has size at most `((2k)^(2/(k-1)) D^(1-1/(k-1)))^n`. |
| `ErdosSzemeredi.set_bound` | `k >= 3`, `N >= 1`; sunflower-free `F` in `2^[N]` has size at most `3(2-1/(16k^3))^N`. |
| `ErdosSzemeredi.sunflower_conjecture` | For every `k >= 3` there exists `c_k` in `(0,2)` working for every `N >= k-1` and every qualifying family: `|F| <= c_k^N`. |

The README reports distinct members, standard sunflower definitions, Lean `4.35.0-rc2`, and only `propext`, `Classical.choice`, `Quot.sound`. It reports successful direct leanchecker/NanoDa/con-ron checks. Challenge holes are deliberate; Solution is reported hole-free. It excludes applications and literature-priority assertions from its formalization. Historical Comparator failure/preparation wording remains; the attachment was not byte-compared with the public PDF. [Source](https://github.com/mbucic4/erdos-szemeredi-sunflowers).

## Evidence boundary

The registry listing establishes that registration was publicly listed at this refresh. It does not establish that this session replayed any kernel. Individual registry records, the pinned GitHub tree, and direct pinned `Challenge.lean`, `Solution.lean`, `verification/axioms.log`, `comparator.json` URLs failed through the web tool. Consequently no exact source-header or axiom-log inspection is claimed. No compilation, import, proof development, final review, or software execution occurred.

Four additional source-text attempts, each returning `Cache miss` without retry:

1. `https://raw.githubusercontent.com/mbucic4/erdos-szemeredi-sunflowers/8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7/Challenge.lean`
2. `https://raw.githubusercontent.com/mbucic4/erdos-szemeredi-sunflowers/8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7/Solution.lean`
3. `https://raw.githubusercontent.com/mbucic4/erdos-szemeredi-sunflowers/8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7/verification/axioms.log`
4. `https://raw.githubusercontent.com/mbucic4/erdos-szemeredi-sunflowers/8b5dc7ba9fa9e64faad39a0ab5badf74cc89f8b7/comparator.json`

The text and JSON saved here are observations and bibliographic metadata transcribed from web-tool responses, not byte-preserved upstream files. Raw source payloads were unavailable. The earlier tool usage-limit problem did not recur; individual fetch failures are itemized instead.
