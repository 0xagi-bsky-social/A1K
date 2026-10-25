# Priority foundation: reported upper bound 68

Research record, 20 October 2026. This is not a final report or an approved
publication. All further final-review rounds were stopped by the user.

## Source and evidence

The source is Oleksiy Babanskyy's *An upper bound for three-sunflower-free
families of four-element sets*, aiXiv 2610.01292v1:
[record](https://aixiv.online/abs/2610.01292),
[repository](https://github.com/aconsciousfractal/Four-Uniform-Three-Sunflower-Bound).
The local repository is pinned to commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c` and remains unmodified.

The paper reports 54 ≤ M(4,3) ≤ 68. Its M is the maximum size of a finite
simple exactly four-uniform family without a three-sunflower; empty cores
are included. Thus its upper bound is directly comparable with ours.

The reported theorem uses external H27, Jin's strict graph homomorphism
theorem, written arbitrary-support reductions, and 42 finite suites.
It is not an end-to-end Lean proof. We have not established the validity
of every part of that external chain.

| Evidence layer | Actual local status |
|---|---|
| Theorem statement, definitions, dependency architecture | Read from pinned primary source |
| Computational input integrity | 1,692 input files match the declared manifest before and after the selected replay |
| Quick suites: `terminal.f69_bridge`, `terminal.primary` | Both replayed normally and with `-O`, exact expected outputs matched |
| Additional suites: `terminal.cross15`, `terminal.crowding`, `terminal.cap61`, `terminal.r16` | All four replayed normally and with `-O`, exact expected outputs matched |
| Entire 42-suite companion | Not replayed; 6 suites and 12 executions completed |
| External H27 and Jin | Not re-proved or replayed here |
| Entire written reduction chain | Not formalized or independently certified here |

Normal and optimized execution of the same checker does not constitute
independence of mathematical assumptions. The receipts bind the actual
commands and outputs:

- `replay-quick-20261020/WRAPPER_RECEIPT.json`
- `replay-quick-20261020/receipts/RECEIPT.json`
- `replay-selected-20261020/RECEIPT.json`

The computational manifest SHA256 is
`ecc54817e8e81242a59ef6b033e74e472d3ffbb3e80f9f0d9f0e8264acf40b18`.

## What can be carried toward exclusion of 68

For every actual member R, its disjoint subfamily is intersecting. H27
therefore gives |N[R]| ≥ |F|−27. Excluding 68 members requires work at
μ≥41, while the paper's nine preliminary blocks are stated at μ≥42.
Their old finite exclusions cannot be reused merely by changing a number.

Some later components already have the weaker hypothesis:

| Prior component | Guard relevant at 68 | Role |
|---|---|---|
| Universal triple-link classification and point/pair/triple caps | Actual sunflower-free families | Structural input, not restricted to 69 members |
| Crowding bound: top three exact singleton counts sum to at most 26 | μ≥41 and maximum point degree≤18 | Controls local degree and support inequalities |
| Companion minimum used degree≥7 and support≤23 at size68 | Same guards, with the stated rooted-signature arguments | A useful prior reduction already present in the external companion |
| Complete R16 point-link implies total size≤61 | μ≥41 and maximum point degree≤18 | Terminal contradiction once such a complete link is forced |
| Original terminal fibre proof | Size69 and its preceding degree/singleton/neighbourhood reductions | Requires a new domain at68 |

The crowding companion's minimum-degree and support statements are prior
results, not claimed as discoveries of this continuation. Recovering and
checking their written bridges helps identify exactly what may be reused.

## New research obligations

1. **High-degree cases at μ41.** Exclude maximum degrees20 and19 without
   assuming the μ42 bootstrap. The crowding lemma with cap18 cannot be
   applied before those cases are discharged.
2. **Remaining upstream restrictions.** At μ41, establish the required
   degree17/18 and low-degree exclusions, singleton≤8, and upper closed
   meeting-neighbourhood bound44, or replace them with a different argument.
   The size69 low-degree graph contradiction does not automatically survive68.
3. **Terminal extension.** Under those still-unproved upstream conditions,
   minimum disjointness-graph degree24 permits Jin with k=6. The domain now
   includes Andrásfai graphs A3 through A6. New deletion and cover arguments
   must cover the added possibilities.
4. **Separate two-star route.** The candidate sharp bound45 for two
   noncooccurring degree20 points may remove an important high-degree
   subcase. Its census pattern and prospective ordinary proof require
   their own coverage argument and formal connection.

The target M(4,3)≤67 is unproved here. A conditional terminal extension,
an improved finite search domain, or successful execution of selected
checkers is not a global extremal breakthrough.

## Concrete continuation results

The terminal analysis now has a draft conditional extension to size68.
It assumes maximum point degree exactly16, all exact singleton counts≤8,
and all closed meeting neighbourhoods≤44, alongside H27 and the named
prior local inputs. Deleting 0,1,2,3 prescribed triples from a separated
8+8 link yields candidate actual-cover capacities 1,2,4,10. An explicit
arbitrary-exterior-point reduction and exact diagnostics cover 5,576 local
omission cases and 124,323 nonindependent star vectors, with no unresolved
vectors. This is not a kernel-checked result or an unconditional bound67.
See [the terminal research note](analysis/prior68-research.md).

The upstream analysis reconstructs the existing μ41/degree18 minimum7 and
support23 arguments. It also tests the weaker singleton-component domains:
8,473 P10 states and 3,012 P9 states remain in the k≤5 relaxation. These are
necessary numerical states, not actual sunflower-free families. Their
existence shows why a new shared-trace argument is needed.
See [the upstream research note](analysis/mu41/mu41-analysis.md).

Even the old high-degree numerical margins cannot be reused unchanged:

- In D20, size68 requires 48 residual members. The original internal
  certificate bounds residual mass by 9733/200 = 48.665, and one exterior
  certificate by 48003/1000 = 48.003. Neither excludes48, even if its old
  hypotheses were available.
- In D19, size68 requires49 residual members. Two original internal bounds
  are 61889/1250 = 49.5112 and 6236/125 = 49.888. These do not exclude49.
- By contrast, the geometric endgames retain slack: under their explicit
  geometric premises, D20 gives total≤65 and D19 gives total≤65
  (19 + floor(516/11)). The missing work is proving entry into those
  geometric regimes at μ41, not merely sharpening the last arithmetic step.

These observations use the written D20/D19 certificate values; their full
linear suites are among the 36 suites not replayed in this continuation.

The separate two-degree20-star route now has an ordinary-proof draft
explaining the earlier 22 positive geometries. Seven residual shapes reduce
to a common identical P10 component; the other components have either equal
supports or differ by one replaced point. A new local check covers P10
components on 19 positions and the final twelve-design tables. The proposed
residual caps are three in the equal-support case and five in the replacement
case. This remains a draft with imported premises and no Lean assembly:
[two-star research note](analysis/sharp45/sharp45-analysis.md).

## Existing A1K result and review boundary

The locally audited Lean implication I27 ⇒ G80 and its structural lemmas
remain valid with their existing dependency statements. They are retained
as formal progress, but 80 is no longer the numerical-frontier completion
criterion relative to the reported68 result.

Six final-review rounds and eleven submissions from the unfinished seventh
round were already recorded. Those historical records are preserved.
The remaining round7 submission, rounds8–10, final Chief/Alpha/Beta audits,
and three-format final publication are stopped. No final output directory
for this continuation has been created.
