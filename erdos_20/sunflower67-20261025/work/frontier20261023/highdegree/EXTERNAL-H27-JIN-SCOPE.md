# External H27 and Jin: source and scope check

24 October 2026. Ordinary source inspection before the final review gate.
The two statements match the conventions used in the current proof.
This note distinguishes imported theorems from local reproduction;
lack of Lean formalization does not make an ordinary theorem unproved.

## H27

The primary source is E. Axante, C. Budala, D. Chitic, B. Dumitru and
M. Nacu, *Sunflower-Free Uniform Families: Recursive Constructions and
Explicit Bounds*, arXiv:2609.06175v1, 5 September 2026.
[Versioned paper](https://arxiv.org/html/2609.06175v1).

Section2.1 defines finite families with distinct members, exact
w-uniformity, and sunflowers of distinct sets with equal pairwise
intersections, allowing an empty core. Proposition6.7 states the
intersecting four-uniform sunflower-free upper bound27. There is no
minimum-degree or preassigned-support hypothesis. Section6.3 reduces
the28-member target to support at most85, proves canonical-augmentation
coverage in Lemma6.6, and reports exhaustion of11720 depth-six roots
and105917089577 nodes. Proposition6.8 supplies equality; its lower
construction is unnecessary for our upper-bound use. Section8 separates
the exhaustive upper-bound computations from its Lean formalization.
[Definitions, Proposition6.7, and verification scope](https://arxiv.org/html/2609.06175v1).

The authors' supplement identifies the decisive H27 evidence as an
archived exhaustive-search ledger, rather than a compact proof
certificate. Its checker authenticates archives, reconstructs frontier
coverage, validates completed records and node accounting, and runs
small controls. This is not a fresh rerun of all historical search
nodes. [H27 artifact documentation](https://github.com/bogdan27182/sunflower-paper/tree/main/artifacts/f43_upper_83/intersecting_27).

Our project has **not** replayed that external ledger or the full
historical search. The appropriate description is “imported
computer-assisted theorem, with its stated computational dependency.”
It is not a locally open conjecture merely because its proof is not
in Lean. The inspected version is a preprint; no journal acceptance
was established in this check.

## Jin

The original citation is Guoping Jin, *Triangle-Free Graphs with High
Minimal Degrees*, **Combinatorics, Probability and Computing 2**(4)
(1993),479–490, DOI10.1017/S0963548300000845. The publisher confirms
these bibliographic details; its2008 online date does not replace
the1993 issue date. [Publisher record](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/trianglefree-graphs-with-high-minimal-degrees/CC3A9FD74582F981BEAD987E00667975).

The exact statement was checked in V. Nikiforov, *Chromatic number
and minimum degree of K_r-free graphs*, arXiv:1001.2070v1, Theorem A,
PDF page2: for1<=k<=9, a triangle-free graph of order n satisfying
delta(G)>(k+1)n/(3k+2) admits a homomorphism to A_k. The inequality
is strict, and no prior three-colourability hypothesis is required
in this range. The source attributes this theorem to Jin and defines
A_k as the complement of the(k-1)st power of C_(3k-1), with A1=K2.
[Theorem A and definition](https://arxiv.org/pdf/1001.2070v1).

The original article's full text was not accessible through the
publisher interface used here. Thus the precise theorem text was
verified through the explicitly named scholarly restatement, while
the original citation was checked at the publisher. This is not a
claim to have independently reconstructed Jin's proof.

## Application to the current conventions

These transfers are elementary deductions in the current proof. For
an actual member R, its disjoint subfamily D(R) is intersecting:
two disjoint members there, together with R, would form an empty-core
sunflower. D(R) remains simple, exactly four-uniform and sunflower-free,
so H27 gives |D(R)|<=27 and the closed meeting neighbourhood satisfies
N(R)>=|F|-27. At cardinality68 this is mu>=41.

The disjointness graph on the actual members is finite and simple.
It is triangle-free, and every independent set is an intersecting
SF4 subfamily, so its independence number is at most27. Once the
ordinary cap15 chain gives N(R)<=43, its minimum graph degree is
at least25. Jin applies directly with k=3 since25*11=275>4*68=272.
Its A3 has cyclic differences3,4,5, matching our fibre convention.
The theorem supplies a homomorphism, not a complete blowup or an
automatically surjective map; `LOW15-direct-Jin-A3-addon.md` separately
derives occupied fibres from the mass and independence bounds.

Local pinned sources inspected first were the prior paper at commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`, its foundation ledger,
and the20 October primary-source receipt. Fresh primary-source opens
on24 October confirmed the statements above. No external exhaustive
search was replayed, no solver or Lean build was run, and no frozen
artifact was modified.
