# Every sunflower-free family of fifteen triples has seven disjoint companions at some member

24 October 2026. Ordinary proof with small finite diagnostic reductions and
independently replayed finite proof trees. This is a research result under its
explicit proof-evidence boundary, not a Lean theorem or a priority claim.

## Literal mathematical target

For every finite simple three-uniform family L without a three-member sunflower,
including empty core, if |L|=15 then there is A in L with at least seven members
of L disjoint from A. Equivalently, no such L has rho(L)<=6.
The statement quantifies over arbitrary ambient support, with no chosen cutoff.

The ordinary/finite reduction in R15-rho6-degree2-support-reduction.md shows
that a hypothetical counterexample has minimum used degree at least3 and
support at most11. Its degree2 exclusions are exact small diagnostics with
arbitrary-support normalization; they are explicit prerequisites of this
assembly and are undergoing a separate reconstruction. They have not been
replaced by a project axiom or called a Lean result.

Maximum degree is5 or6. A complete degree6 point-link is two disjoint triangles.
If there is no degree6 point, a degree5 point-link is C5 or a triangle plus a
two-edge path. These are the three SF2 possibilities from maximum matching
number2 and maximum degree2. Pad unused points to11 and relabel the chosen
complete point-star to its literal canonical model. Every other triple avoids
the root, so the remaining candidate domain is exactly all120 triples of
the ten other points. For the last two branches the global degree cap is5;
the first branch permits6. The target remains15 in every branch.

## Fresh exact producer and independent replay

search_r15_rho6.py constructs a proof tree by bounded search using integer
bit masks. Each candidate rejection is a degree bound, a disjoint-count bound,
or a sunflower with actual selected members. A colour class consists of
mutually incompatible candidates: each pair, together with a selected actual
member, is a sunflower. Consequently a valid extension uses at most one
candidate per class. Increasing selection through the reverse colour order
partitions all extensions by their last chosen candidate; the omitted prefix
contains fewer classes than required remaining members.

replay_r15_rho6_tree.py imports no producer code, heuristics or bit-mask
sunflower test. It independently constructs literal finite sets, checks equal
pairwise intersections, recovers every candidate, rejects changed scope or
seed, checks all colour pairs and every child/prefix coverage, and recomputes
all degree and disjointness restrictions. It rejects solutions, incomplete
trees, reused/cyclic children and orphan nodes.

| Complete root star | Global degree cap | Padded points | Tree nodes | Checked colour pairs | Solutions |
|---|---:|---:|---:|---:|---:|
|Two triangles|6|11|3657|101266|0|
|C5|5|11|5109|170054|0|
|Triangle plus two-edge path|5|11|3455|113537|0|

All three producer runs exhausted their complete domains, each below0.6 seconds.
All three separate replay runs returned PASS, each below0.6 seconds.
The three trees cover12221 nodes and384857 colour incompatibilities.
Wrong target16, deletion of a required child and a changed source commitment
were separately rejected in the two-triangle replay's negative controls.

Receipts are R15-rho6-two-triangles-replay.json, R15-rho6-cycle5-replay.json,
and R15-rho6-triangle-path-replay.json. The corresponding immutable compressed
trees have suffix -search.json.gz. The source hashes are:

- Producer: a4f14ee8e8e24bbe3c1a6f4b5af626f72aa29b1b622a47fcbb344fd920d9bed8.
- Independent replayer: 020a9c4c6bf3ee0c22771e87fbcf0fe850e87053fd5e87a06879d4d59f99c522.

The old R16 trees were not reused as size15 proofs. This is a fresh target15
search on the newly derived eleven-point domain, including the five-degree
branches at11 rather than the old16-member branches' ten-point domain.

## Consequence and remaining assurance boundary

The ordinary arbitrary-support reduction followed by these complete finite
exclusions proves the stated mathematical implication, conditional on the
correctness of the two small degree2 diagnostics and their ordinary bridges.
The three large proof-tree leaves have independent set-based replay; the
small degree2 leaves retain their separately stated evidence status until
the independent reconstruction is recorded. No part is asserted to be Lean
kernel verification, independent human certification or global novelty.

Combining with LOW15-R15-rho7-classification.md gives the useful size15
structure dichotomy under rho<=8: rho7 gives R16 minus one triple; rho8
gives the B4-separated I8+I7 branch. In the cap15 SF4 research problem both
complete R15 deletion types are excluded by separate ordinary hub-incidence
arguments. The 8+7 graph-cover branch is being composed separately. This
file alone is not a global M(4,3)<=67 theorem and does not open final review.
