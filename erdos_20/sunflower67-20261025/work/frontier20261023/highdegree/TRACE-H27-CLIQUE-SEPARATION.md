# H27 cuts from forced intersections of full traces

This is an ordinary arbitrary-support lemma and a discovery procedure. It is
not an LP certificate, a classification of arbitrary intersecting families, a
Lean proof, or a final review. The only numerical theorem imported below is
H27: an intersecting simple SF4 family has at most 27 members.

## Exact prerequisites and proof

Let F be a finite simple family of four-sets with no three-member sunflower,
including one with empty core. Let R be any subfamily whose members avoid a
specified set X. Let U be a finite represented set disjoint from X. The
support of R outside U may be arbitrarily large. Write

    R_s = {A in R : A intersect U = s},  n_s = |R_s|,

for all traces s contained in U of size at most four. Let B be a collection
of **actual members of F**, each wholly contained in U union X. No claim
that B is a complete link is needed for this lemma.

Call two traces s,t compatible if they share a point, or if some B in the
fixed collection satisfies B intersect (s union t) = empty. The second
condition includes the fact that members of R avoid X. It would not be a
valid test if B had an unrepresented point outside U union X.

If s,t are compatible, any distinct A in R_s and C in R_t intersect. A
shared trace point proves this immediately. Otherwise choose the specified
B. Since B lies in U union X, it is disjoint from A and from C. If A,C
were also disjoint, the three distinct members A,C,B would be an empty-core
sunflower. They really are distinct: the nonempty four-set B cannot equal
a member disjoint from it. This is forbidden.

The same argument applies when s=t. A nonempty trace automatically passes
this diagonal test. The empty trace passes if any fixed actual B exists:
two distinct empty-trace members, together with B, would otherwise be
three disjoint members. In the intended root models every root cone is
such a witness. Without a fixed B, the empty class must be omitted from
the clique procedure; there is no automatic self-intersection statement.

Consequently, for any collection C of trace classes that passes the test
for every pair **including the diagonal**, the union of the R_s for s in
C is an intersecting simple SF4 family. H27 gives

    sum_{s in C} n_s <= 27.

The trace classes are disjoint, so there is no multiplicity error. A
selected actual residual marker may itself be counted in one class and
also serve as a witness for other pairs; this causes no subtraction or
double counting. The proof of each pair remains the preceding three-member
argument. No minimum degree, mu bound, finite exterior support, or
classification of I7 is used.

## Solver-free discovery and evidence

`trace_h27_cliques.py` reads a saved `primal_trace` receipt. It uses only the
Python standard library and never imports a model or calls a solver. Its
default fixed members are the recorded root cones and the selected marker
and assigned Z internals. An explicit fixed-member JSON document may be
supplied instead; its actual-member assertions then become explicit
additional premises, not facts established by the script.

The search uses a bitset Bron--Kerbosch algorithm with pivoting on the
positive saved trace support. It reports every violated maximal clique
found, subject to a deadline and output limit. `enumeration_complete`
states whether all maximal cliques of that support were enumerated.
Every violated subclique extends to a violated maximal clique when weights
are nonnegative, so a completed search suffices for separation on this
support; it does not enumerate every violated subclique. The saved decimal
weights are treated exactly as rational numbers for the discovery sum.
They remain a numerical primal sample, not a proof of realizability or an
upper-bound certificate. Absent trace entries have discovery weight zero;
the original producer may have omitted small positive values.

Every reported clique is independently checked using literal Python sets,
separately from the bitset graph. The result records a digest and counts of
witnesses for all unordered pairs including self-pairs; the optional
`--include-pair-witnesses` flag also saves every witness explicitly. The
clique and fixed-member data suffice to recompute them. A witness is either a represented
point shared by both traces or an index into the fixed actual members that
avoids their union. Optional greedy extension examines all represented
traces of size at most four and keeps exactly the same validity test. A
deadline can make that extension partial, without invalidating its rows.

Source provenance consists of hashes of the separator, this note, the
receipt, any explicit fixed-member document, and an optionally supplied
producer source. A producer hash merely quoted by the receipt is labelled
as such unless a source file was supplied and checked. Fixed-member
actuality and H27 remain literal mathematical premises. The script does
not reconstruct or verify the receipt's original LP relaxation.

## Integration into a new D17 source version

The existing `degree17_full_projection.py` must remain unchanged. A future
version can append one row with coefficient one on each clique trace and
right-hand side 27 before assembling its sparse matrix. Use trace masks
and the new model's trace-index map, never column indices copied from a
receipt. Bind the row-data file and separator source by hash in each new
receipt, and replay any resulting exact dual against that new matrix.

The represented universe, excluded root and actual fixed members must be
checked against the receiving branch. Root-cone-only cliques transfer
between branches with the same root geometry. A row using a selected
marker as a witness is conditional on that actual marker, unless a fresh
pair check supplies alternative witnesses available in the new branch.
The ordinary H27 row does not depend on the sampled primal weights.

If the new model refines a smaller represented universe U to U', preserve
the row by putting coefficient one on every fine trace t whose restriction
t intersect U belongs to C. Blindly retaining only the old exact masks
would generally lose the intended aggregation. Conversely, merging trace
classes requires a fresh compatibility check. Exterior marker labels are
actual represented points and must be transported by the same literal
relabeling as the fixed members.

For the current eleven D17 kinds, this applies equally to P10+H0..H7,
P9+P8, and P9+Q8. The lemma needs neither a P-type component nor a Q8 pool
claim. It can therefore be added to a fresh D17 constructor without
altering any existing structural premise or frozen source hash.
