# Degree17 v4: literal fixed-near witnesses for singleton cap7

23 October 2026. Ordinary proof-development addendum. The new source is
prepared from frozen `degree17_full_projection_v3.py`, SHA256

    d247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae.

No model import, catalogue construction, LP, exact replay or Lean command
is run for this source preparation. The older producers, replayers and
hashed notes remain unchanged. The optional H27-clique interface and
its literal validation from v3 are retained.

## The arbitrary-support implication

Let A be an actual member of a finite simple SF4 family and let v in A.
Suppose two actual members B,C satisfy

    v in B and C,       B intersect C={v},
    (B minus{v}) intersect(A minus{v}) nonempty,
    (C minus{v}) intersect(A minus{v}) nonempty.

In the complete triple link at v, the actual anchor is A minus{v}.
The exact-v singleton count at A is the size s of its disjoint class.
If s>=8, universal B4 separation makes the near class intersecting.
But B minus{v} and C minus{v} belong to that near class and are disjoint.
Therefore s<=7. This is the general lemma already stated in
`D18-marked-B4-row.md`; its proof is independent of the root degree,
mu41, the numerical objective, I7 classification and any ambient
support bound.

## Literal actual-member implementation

For each fixed actual anchor A and v in A, the new helper collects
fixed actual B with v in B and B intersect A not equal to{v}. It searches
for a pair with B intersect C={v}, returning the first literal witness.
The fixed list is exactly the complete root star plus the selected
actual marker and assigned-present Z internals. A variable's positive
upper bound is never used to assert that its four-set is present.

Each witnessed pair supplies a separate named row

    sum_{U:U intersect A={v}} n_U
        <= 7-#{B in S_x:B intersect A={v}},

whose label records A,v and the two actual witnesses. This is the exact
family singleton count after subtracting only the fixed root cones.
Selected residual members remain in their trace variables, so are
counted once. Because all fixed members lie in the represented universe
plus the excluded root x, unrepresented exterior completions cannot
alter these intersections. The source retains the weaker ordinary cap10
row as well; adding the new cap7 row leaves its meaning explicit.

The rule applies also at a residual marker anchor and at the root pivot
x of a root-cone anchor. In the latter case no residual can have exact
trace{x}; the entire singleton count is the known root-star offset.
If this exceeds7, the new constant row has a negative right side and
correctly certifies that the selected actual witnesses are impossible.
No arbitrary cap is imposed on an unrepresented exterior point.

## Necessary local-catalogue pruning

The central local catalogue for A=T union{x} stores the non-root
singletons in columns4,5,6, in the same point order as T. When a literal
witness exists for v in T, all local states with that coordinate at
least8 are removed before allocating their selector columns. An actual
family's state cannot be removed by the preceding theorem.

If the root pivot is witnessed and its exact root singleton offset
exceeds7, all states are removed; otherwise no additional root pruning
is required. A resulting empty catalogue means the usual selector
normalization is inconsistent, exactly as it should be for an impossible
actual-marker branch. The direct inequality remains available as well.

The cached universal local catalogue itself is not mutated. Pruning
uses a fresh `alive` mask within the receiving branch's build, so one
marked case cannot contaminate another case's cached catalogue.
The optional degree-distribution ties, resource costs, generic triangle
rows and H27-clique rows are preserved from v3.

## Provenance and validation boundary

The new producer dependency registry hashes the frozen v3 source, this
addendum, and `D18-marked-B4-row.md`. Its literal premises explicitly
state both the cap7 rows and the guarded pruning. The build API and
receipt identity structure remain those of v3; only source/dependency/
literal-premise hashes and the resulting rows/columns change.

Validation at preparation is ordinary source inspection and static AST
parsing only. Numerical behavior, performance, exact arithmetic and
any resulting branch exclusion require separately scheduled runs.

Prepared v4 source SHA256:

    a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2.

Static AST parsing succeeded; the source was not imported or executed.
