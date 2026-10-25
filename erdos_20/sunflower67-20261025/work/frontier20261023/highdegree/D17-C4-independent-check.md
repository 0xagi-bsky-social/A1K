# Independent check of the D17 complete-C4 degree bound

24 October 2026. Ordinary proof development. The deduction and its literal
template predicate pass this inspection under the stated universal imports.
This is not a complete D17 branch check, a final review, or Lean verification.

## The support premise is supplied by the theorem actually used

The frozen prior `paper/main.tex`, lines612–636, states that every SF3
family of17 triples is P10 plus I7 or P9 plus I8 **on disjoint supports**.
The checkout is `work/frontier20261020/prior-art68/repository`, commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.

Thus, if d_F(t)=17, the complete link L_t has this separated form. A
point x lies in only one component, and its complete point-link is its
point-link within that component. This is stronger than generic Q8
core isolation, but it is exactly the high-link17 theorem's conclusion.
The C4 argument does not assume that arbitrary Q8 and I7 supports are
disjoint in settings where only the Q8 core is isolated.

A complete four-cycle at x excludes a P10 component, whose point degree
is5 with C5 link. It also excludes a P9 component: its degree4 links
are paths of four edges on five vertices, obtained from C5 by deleting
one edge. The same observation excludes P8 degree4 points. Consequently
x must be one of the C4 points in I7 or Q8.

The I7 input is the universal arbitrary-support catalogue recorded in
`D17-I7-classification-route.md`, with its independent coverage receipt.
The I8 input is the universal P8/Q8 classification. Neither follows merely
from testing the displayed finite models; both remain explicit imports.

## Independent reconstruction of the finite consequence

`recheck_D17_C4_completion.py` imports neither the original checker nor a
numerical model. It reads the pinned eight I7 families, constructs P10,
all10 one-block deletions, all45 two-block deletions, and Q8. It uses
integer masks and recognizes C4 by an actual cyclic ordering, separately
from the original checker's degree-pattern test. It also directly checks
the intersecting and sunflower-free properties of every template.

All65 models and392 used points were inspected. The exact eight C4
points are H1/5, H2/3, H2/4, H2/5, H7/4, and Q8/2, Q8/3, Q8/4.
Every one contains a component triple on its four neighbours. All
neighbour sets, edges, and complete lists of such triples match the
saved original receipt. This reconstruction passed in0.0022 seconds;
no solver, exhaustive ambient-support search, or Lean job was run.

In particular the conclusion supplies an **actual** T in L_t, not a
candidate completion. It lifts to the actual four-set {t} union T in F.
The argument requires a complete pair-link equal to C4. An embedded C4
inside a larger pair-link would not justify the component identification.

## Application and receiving row

For the complete root link P9(Y) plus Q8(Z), with hubs6,7, triad8,9,10,
and leaves11,12, each triad t has complete root-pair link C4 on the hubs
and the other two triad points. Completeness holds because all members
through the root are the17 prescribed cones. The actual completion
from the lemma is a four-set wholly in Z. Therefore `empty_z` excludes
d_F(t)=17; the ambient degree cap17 gives d_F(t)<=16.

This holds for all three triad points and all exterior marker choices.
It does not use a degree16 no-P9 conclusion, an exterior support bound,
or an assumption that the represented points exhaust the ambient set.

The inspected v10 constructor adds the row only when
`kind == 'P9-Q8' and empty_z`. Its `fixed_degree` counts prescribed
root cones only, exactly4 at each triad point. Every residual trace
containing that point has coefficient1, including selected actual
markers. Consequently the row right side is16-4=12, with no omitted
residual or double-subtracted selected member. No claim about the new
LP optimum follows from this inspection.

## Byte identities

| Input or new evidence | SHA256 |
|---|---|
| D17-C4-internal-completion.md | 47d39e647d8e4c14864de262c46ce576d08a12f66b046d51af6554476efabd77 |
| check_D17_C4_completion.py | a1dfbf89fd0a992c3ab87ff600a374af2703673d61b01b78a960d6d52d8d5f88 |
| D17-C4-completion-literal.json | f4b74d3743d8ae5664ac2fd8aec7b125080bf315f37885ea00112c129d2e18b9 |
| D17-I7-classification-route.md | a86e80d8377f24218194461c7e2dd92ffe44c3d6b4a505240bd050f129dcb504 |
| D17-i7-coverage.json | 030fcb5ec6e64c738f306409fca83ed962c3afefb5225378295d3a6601c196df |
| recheck_D17_C4_completion.py | d3a41aa276258c98c4dac05d384f37578043d5edf18cb3bc3186a40bdb52033e |
| D17-C4-independent-reconstruction.json | ca21041a29a84d48dc400d46ae911f6ae8c2781d2db1540ed1a7a06e6d2d74cc |

The independent receipt also binds the imported I7 literal certificate.
No inspected frozen source or receipt was changed.
