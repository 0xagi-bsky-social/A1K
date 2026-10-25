# Size fifteen with rho at most six: reduction to eleven support points

24 October 2026. Ordinary reduction plus two small saved finite diagnostics.
This is not a full classification or Lean theorem. The checked finite leaves
remain certificate-diagnostic under the stated SuperMath assurance policy.

Let L be a finite simple sunflower-free family of fifteen triples, including
empty cores, with at most six members disjoint from each actual member.
Then every closed neighbourhood has at least nine members. The ordinary note
LOW15-R15-rho6-partial-status.md proves minimum used degree at least two,
maximum degree at most six, pair-codegree at most two, and the two forced
degree-two motifs. We now supply bounded finite evidence excluding both motifs.

## A degree-two point with a degree-six neighbour

With x=0,a=1,b=2,c=3 the mandatory triples are xab,xac,abc and the three
triangle stars a*binom(T,2), b*binom(D,2), c*binom(E,2). All triads avoid
x,a,b,c. There are twelve distinct triples. The x and a degrees are saturated
at two and six. The b and c degrees are five and cannot rise to six: their
used pair with x has codegree one, whereas every used pair at a degree-six
point has codegree two (its SF2 link is two disjoint triangles). No additional
triple can use any of x,a,b,c.

Fix T={4,5,6}. Permutations preserving this triangle make D depend only on
k=|D intersect T|; choose the first k T points and 3-k fresh consecutive labels.
Enumerate all E triples on this union plus three fresh points, retaining only
initial-segment new labels. This covers every possible identification of the
three triads. It normalizes the forced motif, not the full ambient support.

check_r15_degree2_degree6.py generated91 normalized motifs. Eighty-five already
contain a sunflower or have an actual member with seven disjoint companions;
the six remaining motifs permit no thirteenth triple avoiding x,a,b,c.
For that last single triple, padding with three new points covers every
exterior possibility. Each rejected candidate is supplied with two literal
motif triples whose three pairwise intersections agree. The complete witness
lists are in R15-degree2-degree6-literal.json. A family of fifteen is impossible.

## A degree-two point with no degree-six neighbour

Write its triple as xyz. If either of y,z had degree at most four, the condition
N(xyz)>=9 would require the other to have degree five and all three pair
codegrees to be one. Its five-edge point-link would put x at a path leaf and
the other root at the path middle, forcing pair-codegree two instead. Hence
d(y)=d(z)=5. Neither xy nor xz can have codegree two: the other five-degree
point-link would force yz to have codegree two as well and then N(xyz)<=8.
Thus their codegrees are one and yz has codegree two.

The forced form, with x=0,y=1,z=2,w=3, is

    xyz, yzw, xuv, y*binom(D,2), z*binom(E,2),

where D,E avoid x,y,z,w, u,v avoid x,y,z, and the nine triples are distinct.
The second yz member fixes the same w in both five-edge path components.
The points x,y,z are saturated: y or z cannot increase to degree six since
its pair with x has permanent codegree one. Six further triples must avoid
all three points. Normalize D={4,5,6}, E by |D intersect E|, and enumerate uv
on the existing support plus two consecutive fresh labels. This gives78 motifs;
18 survive the literal sunflower/rho tests on the nine mandatory triples.

There is a necessary extra step before treating a finite completion universe
as exhaustive. For each surviving motif, test every next triple avoiding x,y,z
on its support plus three new points. Every permitted triple uses at most one
new point. Its two old points form a pair P. Across all permitted exterior
pair types, the remaining capacities

    sum_P (2 - #{A in the nine-triple motif : P subset A})

are at most three. Each future triple with an exterior point consumes one
unit of one of these capacities. Consequently an entire completion introduces
at most three exterior points, not merely three per triple. Every arbitrary
completion can therefore be relabelled into the checked universe. This is a
derived local support bound. The check fails if the budget exceeds three or
any permitted triple uses two new points.

check_r15_degree2_without6.py independently regenerates all78 motifs, records
the rejected-next-triple witnesses and the projected pair capacities, and
searches every six-element subset of the permitted-next-triple list. Its
increasing-index search checks pair capacities, literal sunflower triples and
the monotone rho bound at every extension. All319 search nodes terminate
without a six-triple completion. The receipt is
R15-degree2-without6-complete.json; zero completions. The earlier probe file
R15-degree2-without6-probe.json is exploratory and is not the completion check.

## Consequent support reduction

Conditional on these finite obstructions and their ordinary normalization,
every used point has degree at least three. Let I count unordered intersecting
pairs of members and r(v) the number of codegree-two partners of point v.
Then I>=15*8/2=60 and

    I=sum_v (binom(d(v),2)-r(v)/2),     sum_v d(v)=45.

For degrees3,4,5,6 the minimum r(v) values are1,2,4,6. Thus each summand is at
most19*d(v)/6-7. It follows that60<=142.5-7*n, so n<=11. If the maximum degree
is at most five, the bound (11*d(v)-23)/4 also gives n<=11. Degree at most four
is impossible: each summand is at most5*d(v)/4, giving I<=56.25<60.

Every remaining L therefore has a degree-six or degree-five point and support
at most eleven. Its complete normalized point-link is respectively two
disjoint triangles, or C5, or a triangle and a two-edge path. Padding to eleven
points is justified by this proof; the size-fifteen residual searches in these
three domains have NOT yet run. The old size-sixteen proof trees do not exclude
size fifteen. No statement that rho<=6 is impossible is made here.

## Frozen diagnostic source identities

- check_r15_degree2_degree6.py:
  a17303505959c6416e16a4400d3f82f848e0f9c5418fe9578c1965fb857ecf60
- check_r15_degree2_without6.py:
  2a939cdb512e94662443e8db6eb67cc9b43ce22dec9da78ec53dac0384e54905

Both actual executions completed below0.1 seconds with explicit deadlines.
They use exact standard-library finite sets/integers and no solver. The new
argument does not depend on the unsaved historical diagnostic.
