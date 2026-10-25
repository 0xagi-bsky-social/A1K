# Independent ordinary check of the complete R15 deletion exclusions

24 October 2026. Ordinary research check, not final review or Lean.
This note does not alter either frozen producer proof.

The complete outer-deletion proof in
`LOW15-R15-outer-deletion-exclusion.md`, SHA256
`b665f4aa18d202df65383768d9ade1247d4feb46b7beea026e383a7e10180550`,
and the complete hub-deletion proof in
`LOW15-R15-hub-deletion-exclusion.md`, SHA256
`9fcacff3efee757a9bc0005fe61639f88e9b532b754b8cd0adbbeba5153155d3`,
are valid under their stated complete-link, maximum degree15,
actual-neighbourhood lower bound41 and singleton cap8 hypotheses.
The hub proof additionally invokes universal B4 at a pool of size8.
Neither proof needs a neighbourhood upper bound or an ambient cutoff.

## Outer deletion

The15 root cones consume23 hub incidences, leaving at most37. Every
one of the four hub anchors is actual, and summing its neighbourhood
bound gives 3S+4P+4T+4q>=104. Three times the hub budget minus this
quantity yields 2P+5T+8q<=7. At an actual hub anchor the singleton
capacity is exactly s_i+p_ij<=8, because all root cones meet it at
the root. Hence S<=32, and P>0 implies S<=30. The three cases P=0,
P>0,T=0 and P>0,T=1 have upper bounds100,102,98 respectively against
the required104. All nonnegative integer possibilities are covered.

## Hub deletion: the complete-P5 guard

The deleted hub triple is123 and the distinguished hub0 has link degree6;
the other hubs each have link degree5. Their total root-cone incidence
is21, leaving at most39. The only anchors used are the three actual
root cones x+(K minus i) for i=1,2,3. No deleted cone is assumed actual.

For a satellite hub i and the other satellite hubs j,k, its five triples
through x are exactly x joined to the graph

    triangle(D_i) plus the two edges {0,j},{0,k}.

The two graph components are disjoint. At singleton equality
b_i+p_ij=8 for the actual anchor Q_j, B4 makes the entire near i-link
intersecting. All five x-cones are near. Therefore a non-x near triple
must cover all their graph edges. It needs two points of D_i to cover
the triangle, leaving one point for both path edges. Their unique
one-point cover is0. Thus the near triple is exactly0 plus an edge
of D_i.

This is a statement about all actual near triples, not merely a finite
list of allowed traces. A residual trace {i,k} is near and lacks0;
every residual triple trace containing i either lacks0 or includes a
further hub outside D_i. The residual K trace also fails the cover form.
They are all forbidden, giving precisely

    b_i+p_ij=8 ==> p_ik+T-t_i+q=0.

The residual trace {0,i} is correctly retained: it can have its two
other points on an edge of D_i. No additional near term is discarded.

## Hub deletion: the scalar contradiction

The three actual-anchor inequalities and the total hub budget give
P+3T+5q<=a<=8, where a is the residual singleton count at0. The
separate degree0 budget gives

    Y+t0>=1+delta_mid+delta_max,

where Y is the satellite triangle pair sum and delta_i=8-b_i.
All these identities include residual triple traces and the K member.

If t0>0, the displayed B4 guard makes every satellite pair bound strict.
If t0=0 and one satellite pair is absent, charging the two possible
path edges to their outer endpoints gives Y<=delta_mid+delta_max,
contradicting the preceding lower bound. Hence all three pairs are
positive, and the B4 guard again makes all three bounds strict.

Since the variables are integers,

    Y<=2*delta_min+delta_mid-3.

Combining this with the lower bound implies delta_min>=4-t0 and then
Y>=9-3t0. But the total budget gives Y<=8-3t0. The contradiction is
valid for every nonnegative integer t0,q; no extra restriction on them
is needed. A zero deficit would simply make a strict pair capacity
negative and already be impossible.

Together with the separate exact-rho7 classification, these two ordinary
lemmas exclude every complete degree15 link having rho exactly7 in the
cap15 SF4 domain. The rho<=6 exclusion and the rho8/B4 branch retain
their separate proof dependencies.
