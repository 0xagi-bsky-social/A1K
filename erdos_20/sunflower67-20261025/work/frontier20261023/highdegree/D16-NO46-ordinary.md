# Cap16 with global no-P9: every neighbourhood has size at most45

23 October 2026. Ordinary proof development, not a final review, solver
certificate or Lean result. No finite enumeration or support cutoff.

Let F be a simple SF4 family of68 members with global degree cap16.
Use the previously established ordinary conclusions in this order:

1. `D16-P10-ordinary-exclusion.md` excludes P10 in every point-link.
2. `D16-NO47-ordinary.md` gives N(R)<=46 for every actual member.
3. `D16-P9-root16-ordinary-exclusion.md` and
   `D16-P9-global-ordinary-exclusion.md` exclude P9 in every point-link.

The third step consequently bounds every exact singleton by8. It used
only N<=46, not the stronger conclusion being proved here. The dependency
order is therefore acyclic. All classification, H27, HP15 and other
imported boundaries are the explicit ones in those three arguments.

For an actual anchor R of size4, write s_i,p_ij,t_i for its exact
singleton, pair and triple counts; t_i omits i. Put S=sum s_i,T=sum t_i,
r_i=sum_(j!=i)p_ij, and delta_i=16-d(i)>=0. We have

    sum d(i)=2N(R)+2-S+T,
    r_i=15-s_i-T+t_i-delta_i.

Use two local ordinary consequences of B4 and triple codegree2 from
`LOW15-large-singleton-core.md`:

* s_i>=8 implies r_i<=6, with no assumption T=0;
* t_l=1 and all s_j>=8 for j!=l imply r_l<=4.

The second uses the actual exact-triple member and a simple bipartite
graph of maximum degree2 and matching number at most2. No support
classification of a singleton7 family is being assumed.

Suppose N(R)=46. The degree sum is94-S+T<=64, so S>=30+T.
Since all s_i<=8, S<=32 and T<=2. Moreover

    sum delta_i=S-T-30.

If T=0, the exhaustive sorted singleton patterns are:

* S30: (6,8,8,8) or (7,7,8,8). The total deficit is0, so every
  singleton8 root has row7, contrary to row<=6.
* S31: (7,8,8,8). The total deficit1 cannot lower all three nominal
  singleton8 rows7 to at most6.
* S32: (8,8,8,8). The total deficit2 cannot lower all four rows7.

If T=1 and S31, the pattern is (7,8,8,8) and all four degrees16.
If the actual triple member omits the singleton7 root, that root has
row8 while all three other singleton counts are8, contradicting the
omitted-row bound4. If it omits a singleton8 root, its row7 directly
contradicts row<=6.

If T=1 and S32, all singletons are8 and the total deficit is1.
The omitted root has row7-delta>=6, contradicting the omitted-row bound4.

Finally T=2 forces S32 and all four degrees16. Each omitted root has
singleton8, t_i=1 and row6, again contradicting the omitted-row bound4.
Every N46 possibility is excluded. Since N<=46 was already proved,

    N(R)<=45 for every actual R when |F|=68 and Delta<=16.

This restores the upper-neighbourhood interface45 by an ordinary mu41
argument. It does not exclude all degree16 links or assert a global
extremal bound67. No old mu42 bootstrap is used.
