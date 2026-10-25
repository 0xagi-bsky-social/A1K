# Degree-19 projection: the family-to-linear-model bridge

23 October 2026. This is ordinary proof development for the size-68 degree-19 branch. It checks the mathematical meaning and necessity of every row family in `degree19_projection_v1.py`, `degree19_projection_v3.py`, `degree19_projection_v4.py`, and `degree19_projection_v5.py`, and explains the weaker-v3 phase-one transfer. No solver, Lean command, signature generator, or trace enumeration was run for this note. Exact certificate replay and source-hash binding are separate tasks. No global bound of 67 is asserted here.

The bridge is valid, conditional on the explicitly identified universal structural results and H27. No unjustified row was found in these four generators under the hypotheses below. This conclusion concerns the row families and the completeness of the necessary local domain; it does not certify any saved numerical result or establish that a list of marked cases covers the entire degree-19 branch.

## 1. Statement and dependencies

Let F be a finite simple four-uniform family with no three distinct members having equal pairwise intersections, including an empty common intersection. Assume:

1. `|F|=68` and every point of F has degree at most 19. The latter is an explicit hypothesis of this branch, to be supplied by a preceding degree-20 exclusion; it does not follow just from the displayed degree-19 link.
2. A point x has its **complete** link equal to P10(Y) disjoint-union P9(Z), on disjoint sets `Y={0,...,5}` and `Z={6,...,11}`. The P10 blocks are

       012 015 023 034 045 124 134 135 235 245,

   and P9(Z) is this model shifted by six with 678 removed. Write D for these nineteen blocks and S0 for the nineteen members `{x} union T`, `T in D`. Thus every member through x is in S0.
3. H27: every intersecting four-uniform three-sunflower-free family has at most 27 members.
4. The imported universal triple-family results hold: the intersecting bound ten and I8/I9/I10 classification; isolation; B4 separation; the general triple bound twenty; the R16 classification and the resulting degree-17--20 decompositions. The universal trace margins and extension-point deductions from `TRACE_FOUNDATIONS.md` are also used, with their stated proofs.
5. Every case restriction supplied to `build` is an actual hypothesis for the family under consideration: a selected marker is present; an assigned component has exactly the listed internal members; an `empty` component has no internal member; and every trace passed in `forbidden` is absent. Absence of arbitrary `forbidden` traces is not proved merely by passing their masks to the generator.

Then F gives a feasible point of the corresponding model, with residual objective exactly 49. In fact its trace coordinates and its one selected local-state coordinate at each central anchor are integral. Consequently an exact objective bound strictly below 49, or an exact infeasibility certificate for that model, excludes the corresponding mathematical case. An objective bound equal to 49 requires a further equality argument.

The frozen structural source root in this note is

    work/frontier20261020/prior-art68/repository/

The relevant locations are:

| Source | Imported content |
|---|---|
| `paper/main.tex:104–109` | H27 is explicitly imported for intersecting SF4 families. |
| `paper/main.tex:188–204` | SF2 capacities: maximum six, pair-link maximum degree two. |
| `paper/main.tex:206–231` | Canonical P10/Q8 and universal I8/I9/I10 classification. |
| `paper/main.tex:272–331` | Isolation and B4; only the five-point Q8 core is generally isolated. |
| `paper/main.tex:333–376` | Degree/codegree bounds, exact-trace capacities, and degree identities. |
| `paper/main.tex:443–462,612–636` | R16 model and universal size-17--20 decompositions. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md`, D.1–D.5 and E1 | Universal rooted compatibility, five trace margins, and at most two high points in an actual member. |
| `companion/upstream/MU42/scripts/local43.py` | Exhaustive construction of rooted signatures from the universal models; the predicates audited below. |

The October 23 deductions `D19-singleton-I04.md` and `C5-internal-compatibility.md` supply the refined P5 and degree-16 C5 consequences. Their arguments are reproduced at the points where the model uses them. The historical F69 certificates, their support limits, and their minimum-degree or mu42 bootstraps are not premises here.

## 2. Projection without an exterior-support bound

Put `R0=F minus S0`. Every Q in R0 avoids x and `|R0|=49`. Usually the projected core is `C=Y union Z`. If the marked member has one point outside this core, give that **actual point** label 12 and enlarge C by that one point. The fixed centre has code label 13. All remaining exterior points retain arbitrary identities and may occur in arbitrarily many different combinations consistent with F.

For every `U subset C`, `|U|<=4`, define

    n_U = #{Q in R0 : Q intersect C = U}.

There are `1+12+66+220+495=794` trace coordinates in the twelve-point case and `1+13+78+286+715=1093` in the thirteen-point case. These are types of intersections, not a bounded universe of actual four-sets. In particular, a proper trace can have several distinct exterior completions. The identity

    sum_U n_U = 49

holds for the mapped family. The maximization generators do not add this as an equality, which only enlarges their feasible domain; it still gives the objective value of the mapped family. The size-68 hypotheses used in other rows remain part of the contradiction setup even though the optimization variable sum is free.

Every tested anchor A is contained in `C union {x}`. Therefore `Q intersect A=U intersect A` when `Q intersect C=U`, and every modeled incidence, disjointness, or exact-trace statistic is an exact sum of the n_U. Neither equality nor inequality of two unprojected exterior labels is inferred from n_U alone. The models may admit additional unrealizable points; the bridge only requires every actual family to be admitted.

### Box bounds and case restrictions

The initial upper bounds are

| Trace size | Upper bound for n_U | Reason |
|---:|---:|---|
| 0 | 49 | There are exactly 49 residual members. |
| 1 | 19 | The trace class is contained in the point star of its core point. |
| 2 | 6 | It is contained in a pair link, an SF2 graph with at most six edges. |
| 3 | 2 | Three distinct completions of a fixed triple would be a sunflower. |
| 4 | 1 | The entire four-set is U; simplicity permits it once. |

All lower bounds initially are zero. Only four-point traces are made binary by their box. A selected four-set M has `n_M=1`. A complete internal assignment sets every four-point trace wholly in the assigned component to zero or one according to that assignment. This is exact: a residual four-set with a four-point trace has no unrecorded exterior point. The same observation justifies component emptiness.

The `forbidden` option means `n_U=0` for each supplied U; when `|U|<4`, it forbids **every** exterior completion of that exact trace. A prior mathematical argument establishing only the absence of one completion would not justify this option. For a marked exterior point, the present catalogue only uses a single label 12, so `n=13` includes every point of each actual marked member.

For each selected M and each fixed block T, the generator also sets `n_U=0` if

    U intersect T = U intersect M = T intersect M.

These are exactly the three pairwise intersections of `Q, M, {x} union T` for any Q of trace U. The centre x is absent from Q and M, and every point of M is projected. The three members are distinct: the central one contains x; if Q=M, the displayed equality would require the three-set T to contain the four-set M. Thus the zero is a literal sunflower exclusion for every possible exterior completion. No omitted exterior coordinates can change these intersections.

## 3. All global linear rows

Write `b(U)=#{T in D : U subset T}` for a projected nonempty U. For `|U|=1,2,3`, the incidence rows are

    sum_{V superset U} n_V <= cap(|U|) - b(U),
    cap(1)=19, cap(2)=6, cap(3)=2.

The left side counts residual incidences; b(U) counts all fixed central incidences. These are respectively the assumed global point cap and the universal pair/triple caps. If U contains the marked exterior point 12, then b(U)=0 as required.

For each **actual** anchor `A in S0 union {selected members}`, the members disjoint from A form an intersecting SF4 family: two disjoint such members together with A would give an empty-core sunflower. H27 therefore gives

    sum_{V : V intersect A is empty} n_V
      <= 27 - #{B in S0 : B intersect A is empty}.

This is the row labelled `disjoint`. It applies to selected anchors because their presence is a case hypothesis. It bounds all completions of the empty trace, without naming exterior support points.

For a nonempty proper subset U of A, residual sets of members with exact trace U on A form an intersecting sunflower-free family after U is removed. Two disjoint residuals, with A, would be a sunflower with core U. The intersecting SF3, SF2, and SF1 bounds are 10, 3, and 1. Hence

    sum_{V : V intersect A = U} n_V
      <= cap_exact(|U|) - #{B in S0 : B intersect A = U},
    cap_exact(1)=10, cap_exact(2)=3, cap_exact(3)=1.

These are precisely the `exact` rows, including the central contribution subtraction. Residues are distinct because F is simple and the exact trace is fixed.

### The size-41 neighborhood filter

For every actual member A, H27 bounds the disjoint family by 27. Thus

    |N_F[A]| = 68 - |D_F(A)| >= 41.

In the usual exact-trace notation this says

    1 + sum_i s_i + sum_{i<j} p_ij + sum_i t_i >= 41.

This is the local catalogue's `sum>=41` filter. The initial 1 counts A itself. The threshold is 41, not the F69 threshold 42. It is conditional on this size-68 contradiction setup and H27, not a universal minimum neighborhood for arbitrary SF4 families.

### The degree-sum-19 rows

Let `A={a,b,c,d}` be any actual member. Within its neighborhood, members avoiding a and b have exact trace `{c}`, `{d}`, or `{c,d}`. Their number is at most `10+10+3=23`. Therefore

    |{Q in F : a in Q or b in Q}| >= 41-23 = 18.

All members through a or b are indeed in N[A]. Since A contains a and b, `d(a,b)>=1`, and inclusion-exclusion yields

    d(a)+d(b) >= 18+d(a,b) >= 19.

This proves both the catalogue filter `ds[i]+ds[j]>=19` and the explicit `pair-degree` rows at selected and central anchors. If `base` is the sum of the two central degrees, their implemented form is

    -sum_V n_V (1[a in V]+1[b in V]) <= base-19.

For a=x the residual coefficient is zero at x and its central degree is already 19. There is no claim of this lower bound for pairs not known to occur in an actual member.

## 4. Complete local-state catalogue at a central anchor

Fix `A={x} union T`, `T in D`, and order its points as `(x,a,b,c)` with `a<b<c`. Use p for its six exact pair counts in the order

    xa, xb, xc, ab, ac, bc,

and t for its four exact triple counts, with t_i counting the triple obtained by omitting the ith anchor point. Let s_i be the corresponding singleton counts. Put

    k_i = 1 + sum_{j != i} p_ij + sum_j t_j - t_i,
    d_i = s_i+k_i.

These are exact link identities. The complete central link fixes `p_xa,p_xb,p_xc`, `t_a,t_b,t_c`, and s_x, because every member whose trace contains x must be in S0. The remaining seven free statistics are

    (p_ab,p_ac,p_bc, t_x, s_a,s_b,s_c).

No central member contributes to any of these seven classes, since all contain x. Their values are exactly the seven bucket sums used later in the linear equalities.

The loop over `q in {0,1,2,3}^3`, `e in {0,1}` covers every possible free pair/triple count by the exact capacities. For each neighbor it considers every integer singleton count in 0,...,10 and keeps only the necessary conditions below. The actual vector is therefore included unless a filter wrongly removes it; the following arguments prove that none does.

The root's data are computed separately for each of the nineteen actual cones. In particular, on Y one has `(s_x,k_x)=(9,10)`. On Z one has `(10,9)`, and deleting 678 changes the exact rooted counts: anchors meeting 678 once have one x-pair count 1 and two x-pair counts 2, while anchors meeting it twice have one missing triple class and all three x-pair counts 2. The code obtains these values by intersections with S0, rather than copying P10 counts to P9. The root itself needs no call to `local_s_candidates`: its complete actual link already verifies its degree and structure.

### Every condition in `local_s_candidates(i,p,t,17,0,0)`

1. **Degree range.** The helper admits `1<=s_i+k_i<=20`, and the caller further enforces `s_i+k_i<=19`. Every anchor point has degree at least one; the stronger upper cap is hypothesis 1. The parameters `r10=r9=0` impose no old positive lower bound on k at s=10 or s=9.
2. **High-link splits.** At degrees 17, 18, and 19, the universal disjoint-support decomposition gives, at every anchor containing the point,

       d=17: (s,k)=(7,10),(8,9),(9,8),(10,7);
       d=18: (s,k)=(8,10),(9,9),(10,8);
       d=19: (s,k)=(9,10),(10,9).

   Indeed the anchor triple in the point link belongs to one intersecting component; that entire component meets it and the other component is disjoint. No classification of an arbitrary I7 is used.
3. **B4.** If `s_i>=8`, the near family K_i is intersecting and has at most ten triples. This proves `k_i<=10`. The universal D6 argument gives `r_i=sum_j p_ij<=6`: if one pair class has three residual edges, it is a triangle; every other pair-class edge must cover that triangle, and each of its three pairs can occur at most twice in K_i.
4. **D8.** If `s_i>=8` and `t_j=1`, every residual edge in class ij contains the unique extension point of the triple class omitting j. The pair-codegree bound in K_i limits such a star to two edges, proving `p_ij<=2` whenever the helper tests `tau_j and alpha_j>2`.
5. **D7.** If additionally `k_i>=9`, K_i is P9 or P10. Its exact singleton counts relative to its anchor triple are each at most two. These are precisely the p_ij, so `max(alpha)<=2`.
6. **Rooted signatures.** For `k_i=8,9,10`, the universal intersecting classification identifies K_i with a k_i-member subfamily of P10, or with Q8 when k_i=8. The helper `signatures()` ranges over **every** k-subset of the ten P10 blocks, adds Q8 at size eight, ranges over every member A of each family, and ranges over every ordering of A's three points. It records the three singleton counts followed by the three complementary-pair counts. These are exactly `(alpha,tau)` for K_i. Hence every actual rooted signature is in `SIG[k_i]`. Repeated isomorphic models or signatures only add duplicate coverage before conversion to a set; they cannot remove an actual signature. This is a syntactic completeness proof of the construction under the imported classification, not a claim that all surviving signatures are simultaneously realizable in an SF4 family.

The projection calls this helper directly. It does **not** call `local43.enumerate_rows`, so that separate function's degree-ordering loop is not imposed on the anchor points. In particular no symmetry argument silently permutes a fixed central point with a neighbor.

### The universal margin and extension-consistency filters

If q of the four singleton counts are below eight, the universal five-margin result gives

    sum p + sum t <= (12,14,17,19,22)[q].

This is exactly the margin filter. Its first two cases use the explicit arguments in `TRACE_FOUNDATIONS` D.3–D.4; the other cases are D.5. None requires mu42, a minimum degree, or a bounded exterior support.

For every occupied triple class t_i=1 there is a unique actual exterior point z_i. If i,j are large, t_i=t_j=1, and p_ij=2, D9 forces `z_i=z_j`. The function `equality_consistent` forms the transitive closure of precisely these forced equalities. If i is large and `k_i>=9`, the rooted P9/P10 model requires all occupied z_j with `j!=i` to be pairwise distinct. Rejecting a row whose forced equality classes violate this distinction is therefore necessary. It is immaterial that the helper may fail to detect other incompatibilities: its acceptance need not imply realizability. It never infers equality merely from equality of two counts.

### At most two degree-19 points in one actual member

For completeness, the E1 proof applies here before any mu assumption. Suppose three points a,b,c of an actual anchor are high, meaning degree at least 19. Their universal high links give `s>=9`, `k>=9`, and `r<=6`. The identity for k forces `T-t_i>=2` at each high point, where `T=sum t`.

If T<=1 this is impossible. If T=2, all three high indices must be unoccupied, leaving at most one index on which the two occupied triple classes could lie. Thus T is 3 or 4. Every anchor pair touches a high point, so D7 bounds every pair count by two.

For T=3, two occupied high indices a,b exist. The model at the third high index requires `z_a!=z_b`; D9 therefore gives `p_ab<=1`. Consequently `r_a<=5` and `k_a=1+r_a+3-1<=8`, a contradiction. For T=4, every pair among the three high indices has weight at most one by the model at the third; therefore `r_a<=4` and `k_a=1+r_a+4-1<=8`, again a contradiction.

This proves the filter `sum(d>=19)<=2`; with the assumed cap 19, “high” means degree exactly 19. Its use is on the integer state of an actual anchor. No claim is needed that a fractional average of state degrees itself obeys a nonlinear high-degree count. Since every pair within Y or within Z lies in a P10/P9 block, the same fact also gives at most one degree-19 point per component in an actual family, although the generators do not add a separate global selector row for that observation.

## 5. The C5 and P5 internal rows and costs

For a component S equal to Y or Z and `y in S`, let

    I_y = #{Q in F : y in Q subset S}.

It is exactly the sum of n_U over four-point traces U contained in S and containing y. In the complete pair-link at `{x,y}`, the nine points `y in Y union {9,10,11}` have a C5 star of five cones. The three points y=6,7,8 have a four-edge P5 star. Their central incidences are respectively five and four; these are the subtractions in the implemented rows.

### Complete C5 stars

For a C5 neighbor the unconditional inequality is

    d(y)-I_y <= 15.

One proof deletes all I_y internal triples from L_y. If sixteen remain, the complete-C5 lemma below says its x-component contains at least one non-star internal cycle cover, whereas none remains. This contradicts the deletion. Equivalently, the earlier universal empty-C5 obstruction gives the same row. The implemented residual inequality is

    sum_{U contains y, U not internal through y} n_U <= 15-5=10.

If a central anchor has `s_y>=8`, B4 makes its K_y intersecting. It contains the complete five-cone C5 star through x. Every other triple avoids x and covers all cycle edges; a C5 needs at least three vertices to cover it, so that triple is wholly on the five other points of S. Thus

    s_y>=8 implies k_y<=5+I_y.

The v5 cost also uses this implication when `d(y)>=16`, even if `s_y<8`. Here is the required stronger justification. A sixteen-member triple family with a complete C5 point-link cannot be R16, whose point degrees are only four and six. Otherwise a root with at least eight disjoint triples and B4 give intersecting parts of sizes 10+6, 9+7, or 8+8. If either part is P-type, isolation makes the supports disjoint: any possible deleted block belongs to the same disjointness class as its P-type part and cannot lie in the opposite part. This works for an arbitrary opposite six- or seven-member part. If both parts are Q8, x cannot be a core point in either, since the hub link contains a triangle and the triad link contains a C4, neither a subgraph of the complete C5; as a leaf in both it would have total degree at most two. Thus Q8/Q8 is impossible without isolating shared leaves.

At sizes 17–19 the universal high-link decompositions directly give disjoint supports. In every case all five star triples belong to the same intersecting component, and every additional member there is an internal three-vertex C5 cover. Every internal belongs there, since the opposite support is disjoint. Consequently at `d(y)>=16`, at **every central anchor**,

    k_y=5+I_y.

This proves the v5 strengthening. The older v1/v3/v4 costs, which activate `max(0,k_y-5)` only for `s_y>=8`, remain valid weaker costs. All versions also require `I_y>=d(y)-15` by the unconditional deletion row. Taking the maximum of two valid lower bounds for the same I_y is legitimate.

The stronger possible tests using only cover-compatible internals or excluding non-cover internals at degree at least sixteen are not imposed by these generators. Their omission enlarges the relaxation and causes no loss in the family-to-model direction.

### P5 high-degree states and their internal lower bounds

Let y be 6, 7, or 8. In L_y the point x has degree exactly four, because its **complete** pair-link is the prescribed path. At degree at least 17 the universal decomposition is into two intersecting families on disjoint supports, and the component K containing x contains all four star triples. A P10 component cannot contain x: every used point of P10 has degree five, contradicting the exact degree four of x in the complete link L_y. This removes precisely the states with `k_y=10`. The remaining allowed states are

| d(y) | Allowed `(s_y,k_y)` | Sufficient internal lower bound used in code |
|---:|---|---:|
| 17 | `(10,7),(9,8),(8,9)` | `I_y>=1` |
| 18 | `(10,8),(9,9)` | `I_y>=4` |
| 19 | `(10,9)` | `I_y>=5` |

For the first state at degree 17, the seven-member x-component needs three non-star triples. Each covers the four-edge path. An exterior triple has at most two path vertices, so it must use the unique two-vertex path cover. At most two such triples can use that pair in an SF3 family. At least one of the three is therefore internal.

If k_y is eight or nine, its intersecting component is P8/P9 or, at eight, possibly Q8. The complete point-link of a Q8 point is a triangle plus a two-edge path, a C4, or a single edge; none can contain the prescribed four-edge path on five distinct vertices. Hence K is P8 or P9. Its six-point support is exactly x together with the five path vertices. Its `k_y-4` non-star triples are internal, and the opposite component is disjoint from this support. Thus `I_y=k_y-4`, giving the bounds in the table (and stronger bounds in some degree-17 states).

The v3/v4/v5 catalogue explicitly removes the forbidden high-degree states. The v1 catalogue retains them, making a larger domain, but the stated internal lower bounds still hold for every actual family. There is no unsupported classification of I7 and no requirement that the entire ambient ground set fit into these component supports.

### P5 deletion and the cover-capacity refinement

The unique two-point covers C_y are

    C_6={9,11}, C_7={10,11}, C_8={9,10}.

Define `J_y=#{Q in F : {y} union C_y subset Q subset Z}`. These count actual internal members already consuming the codegree of the triple `{y} union C_y`, so `0<=J_y<=I_y` and `J_y<=2`.

The unconditional refined inequality is

    d(y)-I_y+J_y<=16.

To prove it, delete from L_y exactly the `I_y-J_y` internal triples not containing C_y. If seventeen or more triples remain, choose seventeen including the four path-star triples. Their universal decomposition has an intersecting x-component of size at least seven. Every non-star triple there covers the path; any surviving internal contains C_y by the deletion, and every exterior triple contains C_y by uniqueness of the two-cover. The pair codegree cap permits at most two such additions, so the component has at most six members, a contradiction.

The residual row is

    sum_{U contains y} n_U - I_y + J_y <= 16-4=12.

The v4/v5 code gives coefficient zero exactly to internal traces through y that do **not** contain C_y; it gives coefficient one to all other residual incidences through y, including J_y. This is the displayed inequality. The v1/v3 row omits J_y, which is nonnegative, so it is a valid weaker consequence.

At a central anchor with `s_y>=8`, B4 makes K_y intersecting. It contains the four star triples and at most I_y internal triples. Each exterior extra contains C_y. At most `2-J_y` such extras are available because all J_y internal members consume the same global pair codegree in L_y, whether or not they occur in this K_y. Hence

    k_y<=4+I_y+(2-J_y)=6+I_y-J_y.

This proves the separate v4/v5 `internal-cover-cost` row

    sum_state lambda_state * 1[s_y>=8] * max(0,k_y-6)
      <= I_y-J_y.

For the actual state the assertion follows from the displayed inequality, and the zero cost at other states uses `I_y-J_y>=0`. The code reconstructs k_y as the fixed central degree four plus the two free pair counts involving y plus the free triple count. That equals the k_y identity above: these are exactly all residual members through y meeting the central anchor outside y. The index `row[4+f]` is the corresponding free singleton s_y in the seven-feature order.

All versions retain the weaker conditional cost `max(0,k_y-6)` on the right-hand-side resource I_y and take its maximum with the degree-specific lower bound 1, 4, or 5 above. Since each bound separately is at most I_y for the actual state, their maximum is at most I_y. The refined cover cost is correctly kept as a separate inequality with resource `I_y-J_y`; the code does not improperly subtract J_y from the independently proved degree-specific bounds.

## 6. Pruning, local selectors, and gluing

For each central anchor, let a local state be its seven free statistics as above, together with the computed costs. Before adding state variables the code prunes a state if one feature is outside the sum of the trace boxes in its bucket, or if an internal cost exceeds the sum of upper boxes for the relevant internal traces.

The actual state's feature is its actual bucket sum, with every n_U lying in its box. Its feature therefore lies between those sums of lower and upper boxes. Its necessary internal cost is at most actual I_y, which is at most the sum of the internal upper boxes. Thus the actual state survives both pruning tests. For the refined cover resource the generator does not perform additional pruning against `I_y-J_y`; retaining more states is safe. In v5 an increased C5 cost may prune more states, but the preceding proof shows it cannot prune an actual state.

Introduce a variable `lambda_{A,r}` between zero and one for each surviving local state r. The normalization is `sum_r lambda_{A,r}=1`. For each of the seven features f the equality is

    sum_{U : U intersect T = f} n_U
      = sum_r lambda_{A,r} * feature_f(r).

For a family F, set the variable of its actual state to one and all others to zero. The equality holds by the definition of the free exact traces. The internal-cost rows are

    sum_r lambda_{A,r} * cost_y(r) <= I_y,

and, in v4/v5, the separately justified cover-cost rows above. The cost proofs establish these for the chosen actual state. This supplies every box, inequality, and equality simultaneously.

The same n_U are used at all nineteen anchors. Hence any degree or internal incidence reconstructed from the trace coordinates is the same global statistic at every anchor; there is no independent choice of a neighbor degree at different anchors in the mapped family. Fractional state mixtures may have additional compatibility defects, which only weaken the model. Completeness here means **inclusion of every actual local state and every actual family**, not characterization of all feasible fractional solutions.

## 7. Exact objective certificates and weaker-v3 phase one

Write a rebuilt model as

    A z <= b,  E z = f,  l <= z <= u,

where z consists of all n_U and all local selectors. All displayed bounds and row coefficients are integers. Let c have coefficient one on every trace coordinate and zero on selectors. For nonnegative integer inequality weights y, arbitrary integer equality weights e, and a positive integer scale L, define

    q=A^T y+E^T e,  H=b^T y+f^T e.

Every feasible z satisfies `q.z<=H`, and its boxes give

    L*c.z <= H + sum_j max(l_j*(L*c_j-q_j),
                           u_j*(L*c_j-q_j)).

This is the `H+correction` formula in the objective receipts. It remains valid for arbitrary rounded weights once nonnegativity and the exact integer combination have been checked; numerical dual optimality is not a mathematical premise. For a mapped size-68 family, `c.z=49`. Strictly less than `49*L` excludes the case. Equality alone does not.

### The rebuilt v3 model is independently a valid relaxation

The phase-one producer explicitly imports `degree19_projection_v3.py`, reads the input receipt's case/empty/assigned/forbidden parameters, and rebuilds that model. An old receipt may have been generated from a different version. Such a mismatch prevents identifying the rebuilt matrices with the old matrices, but it does not invalidate the new v3 mathematical bridge or an independently checked certificate for those rebuilt matrices. The original numerical status 2 is only a trigger for the producer, not an imported infeasibility proof.

For identical case hypotheses, v3 is a weaker relaxation than v4/v5:

* v3's P5 row follows from the v4/v5 row by dropping the nonnegative J_y term.
* v3 drops all `internal-cover-cost` rows.
* v3's C5 cost is at most the v5 cost in every state; it does not activate the `k_y-5` cost at `d(y)>=16,s_y<8`.
* v3/v4 have the same local-state candidates before cost pruning. Every v5 survivor also survives the weaker v3 cost pruning. It can be identified by its seven features, with removed-state selectors set to zero when embedding a v5 point into v3.

The local normalization and seven-feature equalities are otherwise the same; the v3 boxes and all remaining rows are the same under the same case parameters. Thus infeasibility of v3 excludes any family satisfying the stronger models' hypotheses. More directly, Sections 1–6 map that family straight into v3, so the argument does not depend on transporting a numerical solution between versions. The v1 catalogue is still weaker because it omits the extra P5 high-degree filtering; v1 does not accept `forbidden` as an option and must only be compared with matching actual case restrictions.

### Exact phase-one certificate

The numerical phase-one problem appends `t>=0` and minimizes t subject to

    A z-t <= b,
    E z-t <= f,
   -E z-t <= -f,
    l<=z<=u.

To certify infeasibility of the original model, the checker takes nonnegative integer weights on all three inequality groups, combines the two equality-group weights as a signed vector e, and discards the artificial t-column. With q,H as above, original feasibility would imply

    sum_j min(l_j*q_j,u_j*q_j) <= q.z <= H.

Consequently the exact integer inequality

    G = H - sum_j min(l_j*q_j,u_j*q_j) < 0

is a contradiction. Every **original** coordinate, including every local selector, must be included in this box minimum. The artificial slack variable must not be included after its column has been discarded. These are the conventions in `degree19_phaseone.py`.

No particular sum of weights and no exact numerical phase-one minimum is needed for the final contradiction: any checked nonnegative source weights with a negative integer G suffice. The two signed equality contributions are legitimate because the original relation is equality. Rounding/clamping is a candidate-generation procedure; the exact recomputation of q,H, the boxes, and G supplies the arithmetic conclusion.

A usable replay must bind the rebuilt v3 source, imported `local43.py`, marker catalogue, case parameters, row order, complete boxes, and integer weights. `receipt_source_matches_rebuild=false` is an honest distinction between old and rebuilt models, not by itself a mathematical flaw. A negative gap computed only against unbound or differently ordered matrices would not establish the stated case. This note has not rerun or validated any particular saved gap.

## 8. Scope of the resulting proof step

Under the five hypotheses in Section 1, the construction above proves the needed family-to-model implication on an arbitrary finite ambient ground set. No positive minimum degree, support cutoff, fixed exterior universe, old mu42 bootstrap, or binary bound on proper traces is used. The point cap 19, size 68, H27, universal structural theorems, and each case restriction remain explicit dependencies.

The equality treatment in `Ysingle-equality-proof.md` is a separate argument: an exact residual bound of 49 forces a tight C5 row, symmetry transports the forced degree, the complete-C5 structure synchronizes P10 tails, and `doubled-P10.md` supplies the ensuing ordinary contradiction. Neither synchronized tails nor doubled-P10 isolation is silently encoded as a row in v1/v3/v4/v5. Likewise, a complete enumeration of internal assignments or exterior marker orbits and a proof that those cases exhaust all possible F are distinct from the bridge proved here.

The remaining certificate task is exact replay against the pinned matrices and boxes. The remaining global research task is to combine the applicable excluded cases and any equality arguments with a complete case-cover argument. This note supplies neither an end-to-end Lean theorem nor a global size-67 conclusion.
