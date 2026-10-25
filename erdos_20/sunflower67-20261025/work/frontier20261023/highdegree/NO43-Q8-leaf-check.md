# Independent ordinary check of the NO43 terminal step

23 October 2026. This is a bounded proof-development check, not a final audit
or a new verification of the imported classification/cross-star certificates.
No LP, Lean build or finite-support search was used.

The argument in `LOW14-NO43-ordinary-closure.md` correctly excludes every
N43 anchor in the following domain: a simple SF4 family, mu>=41, global
degree at most14, exact singleton counts at most8, and the ordinary
common-triangle core reduction in `LOW14-Wagner-research.md`. The I8
classification, P8/Q8 isolation, B4 and the actual cross-star theorem are
explicit imports. The common-triangle reduction is an arbitrary-support
argument, not an assumption that the whole family has seven-point support.

## The point where Q8 needs more than core isolation

For R of size4 and the derived exterior triangle T, fix i in R. The near
part K_i of its triple link consists of R minus i and five triples j union e,
where j belongs to R minus i and e is an edge of T. The eight far triples
D_i avoid R. Triple codegree at most2 implies that each edge of T occurs
at most twice among those five near triples. The three multiplicities are
therefore2,2,1. Thus every t in T belongs to at least three near triples.

The graph obtained by removing t from these near triples is simple and
bipartite, on (R minus i) and (T minus t). Each vertex has degree at most2:
this also follows directly from the triple codegrees of {i,t,j} and
{i,t,u}. A bipartite graph with at least three edges and maximum degree2
has a two-edge matching. Otherwise its edges would be pairwise intersecting;
three distinct pairwise intersecting graph edges form a triangle or a
three-edge star, both excluded here.

If D_i is P8, isolation already puts its whole support outside K_i. An
exceptional deleted P10 block would avoid R minus i and therefore be far,
so cannot be a member of K_i. If D_i is Q8, its five-point core is outside
K_i for the same reason: either exceptional hub-plus-two-leaves triple
also avoids R minus i. Since K_i uses all of (R minus i) union T, this
puts both Q8 hubs outside R union T.

Suppose a Q8 leaf were t in T. Its actual far triple is {t,h,k}. Add the
two actual near triples whose remainders after deleting t are disjoint.
Those remainders lie in (R union T) minus {i,t}, whereas h,k lie outside
R union T. The three triples have pairwise intersection exactly {t}.
Their lifts are three distinct actual four-sets with common intersection
{i,t}, a forbidden sunflower. Hence the Q8 leaves also avoid T.

Consequently every far triple D_i avoids the entire seven-point core.
This supplies the leaf-separation step which core isolation alone would
not supply, without assuming that different far supports are disjoint.

## The imported cross-star guard is actually satisfied

Choose any actual pair-core member B={k,l} union e and let i,j be the
complementary root points. B lies in R union T, avoids i,j and is disjoint
from every triple in D_i and D_j. If U in D_i and W in D_j were disjoint,
then {i} union U, {j} union W and B would be pairwise disjoint actual
four-sets. Thus D_i,D_j are cross-intersecting.

Both families are intersecting SF3 of size8; their distinct centres i,j
lie outside both supports; all sixteen lifts belong to the same F. These
are the precise source guards. The cross-star theorem gives an actual
anchor C with

    N[C] <= d(i)+d(j)-d(i,j)+4 <= 14+14-1+4 =31 <41.

Here d(i,j)>=1 because R itself is actual. Its weaker HP15 consequence
would also suffice. The source is the frozen prior paper, lines968--1024;
classification/isolation/B4 are at lines188--331, and the universal
point/pair/triple degree caps at lines333--350.

## Scope and source boundary

I also checked the three ordinary common-triangle reductions (0,2,3),
(1,1,3), (1,2,2). The crucial last case uses Hall's condition for two
two-edge categories and one singleton: a star with at least three edges
has distinct representatives and makes a sunflower; a star with at most
two edges repeats the singleton edge three times. Triangle supports then
propagate along the four-cycle of size-two categories. This does not rely
on the nine-orbit census.

This check establishes the stated local NO43 contradiction. The separate
Jin/Wagner argument proving that some N43 anchor must exist is not needed
for this local lemma. It is supplied in the companion ordinary-closure
note and remains dependent on the imported graph theorem. No global67
conclusion or end-to-end Lean claim is made here.
