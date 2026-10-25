# Insertable definitions and obligation-to-source map

Production source map, 24 October 2026. This file records definitions and completed evidence; it is not a review vote. The manuscript and source notes are unchanged. File names below are relative to `work/frontier20261023/highdegree/`, except for the explicitly named frozen prior. The frozen prior is `work/frontier20261020/prior-art68/repository/paper/main.tex`, commit `90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.

## Insertable definitions

**Families, links and neighbourhoods.** An SF\(r\) family is a finite simple \(r\)-uniform family with no three distinct members having equal pairwise intersections; the empty intersection is included. Its support consists of its used points. For a four-uniform family \(\mathcal F\), write
\[
d(x)=|\{A\in\mathcal F:x\in A\}|,\qquad
\Delta=\max_x d(x),\qquad
L_x=\{A\setminus\{x\}:A\in\mathcal F,\ x\in A\}.
\]
The symbol \(L_x\) always denotes the complete point-link. For an actual member \(Q\in\mathcal F\), put
\[
N_{\mathcal F}[Q]=\{A\in\mathcal F:A\cap Q\ne\varnothing\},\quad
N(Q)=|N_{\mathcal F}[Q]|,\quad
D_{\mathcal F}(Q)=\{A\in\mathcal F:A\cap Q=\varnothing\}.
\]
Thus \(Q\in N_{\mathcal F}[Q]\), and \(N_{\max}(\mathcal F)=\max_{Q\in\mathcal F}N(Q)\) is a scalar maximum of **closed** neighbourhood sizes. The complementary scalar is \(\mu(\mathcal F)=\min_{Q\in\mathcal F}N(Q)\). The disjointness graph has the members of \(\mathcal F\) as vertices and degree \(|\mathcal F|-N(Q)\) at \(Q\); these graph degrees differ from point degrees \(d(x)\). Sources: frozen prior, “Notation and the proof architecture,” lines 128–166; the pointwise bounds in `D16-complete-argument.md` and `LOW15-NO44-ordinary-closure.md` give the corresponding bounds on \(N_{\max}\).

**Exact singleton classes and anchor traces.** For \(Q\in\mathcal F\) and \(i\in Q\), the exact singleton class is
\[
\mathcal S_i(Q)=\{A\in\mathcal F:A\cap Q=\{i\}\},\qquad
s_i(Q)=|\mathcal S_i(Q)|.
\]
Its triple-tail family is \(\{A\setminus\{i\}:A\in\mathcal S_i(Q)\}\); its size is the same \(s_i(Q)\). This is an exact intersection condition, not the whole star at \(i\). Define \(p_{ij}(Q)\) by exact trace \(\{i,j\}\) and \(t_i(Q)\) by exact trace \(Q\setminus\{i\}\), and put
\[
S=\sum_{i\in Q}s_i,\qquad P=\sum_{\{i,j\}\subset Q}p_{ij},\qquad
T=\sum_{i\in Q}t_i.
\]
Simplicity makes the full-trace class on the actual four-set \(Q\) exactly \(\{Q\}\). Consequently
\[
N(Q)=1+S+P+T,\qquad \sum_{i\in Q}d(i)=4+S+2P+3T.
\]
The universal exact-class capacities are \(s_i\le10\), \(p_{ij}\le3\), \(t_i\le1\). Source: frozen prior, “Exact traces and the near-transversal argument,” lines 352–373.

**Residual families and four-hub traces.** After fixing a point \(x\) of degree \(d\), let
\[
\mathcal R_x=\{A\in\mathcal F:x\notin A\},\qquad r=|\mathcal R_x|=|\mathcal F|-d.
\]
At cardinality 68, \(r=68-d\). For a represented support \(W\), a trace variable counts *all* members of \(\mathcal R_x\) having that exact intersection with \(W\), including every exterior completion. The empty trace is retained and the sum of all trace counts is \(r\); only a four-point trace is binary by simplicity. No ambient support cutoff follows from using finitely many trace coordinates.

In the R16-deletion arguments, \(W=K\) is the four-hub set. Define residual counts \(s_i,p_{ij},t_i,q\) for exact traces \(\{i\},\{i,j\},K\setminus\{i\},K\), respectively, and set
\[
S=\sum_i s_i,\qquad P=\sum_{i<j}p_{ij},\qquad T=\sum_i t_i,
\qquad E_0=S+P+T+q.
\]
Here \(q\in\{0,1\}\) counts the possible residual member \(K\), and \(E_0\) counts residual members meeting \(K\). Their hub-incidence total is \(S+2P+3T+4q\); residuals avoiding \(K\) are allowed. These are residual counts, so the anchor identities with an added 1 or 4 do not apply to them. In particular, when \(x\cup(K\setminus\{i\})\) is an actual cone in a complete size-15 link, its neighbourhood is exactly \(15+E_0-s_i\). Sources: `D18-complete-argument.md`, “Necessary models and exact-certificate interface”; `LOW15-R15-outer-deletion-exclusion.md`, “Complete-link model and residual traces”; `LOW15-R15-hub-deletion-exclusion.md`, “Residual hub traces and actual anchors.”

**Literal canonical families.** A string such as \(012\) denotes \(\{0,1,2\}\). On six distinct points,
\[
P_{10}=\{012,015,023,034,045,124,134,135,235,245\}.
\]
Write \(P_9\) and \(P_8\) for one-block and two-block deletions from \(P_{10}\). The two \(P_8\) omission types are distinguished by intersection size 1 or 2 of the deleted blocks. Representatives are \(P_{10}\setminus\{034,135\}\) and \(P_{10}\setminus\{012,015\}\), respectively. The latter has unique two-cover \(\{3,4\}\).

For four distinct hubs \(K=\{u,v,a,b\}\) and disjoint triads \(D,E\), all ten points distinct, define the canonical R16 family by
\[
R_{16}=\{\{u\}\cup P,\{v\}\cup P:P\in\tbinom D2\}
\;\cup\;\tbinom K3
\;\cup\;\{\{a\}\cup P,\{b\}\cup P:P\in\tbinom E2\}.
\]
For \((u,v,a,b)=(0,1,2,3)\), \(D=\{4,5,6\}\), \(E=\{7,8,9\}\), its sixteen literal triples are
\[
\{012,013,023,045,046,056,123,145,146,156,278,279,289,378,379,389\}.
\]
The four triples in \(\binom K3\) are *hub triples*; the other twelve are *outer triples*. For an SF3 family \(L\), put
\[
\rho(L)=\max_{A\in L}|\{B\in L:A\cap B=\varnothing\}|.
\]
The universal R16 theorem classifies the domain \(|L|=16,\rho(L)\le7\) as this canonical family. The size-15 theorem with \(\rho(L)=7\) gives a single deletion from this family. Sources: frozen prior, “The canonical ten- and eight-member families,” lines 206–226, and “The universal sixteen-link classification,” lines 443–462; `LOW15-R15-rho7-classification.md`, theorem and display (R); `D16-I8-deletion-cover-reconstruction.md`, “Why exactly eight literal models suffice.” The sixteen-item list above is the direct expansion of (R), with the stated relabelling.

**Component sums and permitted Q8 sharing.** Let \(I_j\) denote an intersecting SF3 family of size \(j\). In the high-link decompositions below, \(\sqcup\) means both a disjoint union of triple families and **disjoint supports**:
\[
\begin{array}{c|l}
|L|&\text{complete-link alternatives}\\\hline
17&P_{10}\sqcup I_7\quad\text{or}\quad P_9\sqcup I_8\\
18&P_{10}\sqcup I_8\quad\text{or}\quad P_9\sqcup P_9\\
19&P_{10}\sqcup P_9\\
20&P_{10}\sqcup P_{10}.
\end{array}
\]
This follows from the universal maximality/high-link lemma (frozen prior, lines 612–635). It does not impose full support separation on every lower-degree B4 partition.

Specifically, on seven distinct points,
\[
Q(h,k;U;\ell,m)=\{\{h\}\cup e,\{k\}\cup e:e\in\tbinom U2\}
\cup\{\{h,k,\ell\},\{h,k,m\}\},\qquad |U|=3.
\]
Its core is \(\{h,k\}\cup U\), and its leaves are \(\ell,m\). In a size-16 \(I_8+I_8\) B4 partition, a \(P_8\) support is disjoint from the other support. For two \(Q_8\) parts, each core avoids the entire opposite support, while zero, one or two leaves may be shared. In a size-15 \(Q_8+I_7\) partition, the Q8 core avoids the I7 support, but a Q8 leaf may coincide with an I7 point \(v\) exactly when the residual point-link of \(v\) in I7 is intersecting. For the source catalogue \(H_0,\ldots,H_7\), the allowed vertices are none for \(H_0,H_1,H_3,H_4,H_5\), \(\{0\}\) for \(H_2,H_6\), and \(\{5,6\}\) for \(H_7\). This produces thirteen Q8/I7 gluings. Sources: frozen prior, “Isolation and a separated neighborhood,” lines 278–331; `D16-I8-deletion-cover-reconstruction.md`, “Why exactly eight literal models suffice”; `LOW15-A3-cover-independent-bridge.md`, “Every rho8 degree15 link is in the 8+7 domain” and “Exact ordinary criterion for a Q8 leaf gluing.”

**Cyclic graph and fibre notation.** The Andrásfai graph \(A_k\) has vertex set \(\mathbb Z/(3k-1)\mathbb Z\), with \(i\sim j\) when \(j-i\) modulo \(3k-1\) lies in \(\{k,k+1,\ldots,2k-1\}\). A graph homomorphism from the disjointness graph partitions actual members into fibres of masses \(a_i\); put
\[
b_i=\sum_{j\sim i}a_j,\qquad t_i=\#\{\text{actual }x\text{-star members in fibre }i\},\qquad
q_i=\sum_{j\sim i}t_j.
\]
Here \(q_i\) is a fibre star count and differs from the residual full-hub-trace count \(q\). The deviation variables are \(r_i=b_i-24\) in D16 and \(r_i=b_i-25\) in cap15; they differ from the residual cardinality \(r\). In D16 the surjective images have \(k\in\{3,4,5,6\}\), and
\[
0\le r_i\le3,\quad \sum_i r_i=24-4k,\quad
a_i=4+r_i+r_{i+k}+r_{i+2k-1}.
\]
In cap15, \(k=3\), so indices are modulo 8 and adjacency differences are 3,4,5; the direct Jin argument proves positivity of all eight fibres before using their lower adjacent-mass bound, and gives
\[
r_i\in\{0,1,2\},\quad \sum_i r_i=4,\quad
a_i=7+r_i+r_{i+3}+r_{i+5}.
\]
On an occupied star fibre, \(q_i\le r_i\). These are necessary homomorphism consequences; they do not assert that every permitted inter-fibre edge occurs. Sources: `D16-complete-argument.md`, “Graph representation”; `LOW15-direct-Jin-A3-addon.md`, complete argument; `LOW15-A3-star-fibre-reduction.md`, “The support of a degree15 star.”

## Obligation-to-source table

“Ordinary” below describes written mathematical arguments. A finite receipt marked PASS supplies exact executable evidence with its stated ordinary prerequisites; it does not mean Lean kernel verification or independent human certification. Imported I7/R16, H27, Jin, and guarded prior results retain their separate assurance boundaries.

| Obligation | Exact source and locator | Conclusion and assurance |
|---|---|---|
| Theorem 2: eliminate degree 1 in a hypothetical size-15 SF3 family with \(\rho\le6\) | `LOW15-R15-rho6-partial-status.md`, “Minimum degree and derived support bounds,” first paragraph; `R15-degree2-independent-ordinary-check.md`, “Ordinary motifs and why their normalization covers arbitrary support,” first paragraph | \(N_L[A]\ge9\) and the complete five-edge SF2 point-link exclude a degree-one point. Ordinary argument on arbitrary support. Only this completed paragraph is needed from the older partial note. |
| Theorem 2: degree 2 with a degree-6 neighbour | `R15-rho6-degree2-support-reduction.md`, “A degree-two point with a degree-six neighbour”; `R15-degree2-independent-ordinary-check.md`, “Ordinary motifs and why their normalization covers arbitrary support” and “Independent exact check”; `recheck_R15_degree2_support.py`; `R15-degree2-independent-check.json` | 91 normalized forced motifs, 6 surviving initial obstructions, and no admissible thirteenth triple. Three fresh labels cover every possible single additional triple. The independent receipt is PASS and reconstructs domains and literal witnesses without importing either producer. |
| Theorem 2: degree 2 without a degree-6 neighbour and whole-completion support | `R15-rho6-degree2-support-reduction.md`, “A degree-two point with no degree-six neighbour”; `R15-degree2-independent-ordinary-check.md`, “The whole-completion exterior bound” and “Independent exact check”; `recheck_R15_degree2_support.py`; `R15-degree2-independent-check.json` | 78 normalized motifs, 18 survivors. Every admitted new-point triple uses one fresh point and one old pair; the sum of remaining old-pair capacities is at most 3, bounding the whole completion to three new points. The independent implementation checks all 74,761 six-subsets, with zero completions. PASS; arbitrary-support normalization is supplied by the written bridge. |
| Theorem 2: support at most 11 and complete root cases | `R15-degree2-independent-ordinary-check.md`, “Eleven-point support and complete root cases”; `R15-rho6-degree2-support-reduction.md`, “Consequent support reduction” | After excluding degrees 1 and 2, \(I\ge60\), \(\sum d=45\), and \(I\le\sum_v(19d(v)/6-7)\) give support \(n\le11\). Degree at most 4 gives \(I\le225/4<60\). A complete root point-link is therefore two triangles, C5, or a triangle plus a two-edge path. Ordinary derived support bound. |
| Theorem 2: complete target-15 tree exhaustion and assembly | `R15-rho6-finite-closure.md`, “Literal mathematical target” and “Fresh exact producer and independent replay”; `search_r15_rho6.py`; `replay_r15_rho6_tree.py`; `R15-rho6-two-triangles-search.json.gz`, `R15-rho6-cycle5-search.json.gz`, `R15-rho6-triangle-path-search.json.gz`; `R15-rho6-two-triangles-replay.json`, `R15-rho6-cycle5-replay.json`, `R15-rho6-triangle-path-replay.json`; `R15-rho6-completed-evidence.md` | On the derived eleven-point universe, the initial residual domain is all 120 triples avoiding the root. The three independent replays report 3,657/5,109/3,455 nodes and 101,266/170,054/113,537 checked colour pairs, all PASS with zero solutions. The completed-evidence note combines the low-degree reconstruction with these fresh size-15 trees to conclude universally \(\lvert L\rvert=15\Rightarrow\rho(L)\ge7\). Ordinary computer-assisted proof; no size-16 exhaustion is transferred. |
| Exact-\(\rho=7\) classification | `LOW15-R15-rho7-classification.md`, theorem; “Eliminate H0,H1,H3,H4,H5”; “Eliminate H6”; “Eliminate H7”; “The six-core form for H2”; “One uv-triple”; “Two uv-triples” | Every size-15 SF3 family with \(\rho=7\) is R16 minus one triple. Written classification on arbitrary support, conditional on the complete I7 catalogue/mixed-trace obstruction imported from frozen prior lines 465–529 and the ordinary H2 shape reduction at lines 574–611. It makes no \(\rho\le6\) classification assumption. |
| Exact-\(\rho=7\): outer deletion impossible as a complete cap15 link | `LOW15-R15-outer-deletion-exclusion.md`, “Complete-link model and residual traces,” “Four actual neighbourhood inequalities,” and “Singleton capacities at the actual hub anchors”; `LOW15-R15-hub-exclusion-independent-check.md`, “Outer deletion” | Under complete-link, cap15, \(\mu\ge41\), and singleton cap8 hypotheses, the four actual hub anchors and residual budget give \(3S+4P+4T+4q\ge104\), \(S+2P+3T+4q\le37\), hence \(2P+5T+8q\le7\). Exact singleton capacities finish all cases. Ordinary incidence proof; no finite support census. |
| Exact-\(\rho=7\): hub deletion impossible as a complete cap15 link | `LOW15-R15-hub-deletion-exclusion.md`, “Residual hub traces and actual anchors,” “The neighbourhood lower bound on the satellite triangle,” “Literal B4 equality guard for the complete five-star,” “Every satellite pair capacity must be strict,” and “The one-unit contradiction”; `LOW15-R15-hub-exclusion-independent-check.md`, its two “Hub deletion” sections | Only the three surviving actual anchors are used. The B4 guard \(b_i+p_{ij}=8\Rightarrow p_{ik}+T-t_i+q=0\) retains \(p_{0i}\). Strict satellite capacities give \(Y\ge9-3t_0\) against \(Y\le8-3t_0\). Ordinary arbitrary-support proof, with an independent written reconstruction; no numerical feasibility claim. |
| D16: geometric cover domain and arbitrary exterior transfer | `D16-I8-deletion-cover-reconstruction.md`, “Why exactly eight literal models suffice,” “Arbitrary exterior points are retained,” and “The raw12 cases have an actual-family bound10”; `replay_d16_i8_deletion_covers.py`; `D16-I8-cover-independent-replay.json`; `D16-complete-argument.md`, “Arbitrary-support cover capacities and nonindependent stars” | Eight literal I8+I8 models include shared Q8 leaves. All 5,576 deletions of size at most 3 are checked; PASS. At least 13 remaining triples force every ambient four-cover to use at least three support points. Simplicity and triple codegree2 give \(2\lvert C_3\rvert+\lvert P_4\rvert\); six raw-12 cases have the written pair-incidence bound10. Actual capacities are \((1,2,4,10)\). |
| D16: independent star support and the fibre inequality | `D16-I8-full-quasi-transversals.md`, “The full four-transversal is unique”; `D16-fibre-independent-preparation.md`, “Current ordinary interface and its exact scope” and “Exact down-set inequality”; `D16-complete-argument.md`, “Graph representation” | An independent star support lies in a cyclic \(k\)-window of mass at least24 and supplies at least8 nonstar full covers, contradicting the bound1. For nonindependent support, actual cone sets \(D_i\) give \(\sum_{j:D_j\subseteq D_i}(a_j-t_j)\le c_{q_i}\) when \(q_i\le3\). Inclusion is of occupied-neighbour sets, while \(q_i\) counts their full multiplicities. Ordinary bridge. |
| D16: complete nonindependent fibre enumeration | `D16-fibre-independent-preparation.md`, “Different star enumeration”; `d16_fibre_reconstruction.cpp`; `replay_d16_fibres.py`; `D16-fibre-k3-independent.json`, `D16-fibre-k4-independent.json`, `D16-fibre-k5-independent.json`, `D16-fibre-k6-independent.json`; `D16-complete-argument.md`, “Arbitrary-support cover capacities and nonindependent stars” | The first occupied image edge partitions all nonindependent star vectors. Profile counts are 543/1,541/103/1 and star counts 33,912/87,790/2,621/0 for \(k=3,4,5,6\), with zero unresolved. All four receipts say PASS and `complete_conditional_k_exclusion: true`. Combined with the ordinary independent-support argument, this excludes \(\Delta=16\) under the assembly's named inputs, including actual degree16 existence and guarded R61. |
| Cap15: neighbourhood and actual degree15 prerequisites | `LOW15-NO44-ordinary-closure.md`, “Statement and dependency order,” “The four profiles and the literal obstruction,” and “The rho7 theorem excludes both patterns”; `LOW14-NO43-ordinary-closure.md`, “Cross-star contradiction” and “Independent graph step: N43 must exist under cap14”; `LOW15-complete-argument.md`, “Precise statement and upstream imports” | The acyclic no-P10, N45, no-P9, excluded-P8 and guarded exact-rho7 route gives singleton cap8 and \(N_{\max}\le43\) at cap15. The separate cap14 exclusion then supplies an actual degree15 point. These conclusions retain the named H27, B4/isolation, I7, HP15/crowding and Jin dependencies. |
| Cap15: direct A3 image and correct positivity order | `LOW15-direct-Jin-A3-addon.md`, entire argument | Apply Jin directly at \(k=3\): \(25\cdot11>4\cdot68\). With possibly empty fibres, \(b_i\le27\), \(e_i=27-b_i\ge0\), and \(\sum e_i=12\); then \(a_i=13-e_i-e_{i+3}-e_{i+5}\ge1\). Only now use \(b_i\ge25\), obtaining the stated \(r_i,a_i\) identities. Ordinary replacement of the frozen notes' initial k=4/empty-fibre route; later star and cover arguments are unchanged. |
| Cap15: star-support analysis and demanded cover counts | `LOW15-A3-star-fibre-reduction.md`, “The support of a degree15 star” and “Concrete one- and two-deletion requirements”; `LOW15-A3-cover-independent-bridge.md`, “A3 arithmetic and the star support” | Independent support requires at least10 actual full covers. Every nonindependent support is, up to symmetry, \(\{0,1,2,3\}\) with sole edge \(\{0,3\}\), endpoint weights 1 or2, and both interior weights at least4. Deleting an endpoint's actual cones gives at least11 covers for one deletion or12 for two. Ordinary graph argument permitting missing inter-fibre edges. |
| Cap15: complete rho8 gluing domain | `LOW15-A3-cover-independent-bridge.md`, “Every rho8 degree15 link is in the 8+7 domain” and “Exact ordinary criterion for a Q8 leaf gluing”; `replay_low15_eight_seven_covers.py`, `I7_TEXT`, `SAFE_LEAVES`, and `models()`; `LOW15-complete-argument.md`, “Exclude rho=8 by A3 and independently reconstructed cover bounds” | B4 and I8/I7 classification yield I8+I7. The excluded P8 omission-intersection1 type leaves eight separated P8-i2/I7 models plus thirteen Q8 gluings. The ordinary leaf criterion proves the complete gluing domain without a support cutoff. The selected reconstruction has 21 models; the older bridge's enlarged 29-model domain is not its case count. |
| Cap15: arbitrary-support cover bound, finite completion, and branch conclusion | `LOW15-A3-cover-independent-bridge.md`, “Arbitrary-support covers and exact capacity reductions”; `replay_low15_eight_seven_covers.py`; `LOW15-eight-seven-cover-independent-replay.json`; `LOW15-complete-argument.md`, “Exclude rho=8 by A3 and independently reconstructed cover bounds” and “Completed finite evidence and remaining assurance boundary” | The independent deletion-first reconstruction checks all \(21(1+15+105)=2,541\) cases. PASS; raw maxima of \(2\lvert C_3\rvert+\lvert P_4\rvert\) are 2/4/10 for deletion sizes 0/1/2, with no incidence correction needed on this selected domain. Thirteen surviving triples force at least three support points in every ambient four-cover, so exterior completions are covered by triple codegree2. The maxima contradict demands 10/11/12. With the separate \(\rho\le6\) and exact-\(\rho=7\) exclusions, this closes cap15 conditionally on the named imports. |

## Evidence-status and literal checks performed for this map

The older preparation/reduction files retain their original “not yet run” paragraphs. Completion is recorded by `R15-rho6-completed-evidence.md`, `D16-complete-argument.md`, `LOW15-complete-argument.md`, and their named PASS receipts. Those earlier paragraphs describe the date of preparation, rather than the current completion state. The direct Jin add-on replaces only the initial cap15 image argument.

This source-map task inspected the five requested completed notes and the pointers named above. Read-only checks matched 25 current source/tree/bridge/receipt hash bindings: the three independent low-degree/cover sources, all three size-15 trees and their checker, and the four D16 receipts' independent source, cover checker, ordinary bridge and cover receipt. Two additional literal checks confirmed the displayed R16 list equals the parameterized 16-triple construction and the displayed P10 has ten blocks, point degrees5 and pair codegrees2. All 27 checks matched. No producer, proof-tree replay, fibre census or review-output inspection was run for this editing task.
