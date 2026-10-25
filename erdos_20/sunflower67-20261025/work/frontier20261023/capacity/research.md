# Two simultaneous augmentations of a glued sunflower-free Sperner family

Working research note, 2026-10-23. Final specialist review, Chief/Alpha/Beta audit, and publication are closed. This is a candidate mathematical advance supported by two exact local diagnostic programs; it is not a Lean theorem, independently reproduced result, or certified global novelty claim.

## Statement and convention

A three-sunflower consists of three distinct sets with equal pairwise intersections; the common intersection may be empty. A family is Sperner when no two distinct members are comparable by inclusion. Let g(n) be the maximum size of a three-sunflower-free Sperner family on n points. Write μ₃ = limsup g(n)^(1/n). If a different upstream convention uses the maximum over all sunflower-free families, the same lower bound applies, since our witnesses are Sperner.

The explicit family C below has 252271 members on 28 points, is Sperner, and has no three-sunflower. At its two distinguished coordinates its counts (N00,N01,N10,N11) are (33948,64728,64728,88867). Iterated complementary-coordinate gluing therefore gives

μ₃ ≥ (64728 + sqrt(3016856916))^(1/26).

Exact rational comparison shows this base is strictly between 1.56785134269 and 1.56785134270, and is larger than (1127 + sqrt(925536))^(1/17), the prior base being compared. Attribution and current literature priority must be checked by the parent research task before calling this a new record. This is a lower bound for nonuniform families as the ground-set size grows, not a four-uniform upper bound, and not a proof of the Erdős–Rado sunflower conjecture.

## Seeds and explicit construction

Coordinates of F are the ten edges of K5 in lexicographic order: 01,02,03,04,12,13,14,23,24,34. Its 75 members are the five four-edge stars; the ten K(2,3) edge sets; and the sixty complements of trees with degree sequence (3,2,1,1,1). Equivalently the last trees have edges vw,wt,vz,vz′ with v,w,t distinct and z,z′ the remaining vertices.

The 121-member seed H lives on Z/11Z. It consists of the distinct affine images aS+b with a in {1,3,4,5,9}, b in Z/11Z, and S one of {0,1,2,3,4,5,6}, {0,1,2,3,4,6,7}, {0,1,2,6,9}. The finite seed checks recorded below prove computationally that F and H are Sperner and three-sunflower-free. The punctured sets h\{0} are all nonempty, distinct, and pairwise intersecting, including across the two classes h∋0 and h∌0.

For bitmasks, erase(s,p) deletes bit p and shifts subsequent coordinates down by one; insert_zero is its inverse with a zero bit at p. On the nine F coordinates other than edge 03 (coordinate 2), define A by the fifteen decimal masks

118, 223, 251, 253, 319, 333, 379, 403, 445, 446, 478, 487, 491, 494, 501.

These are the fifteen augmenting sets in the checked upstream one-branch seed. Here they are explicit data rather than an assumed theorem. A is Sperner and three-sunflower-free; no a in A is contained in any punctured F member; and two distinct members of A together with any punctured F member never have equal pairwise intersections. The recorded small exhaustive check verifies all three statements.

Attach separate copies H₂,H₃ at F coordinates 2=03 and 3=04. Retain the other eight F coordinates, followed by the ten nonzero coordinates of H₂, then the ten nonzero coordinates of H₃. For f in F let f° be its eight-coordinate restriction. Let H_v = {h\{0}: h in H, 1_(0∈h)=v}. The base family consists of

(f°, h₂, h₃), with h₂ in H_(1−f₂), h₃ in H_(1−f₃).

There are 250659 such members. Let A₂=A. Let A₃ be obtained by inserting zero at F coordinate 2, permuting K5 vertices 3 and 4, and deleting F coordinate 3. The family E₂ consists of (a°, ∅, h₃), a in A₂, h₃ in H_(1−a₃). The family E₃ consists of (a°, h₂, ∅), a in A₃, h₂ in H_(1−a₂). Each has 806 members. Set C=base∪E₂∪E₃. All three pieces are disjoint because the H traces are nonempty. The two retained port coordinates are original F edges 01 and 02, now coordinates 0 and 1.

## General complementary-coordinate gluing lemma

If U and V are Sperner and three-sunflower-free on disjoint sets with distinguished coordinates u and v, form U⋆V from all punctured unions U′∪V′ whose deleted bits are complementary. Then U⋆V is Sperner and three-sunflower-free; the representation by a compatible pair is injective.

Proof: distinct members of a Sperner family cannot have identical punctures, so the representation is injective. If one glued set is contained in another, containment in each punctured block holds. A strict comparison in the U block can avoid violating the original Sperner property only when its deleted bits are 1 then 0; the complementary V bits are then 0 then 1, which makes the V comparison violate its Sperner property. This excludes strict containment.

For a sunflower triple in the glued family, each punctured block has equal pairwise intersections. Adding back its distinguished bit preserves that equality unless exactly two of the three bits are 1. In a Sperner, three-sunflower-free family, any triple, repetitions permitted, with equal pairwise intersections must consist of three identical members: three distinct members are forbidden, while exactly two identical members would be contained in the third. The two complementary bit triples cannot both have exactly two ones. Thus one restored block triple consists of three identical sets; its bits are constant, so the other block also has constant restored bits and consists of three identical sets. The alleged glued triple is constant, contradicting distinctness. ∎

## Single-branch augmentation lemma

Let F,H be as above, attach at x and y, and suppose all punctured H members are nonempty and pairwise intersecting. Let A be a Sperner, sunflower-free family on the punctured F ground set. Assume (i) no member of A is contained in any punctured F member, and (ii) two distinct A members and any punctured F member never form a three-sunflower. Then (F⋆H)∪A is Sperner and three-sunflower-free, where members of A have empty H block.

Proof: inclusion from a base member into A is impossible by nonempty H block, while inclusion from A into a base member is excluded by (i). Inside either piece the property holds. A triple with one A member and two base members cannot be a sunflower, since the H-block intersection of those base members is nonempty, whereas either intersection with A has empty H block. A triple with two distinct A members and one base member is excluded by (ii). The all-base and all-A cases are already excluded. ∎

## Simultaneous-augmentation union lemma

The individually augmented two-branch families base∪E₂ and base∪E₃ are obtained by applying the preceding single-branch lemma and then gluing the other H copy. Hence each is Sperner and sunflower-free. It remains to inspect comparisons or triples using both E₂ and E₃.

An E₂ member has empty H₂ block and nonempty H₃ block; an E₃ member has nonempty H₂ block and empty H₃ block. Neither can contain the other. For a triple meeting both E₂ and E₃, if the third member lies in the base, its H₂ intersection with the E₃ member is nonempty, while the E₂–E₃ intersection has empty H₂ block. If the third member lies in E₂, the two E₂ members have nonempty H₃ intersection, while their intersections with the E₃ member have empty H₃ block. The case of a third E₃ member is symmetric. The pairwise-intersecting punctured H property proves every claimed nonemptiness, even when two traces coincide. Thus no such triple is a sunflower. This proves the asserted properties of C. ∎

## Transfer matrix and the asymptotic lower bound

For a family with two ordered ports, let W=[[N00,N01],[N10,N11]]. A complementary gluing identifies the right port bit of one block with the complement of the left port bit of the next, then deletes both coordinates. If J=[[0,1],[1,0]], the port-count matrix after k blocks is W(JW)^(k−1). Here T=JW=[[64728,88867],[33948,64728]]. All entries are positive. The number of members after k blocks is the sum of entries of W T^(k−1), on 28k−2(k−1)=26k+2 points. The gluing lemma supplies sunflower-free Sperner witnesses at every k. T has eigenvalues 64728±sqrt(88867·33948); positivity, or its explicit two-by-two diagonalization, gives exponential growth rate ρ=64728+sqrt(3016856916). Taking the (26k+2)-th root and letting k tend to infinity proves μ₃≥ρ^(1/26).

## Exact improvement, without reliance on floating point

Take p=156785 and q=100000. The saved exact check verifies

p^26−64728q^26>0,
3016856916q^52−(p^26−64728q^26)^2>0,
p^17−1127q^17>0,
(p^17−1127q^17)^2−925536q^34>0.

Consequently the new base is >p/q=1.56785, whereas the prior expression (1127+sqrt(925536))^(1/17) is <p/q. The same integer inequalities at denominators 10^11 establish the displayed tight interval. The two positive integer margins are retained verbatim in verify_structural28.result.json.

## Saved evidence and limitations

The literal sorted witness is candidate28.masks, SHA-256 9a4e625eaf4dabb5f10ab73db1e081e629b803c356d7b90939acd0634a3f4f54. It uses the 28-coordinate convention above. candidate28.rectangles.json records its 105 Cartesian-product rectangles.

verify_structural28.py reconstructs the seeds and augmentation independently of project imports, checks the small hypotheses, reassembles the literal witness, confirms disjointness/cardinality and port counts, and checks the exact integer comparisons. Its saved result is PASS. It depends on the mathematical lemmas written here for the full-size sunflower conclusion.

verify_rectangles_resume.py uses a different, factorized exhaustive method and no project imports. Its saved PASS covers all 11025 ordered rectangle pairs, all 198485 unordered rectangle triples with repetition, and all 27 block-state triples. It also reconstructs 252271 literal members with the same witness hash, compares 180 random small cases against brute force, and rejects planted sunflower and empty-set containment controls. Its saved checker hash is 9aa7b3f6d550c13e6ee936d00eb96e75a4fc005a2609c4c6361fae5b42e79150. These two methods belong to the same AI workflow; they are not independent third-party replication.

Remaining obligations: inspect the factorized checker's mathematical completeness and source hashes; bind upstream source/version and definitions for the prior expression and seeds; complete the refreshed literature comparison before assigning novelty; obtain any desired Lean kernel replay or independent reproduction separately. No review/publication gate is opened by these diagnostics alone.
