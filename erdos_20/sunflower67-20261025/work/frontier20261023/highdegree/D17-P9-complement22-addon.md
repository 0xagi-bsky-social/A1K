# D17 v7: guarded P9 complement rows

23 October 2026. Discovery model addition only. No model import, construction,
solver execution, replay, final review or Lean process is claimed here.
The ordinary proof is `P9-disjoint-complement22.md`, independently developed
and checked by local_arithmetic. This implementation note records the exact
trace projection and the receiving-branch guards.

In a finite simple SF4 family with mu>=41 and global degree cap at most18,
suppose the complete x-link is H union K, where H is P9 on six points Y
and every K triple avoids Y. For every actual Q disjoint from {x} union Y,
the ordinary lemma proves |D(Q)|<=22. It retains the complete surviving
K' in D(Q), including all multiplicities. For k=0 it uses the complete-P9
bound20 with internal four-sets included; k=1,2 give20+k. For k>=3 the
common intersection has size at most1, and a common point gives at most
seven x-avoiders by HP15 applied to the copied H blocks plus one actual
exceptional transversal at a time. Pair codegree6 then gives16+k<=22.
No classification or point-degree bound on K is required. The two
complementary exceptional transversals are never asserted to form an
intersecting tail family together.

The v7 constructor preserves every v6 row. Its only new mathematical
rows apply when the literal Y component has nine blocks, the remaining
complete root-link triples avoid Y, and Q is among the fixed actual
members with Q intersect ({x} union Y)=empty. P10 branches receive no
new rows. On P9 branches every selected pure-Z internal member qualifies;
other selected members qualify exactly when this literal avoidance holds.
Unselected trace classes are not promoted to actual anchors.

Let r_Q count the prescribed root cones disjoint from Q and a_Q the
prescribed root cones meeting Q. With residual trace variables c_s,

    sum_(s intersect Q empty) c_s <=22-r_Q,
    -sum_(s intersect Q nonempty) c_s <=a_Q-46.

The second row is valid because |F|>=68 and |D(Q)|<=22 imply N(Q)>=46.
It is included separately because the relaxation does not impose a fixed
residual total. Both offsets subtract only prescribed root cones. Selected
residual actual members remain counted in c_s, so they are not subtracted
again. Every Q is fully represented, making its intersection with an
arbitrary-support residual member exactly its intersection with s. This
proves both row projections without an exterior-support bound.

Source provenance and replay scope:

* Parent constructor: `degree17_full_projection_v6.py`, SHA256
  `8f43465ef15e09ba5ea8f472a4382f844ccb3ebeface8841f7963625f65e8138`.
* New constructor: `degree17_full_projection_v7.py`. Its receipt source
  hash binds its exact bytes; both this note and the ordinary complement
  proof enter its existing source-hash dependency dictionary.
* HP15 retains its prior mu41/cap18 ordinary bridge and the saved prior
  finite replay provenance already bound by v6. No new certificate is
  being substituted for that import.
* v6 and all preceding constructors/replayers remain unchanged. A v7
  receipt requires a separately adapted replayer; an older replayer is
  not implicitly authorized to accept the new source hash or rows.

The addition is an exact necessary-condition projection under the stated
ordinary and imported premises. A future rounded dual would certify the
finite relaxation, with its own arithmetic replay still required.
