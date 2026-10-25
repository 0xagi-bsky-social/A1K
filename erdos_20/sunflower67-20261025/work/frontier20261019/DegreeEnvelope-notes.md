# Degree selection and quadratic envelopes

All nine declarations in `lean/DegreeEnvelope.lean` elaborated successfully with the pinned Lean 4.26.0 runtime via the shared serialized compiler. This does not establish a clean replay of the A1K/mathlib cache.

- `exists_top_two`, `exists_top_three`, `exists_top_four`: arbitrary finite support and natural weights; no upper bound or positivity hypothesis required. The final selected value bounds all values outside the earlier selected points.
- `degree_envelope`: arbitrary finite exceptional set E contained in s, positive natural weights on s, and integer D bounding the remaining weights. It proves the falling-square upper bound using exact integer subtraction.
- `envelope_three`, `envelope_four`: specializations to E={x,y} and E={x,y,z}, matching the intended top-degree arguments.
- `sum_falling_eq_square_sub`: the exact identity converting the falling-square sum to square sum minus degree sum.
- `support_degree_pos`, `support_degree_sum`: reusable support incidence bridges for arbitrary finite uniform families.

All printed roots depend only on the allowed foundational axioms propext, Classical.choice, Quot.sound (the purely algebraic sum identity requires only propext and Quot.sound). Parent root must include these roots in its fail-closed environment audit before assigning the axiom-audited assurance grade.

The exact stable source SHA-256 is `f0f0aa819f803d5b01a647289700686a82116474fe71e53a6cf4d14370c9fb01`. Compiler receipt: `logs/DegreeEnvelope.json`; exit code 0, source_stable true.

For support56 assembly, specialize envelope_three to w=degree F and s=support F. Rewrite with sum_falling_eq_square_sub and support_degree_sum F 4 hu, then use F.card=28. If n>=57 and c=w z>=0, then c*(112-n)<=55*c. The support53 assembly is identical with envelope_four, d=w t, n>=54 and d*(112-n)<=58*d.
