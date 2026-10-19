# Independent physics-route review

Reviewer verdict (19 October 2026): **accept the restricted raw-D reflection-positivity obstruction**. This is not a proof or disproof of C1, and is not a no-go theorem for every QFT representation. No claim about the recent singular-configuration paper is certified by this review.

## Formal-English obligations and correspondence ledger

For arbitrary real numbers t,s, define K(t,s) to have rows (1,1,1), (1,1,t), (1,t,s).

- **RP1:** det K(t,s) = −(t−1)². Expand the 3×3 determinant; s cancels. Lean: `Atiyah.ReflectionObstruction.det_kernel`.
- **RP2:** For v=(s+1,−(s+1),2(t−1)), vᵀK(t,s)v = −4(t−1)². Expand the quadratic form. Lean: `negative_witness_identity`.
- **RP3:** If t≠1, K(t,s) is not positive semidefinite. Its quadratic form at v is strictly negative by RP2. Lean: `not_posSemidef`.

These are standalone real matrix statements. They neither define the normalized Atiyah determinant nor formalize Schwinger distributions, test-function localization, or geometry. `lake build Atiyah.ReflectionObstruction` passes; a dedicated transitive axiom audit passes for all 7 imported project declarations, allowing only propext, Classical.choice, and Quot.sound. These checks ran on the working tree based on commit `3ae821c2eaa9a03c7df62477b435515be19a4c31`; the integrating agent must run the whole-library audit and report the final checked commit.

## Normalization and geometric realization

The side-length formula in PHYSICS_ROUTES is consistent: dividing the three-point determinant `8uvw + (−u+v+w)(u−v+w)(u+v−w)` by `8uvw` gives the stated D₃. Strict triangle inequalities imply D₃>1, and the equilateral value is 9/8. For collinear distinct triples at least one triangle factor vanishes, giving 1. Bou Khuzam–Johnson use pair determinant 2u and hence three-pair product 8uvw. Their lift normalization does not mean their determinant is the dimensionless D used here. Source: https://sigma-journal.com/2014/070/sigma14-070.pdf (Section 1, pages 2–3); direct journal PDF retrieval confirms At₂=2u and At₃=uvw[6+2(cos A+cos B+cos C)].

There is no realizability problem hidden in the three test configurations. With reflection θ(x,y,z)=(−x,y,z), take a=(1,0,0), b=(1,1,0), c=(1,−1,0). All are in the strict positive half-space; b≠c; every union θAᵢ∪Aⱼ consists of distinct points. The triangle θa,b,c is noncollinear. The two off-diagonal three-point entries agree because D₃ is real and depends only on the three side lengths. The four-point diagonal is a reflected-pair configuration and is real under the usual conjugation-under-reflection symmetry. More strongly, any proposed positive kernel must already have real diagonal entries, so no global reflection-invariance assertion for general complex Dₙ is needed for the contradiction.

## The point-kernel and distributional caveat

The point matrix is a necessary condition if the hierarchy is being proposed as ordinary continuous correlation functions away from collisions, with scalar bosonic fields, the standard reflection adjoint, and the constant observable included. A distribution-valued OS axiom does not literally permit delta functions as test functions. To bridge it, use real nonnegative smooth unit-mass bumps near a,b,c, all with compact support in the positive half-space, and the symmetrized product bump near the pair (b,c). The degree-zero test is 1. Keep these neighborhoods disjoint and away from the plane. Every reflected product support then stays away from collision diagonals. The smeared 3×3 Gram entries converge to the displayed point entries by continuity, including the degree-four entry. A strictly negative determinant therefore persists for sufficiently small neighborhoods, contradicting OS positivity. Contact terms supported on collision diagonals cannot change these entries. This is a mathematical argument, not a Lean-checked statement here.

Including the empty configuration is essential to this particular 3×3 witness. Conventional full OS positivity includes the degree-zero component (the identity/vacuum), so that use is legitimate. A different proposal that only tests one fixed particle-number sector is not refuted by this cross-degree witness. Similarly, arbitrary degree-dependent normalizations can change the displayed matrix and are outside its scope. Normalization factors that merely rescale each test vector by a nonzero scalar produce congruent Gram matrices and cannot remove a negative direction.

## Remaining physics routes

The Gram/coherent-state route correctly distinguishes semidefiniteness from independence. The wedge/determinant identity uses an orthonormal basis of Sym^(n−1)(C²); a raw monomial coefficient basis generally contributes a fixed metric determinant factor. Weighted diagonal dominance is sufficient, not necessary. Orthogonality of the ordered collinear monomials holds in the SU(2)-invariant metric, but a quantitative neighborhood theorem still needs a genuine perturbation estimate.

The Nahm comparison does not supply an unproved phase or positivity theorem: strict accretivity is explicitly an additional sufficient condition. Under Q→QV with diagonal unitary V, choosing U→UV gives V†(MU)V, so the phase-gauge assertion is correct.

The tensor-network discussion correctly warns that a Berezin integral is not a positive measure and that symplectic contractions do not automatically give Hermitian Gram forms. Reflection symmetry is a hypothesis to exploit, not a factorization proof. All three routes remain research programs; the note does not mistake any of them for an independence theorem.
