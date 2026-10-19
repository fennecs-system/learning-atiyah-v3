# Independent skeptical review: two separated fixed cores

Review status: mathematical argument and completed implementation independently reviewed. All four two-cluster modules independently compiled with Lean 4.19.0. An independent `scripts/check.sh` run completed successfully and audited 219 project declarations. This checked the working tree based on commit `3ae821c2eaa9a03c7df62477b435515be19a4c31`, including the then-uncommitted two-cluster modules; the final committed integration needs its own recorded audit.

## Exact acceptable statement

Fix distinct configurations A=(a_i) of size m and B=(b_j) of size k in R x C. Assume independence of each core's Atiyah point forms (equivalently, for every lift family, once lift existence and gauge invariance have been established). Fix u != 0. There is a threshold R0, depending on these fixed data, such that for every real R>R0 the points (a_i, R u+b_j) are distinct, admit displacement Hopf lifts, and their point forms are independent for every lift family.

This is conditional on both cores. Neither general C1 nor independence at every finite separation follows. Translating the second cluster preserves its internal directed differences. The theorem must retain the offsets b_j, rather than proving only coincident points R u.

## Boundary proof and necessary degree hypothesis

Write L=L_v and M=L_{Jv} for a nonzero Hopf lift v of u. These are independent linear forms, so a linear change of variables identifies them with X and Y. The limiting forms are L^k q_i and M^m r_j, where q_i and r_j are the core forms.

Each q_i is homogeneous of degree m-1 and each r_j is homogeneous of degree k-1. If a relation gives L^k Q=-M^m S, coprimality forces M^m to divide Q. Since deg Q <= m-1, Q=0; then S=0. Independence of the cores kills all coefficients. Equivalently, in L,M coordinates the first subspace has L-exponent at least k, and the second has M-exponent at least m; their common total degree is m+k-1, so their monomial supports are disjoint.

Degree control is essential here. Independence of arbitrary ambient polynomials q_i,r_j alone is insufficient: for m=k=1, choose q_1=M and r_1=L to obtain the same nonzero product LM in both blocks. Thus the distant-point boundary theorem's lack of a degree assumption cannot be copied into this two-core algebra lemma. Homogeneity must actually be established for the geometric point forms, not introduced as an additional geometric hypothesis in the final theorem. Empty cores require separate treatment or a carefully stated natural-number degree convention.

## Convergence and gauge obligations

For every cross pair use d_ij(R)=u+R^-1(b_j-a_i), which tends to u. A single local Hopf section near u handles all pairs eventually, including polar u. Reverse edges use the antipode. Actual cross-edge lifts are sqrt(R) times these local lifts, for R>0.

Normalize first-cluster point forms by (sqrt R)^k and second-cluster forms by (sqrt R)^m. Internal lifts remain fixed. Coefficient convergence follows from finite products. The finite-coefficient witness openness lemma is suitable and does not require a global norm on the whole polynomial ring. All tail conditions must be intersected before extracting one R0. Cross-collision avoidance follows from d_ij eventually nonzero; within-core distinctness is preserved exactly.

The conclusion must restore physical displacement lifts and transfer independence from the constructed family to every lift family via nonzero edgewise proportionality. Independence of one convenient normalized family is not yet the advertised configuration-level theorem.

## Newly found external claim: evidence and limits

Primary source inspected: Jan Eickhoff, *Singular Atiyah Configurations*, Zenodo v3, 28 September 2026, DOI https://doi.org/10.5281/zenodo.23024340. The initially supplied v2 record https://zenodo.org/records/22738747 explicitly links this newer version. Metadata and the complete v3 PDF were inspected on 19 October 2026. It is a preprint; this review does not certify its result or a community consensus.

Theorem 6.2 claims singular configurations along explicitly defined paths containing two coaxial m-point cyclic orbits and two axial groups. For fixed m>=1, u,d>0 and v>=0, it takes growing axial cardinalities a_N,b_N and radii R_N, with b_N->infinity, R_N->infinity, log R_N=o(b_N), and bounded a_N/b_N above the stated positive threshold. Theorem A includes m=1, yielding claimed planar examples with two off-axis points and many axial points.

The mechanism is concrete: cyclic Fourier blocks extend continuously to two collision limits, one with positive determinant. Axial elimination expresses the other determinant using four evaluations. A lower-row evaluation ratio is claimed to grow exponentially while the upper-row ratio grows at most linearly; opposite endpoint signs would then imply a distinct-point interior zero. An initial audit of the factor formulas, elimination determinant, and estimates through Section 6 found no decisive flaw. This is not a complete independent verification, an exact numerical certificate, or a Lean proof. Signs and complex-conjugation conventions still deserve direct symbolic and numerical checks.

If correct and connected to this repository's definitions, the preprint would refute universal C1. It does not refute the existing conditional distant-point theorem or the proposed fixed-two-core theorem: those assume independent fixed cores and assert a data-dependent tail, whereas the preprint's asymptotic family changes cardinalities and core geometry and uses colliding endpoint paths. No uniform separation threshold over growing cores is provided by either conditional result.

The project should distinguish "not proved in this repository" from an unqualified current-literature claim that general C1 is open. Treat this source as a claimed counterexample pending verification, retain conditional theorem labels, and do not infer either correctness or incorrectness merely from its conflict with the conjecture.

An independent 200-decimal-digit floating-point reproduction of the m=1 boundary elimination gives supporting numerical evidence. With u=d=1, v=0, b=N, R=N+2, x=sqrt(2)-1 and a=ceil((1+x)N/(2x)), at N=30 (a=52, total n=84) it gives A_beta/A_gamma approximately 5.3929843268 and B_beta/B_gamma approximately 2.9866900947, with all four evaluations positive. Hence the reproduced boundary formula is negative. N=10 gives a positive determinant, while N=60 and N=100 give negative values. This computation used the polynomial products and the truncated inverse-series elimination directly, without fitting asymptotic rates. It is floating-point evidence, not rigorous interval arithmetic, an interior singular configuration, or verification that the boundary formula equals a separately constructed physical matrix.


## Completed implementation review

Independently read and compiled `TwoClusterAlgebra`, `TwoClusterGeometry`, `TwoClusterLift`, and `TwoCluster` with the restored Lean 4.19.0 environment. All four compilations exited successfully. The final `two_cluster_extension` has exactly the fixed-core hypotheses and universal actual-lift conclusion above. It includes `Nonempty (LiftFamily pR)` and exact configuration coordinates, so neither lift-vacuity nor a merely normalized-family conclusion is present.

The algebra implementation proves a sufficient transformed `degreeOf 1 < m` bound directly from each core point form's number of linear factors. It therefore avoids asserting a separate unimplemented homogeneous-space basis equivalence. Only the first block needs that bound: once it vanishes, multiplication cancellation and second-core independence finish. The empty first-core branch is explicit, and empty second cores cause no gap. The invertible substitution is justified by a constructed left inverse; the antipodal determinant supplies its nonzero denominator. Local-section convergence retains both Hopf poles.

The full integration intersects incidence, separation, positive-R, and independence tails, restores the two different square-root powers k and m, transfers through the finite-index equivalence, and applies arbitrary-lift invariance. No extra geometric nonvanishing assumption is hidden in the final theorem. These are genuine conditional fixed-two-core results, not a proof of universal C1.

## Independent exact boundary-certificate review

Reviewed and ran `scripts/check_boundary_certificate.py` at default N=30 and 2048 bits. Its intervals represent integers divided by a common power of two. Addition and negation are exact; multiplication takes extrema of all four endpoint products and rounds outward using integer floor and ceiling; division by a positive integer rounds outward; radical enclosures follow from `isqrt`. The ceiling calculation for a is certified by agreement at both endpoints.

Source correspondence was checked for m=1,u=d=1,v=0,R=N+2: x=y=sqrt(2)-1, alpha=sqrt((R-1)^2+1)-(R-1), and tau=(sqrt((R-1)^2+1)-1)/(R-1). The two coupling factors are multiplied by the same positive k=R-1. The inverse-series recurrence computes d_j=c_j+(alpha+x)d_(j-1)-alpha*x*d_(j-2); the returned eliminated coefficients are d_a, c_(a+1)-alpha*x*d_(a-1), and c_(a+2),..., exactly those of W_C. Evaluation at y and 1 and subtraction then enclose the scaled numerator of the paper's boundary determinant formula.

The run certifies positivity of all four W evaluations and 1-y, and gives the exact integral enclosure

    -30666146689591218473741 <= scaled numerator <= -30666146689591218473740.

Thus the explicit boundary expression is rigorously negative, using integer arithmetic rather than floating-point sign inference. This is stronger than the initial decimal reproduction. The Python arithmetic is independently reviewed but not Lean-verified. The source-to-physical-matrix identity, continuous extension along distinct interior configurations, positive opposite endpoint, and intermediate-value implication remain mathematical obligations outside this executable certificate; it does not by itself certify an admissible interior counterexample. The collision boundary must not be advertised as a distinct configuration.
