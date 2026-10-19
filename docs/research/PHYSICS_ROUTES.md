# Physics routes and a reflection-positivity obstruction

Research note, 19 October 2026. This note separates algebraic identities, established background, proposed sufficient conditions, and an unverified recent counterexample claim. It does not assert a proof of C1.

## Scope and current literature

For distinct points in Euclidean three-space, let the opposite edge spinors be related by the quaternionic structure, and let `p_i` be their degree `n-1` symmetric products. C1 asks whether these n vectors are independent.

Berry–Robbins motivated the associated equivariant flag-map problem through spin and geometric phase [1]. Atiyah–Bielawski constructed such a map through Nahm equations [2]. Existence of that map does not prove independence of Atiyah's particular polynomial frame.

Eickhoff's *Singular Atiyah Configurations*, v3 dated 28 September 2026, claims counterexamples to Euclidean C1 of arbitrarily large size, including planar ones [3]. I inspected its introduction, stated Theorem A, proof outline, and polynomial conventions in the locally downloaded PDF text. Its construction uses two cyclic orbits and axial points, a real Fourier block, and an endpoint sign change. This is a directly relevant claim about the original independence problem, not merely a different determinant normalization. Its full proof and estimates have **not** been independently verified in this note. Any proposed universal positivity theorem must first confront this claim. A collaborator is auditing it separately.

## Exact no-go: the raw normalized determinants are not an OS-positive hierarchy

Use the standard Atiyah–Sutcliffe normalized determinant D: divide the coefficient determinant by the product of pairwise spinor determinants, with conventions chosen so D is 1 for collinear configurations. Thus D_1=D_2=1; extend D_0=1. In the three-point case, with side lengths u,v,w,

\[
D_3=1+\frac{(-u+v+w)(u-v+w)(u+v-w)}{8uvw}
    =\frac{3+\cos A+\cos B+\cos C}{4}.
\]

In particular an equilateral triangle has D_3=9/8, while a degenerate collinear triangle has D_3=1. The unnormalized determinant in [4] is `8uvw` times this D_3. This normalization distinction matters.

Suppose the raw D_n were scalar Euclidean correlation functions satisfying Osterwalder–Schrader reflection positivity [5]. Reflect through a plane by theta. For finite configurations A_i in the positive half-space, reflection positivity would require the matrix

\[
K_{ij}=D_{|A_i|+|A_j|}(\theta A_i\cup A_j)
\]

to be positive semidefinite. Choose A_0 empty, A_1={a}, A_2={b,c}, with theta(a),b,c noncollinear and all unions collision-free. Then

\[
K=\begin{pmatrix}1&1&1\\1&1&t\\1&t&s\end{pmatrix},
\qquad t=D_3(\theta a,b,c)>1.
\]

Reflection and permutation symmetry make the off-diagonal entries real and equal here. Independently of the finite value of s,

\[
\det K=-(t-1)^2<0.
\]

This proves that this proposed correlation hierarchy fails reflection positivity. Equivalently, the first two vectors have zero squared distance but different inner products with the third vector. The same contradiction can be expressed with smooth test functions localized in small disjoint neighborhoods: continuity away from collisions preserves a strict negative determinant.

This is an original elementary derivation in this note, not a quoted result from [5]. It rules out the raw D_n scalar hierarchy with the stated normalization. It does not rule out other observables, matrix-valued fields, different n-dependent normalizations, or every possible QFT representation. It also does not establish or refute C1.

For matrix identities below, coordinates on the spin space use an orthonormal
basis for its invariant Hermitian inner product. Raw monomial coefficient
coordinates require the corresponding metric matrix.

## Route 1: coherent-state frame bounds on restricted geometry

Set m=n-1 and H=Sym^m(C^2), with its SU(2)-invariant Hermitian metric. Regard the columns as P e_i=p_i. Exact identities give

\[
G=P^\dagger P,\qquad \det G=|\det P|^2
=\|p_1\wedge\cdots\wedge p_n\|^2.
\]

The spin coherent-state resolution, with normalized sphere measure and unit spinor representatives z, is

\[
I_H=n\int_{S^2}|z^{\otimes m}\rangle\langle z^{\otimes m}|\,d\mu(z).
\]

It supplies an exact positive integral expression for G. The p_i are symmetrized products of spin-one-half states; generally they are not single spin-m/2 coherent states. Positivity of G is automatic even at dependent columns. Strict positivity is the missing claim, equivalent to C1. A positive integral formula alone proves nothing further about independence.

A stronger, independently testable sufficient condition is weighted diagonal dominance:

\[
\exists w_i>0:\quad G_{ii}w_i>\sum_{j\ne i}|G_{ij}|w_j.
\]

For normalized columns q_i, form B with zero diagonal and off-diagonal entries `|<q_i,q_j>|`. The condition rho(B)<1 suffices. This can fail even for independent vectors, so it should not be silently treated as necessary.

**Next experiment/lemma.** For fixed n, bound rho(B) for configurations whose ordered pair directions deviate by at most epsilon from a fixed ordered collinear configuration. Collinear columns are mutually orthogonal monomials, hence B=0. Turn continuity into an explicit epsilon(n) using spinor-product perturbation estimates. This gives a restricted quantitative theorem even if universal C1 fails. First numerically test rho(B) outside that region to delimit, rather than assume, its scope.

## Route 2: a quantitative comparison with the Nahm frame

Choose a unitary representative Q of the Atiyah–Bielawski flag and form M=Q^dagger P. The known Nahm theorem supplies Q; it supplies no inequality on M. A concrete proposed sufficient condition is

\[
\exists\text{ diagonal unitary }U:\quad
\frac{MU+U^\dagger M^\dagger}{2}\succ0.
\]

Strict accretivity implies invertibility immediately. Gauge changes of the representative Q can be absorbed by matching diagonal phases and unitary conjugation. The missing ingredient is a geometric phase choice with strict accretivity, not equivariant topology.

**Next experiment.** Solve the correctly specified Nahm boundary problem for small n, construct Q, and optimize the phases in U to maximize the minimum eigenvalue of the Hermitian part. A negative optimum would refute this bridge even in a configuration where C1 holds. Numerical failure to find a positive optimum alone is not a certificate: use validated optimization or a separate upper bound. If the reported singular configurations validate, this condition cannot hold globally and should instead be studied on restricted families.

## Route 3: tensor-network cancellation and zero-mode detection

Malkoun already formulates graph amplitudes through vertex symmetrization and symplectic edge contractions, recovering the Atiyah determinant for a complete graph [6]. The spin-network connection is therefore existing literature, not a new connection claimed here. That paper also uses positive-semidefinite matrix and permanent inequalities in certain sparse graph cases.

The formal Grassmann Gaussian identity

\[
\det P=\int d\bar\psi\,d\psi\;e^{-\bar\psi P\psi}
\]

(with a consistent integration-order convention) is algebraic. Berezin integration is not a positive measure. Doubling gives det(P^dagger P)>=0, but does not exclude fermionic zero modes. Similarly, a product of noncommuting positive projections need not have a positive transition amplitude between different states.

**Next experiment/lemma.** For a specified reflection-symmetric family, cut the existing tensor network and compute the induced form on its boundary tensor space. Test whether the actual contraction can be written A^dagger A, with the required complex conjugations, and then identify an explicitly nonzero component of A. Symplectic bilinear edge contractions are not Hermitian pairings; reflection symmetry alone does not establish this factorization. Compute the boundary form at n=4 and n=6 before conjecturing positivity. An indefinite boundary form falsifies that proposed factorization; a positive form without a nonzero boundary vector still does not prove C1.

## Recommended order

Audit the recent singular-configuration argument first. Retain the exact raw-D reflection-positivity obstruction regardless of that audit. Prioritize restricted frame bounds or a classification of fermionic zero modes over another merely formal positive-semidefinite rewrite of the determinant.

## Primary sources

1. Berry and Robbins, *Indistinguishability for quantum particles: spin, statistics and the geometric phase* (1997), [author-hosted PDF](https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry286.pdf).
2. Atiyah and Bielawski, *Nahm's equations, configuration spaces and flag manifolds*, [arXiv:math/0110112](https://arxiv.org/abs/math/0110112).
3. Eickhoff, *Singular Atiyah Configurations*, v3, 28 September 2026, [Zenodo primary record](https://zenodo.org/records/23024340). Claim under audit, not treated here as independently verified.
4. Bou Khuzam and Johnson, *On the Conjectures Regarding the 4-Point Atiyah Determinant* (2014), [journal PDF](https://www2.math.ethz.ch/EMIS/journals/SIGMA/2014/070/sigma14-070.pdf), especially the three-point normalization and formula.
5. Osterwalder and Schrader, *Axioms for Euclidean Green's functions* (1973), [journal PDF](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/cmp/1103858969.pdf). Used for the positivity framework, not as a source of the no-go derivation above.
6. Malkoun, *Finite graphs and configurations of points*, [arXiv:2508.13472v3](https://arxiv.org/html/2508.13472v3), especially the tensor construction, sparse-graph inequalities, and Section 7.
7. Lieb, *The classical limit of quantum spin systems* (1973), [author-institution publication record](https://collaborate.princeton.edu/en/publications/the-classical-limit-of-quantum-spin-systems/). Background on coherent-state integral methods, not a C1 nonvanishing theorem.
