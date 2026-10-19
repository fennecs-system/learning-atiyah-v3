# What the separated-point proof says

Suppose a fixed cluster has independent Atiyah polynomials q₁,…,qₘ. Add a point
very far away. From every old point, it appears in nearly the same direction L.
From the new point, the cluster appears in the opposite direction M. After
nonzero rescaling the polynomial family approaches

    Lq₁,…,Lqₘ,M^m.

Evaluate a proposed dependence at the zero of L. Only M^m survives, so its
coefficient is zero. Cancel L in what remains; independence of the original
qᵢ kills every other coefficient. Independence persists under small changes,
so actual configurations sufficiently far along the ray are independent.

This is an end-to-end Lean theorem. It assumes the core is already independent;
it neither proves arbitrary cores independent nor supplies a numerical threshold.
“Extremal” here means a limiting geometry, not a proven minimizer of a determinant.

## A hierarchy of scales

Repeatedly add a distant point, fixing previous choices before choosing the
next distance. This constructs good configurations of any finite size.
The next broader operation is to merge two fixed good clusters. Its boundary
families L^k qᵢ and M^m rⱼ occupy complementary subspaces: a common form would
be divisible by L^k M^m of degree m+k, exceeding its degree m+k−1.
See proofs/TWO_CLUSTER.md for formalization status.

Repeating binary merges suggests cluster trees. The choices of separation are
nested and depend on the child clusters; no universal scale ratio follows.
Stars with many comparable arms or concentric rings require different analysis.
Symmetry is a separate property, not a guarantee of independence.

## Why pulling every configuration apart does not prove C1

An invertible matrix at the separated endpoint does not imply invertibility
along the path: the determinant can cross zero. A uniform dilation does not
change pairwise directions at all. A genuine deformation proof needs a new
nonvanishing invariant or bound along the entire path.

This caution is substantive: Eickhoff's September 2026 preprint
https://zenodo.org/records/23024340 claims singular configurations, using a
sign change along a symmetric path. The project is auditing rather than
assuming that result. Conditional separation does not contradict it: our
thresholds concern fixed good cores, not arbitrary motions or growing families.

## Physics ideas worth testing

The point forms can be viewed as spin states. Their Gram matrix is automatically
positive semidefinite, but strict positivity is precisely the missing independence.
Writing a determinant as a fermionic integral does not remove zero modes.
Useful physics targets therefore need extra content: a quantitative spectral
gap for a restricted geometry, or a tensor-network factorization with a proven
nonzero component. See research/PHYSICS_ROUTES.md for concrete tests and a
small exact obstruction to one naive reflection-positivity proposal.
