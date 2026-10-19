# Two fixed clusters: proof guide

Status: **end-to-end checked conditional theorem**
`Atiyah.TwoCluster.two_cluster_extension`. The actual enlarged configuration,
lift existence, and independence for every lift choice are all in the conclusion.

## Target

Let A=(a_i) and B=(b_j) be fixed distinct-point configurations of sizes m,k,
each with independent Atiyah point forms for arbitrary displacement Hopf lifts.
For u≠0, prove existence of R₀ such that every R>R₀ gives a distinct union
A ∪ (Ru+B), with independent forms for every lift family. R₀ may depend on
both entire cores and u. This is conditional gluing, not general C1.

## TC1: geometric separation and local lifts

For every pair i,j, u+R⁻¹(b_j−a_i) tends to u. A local Hopf section gives
spinors s_ij(R) tending to the same v≠0. Their antipodes tend to Jv. Multiplying
by √R gives actual cross-edge displacement lifts. Cross collisions eventually
cannot occur. Existing internal lifts of both cores are preserved under translation.

## TC2: normalized columns

Write L=linearForm(v), M=linearForm(Jv), and q_i,r_j for the core forms.
Divide each A column by (√R)^k, and each B column by (√R)^m. The normalized
forms converge coefficientwise to L^k q_i and M^m r_j, respectively.

## TC3: complementary boundary subspaces

For m,k>0, core forms have degrees m−1 and k−1 and give bases of the corresponding
homogeneous binary-form spaces. The boundary subspaces are
L^k Sym^(m−1)(C²) and M^m Sym^(k−1)(C²). Their intersection is zero: a common
form is divisible by L^k M^m, of degree m+k, but has degree m+k−1.
Their dimensions sum to m+k, proving independence of the combined family.
If either core is empty, the combined family reduces to the other core; Lean
handles these cases directly without interpreting a negative homogeneous degree.

In binary polynomial rings, nonproportional linear forms are relatively prime
in the divisor sense; their generated ideal need not be the unit ideal. Do not
substitute Bezout/IsCoprime for the needed divisibility statement. An invertible
linear substitution to coordinate variables gives an alternative support proof:
the first family occupies second-coordinate exponents below m, and the second
family occupies exponents at least m.

## TC4: stability

Use the fixed finite coefficient witness established in GeometricLimit.
Coefficientwise convergence to an independent family implies eventual independence.
No global topology on the entire polynomial ring or uniform degree truncation
is assumed.

## TC5: actual configurations

Construct the union with exact coordinates a_i and Ru+b_j and actual Hopf
incidence on every edge. Restore the nonzero column scalars, then use the
proved gauge equivalence to obtain independence for arbitrary lift choices.

## TC6: tail and recursion

Intersect separation, incidence, R>0, and independence tails and extract R₀.
Binary-tree recursion must choose each new separation after fixing its child
clusters; no universal separation ratio or simultaneous power-law scaling
follows without extra estimates.

## Status ledger

| Step | Intended owner/module | Status |
| --- | --- | --- |
| TC1–TC2 | `TwoCluster.exists_cross_lifts`, `eventually_separated`, `clusterForms_tendsto` | Checked |
| TC3 | `TwoClusterAlgebra.boundary_independent` | Checked via variable substitution and coefficient support separation |
| TC4 | GeometricLimit | Existing generic theorem checked |
| TC5 | `TwoCluster.independent_glue` | Checked actual lift construction, column scaling, and gauge transfer |
| TC6 | `TwoCluster.two_cluster_extension` | Checked single universal tail for fixed cores |

## Research status correction

A September 2026 preprint by Jan Eickhoff, Singular Atiyah Configurations,
https://zenodo.org/records/23024340, claims counterexamples to general C1.
This project is auditing that claim; it has not formalized the counterexamples.
Conditional gluing is compatible with singular configurations outside the
separated tails. Do not describe general C1 as currently open without qualification.

The recursive binary-tree construction is a mathematical consequence by finite
iteration with sequential choices of scales. A tree data type and recursive
constructor have not yet been implemented in Lean.
