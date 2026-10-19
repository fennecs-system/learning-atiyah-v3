# Distant-point extension: formal English proof and Lean correspondence

Status: complete mathematical argument below; only the explicitly listed Lean
components are formalized. This is **not yet an end-to-end Lean theorem about
geometric distant-point configurations**. The document is a proof guide with
precise obligations, not an axiom used by the library.

## Statement (DP)

Let m ≥ 1 and let a₁,…,aₘ be fixed distinct points of Euclidean three-space.
Assume that their Atiyah point polynomials are linearly independent (C1 for
this particular core configuration). Fix a unit vector u. Then there is R₀,
depending on the core and u, such that for every real R > R₀ the configuration

    a₁,…,aₘ,Ru

has distinct points and linearly independent Atiyah point polynomials.

This is the precise meaning of a fixed core with one sufficiently distant
point. It does not assert independence for every finite spike length or remove
the hypothesis on the core. It gives no effective numerical threshold and does
not prove the stronger normalized determinant inequality C2.

## Conventions

Use homogeneous binary forms V_d = H⁰(ℙ¹_ℂ, O(d)), a complex vector space of
dimension d+1. Each directed displacement determines a projective linear form;
choose nonzero representatives. Multiplying representatives by nonzero scalars
rescales point forms and preserves linear independence.

Fix representatives q₁,…,qₘ ∈ V_{m−1} for the core. By the hypothesis and the
dimension count these form a basis. The proof uses a local section of the
projective direction map near u, not a nonexistent global continuous section
of the Hopf fibration.

## Proof, with stable step identifiers

### DP1 — A parameter at infinity

Put t = 1/R. For each core point define

    dᵢ(t) = (u − t aᵢ) / ‖u − t aᵢ‖.

For t > 0 this is the unit direction from aᵢ to Ru: multiplying a nonzero vector
by the positive scalar R does not change its normalization. At t=0 the
unnormalized vector is u, whose norm is 1. Thus every dᵢ extends continuously
to t=0, with dᵢ(0)=u. Since there are finitely many points, a single neighborhood
works for all i.

### DP2 — Local lift choices

Choose a local continuous section assigning a nonzero linear form to directions
near u. Let Lᵢ(t) be the form of dᵢ(t), and let L be its value at u. Choose the
opposite directed factors Mᵢ(t) by antipodal conjugation of these lifts. Then

    Lᵢ(t) → L,     Mᵢ(t) → M,

where L and M are nonproportional linear forms. This nonproportionality follows
from the antipodal relation; for spinors (a,b) and (−conj b,conj a), the pair
determinant is |a|²+|b|² > 0.

Local sections exist in either standard affine chart of ℙ¹. If one pole lies in
a chosen chart, use the other chart. No direction is excluded. Replacing the
normalized directional lifts by the displacement-sized lifts used in the code
only introduces nonzero factors; this must be justified by a formal lift-choice
invariance lemma before applying this proof to the repository's C1 definition.

### DP3 — Limit of point forms

In these representatives the m old point forms and the new point form are

    Pᵢ(t) = qᵢ Lᵢ(t),       P_*(t) = ∏ᵢ Mᵢ(t).

Multiplication of fixed-degree forms is polynomial in coefficients and hence
continuous. Consequently the coefficient vectors converge to those of

    Lq₁,…,Lqₘ,M^m.                         (LIMIT)

All forms are in V_m. Use one fixed basis of V_m throughout; do not compare
matrices in a t-dependent basis without also tracking its invertibility.

### DP4 — Independence at the boundary

Let z be the zero of L in ℙ¹, and choose a nonzero homogeneous representative w
of z. Because L and M are nonproportional, M(w) ≠ 0. Suppose

    Σᵢ cᵢ Lqᵢ + c_* M^m = 0.

Evaluating at w gives c_* M(w)^m = 0, so c_*=0. We then have
L(Σᵢ cᵢqᵢ)=0. The binary polynomial ring is an integral domain and L≠0, so
Σᵢ cᵢqᵢ=0. Core independence gives every cᵢ=0. Therefore (LIMIT) is independent.
Since it consists of m+1 forms in the (m+1)-dimensional V_m, its coefficient
matrix A₀ has nonzero determinant.

### DP5 — Stability away from the determinant divisor

Let A(t) be the coefficient matrix of the forms in DP3. Then A(t)→A₀ and
`det A₀ ≠ 0`. The determinant is continuous, and the complement of {0} is open.
Hence `det A(t) ≠ 0` for all sufficiently small positive t. Equivalently there
is a threshold after which `det A(1/R) ≠ 0` for all R. This is universal over the
tail, not just a subsequence of good distances.

### DP6 — Return to actual configurations

Increase the threshold so that R₀ > maxᵢ ‖aᵢ‖ and R₀ > 0. For R>R₀, Ru cannot
equal a core point, because ‖Ru‖=R. The original core points are distinct by
hypothesis. DP2's nonzero changes of lift representatives preserve independence,
so the conclusion is C1 for the actual enlarged configuration. ∎

## Algebraic-geometric interpretation

For z = Z(L), multiplication and evaluation give an exact sequence

    0 → H⁰(ℙ¹,O(m−1)) --·L→ H⁰(ℙ¹,O(m)) --ev_z→ O(m)|_z → 0.

The forms Lqᵢ give the kernel summand, and M^m gives the missing one-dimensional
quotient because M(z)≠0. This is why the boundary matrix is nonsingular. In the
product of coefficient projective spaces its limit avoids the determinant
divisor. The nearby geometric family therefore also avoids that divisor.

The polynomial algebra of this argument is algebraic over ℂ. The path from
Euclidean point configurations involves norms and conjugation: its continuity
is not a claim that it is a complex algebraic morphism. Neither a scheme-level
compactification nor this exact sequence as a sheaf theorem is implemented in
Lean here; the formalized core uses polynomial evaluation and linear algebra.

## Return to the planar cells

For a planar family choose real lifts and write coefficient vectors as rows of
B(R) = A(R)ᵀ, matching the cell module's convention. Eventual nonvanishing of
det A(R) gives eventual nonvanishing of det B(R). The checked obstruction
identity then says every signed winner cone has zero lineality. Thus the
spike extension also preserves pointedness of these cones for sufficiently
large R, conditional on the missing geometric convergence bridge. Ordinary
winner-label changes do not invalidate this conclusion; the obstruction is a
common annihilator, not a tie between two labels.

## English ↔ Lean ledger

This table is maintained from actual theorem statements, including their
hypotheses. A local checked component does not silently discharge its missing
geometric inputs.

| English obligation | Lean component | Scope |
| --- | --- | --- |
| DP1: normalized direction converges | `FarDirection.tendsto_direction_far` | Normalized direction of R • u − a converges to u as R → +∞. |
| DP2: coherent local projective lift, antipodal factor, gauge comparison | Partial existing `PlanarLift` and `Configuration` lemmas | Local continuous complex sections and lift-choice comparison remain open formalization tasks. |
| DP3: coefficientwise convergence of actual point forms in a fixed basis | No end-to-end theorem yet | Must connect finite products, degree/basis conventions, and the geometric lift family. |
| DP4: limiting polynomial independence | `SpikeLimit.boundaryFamily_pow_independent` | Algebraic affine-chart version; does not itself identify a geometric limiting family. |
| DP4: independence implies nonzero square coefficient determinant | `SpikeLimit.fin_cons_boundary_pow_det_ne_zero` | Independent n-polynomial core of degree < n and a ≠ b give a nonzero determinant for (X−b)^n and (X−a)qᵢ. |
| DP5: convergent nonsingular limit implies eventual nonsingularity | `exists_threshold_det_ne_zero` | Takes matrix convergence and limit nonvanishing as explicit inputs. |
| DP6: distinctness and comparison with the full C1 definition | `FarDirection.eventually_far_avoids_cluster` proves eventual collision avoidance | Gauge comparison and the final geometric DP theorem are not yet assembled. |

## Corrections enforced by the English/Lean comparison

1. The distant-point assertion needs a **core independence hypothesis**. The
   boundary argument cannot produce it from separation alone.
2. An abstract independent family of polynomials is not automatically a square
   coefficient basis: the degree bound and ambient dimension matter.
3. A chosen lift can jump at a chart boundary. Use local projective sections
   and prove invariance under nonzero rescaling, rather than assuming the
   canonical square-root implementation is globally continuous.
4. Stability requires convergence of matrices **in a fixed gauge and basis**.
5. For the real cell interpretation, coefficient vectors are rows in `Cells`
   but polynomial coefficients are columns in `Algebraic`; the transpose is
   required when applying the pointedness theorem.

## Provenance and interpretation of the ML observation

Atiyah–Sutcliffe already describe factorization for separated clusters in §5 of
[The Geometry of Point Particles](https://arxiv.org/pdf/hep-th/0105179), including
an asymptotic correction to their energy. The proof above is a formulation of
that boundary mechanism suitable for C1 and formalization, not a claim that
cluster separation is newly discovered.

The observation motivating this task was that learned/search-generated
configurations often had one point much farther from the others. Keep that as
an empirical observation about the previous experiment. Because the previous
oracle had a sign/index bug, it does not yet establish that those samples are
extremal for the true Atiyah determinant. It nevertheless identifies a useful
geometric boundary stratum to understand and then test with a corrected oracle.
