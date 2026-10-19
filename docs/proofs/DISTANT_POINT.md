# Distant-point extension: formal English proof and Lean correspondence

Status: **end-to-end checked conditional configuration theorem**:
`Atiyah.DistantPoint.distant_point_extension`. The only independence hypothesis
is C1 for the fixed core. This does not prove general C1 or the C2 inequality.

## Statement (DP)

Let a₁,…,aₘ be a fixed configuration of distinct points in ℝ × ℂ, and suppose
its Atiyah point forms are independent for every choice of Hopf lifts. Let
u ≠ 0. There exists R₀ such that for every real R > R₀, the enlarged
configuration (Ru,a₁,…,aₘ) has distinct points, admits Hopf lifts, and has
independent point forms for **every** choice of those lifts.

The threshold depends on the core and the ray direction. It is existential,
not an effective numerical bound. No claim is made about every finite spike
length or an arbitrary core whose independence is unknown. Lean also covers
the empty core, although the intended application has m ≥ 1.

`Configuration.C1 m` is the universal conjecture for all m-point configurations.
The main theorem assumes its per-configuration assertion for the fixed core;
`distant_point_extension_of_c1` supplies the universal C1 hypothesis as a
corollary. Neither theorem asserts `C1 (m+1)`.

## Conventions

A spinor v=(a,b) gives the binary form L_v=aX₀+bX₁. Its Hopf image is
((|a|²−|b|²)/2, a conjugate(b)). Define J(a,b)=(-conjugate(b),conjugate(a));
then Hopf(Jv)=−Hopf(v). Point forms are products over outgoing edges.

The code uses the ambient binary polynomial ring. Its homogeneous degree-m
part is H⁰(ℙ¹, O(m)), but no sheaf implementation is needed. The default norm
on ℝ × ℂ is the product/max norm, not the Euclidean norm. The proof uses only
the usual finite-dimensional topology and a nonzero direction; it does not
identify that norm with Euclidean length.

## Proof, with stable step identifiers

### DP1 — A parameter at infinity

For each core point define dᵢ(R)=u−R⁻¹aᵢ. Then dᵢ(R)→u as R→+∞. Since u≠0,
each dᵢ(R) is eventually nonzero, simultaneously for all i by finiteness.
For positive R the physical displacement Ru−aᵢ is R dᵢ(R). This also proves
the new point eventually avoids the entire core.

The previous normalized-direction proof remains available in `FarDirection`,
but normalization is unnecessary in the integrated proof.

### DP2 — Local lift choices

Choose a local section s of the Hopf map near u, continuous at u, with
Hopf(s(q))=q throughout a neighborhood. Its construction uses one of two
explicit square-root charts. The two charts cover every nonzero displacement,
including both poles; no global continuous section is asserted.

Set v=s(u) and bᵢ(R)=s(dᵢ(R)). Then v≠0, bᵢ(R)→v, and eventually
Hopf(bᵢ(R))=dᵢ(R) for every i. Continuity of J gives Jbᵢ(R)→Jv.

Choose any actual core lift family, with independent point forms qᵢ.
For R>0 the actual old-to-new lift is √R bᵢ(R); the reverse lift is
√R Jbᵢ(R), because Hopf(√R w)=R Hopf(w). Keep all old core lifts fixed.
These choices form an actual lift family for the enlarged configuration.

### DP3 — Limit of normalized point forms

Divide the new point form by (√R)^m and each old point form by √R. These
nonzero scalings yield

    F_*(R) = ∏ᵢ L_{Jbᵢ(R)},       Fᵢ(R) = L_{bᵢ(R)} qᵢ.

Every coefficient converges to the corresponding coefficient of

    L_{Jv}^m,       L_v q₁,…,L_v qₘ.                  (LIMIT)

For multiplication, each fixed coefficient is a finite sum of products of
coefficients; induction gives convergence of the finite product. All
coordinates are fixed throughout. Lean proves these statements directly for
homogeneous binary polynomials, without choosing affine roots.

### DP4 — Independence at the boundary

Write v=(a,b) and take w=(-b,a). Evaluation gives L_v(w)=0 and

    L_{Jv}(w)=|a|²+|b|² ≠ 0.

In a relation c_* L_{Jv}^m + Σᵢ cᵢ L_v qᵢ=0, evaluation at w forces c_*=0.
The polynomial ring is an integral domain and L_v≠0, so cancellation gives
Σᵢ cᵢqᵢ=0. Core independence forces every cᵢ=0. Thus (LIMIT) is independent.
This argument includes both pole cases; it does not assume two finite roots.

### DP5 — Stability using a finite coefficient witness

Let S be the union of the supports of the finitely many forms in (LIMIT).
Restriction to the coordinates in S is injective on their span: all other
coefficients of every vector in that span are zero. The projected limiting
family is therefore independent in the finite-dimensional vector space ℂ^S.

The set of independent finite families in that normed space is open. By DP3,
the projected F(R) converge to the projected (LIMIT), so they are independent
for all sufficiently large R. Independence after projection implies
independence of the full binary forms F(R).

This replaces the earlier square coefficient determinant argument in the
implemented proof. No degree bound on the varying family is needed for this
finite-witness lemma, and no coefficient truncation is assumed injective on
the entire polynomial ring. The older determinant lemmas remain valid
alternative components.

### DP6 — Actual configurations and arbitrary lift choices

Intersect the finitely many tail conditions: R>0, collision avoidance, local
incidence, and independence from DP5. Restore the nonzero column scalars from
DP3 to obtain independence of the constructed actual lift family.

Finally, two nonzero spinors with equal Hopf image differ by a nonzero complex
scalar. This is proved directly from the Hopf equations, including the pole
case. Applying it separately to every directed edge shows that replacing a
lift family rescales each point form by a product of nonzero scalars. Such
column rescaling preserves independence. Thus every lift family of the actual
enlarged configuration is independent. Extract R₀ from the common tail. ∎

## Algebraic-geometric interpretation

For z=Z(L_v), multiplication and evaluation give

    0 → H⁰(ℙ¹,O(m−1)) --·L_v→ H⁰(ℙ¹,O(m)) --ev_z→ O(m)|_z → 0.

The forms L_v qᵢ span the kernel; L_{Jv}^m supplies the missing quotient
direction. The boundary family avoids the determinant divisor. The formal
proof implements the polynomial and linear algebra underlying this statement,
not the sheaves or a scheme-level compactification. The geometric path uses
norms and conjugation, so it is not claimed to be a complex algebraic morphism.

## Relation to planar cells

For real coefficient representatives, independence excludes any nonzero common
dual annihilator. The existing checked obstruction theorem identifies this
with pointedness of the signed winner cones. The integrated distant-point
proof proceeds in complex binary forms and does not introduce a complex ± fan.
An explicit real coefficient-matrix corollary connecting the new theorem to
those particular cell definitions remains separate from the configuration
C1 theorem proved here.

## English ↔ Lean ledger

| Obligation | Checked declaration |
| --- | --- |
| DP1: ray limit and collision avoidance | `ContinuousLift.exists_ray_lifts`; `DistantPoint.eventually_ray_avoids` |
| DP2: local section, both poles, antipode | `ContinuousLift.exists_local_hopf_section`, `hopf_antipode`, `continuous_antipode` |
| DP2: physical displacement scaling | `Configuration.hopf_sqrt_smul`; `DistantPoint.rayLift` |
| DP3: actual point-form formulas/scalars | `DistantPoint.pointForm_extend_zero`, `pointForm_extend_succ`, `pointForm_rayLift` |
| DP3: coefficient convergence | `GeometricLimit.coeff_tendsto_mul`, `coeff_tendsto_prod`, `coeff_tendsto_linearForm` |
| DP4: homogeneous boundary independence | `GeometricLimit.boundary_independent` |
| DP5: finite witness and eventual independence | `GeometricLimit.eventually_independent_of_coeff_tendsto`, `eventually_spike_independent_fin` |
| DP6: arbitrary lifts and nonzero rescaling | `Configuration.linearIndependent_pointForm_iff`; `DistantPoint.independent_rayLift` |
| Complete DP, actual configurations and universal lift choices | `DistantPoint.distant_point_extension` |

## Corrections made through English/Lean comparison

- Keep the core independence hypothesis explicit; separation cannot supply it.
- Distinguish the Euclidean radius in the Hopf formula from the product norm.
- Use local sections, with both poles covered, instead of a global Hopf section.
- Use homogeneous evaluation to avoid affine-root exclusions.
- Use a fixed finite coefficient witness: the direct proof needs no degree
  bound, whereas the alternative square determinant proof does.
- Restore displacement-sized lifts and prove arbitrary-lift invariance before
  asserting a configuration-level theorem.

## Provenance and interpretation of the ML observation

Atiyah–Sutcliffe describe separated-cluster factorization in §5 of
[The Geometry of Point Particles](https://arxiv.org/pdf/hep-th/0105179).
This is a formalization of that boundary mechanism, not a novelty claim.

The earlier spiky samples motivate studying this boundary stratum. Because the
old oracle had a sign/index bug, those samples do not establish extremality for
the true determinant. The theorem concerns sufficiently separated cores whose
independence is known; it gives no quantitative assertion about those samples.
