# Proof attack through cells and the determinant divisor

## 1. The algebraic-geometric formulation

For a configuration, pairwise directions determine projective linear forms
`[ℓᵢⱼ] ∈ ℙ¹`. Multiplication gives the point forms
`[ρᵢ] ∈ ℙ(Symⁿ⁻¹ ℂ²) ≅ ℙⁿ⁻¹`. On the product of n coefficient projective
spaces, the determinant is a multihomogeneous equation of multidegree
`(1,...,1)`. Let Δ be its vanishing locus.

C1 asks whether the geometric configuration construction avoids Δ everywhere.
The incidence description of Δ is

```
I = { (ρ₁,…,ρₙ,[v]) : <v,ρᵢ> = 0 for all i },
Δ = projection(I).
```

The finite-dimensional vector statement is formalized in `Obstruction`.
The projective spaces, scheme structures, and projection are explanatory
language at present, not Lean constructions.

The geometric map is not a holomorphic algebraic map from unrestricted complex
point coordinates: Euclidean lengths and conjugation intervene. Work over the
real algebraic incidence space of lifts, with collision loci removed. In the
planar slice, introduce real `aᵢⱼ,bᵢⱼ` subject to

```
aᵢⱼ² - bᵢⱼ² = 2 xᵢⱼ,     aᵢⱼ bᵢⱼ = yᵢⱼ.
```

Reverse directed edges by `J(a,b)=(-b,a)`. These polynomial equations avoid
mistaking a chosen square-root section for a regular map. They must retain the
real/noncollision conditions: a proof about an arbitrary complexification can
be stronger than, or different from, the original question.

## 2. What the cell reduction proves

For coefficient vectors ρᵢ in ℝⁿ, signed winner cones are intersections of
homogeneous linear half-spaces. Every signed cone C has

```
C ∩ (-C) = {v : <v,ρᵢ>=0 for every i}.
```

Therefore one (equivalently every) signed cone is pointed iff the coefficient
matrix is nonsingular. The strip intersection

```
B = {v : |<v,ρᵢ>| ≤ 1 for every i}
```

contains the entire line ℝw iff w is a common annihilator. The complete-line
criterion is checked. Boundedness of B and a positive minimum on the unit
sphere remain separate formalization tasks; they are not claimed proved here.

This is an exact reformulation, not an independent reason why geometric
configurations have no annihilators. Proving that the cones are pointed by
assuming their defining normals form a basis would simply restate C1.

## 3. Ordered milestones

1. **Definition bridges.** General Hopf lift existence is proved. Prove projective
   uniqueness of lifts; outgoing forms have degree n−1 and are compatible with
   the standard stereographic conventions. Connect forms to square coefficient
   matrices via an explicit basis.
2. **Geometric baselines.** The geometric planar two-point case is proved. Next handle ordered
   collinear configurations and the full complex two-point case. In a suitable basis the latter give nonzero
   multiples of `X₀^i X₁^(n−1−i)`. `Algebraic` proves the monomial matrix core,
   not the geometric change-of-coordinates step.
3. **Known noncollinear case.** Formalize a known n=3 argument, then the n=4
   Gram-matrix proof of Malkoun. Separate spinor identities, PSD facts, kernel
   intersections, and collinear degeneracies. PSD alone is automatic for Gram
   matrices; strict positivity is the substantive condition.
4. **Research extension.** Search for a configuration-specific decomposition
   forcing the dual-incidence locus to be empty. An exact sum-of-squares or
   Gram decomposition with a verified zero-set analysis would be useful.
   Numerical candidates and CAS output must become exact identities/certificates
   checked in Lean.

## 4. Candidate routes and failure conditions

- **Positivity on the incidence cover:** express an appropriate determinant
  norm or Gram determinant modulo the lift equations. Sum-of-squares positivity
  is insufficient unless simultaneous vanishing is excluded on the distinct-point
  real locus. Do not silently invert a factor that can vanish for admissible
  horizontal, collinear, or coplanar configurations.
- **Cell specialization:** understand how the normal fan varies under motion of
  points. Showing generic cones are pointed leaves a possible exceptional locus.
  A wall-crossing argument must control rank-defect walls, not just label ties.
- **Projective divisor:** proving the pulled-back determinant is not identically
  zero yields only generic nonvanishing. A single monomial configuration does
  not exclude exceptional real zeros.
- **Boundary/compactness:** distinct configurations are noncompact modulo some
  normalizations because partial collisions persist. No global positive margin
  is assumed. Boundary strata must be analyzed before an induction from collisions.
- **Gauge:** nonzero rescaling preserves C1 but changes the fan and numerical
  conditioning. Record the gauge whenever comparing cells or optimizing margins.
- **3D versus planar:** full C1 is over complex coefficients. A finite ± fan is
  specifically real; use complex dual incidence or Hermitian Gram matrices in 3D.

## 5. Relation to the earlier ML experiment

The original classifier can probe the normal fan and learned representations,
while a normalized witness search can probe near-annihilators. Neither class
accuracy nor aggregate next-token loss establishes independence. In v2, input
entropy dominated the loss; moreover, a reversed-index error in the lower Hopf
branch invalidated its geometric oracle. `PlanarLift.exchanged_lower_branch`
formalizes that exact error: the wrong formula represents `(-x,y)`.

This proof project and the interpretability project have different success
criteria. No training run, grokking result, or general conjecture proof is
claimed by this repository.
