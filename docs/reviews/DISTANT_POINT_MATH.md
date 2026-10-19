# Independent mathematical review of the distant-point claim

Final verdict: **accepted for the repository's configuration-level conditional
C1 assertion**. `DistantPoint.distant_point_extension` meets the exact contract
below, and an independent `lake env lean Atiyah/DistantPoint.lean` run succeeds.
No mathematical blocker remains in the inspected chain. The final repository
audit and exact commit identification remain the integrator's responsibility.

Review baseline: `Configuration`, `FarDirection`, `SpikeLimit`,
`DeterminantStability`, and DP1–DP6 as present when this review began.
The written conditional argument is mathematically sound. No counterexample to
the stated fixed-core, fixed-ray, sufficiently-large-distance assertion was
found. The initial checked components do not yet prove that assertion.

Validation: all four baseline modules named above compiled directly with
`lake env lean` after sourcing `/workspace/scratch/atiyah/lean-env.sh`.
This verifies those components, not the missing end-to-end theorem. This
review is a live working-tree review, not a replacement for the final commit's
full `scripts/check.sh` and axiom audit.

## Exact acceptance criterion

For each fixed `p : Configuration.Config m`, assume
`∀ L : Configuration.LiftFamily p, LinearIndependent ℂ (Configuration.pointForm L)`.
For every fixed `u : Configuration.Space` with `u ≠ 0`, prove that there exists
`R₀ : ℝ` such that for every `R > R₀` there exists
`pR : Configuration.Config (m+1)` satisfying both:

* `pR.point = Fin.cons (R • u) p.point`;
* `∀ L : Configuration.LiftFamily pR,
  LinearIndependent ℂ (Configuration.pointForm L)`.

Lift existence for `pR` is already supplied by `liftFamily_nonempty`. It is also
acceptable to spell out existence in the conclusion. A theorem assuming only
one independent core lift is stronger once lift-choice invariance is proved.
Restricting to `1 ≤ m` is consistent with the requested statement. Allowing
`m = 0` is harmless but needs explicit treatment by the implementation.

The quantifier order matters: `R₀` may depend on this core and this ray. A
subsequence, a dense set of good distances, or a threshold depending on the
chosen enlarged lift does not satisfy this criterion. Neither global `C1 m`
nor global `C1 (m+1)` is the fixed-configuration assertion above.

## Required bridges and failure checks

1. **Actual Hopf fibers.** Equal nonzero Hopf images must imply nonzero complex
   proportionality of spinors. This must cover both coefficient-zero cases.
   Product scalars must then give lift-choice invariance for the actual
   `pointForm`, including arbitrary and mutually incoherent directed lift
   choices allowed by `LiftFamily`.
2. **Local section at every ray.** A section continuous at the nonzero ray
   vector and incident on a neighborhood suffices. A formula dividing by its
   first coefficient alone is insufficient at the excluded pole. A second
   chart or an equivalent explicit construction is mandatory.
3. **Physical scale.** The original Hopf equation uses the displacement, not
   merely its direction. For `R > 0`, a section at `u - R⁻¹ • p.point i` can
   be multiplied by `sqrt R` to lift `R • u - p.point i`. The reverse factor
   uses antipodal conjugation. Omitting the square root gives the wrong
   quadratic scaling. Column gauge factors must be nonzero on the same tail.
4. **Finite-product identification.** The old point forms must be identified
   with the core forms times one extra factor, and the new form with the
   product of reverse factors. This includes correct `Fin.cons` indexing and
   removal of the diagonal. It is not enough to define a convenient family
   whose relationship with these products remains an assumption.
5. **Boundary geometry.** For spinor `(a,b) ≠ 0`, the antipode
   `(-conj b,conj a)` gives a linearly independent pair. Their determinant is
   `normSq a + normSq b`, which is strictly positive. Both pole cases are
   admissible. The existing affine theorem requiring two distinct finite
   roots does not cover these cases without a checked coordinate-change
   bridge. Working directly with binary forms avoids that issue.
6. **Coefficient topology and degree.** Independence in the ambient binary
   polynomial ring must pass to a fixed finite coefficient space that sees
   enough coefficients of the limit family. A topology on an infinite
   polynomial ring or a truncated matrix alone does not establish this
   bridge. A degree bound and full coefficient basis suffice, but are not
   necessary: a finite support witness for the limit also suffices, as
   explained in the subsequent review below.
7. **Final openness and collision avoidance.** Apply openness only after
   proving convergence in that fixed space and independence of its limit.
   Take a single tail satisfying all finitely many incidence, chart,
   noncollision, and positivity conditions. The returned configuration must
   contain precisely the specified points.

## Norm convention requiring care

`Configuration.Space` is the product `ℝ × ℂ`. Its default Lean norm is the
product max norm, not the Euclidean norm `sqrt (x² + normSq z)` used to write
Hopf sections. The topology is appropriate and the arbitrary-norm
`FarDirection` lemmas are valid; the issue is a possible mistaken identity,
not a mathematical obstruction. Do not identify these two norms. Quantifying
over all `u ≠ 0` and using the unnormalized near-limit displacement avoids any
unit-vector convention. Alternatively document explicitly the norm used by a
unit-ray theorem and derive the desired Euclidean-ray formulation.

## Scope of the result

Success proves a conditional, pointwise distant-point extension. It gives no
effective threshold, no uniform threshold over all cores or rays, no assertion
for every finite spike length, no C2 bound, and no proof of general C1. A
separate bridge to standard published root conventions remains relevant to
claims beyond the repository's incidence-based definition.

## Subsequent review: `GeometricLimit`

Independent `lake env lean Atiyah/GeometricLimit.lean` check succeeded.

`eventually_independent_of_coeff_tendsto` supplies a valid stronger route to
DP5 than a square homogeneous coefficient matrix. Its fixed set `S` is the
union of supports of the finitely many *limit* polynomials. Restriction to `S`
preserves their independence because every omitted coefficient is zero in
every limit polynomial. Linear independence is open in the resulting finite
coefficient space. Independence after projection implies independence before
projection, so nearby polynomials need no degree or support bound. In
particular, the proof does not silently assume that projection is injective on
the full polynomial ring.

`coeff_tendsto_mul` uses the finite antidiagonal formula for each coefficient;
finite products and spinor linear forms then give the required convergence.
`boundary_independent` evaluates at `(-b,a)`, a zero of the outgoing form.
The opposite form evaluates to `normSq a + normSq b ≠ 0`, including either
pole. Cancellation uses the integral domain property and core independence.
The exponent-zero case is valid as well.

The final `eventually_spike_independent_fin` has appropriate assumptions:
independence of the fixed core family, a nonzero limiting spinor, and
convergence of every outgoing spinor. It assumes no finite-parameter
independence and no premise equivalent to the distant-point conclusion.
It remains the assembly's responsibility to construct those spinors and
connect its convenient product family to actual `pointForm` values for every
enlarged lift.

## Final assembly review: `DistantPoint`, `Gauge`, `ContinuousLift`

The theorem `distant_point_extension` takes only a fixed distinct core,
independence for its lift families, and a nonzero ray vector. Its output
configuration has exactly `Fin.cons (R • u) p.point`, includes lift existence,
and quantifies over **all** its lift families. It obtains one threshold before
quantifying over `R` and the enlarged lifts. The `_of_c1` corollary applies a
global core hypothesis only to the selected core; it makes no global
`C1 (n+1)` claim.

Checked assembly details:

* `extendLift` uses `b i` for the directed edge from old point `i.succ` to new
  point `0`, and `c i` for the reverse edge. These match `point j - point i`.
  The diagonal is ignored consistently. `pointForm_extend_zero` gives the
  product of all reverse factors; `pointForm_extend_succ` gives exactly one
  new outgoing factor times the old point form.
* `exists_ray_lifts` uses a single chart continuous at the nonzero `u`.
  Its incidence statement is eventually simultaneous over the finite core.
  The south-chart construction uses antipodal conjugation after negation,
  so its Hopf image is the original displacement, including the pole.
* `rayLift` multiplies each new-edge spinor by the positive real `sqrt R`.
  `hopf_sqrt_smul` restores the actual displacement. The old point forms gain
  scalar `sqrt R`; the new point form gains `(sqrt R)^n`. Both scalars are
  nonzero on the positive tail, including exponent zero.
* `Gauge.hopf_eq_exists_smul` splits on the first coordinate and handles both
  zero-coordinate cases. Its product argument compares arbitrary directed
  families; it imposes no coherence restriction absent from `LiftFamily`.
  `independent_rayLift` therefore upgrades the constructed family to every
  actual lift family, rather than merely producing one good family.
* The final filter intersection includes independence, local incidence,
  collision avoidance, and positivity. Extracting `R₀` from `atTop` and using
  `R > R₀ ⇒ R ≥ R₀` gives a universal tail. No subsequence or gauge-dependent
  threshold is substituted.

The implementation uses nonzero unnormalized ray vectors, so the max-norm
warning above causes no remaining restriction or mistaken Euclidean identity.
It also handles the empty core consistently. The accepted theorem is stronger
in these harmless respects than the original unit-ray, nonempty-core wording.
