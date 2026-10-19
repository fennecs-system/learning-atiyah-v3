# Independent kernel and theorem-semantics review

Reviewer scope: axiom audit coverage, intended theorem versus actual statements,
vacuity and hidden assumptions. Compilation alone is not treated as proof of the
English distant-point statement.

## Baseline checked

At baseline commit `1daf53cb4a7c7f764404f41b673deb555dd771fd`, running
`source /workspace/scratch/atiyah/lean-env.sh && scripts/check.sh` completed
successfully. The audit reported **152 project declarations**. Concurrent new
files were not yet imported by `Atiyah.lean` and are not covered by that result.

`Check.lean` imports the root library and recursively collects dependencies of
every non-internal declaration whose root namespace is `Atiyah`. It permits
only `propext`, `Classical.choice`, and `Quot.sound`. A helper hidden by an internal
name is still audited transitively when a public project theorem depends on it.
An unimported file or an unused declaration outside the project namespace is
not covered. The check does not validate prose, intended mathematical meaning,
or the adequacy of hypotheses.

## Baseline semantic verdict

**Pass as checked components; not an end-to-end distant-point theorem.** No
`sorry`, `admit`, custom axiom, `native_decide`, contradictory assumption, or
target-equivalent hypothesis was found in the baseline source.

* `Config.distinct` is actual injectivity of the points. Neither poles nor
  collinear configurations are removed from the full definition.
* `C1 n` quantifies over every configuration and every displacement Hopf lift.
  It includes lift existence explicitly, and `liftFamily_nonempty` proves that
  existence independently. The intended universal assertion is not vacuous.
* `pointForm` is the product of all outgoing off-diagonal linear forms. Its
  factors and products are proved nonzero; diagonal lift entries are irrelevant.
* `c1_one` proves only the one-point case. `c1_iff` removes a separately proved
  existence conjunct; it does not prove general independence.
* `SpikeLimit` assumes independence of the core, an appropriate hypothesis for
  the distant-point claim. Its polynomial boundary determinant requires and uses
  degree bounds. It has no geometric input identifying those polynomials with
  actual configurations.
* `DeterminantStability` assumes convergence and nonzero limiting determinant.
  This is a legitimate analytic component, but those hypotheses must be derived
  from geometry before an end-to-end claim is warranted.
* The arbitrary-filter stability lemma can be vacuous at the bottom filter.
  The real-threshold specialization uses `atTop` on the reals and yields every
  sufficiently large parameter, so this does not undermine the intended use.
* `Space = ℝ × ℂ` uses the standard product norm (maximum of coordinate norms),
  not the Euclidean norm suggested by some prose. The direction lemmas work for
  any norm and retain the same rays; this is not a false theorem. Geometric
  assertions involving Euclidean unit lengths must distinguish the two norms.

## Incoming modules and assembly

`ContinuousLift` semantic review: **pass**. Its section theorem requires only a
nonzero displacement, proves incidence at the basepoint and throughout a
neighborhood, and supplies continuity at the basepoint. The north chart and its
antipodal counterpart cover all nonzero displacements, including both poles.
The antipodal determinant is the sum of two nonnegative squared moduli; its
nonvanishing hypothesis is precisely a nonzero spinor. No excluded affine-root
case or global continuous section is assumed. Standalone compilation was
reported by its author; the final root-library audit remains pending.

Current `Gauge` semantic review: **pass**, subject to final compilation/audit.
It proves projective uniqueness from the actual equal-Hopf-image equations,
then obtains nonzero column scalars for actual `pointForm` products. The
independence equivalence compares arbitrary lift families on the same
configuration, with no unit-phase or regularity assumption on the families.

`GeometricLimit` semantic review: **pass**. The union of supports of the finitely
many limiting polynomials provides a finite coefficient projection preserving
their independence. Openness of independence in that finite-dimensional space
gives eventual independence of the projected family, hence of the full forms.
This is valid even if nearby supports enlarge; there is no missing degree bound
in this route. Degree bounds are needed for the alternative square coefficient
determinant argument, not for this finite-minor argument. Product convergence is
proved coefficientwise using finite antidiagonal sums. The boundary evaluation
uses `(-v.2,v.1)` and the antipodal determinant, including both poles. The eventual
product-family theorem assumes only core independence and spinor convergence,
not eventual independence in disguise.

Current `DistantPoint` bridge semantic review: **pass**. `extend` preserves actual
point injectivity, `extendLift` uses correctly oriented displacements, and
`rayLift` multiplies local lifts by `sqrt R` for positive R to recover the
displacement-sized Hopf equations. The old point columns scale by `sqrt R`,
while the new point column scales by its n-th power. All are nonzero.
`independent_rayLift` transfers the conclusion to every lift family.

## Final theorem semantic verdict

**Pass: an end-to-end conditional distant-point theorem.** Independently running
`lake env lean Atiyah/DistantPoint.lean` succeeded. The theorem
`DistantPoint.distant_point_extension` assumes exactly a distinct fixed core,
independence of its point forms for all lift choices, and a nonzero ray axis.
It produces a real threshold and, for every larger real parameter, a distinct
configuration whose point function is exactly `Fin.cons (R • u) p.point`, with
explicit lift existence and independence for every lift family. The existential
configuration cannot secretly substitute different points because its point
function is fixed by equality. The real tail is nonempty. No convergence or
finite-parameter independence assumption is left to the caller.

The proof derives local converging lifts from geometry, applies the homogeneous
boundary argument and finite coefficient stability, restores displacement sizes,
and transfers to arbitrary actual lifts. The original `Configuration.lean` is
unchanged. A fresh forbidden-token source scan found only prose occurrences of
the word `axiom`, not forbidden proof declarations or tactics.

The result is stronger than the English unit-ray version because any nonzero
axis works, and also permits an empty core. Neither extension is problematic.
It does **not** prove `C1 (n+1)` from `C1 n`: the threshold may depend on the fixed
core and direction, and no claim is made about shorter distances.

## Final independent build and axiom check

After all four new modules were imported into `Atiyah.lean`, a fresh independent
`scripts/check.sh` run completed successfully and reported **197 project
declarations** audited. Separate `#print axioms` checks of
`Atiyah.DistantPoint.distant_point_extension` and
`Atiyah.DistantPoint.distant_point_extension_of_c1` each reported exactly
`[propext, Classical.choice, Quot.sound]`.

This check covers the integrated working tree based on commit
`1daf53cb4a7c7f764404f41b673deb555dd771fd`; the new theorem files were not yet
committed at this review's final check. The delivery record must identify the
final commit and rerun the same check there. The revised DP1–DP6 English guide
was reviewed and matches the homogeneous, finite-coefficient-witness route.

**Final verdict: PASS for the advertised conditional distant-point extension;
general C1 remains open.**

A determinant theorem about an arbitrary convergent matrix family is not a
substitute for that final bridge. A theorem for one chosen gauge must either
state that limited scope or invoke a proved gauge-invariance theorem. New modules
must be imported into the root before the project audit covers them.
