# Learning Atiyah v3

A Lean 4 research project studying Atiyah configuration independence (C1)
through polynomial coefficients, dual incidence, signed winner cones, and
conditional separation theorems.

**The 84-point singular specialization is formalized in Lean.** The theorem
[`SingularCounterexample.not_C1_84`](Atiyah/SingularCounterexample.lean) proves
`¬ Configuration.C1 84`. Its companion existence theorem supplies an actual
distinct configuration with dependent complex point forms for every Hopf lift
family, and explicitly includes lift existence. The witness occurs strictly
inside the specified planar path, not at its colliding endpoints.

This verifies the m=1, 84-point specialization of Jan Eickhoff's September 2026
preprint [Singular Atiyah Configurations](https://zenodo.org/records/23024340).
It does not formalize the preprint's full arbitrary-size family. Earlier
statements here that general C1 remained open missed that preprint; the
conditional distant-point and two-cluster theorems remain compatible with the
counterexample.

Read the [simplified explanation](docs/SINGULAR_EXPLAINED.md),
[formal English proof and correspondence ledger](docs/proofs/SINGULAR_FAMILY.md),
and [independent statement review](docs/reviews/SINGULAR_REVIEW.md).

## Build and audit

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
./scripts/check.sh
```

Lean and mathlib are pinned to **4.19.0**; `lake-manifest.json` pins all dependency
commits. `Check.lean` audits every public declaration under `Atiyah`, transitively,
allowing only `propext`, `Classical.choice`, and `Quot.sound`. The GitHub workflow
builds with the normal Lean release and runs the same audit.

## Mathematical direction

Write the coefficient vectors of the point polynomials as columns of `A`.
The universal bad locus is the determinant divisor `det A = 0`. Equivalently,
there is a nonzero dual vector annihilating all columns: a point of the
projectivized dual-incidence locus.

For real planar coefficients, the signed winner cones are the cones defined by

```
s · <v, ρᵢ> ≥ <v, ρⱼ> and s · <v, ρᵢ> ≥ -<v, ρⱼ>   for every j.
```

Their common lineality space is the annihilator of all coefficient vectors.
Thus the nonsingularity problem is exactly the assertion that these cones are
pointed. The equivalence is proved. The singular construction shows that universal
geometric pointedness cannot hold.

Independent rescaling of polynomial columns multiplies the determinant by the
product of the scales. Its vanishing locus therefore has the expected projective
meaning, even though the detailed classifier changes with the chosen scales.
The source proves this algebra; it does not implement scheme-level objects.

## Modules and status

| Module | Checked content |
| --- | --- |
| `Configuration` | Full configurations in ℝ × ℂ, Hopf incidence lifts, binary forms; nonzero factors/products; lift existence for every configuration; one-point C1. General C1 is a proposition, not a theorem. |
| `PlanarLift` | Polynomial lift equations, antipodal/deck identities, total real lift including horizontal directions, and a regression theorem identifying the v2 sign error. |
| `Cells` | Convex signed cones, absolute cells as unions, exact common lineality, strip invariance and complete-line criterion. |
| `Obstruction` | Determinant nonvanishing iff no nonzero dual annihilator, iff positive absolute evaluation in every nonzero real direction, iff signed cones are pointed. |
| `PlanarConfiguration` | Coherent geometric pair lifts, degree bounds, coefficient matrices, the pointed-cell bridge, and positive determinant for every two-point configuration. |
| `Algebraic` | Coefficient matrices, determinant scaling, monomial/scaled-monomial baselines. This is not yet a geometric collinear proof. |

The full 3D definition uses homogeneous binary forms and arbitrary Hopf lifts.
It explicitly requires lift existence, avoiding a vacuous statement. Existence
and independence of lift choices are proved. The `HomogeneousBridge` module now proves the fixed-degree binary-form
dehomogenization bridge. The singular-family modules explicitly reconcile
the real polynomial sign convention with these homogeneous forms. The
distant-point theorem works directly with binary forms. The real finite signed-fan picture does not directly generalize to complex
absolute values, which involve continuous phases.

## Distant-point subcase

The [formal English proof](docs/proofs/DISTANT_POINT.md) and the checked theorem
[`DistantPoint.distant_point_extension`](Atiyah/DistantPoint.lean) establish:

> If a fixed core has independent Atiyah point forms, adding one point
> sufficiently far along any fixed nonzero ray preserves independence.

The conclusion gives actual distinct points, existence of displacement Hopf
lifts, and independence for **every** lift family, on a single tail R > R₀.
This is end-to-end for the advertised conditional subcase. It does not prove
independence of an unknown core, give an effective threshold, cover every
finite spike length, or establish C2.

| Module | Checked content |
| --- | --- |
| `FarDirection` | Normalized direction convergence and eventual avoidance of a finite core. |
| `SpikeLimit` | Affine polynomial boundary independence and square determinant certificates. |
| `DeterminantStability` | Determinant openness and a real signed-cell consequence. |
| `Gauge` | Nonzero Hopf lift proportionality, arbitrary-lift invariance, physical scaling. |
| `ContinuousLift` | Local continuous sections at every nonzero displacement, both poles, antipodal factors, convergent ray lifts. |
| `GeometricLimit` | Homogeneous boundary independence, coefficient convergence, and openness via finite coefficient witnesses. |
| `DistantPoint` | Actual enlarged configurations and the complete conditional distant-point theorem. |

The integrated proof uses homogeneous forms and a finite coefficient witness,
so it needs neither an affine-root chart nor a degree/basis conversion.
Independent [mathematical](docs/reviews/DISTANT_POINT_MATH.md) and
[kernel/statement](docs/reviews/DISTANT_POINT_KERNEL.md) reviews record the
acceptance criteria and results.

## Two-cluster gluing and independent research

`TwoCluster.two_cluster_extension` proves that two fixed cores satisfying C1
remain independent when one is translated sufficiently far along any nonzero
ray. The exact combined points, distinctness, lift existence, and independence
for every lift family are in the conclusion. See the
[English proof](docs/proofs/TWO_CLUSTER.md) and
[independent review](docs/reviews/TWO_CLUSTER_REVIEW.md).

The new modules `TwoClusterAlgebra`, `TwoClusterGeometry`, `TwoClusterLift`, and
`TwoCluster` implement the boundary complementarity, coefficient limits, actual
physical lifts, and final theorem. Binary-tree recursion is not yet a separately
implemented constructor; it follows mathematically by finite sequential gluing.

Read [the simplified explanation](docs/SEPARATION_EXPLAINED.md),
[physics/QFT routes](docs/research/PHYSICS_ROUTES.md), and
[the independent geometry investigation](docs/research/INDEPENDENT_GEOMETRY.md).
`ReflectionObstruction` checks a small matrix obstruction to one raw-determinant
reflection-positivity proposal; it does not rule out every QFT construction.

## Singular configuration verification

The proof chain is geometry → explicit polynomial rows → exact boundary
elimination → kernel-checked radical arithmetic → an interior determinant
zero → dependence of the actual complex homogeneous point forms.

`SingularCertificate.computedQuad_eq` checks the complete integer calculation
using `decide +kernel`. `SingularCertificateBridge` proves that the list
algorithm is the polynomial elimination used by `SingularElimination`.
`SingularBoundary.pathDet_one_negative` discharges the endpoint sign;
`SingularCounterexample` applies it to the geometric existence theorem.
There is no unproved sign hypothesis in the final theorems.

The Python scripts `scripts/check_boundary_certificate.py` and
`scripts/check_boundary_quad.py` are supplementary reproducibility checks.
Neither script is a premise of the Lean proof.

## Agent workflow

The project uses several agents to propose proofs and repair them against Lean's
compiler and kernel. No model parameters are trained; this is compiler-guided
proof search, not an RL training run. A successful reduction is not counted as a
proof of its remaining geometric premise.

Maintain the English and Lean arguments together using [the proof workflow](docs/PROOF_WORKFLOW.md).

See [the attack plan](docs/ATTACK.md) and [the session record](docs/SESSION.md).

## Sources

- Atiyah and Sutcliffe, [The Geometry of Point Particles](https://doi.org/10.1098/rspa.2001.0913).
- [Existing Lean statement of C1](https://github.com/google-deepmind/formal-conjectures/pull/4768).
  This project uses its own incidence-based definitions; the upstream statement
  is a reference, not an imported theorem or dependency.
- Malkoun, [A new proof of Atiyah's conjecture on configurations of four points](https://arxiv.org/abs/2209.02457).
- Mazur–Petrenko, [On the conjectures of Atiyah and Sutcliffe](https://arxiv.org/abs/1102.4662).
- Earlier experiment: [learning-atiyah-conjecture-v2](https://github.com/fennecs-system/learning-atiyah-conjecture-v2).
