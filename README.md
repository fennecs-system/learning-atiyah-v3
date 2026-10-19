# Learning Atiyah v3

A Lean 4 research project attacking the original Atiyah configuration conjecture
(C1) through polynomial coefficients, dual incidence, and signed winner cones.

**The general conjecture is not proved.** This repository contains checked
reductions and small baselines. The missing geometric nonvanishing argument is
explicit; no open theorem is admitted into the library.

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
pointed. The equivalence is proved; geometric pointedness for all configurations
is still open here.

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
It explicitly requires lift existence, avoiding a vacuous statement. Existence is proved. Independence of lift choices, the binary-form basis bridge
to coefficient matrices, and the full identification with other standard conventions
must still be completed before claiming an end-to-end formalization of those reductions
for C1. The real finite signed-fan picture does not directly generalize to complex
absolute values, which involve continuous phases.

## Agent workflow

The project uses several agents to propose proofs and repair them against Lean's
compiler and kernel. No model parameters are trained; this is compiler-guided
proof search, not an RL training run. A successful reduction is not counted as a
proof of its remaining geometric premise.

See [the attack plan](docs/ATTACK.md) and [the session record](docs/SESSION.md).

## Sources

- Atiyah and Sutcliffe, [The Geometry of Point Particles](https://doi.org/10.1098/rspa.2001.0913).
- [Existing Lean statement of C1](https://github.com/google-deepmind/formal-conjectures/pull/4768).
  This project uses its own incidence-based definitions; the upstream statement
  is a reference, not an imported theorem or dependency.
- Malkoun, [A new proof of Atiyah's conjecture on configurations of four points](https://arxiv.org/abs/2209.02457).
- Mazur–Petrenko, [On the conjectures of Atiyah and Sutcliffe](https://arxiv.org/abs/1102.4662).
- Earlier experiment: [learning-atiyah-conjecture-v2](https://github.com/fennecs-system/learning-atiyah-conjecture-v2).
