# Initial proof-search session — 2026-10-19

## Scope

User authorized a new Lean project and pushes to `fennecs-system/learning-atiyah-v3`,
with several agents and an algebraic-geometric presentation. The original target
is C1; C2's normalized determinant inequality is not claimed.

## Work distribution

- Cells agent: signed cones, lineality, dual-strip lines.
- Obstruction agent: matrix/dual incidence and the pointed-cell equivalence.
- Lift agent: corrected planar Hopf branches and geometric baselines.
- Algebraic agent: coefficient determinant scaling and monomial baselines.
- Configuration agent: 3D incidence definitions and small cases.
- Integrator: toolchain, cross-module review, audit, documentation and GitHub.

Two initial agent tasks stopped at a usage limit. The resumed session reused
surviving source and completed work with fresh agents. Successful proofs were
iterated against Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Validation environment

The official Lean 4.19 Linux binary and official mathlib cache were used.
The local execution environment exposes `/proc/self/exe` but not the numeric
PID path expected by Lean's runtime. A local `readlink` compatibility shim
redirected only the current process's `/proc/<pid>/exe` query to
`/proc/self/exe`. It changed no proof checking or source declarations. The shim
is not a project dependency; CI uses the normal unmodified release.

The checked library contains no admitted results or custom axioms.
`Check.lean` audits every public project declaration for transitive axiom dependencies.
See GitHub Actions for verification with the normal release environment.

## What remains

Generic linear-algebra reductions are not the missing geometric proof.
The full C1 proposition is deliberately a definition. Consult README.md and
ATTACK.md for the exact gaps between current modules and the general theorem.

## Final local verification

- Complete `lake build`: passed.
- `lake env lean Check.lean`: passed for 131 public project declarations.
- 59 named theorem declarations in the six mathematical modules.
- In addition to the initial reductions, the agents proved general Hopf lift
  existence, the planar degree bound, and positive determinant/pointed cells for
  every pair of distinct planar points.
- No general C1, n=3, n=4, or arbitrary-n collinear proof is claimed.

## Distant-point follow-up — 2026-10-19

The user requested a formal-English proof guide corrected in both directions
by Lean, and a subcase motivated by one distant point in the old ML samples.
Three proof agents developed the algebraic boundary, determinant stability, and
normalized-direction limit; a mathematical review supplied the complete paper
argument and literature provenance. An environment agent restored the pinned
local toolchain.

Added `docs/PROOF_WORKFLOW.md` and the step-indexed distant-point guide. The
conditional paper theorem assumes independence of the fixed core and gives
independence after adding a point sufficiently far along a fixed ray. Its full
geometric Lean statement is not yet proved: local continuous complex lifts,
gauge comparison, and coefficient convergence remain explicit obligations.

Validation: complete `scripts/check.sh` passed; 152 public project declarations
passed the transitive axiom audit. Three new modules add 18 named theorems.
No `sorry`, custom axioms, or conjecture assumptions were added as declarations.
The core independence hypothesis is explicit in the conditional extension.

## End-to-end distant-point proof — 2026-10-19

At the user's request, three minimally seeded implementation agents explored
separate gauge, local-section, and homogeneous-limit approaches. Two separate
judgment agents challenged mathematical scope and kernel/statement validity;
the integrator constructed the actual enlarged configuration and final theorem.
Skeptical instructions treated claimed bridges as unproved and sought
counterexamples or hidden assumptions, without asserting false facts.

Result: `Atiyah.DistantPoint.distant_point_extension` is an end-to-end checked
conditional theorem for actual configurations. Given a fixed independent core
and any nonzero ray direction, all sufficiently large ray parameters give
independent point forms for every displacement Hopf lift family. The theorem
also proves existence of those lift families and fixes the new points exactly.

The implementation improved the English guide: direct homogeneous evaluation
handles poles, and a finite coefficient witness proves stability without a
degree/basis bridge. It also distinguishes the product norm on ℝ × ℂ from the
Euclidean radius used in the Hopf formula. Gauge invariance and square-root
physical scaling are now proved, not remaining assumptions.

Validation: complete local `scripts/check.sh` passed, including 197 public
project declarations in the transitive axiom audit. Both judgment agents
independently compiled the final theorem and accepted its mathematical scope.
The final theorem's axiom dependencies are exactly `propext`, `Classical.choice`,
and `Quot.sound`. No admissions or custom axioms were added. The original
configuration and C1 definitions were not weakened or changed.

Four new Lean modules contain 32 public theorem declarations. The English guide
and independent review reports record the exact proof and scope. General C1,
C2, effective thresholds, and all finite spike lengths remain unproved here.

## Two-cluster gluing, fresh attacks, and a status correction — 2026-10-19

User requested skeptical agents, independent attack approaches, and fresh-context
physics/QFT investigation. Three implementation agents handled boundary algebra,
geometry/convergence, and physical lift/gauge assembly; two independent reviewers
checked the cluster proof and physics proposal. Fresh agents independently explored
physics and geometry without first reading the cluster strategy.

Checked outcome: `TwoCluster.two_cluster_extension` proves an exact actual
configuration A ∪ (Ru+B), for fixed C1 cores A,B and any nonzero u, satisfies
C1 for every sufficiently large R and every displacement lift choice. Empty
cores and both Hopf poles remain included. `ReflectionObstruction` separately
proves a 3×3 candidate correlation kernel cannot be positive semidefinite when
t≠1, ruling out one raw-determinant QFT proposal, not all physical approaches.

Important literature correction: fresh search found Jan Eickhoff's Singular
Atiyah Configurations v3 (28 September 2026), claiming general C1 counterexamples.
Earlier unqualified statements that general C1 remained open missed this source.
The project has not formally verified its counterexamples. Independent manuscript
review found no decisive flaw, and a reproducible exact interval calculation now
certifies a negative boundary expression for its 84-point planar-family parameters.
The physical-matrix identification, positive initial endpoint, and interior
singular-configuration argument are not certified by that script. Conditional
fixed-core separation is compatible with the claim.

Validation: integrated `scripts/check.sh` passed for 226 public declarations.
An independent reviewer ran the cluster-only build/audit (219 declarations),
and the physics reviewer compiled/audited its 7 declarations. Root additionally
ran the exact integer-only boundary script successfully. No admissions/custom
axioms or altered original configuration definitions were introduced.

Saved a simplified separation explanation, the English two-cluster proof,
separate physics and geometry reports, and both review reports. Binary-tree
recursion is a mathematical iteration principle; no tree constructor or uniform
scale ratio has been formalized yet. Next priorities are exact geometric
verification of the reported singular family and restricted nonvanishing/
quantitative spectral bounds, rather than assuming universal positivity.

## 2026-10-19 — Formal verification of the reported singular specialization

The m=1 specialization with a=52, b=30, R=32 is now checked end to end.
`SingularCounterexample.not_C1_84` proves `¬ Configuration.C1 84` with no
hypotheses. The companion `exists_singular_planar_config` supplies actual
injective planar points, nonempty physical Hopf lifts, and dependent complex
point forms for every lift family. `exists_singular_parameter` locates the
witness strictly inside the explicit parameter interval, excluding the
colliding endpoints.

The proof includes the physical lift and normalized-row identities, the
common variable sign change, fixed-degree homogeneous dehomogenization,
exact polynomial elimination, and a kernel-checked computation in
Z[sqrt(2),sqrt(962)]. The list-based arithmetic is proved to implement that
polynomial elimination. Scaling both special rows by 31 multiplies the
coefficient determinant by 961. The actual endpoint determinant is negative,
while the opposite endpoint determinant is 1. The real intermediate-value
theorem then gives a singular interior configuration.

Validation: `scripts/check.sh` completed successfully; its transitive audit
passed for all **621 public project declarations**, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Two reviewers separately imported the
final theorems and checked their statements and axiom lists. No `sorry`,
`admit`, custom axiom, `native_decide`, or modified conjecture definition was
introduced. The exact computation uses `decide +kernel`. The final result
is imported by the default `Atiyah` target and normal GitHub CI.

The proof and simplified explanation are in `docs/proofs/SINGULAR_FAMILY.md`
and `docs/SINGULAR_EXPLAINED.md`. This verifies one concrete 84-point
specialization, not the preprint's complete arbitrary-cardinality family.
The existing distant-point and two-cluster results remain conditional on
independent cores and are compatible with this counterexample.
