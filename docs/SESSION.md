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
