# Working on this proof project

Read README.md and docs/ATTACK.md before changing mathematical scope.

- Use Lean 4.19.0 and the pinned mathlib manifest.
- Assign separate files to working agents; coordinate shared definitions before editing them.
- Iterate candidate proof -> compiler diagnostics -> repair. This is proof search,
  not reinforcement-learning weight training.
- Never add `sorry`, `admit`, `axiom`, `native_decide`, or an assumption equivalent
  to the target conjecture to make a theorem compile. Open goals are named `Prop`
  definitions or documented research tasks, not asserted theorems.
- Do not weaken distinctness, erase pole/collinear cases, or substitute generic
  nonvanishing for universal nonvanishing.
- Distinguish real planar cells from the full complex three-dimensional problem.
- Put unverified scratch outside the default library; describe failed mathematical
  routes in docs/ATTACK.md rather than leaving broken Lean in the build.
- Before delivery run scripts/check.sh and report the exact checked commit.
- Keep README status and remaining bridges accurate. No claim of solving C1
  without a theorem for all configurations and an audited chain to its definition.

## English/Lean synchronization

- Follow docs/PROOF_WORKFLOW.md. Before a new proof attack, write a formal-English
  statement with stable step IDs and a correspondence ledger.
- Update the English guide when Lean exposes missing hypotheses or changes the
  statement. Conversely review that each Lean theorem actually discharges its
  English obligation rather than a weaker or merely conditional substitute.
- Keep complete paper proofs, checked components, and end-to-end checked
  configuration cases distinctly labelled.
