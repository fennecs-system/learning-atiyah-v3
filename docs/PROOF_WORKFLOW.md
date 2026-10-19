# Bidirectional formal-English and Lean proof development

A proof lives in two synchronized representations:

1. A formal-English argument with exact hypotheses, quantifiers, conventions,
   intermediate claims, and cited external results.
2. Lean definitions and proofs with the same mathematical content.

Neither representation is merely an appendix to the other. Use this loop:

- Write a target statement in English before attempting tactics. Identify what
  varies, what stays fixed, and which constants depend on which data.
- Break the argument into stable labelled obligations (for example DP1–DP6).
- Give each obligation an owned Lean module/lemma and record all extra hypotheses.
- Compile candidate proofs; use type/goal failures to inspect the mathematics,
  not just to search for a tactic that closes a weakened statement.
- Revise the English argument when Lean exposes a missing dimension bound,
  normalization choice, exceptional case, or unjustified implication.
- Review in the other direction: a compiled lemma may be true but insufficient
  for the English claim. Record the missing bridge explicitly.
- Build and audit the complete library before marking a step checked. Update the
  correspondence ledger in the same commit as changes to theorem statements.

## Status vocabulary

- **Mathematical argument:** complete written reasoning, not yet fully formalized.
- **Checked component:** a Lean theorem has compiled and passed the axiom audit.
- **Conditional reduction:** a checked theorem whose inputs include separately
  stated mathematical obligations. Do not report its conclusion unconditionally.
- **End-to-end checked case:** a theorem reaches the named configuration-level
  target from only the advertised geometric hypotheses.
- **Open research goal:** no proof; encode as a proposition or document it.

The [distant-point argument](proofs/DISTANT_POINT.md) is the first worked example.
