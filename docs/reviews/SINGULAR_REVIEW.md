# Independent singular-family audit

Reviewer scope: the fixed planar family m=1, a=52, b=30, R=32,
u=d=1, v=0. This is a review of a proposed proof chain, not a declaration
that the chain has been completed. Initial repository revision:
`f3c19f0da9f7a8230ef1280cad58a1f4387c9fea`.

## Acceptance criteria

An end-to-end result must produce a `Configuration.Config 84`, a displacement
`LiftFamily`, and failure of complex linear independence of its `pointForm`
family. Gauge invariance can then strengthen the conclusion to every lift.
A negative boundary expression, an abstract IVT theorem, or an abstract
polynomial determinant zero does not alone meet this criterion.

## Conventions and geometry

The manuscript uses factors a Z0 - b Z1; this repository uses a X0 + b X1.
For the real planar family these agree after the common invertible substitution
Z1 = -X1. This is a single substitution for all 84 forms. It preserves linear
independence but must be implemented or avoided by defining compatible rows.
There is no need to resolve the manuscript's complex-conjugation typography
for this real slice, and this audit makes no claim for general complex rings.

For an ordered forward displacement (delta,w), let
D=delta+sqrt(delta^2+w^2), s=w/D. At interior parameters every height difference
is positive, hence D>0. The spinor (sqrt(D),sqrt(D)*s) has repository Hopf image
(delta,w). Its antipode (-sqrt(D)*s,sqrt(D)) has image (-delta,-w).
After the common variable substitution, the forward factor is sqrt(D)(1-sT)
and the reverse factor is -sqrt(D)(T+s). These factors are nonzero scalar
multiples of the manuscript factors. Reverse signs contribute fixed row signs;
they must not be silently used to transfer determinant *sign*. For dependence,
nonzero row scaling suffices.

The path is strictly increasing in height for 0<t<1: lower heights are at
most zero, A has height 31, B has height 32, and upper heights exceed 32.
Within each axial group the step t(1-t) is positive. The coordinates in the
new `SingularGeometry.path` definition match the manuscript exactly.

At t=0 and t=1 the path has collisions. Endpoint coefficient matrices are
continuous extensions of normalized interior rows, not point forms of a
valid Config 84. The IVT conclusion must be in the strict interval; endpoint
nonzero determinants exclude endpoint roots. No endpoint lift existence or
endpoint distinctness may be assumed.

## Arithmetic and determinant audit

The dependency-free Python certificate was rerun at 256 bits. It certified
all four residual evaluations positive and the scaled numerator in
[-30666146689591218473741,-30666146689591218473740]. Integer square-root
bounds and outward floor/ceiling multiplication are sound interval operations.
The recurrence computes coefficients d_j of C/L, then the residual W has
constant d_a, linear coefficient c_(a+1)-alpha*x*d_(a-1), and remaining
coefficients c_(a+2), etc. This matches the manuscript elimination formula.
The ring couplings are both multiplied by 31, multiplying the numerator by
31^2>0. The denominator 1-y is positive.

An independent direct numerical expansion of all 84 normalized path rows,
followed by 120-digit Decimal Gaussian elimination, gave

| t | determinant (approximate) |
|---|---:|
| 9/10 | +1.64274816030556e17 |
| 99/100 | -8.72678171947989e18 |
| 1 | -5.44749083940297e19 |

These values are evidence only, not rigorous certificates. The rational
interior endpoints could avoid collision limits, but would require bounds for
many varying radicals and an 84-square determinant. The boundary computation
uses only sqrt(2) and sqrt(962), so it is likely the shorter formal route.

The elimination basis in manuscript Lemma 3.3 has determinant +1: first
eliminate columns below a using the lower rows' constant pivot 1; the two
middle monomials give pivots at a,a+1; subsequent upper rows are monic and
are triangular when ordered by their highest degrees. Evaluating degree-less-
than-two remainders at y and 1 has determinant 1-y>0. Thus the stated sign
orientation is consistent with row order lower,A,B,upper and ascending powers.
Transposing the coefficient matrix preserves its determinant.

## Formal scope checkpoints

- `SingularGeometry.config` is actual configuration data only for interior t.
- `normalized_incidence` is one pair identity, not yet a full LiftFamily or
  pointForm/product identification.
- `SingularRows.det_zero` means the determinant with all slope inputs zero;
  it is not itself the theorem that geometric path slopes extend to zero.
- `SingularRows.det_continuous` assumes continuity of slope inputs. The path
  slope formulas and their endpoint extensions must discharge those inputs.
- A proof that a literal `boundaryQuad.eval` is negative must be accompanied
  by a kernel-checked equality to the residual numerator. An external script
  selecting that constant is not such a proof.
- The residual numerator must be linked to the determinant of the same
  normalized rows used throughout the continuous path.
- Coefficient determinant zero must imply polynomial dependence, including
  the degree bound; truncating arbitrary higher-degree polynomials to 84
  coefficients would not suffice.
- Real polynomial dependence transfers to complex homogeneous binary forms,
  but the field-extension and homogenization steps must be justified.

Pending bridges must remain explicitly named obligations until checked.

Independent compilation during development: `lake env lean` exited 0 for
`Atiyah/SingularRows.lean`, `Atiyah/SingularGeometry.lean`, and
`Atiyah/SingularCertificate.lean` using the session's pinned Lean environment.
The first two emitted only linter warnings. These per-file checks are not a
replacement for the final integrated `scripts/check.sh` and its axiom audit.

`SingularCrossing.exists_dependent_rows` was also statement-reviewed: it
explicitly requires the degree bound at every interior parameter and obtains
real dependence, not complex geometric dependence. `SingularElimination`
exposes its determinant-one basis and remainder-decomposition obligations;
its block algebra does not disguise those missing polynomial identities.

## Constructive decomposition addition

At the coordinating agent's request, the reviewer added and independently
compiled `SingularDivision.lean` (no errors or warnings). This proves the
constructive low-degree elimination and quadratic decomposition, with exact
degree bounds. Its finite geometric inverse modulo X^a is not yet identified
with the certificate's list recurrence. It supplies an actual polynomial
identity to the matrix elimination work, but does not close that arithmetic
algorithm bridge. Stable SD1–SD3 obligations are recorded in its module header.

The duplicate independent Crossing/Elimination compilation sessions were
cancelled on request to reduce shared resource contention; their success is
not claimed by this review.

## Later checked semantic bridges

`SingularCertificateBridge.lean` has now compiled successfully. Its SCB1–SCB5
ledger proves list multiplication and evaluation semantics, the prefix fold
invariant, exact low-axis decomposition for the actual `eliminated` list,
concrete ring-list product formulas, and degree bounds. Thus the earlier
list-recurrence identification objection is discharged at the polynomial
level. The full coefficient determinant link still belongs to the boundary
elimination module and must be checked when integrated.

The updated geometry source now constructs a physical `LiftFamily`, proves
positive row scaling, and relates actual pointForm independence to normalized
binary-form independence. The RowBridge source explicitly applies common
reflection T↦−T and the nonzero product of reversed-edge signs; it uses
homogeneity for the dehomogenization bridge. These statements address the
specific convention and normalization concerns above. They do not by
themselves identify grouped path rows with the generic SingularRows matrix.

The arithmetic author reports successful kernel checking of computedQuad_eq
and boundary_numerator_negative. Unlike the initial literal-constant theorem,
these statements explicitly identify the computed list numerator. This review
has inspected their statements and source, without repeating the costly
kernel computation independently.

## Full source-chain audit before final compilation

Verdict at this checkpoint: **the source argument reaches the advertised
84-point geometric target once the unconditional boundary sign is supplied
to the family theorem. No mathematical gap or hidden target assumption was
found in the inspected chain. This is a source-level verdict, pending final
compilation, import integration, and the transitive axiom audit.**

The specific chain inspected is:

1. `SingularCertificate.boundary_numerator_negative` proves the exact real
   list numerator negative. `computedQuad_eq` uses kernel reduction, not
   `native_decide`. Its interpretation through Quad.eval is explicit.
2. `SingularCertificateBridge` gives the actual list-to-polynomial products,
   exact low-axis subtraction, residual evaluations, and residual degree bounds.
3. `SingularElimination.det_boundaryMatrix_from_lower_elimination` identifies
   the residual evaluation determinant with (beta−gamma) times the full square
   coefficient determinant. Its intermediate basis determinant and coefficient
   decomposition are proved, not assumptions equivalent to this final identity.
4. `SingularBoundary.boundary_scaled_negative` instantiates those lemmas with
   the two exact 84-point ring rows. `xx<1` is separately proved. Both ring rows
   are scaled by positive 31, so `scaled_det` has the exact multiplier 961.
   `endpoint_det` uses the same equivalence on row and column indices; it
   introduces no permutation-sign ambiguity. `pathDet_one_negative` has no
   mathematical hypotheses.
5. `SingularEndpoint` proves continuity of the same pathDet on [0,1] and its
   initial value 1. In particular, the beta slope at t=1 has zero height gap
   but transverse radius 32, so its denominator is still positive. The proof
   explicitly handles this boundary case; it does not incorrectly require all
   closed-interval height gaps to be strictly positive.
6. `SingularCrossing.interior_zero` uses the two strict endpoint signs to
   exclude t=0 and t=1. No endpoint is used as a Config 84.
7. `SingularFamily.dependent_at_zero` uses the transpose relation between the
   row coefficient matrix and the repository's column coefficient matrix;
   determinant is unchanged. The degree bound is <84, avoiding loss of higher
   coefficients. `complex_dependent_of_det_zero` transfers the same singular
   matrix to complex coefficients.
8. `SingularGroupedRows.paperRow_eq_map_row` proves the exact outgoing-factor
   products for all four groups. `SingularRowBridge` proves the common sign
   substitution and nonzero reversed-factor row signs. `HomogeneousBridge`
   proves a left inverse for dehomogenization on the homogeneous degree-83
   forms, so no unjustified injectivity on arbitrary binary polynomials occurs.
9. `SingularGeometry.config` uses the literal prescribed 84 planar points and
   strict interior height monotonicity. `lifts` proves the actual displacement
   Hopf equations. `pointForm_eq` and positive row scales connect normalized
   products to physical forms. The existing Gauge theorems give equivalence
   for every other `LiftFamily` of that same configuration.
10. `SingularFamily.exists_singular_config` returns a genuine Config 84,
    nonempty lift families, and failure of complex independence for **every**
    such family. `not_c1_of_endpoint_neg` contradicts the exact repository C1
    definition. The only remaining parameter of these assembly theorems at
    review time is `hneg : pathDet 1 < 0`, discharged by item 4. An unconditional
    public wrapper must actually apply that theorem before delivery.

The Hopf convention agrees with the manuscript on this real slice after the
explicit common variable sign change: repository hopf has first component
(a²−b²)/2 and transverse component a*b, so the physical spinor scaling gives
the literal displacement rather than only an unspecified projective direction.
The factor-of-two difference from the manuscript's normalized unit-sphere Hopf
formula is exactly radial normalization. This review claims the fixed m=1,
n=84 counterexample only; it does not verify arbitrary cardinalities, nonreal
cyclic rings, hyperbolic configurations, or a numerically located witness t.

Final acceptance still requires importing the final result in `Atiyah.lean`,
running `scripts/check.sh` at an identified commit, and checking the final
unconditional theorem statements and allowed axiom list. Any unused new module
claimed as audited must also be imported into that audit's environment.

## Independent compiled final-theorem check

The reviewer ran a small standalone Lean file importing
`Atiyah.SingularCounterexample`, checking all four final declarations and printing
their transitive axiom dependencies. The command exited **0**. No full build was
duplicated. The exact axiom output was:

```
'Atiyah.SingularCounterexample.not_C1_84' depends on axioms: [propext, Classical.choice, Quot.sound]
'Atiyah.SingularCounterexample.exists_singular_config' depends on axioms: [propext, Classical.choice, Quot.sound]
'Atiyah.SingularCounterexample.exists_singular_planar_config' depends on axioms: [propext, Classical.choice, Quot.sound]
'Atiyah.SingularCounterexample.exists_singular_parameter' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#check` confirmed `not_C1_84 : ¬ Atiyah.Configuration.C1 84` with no hypotheses.
The planar theorem additionally states that every transverse imaginary
coordinate is zero; it includes lift existence and dependence for every lift.
The parameter theorem explicitly uses `Set.Ioo 0 1`. Printing C1 confirmed the
original universal configuration/lift definition, not a renamed weakening.

**Accepted independent final-theorem verdict:** the compiled imported theorem
chain proves an actual planar 84-point counterexample in the repository's
stated Hopf-incidence model, with arbitrary-lift dependence and only the three
allowed foundational axioms. The reviewer found no discrepancy between these
statements and the audited fixed-family claim. Repository-wide acceptance
remains contingent on the coordinating agent's full `scripts/check.sh` run and
recording its final commit. The working tree was still based on initial commit
`f3c19f0da9f7a8230ef1280cad58a1f4387c9fea` when this independent check ran; that
base commit alone does not contain the new result.

Root integration validation: the default `scripts/check.sh` completed
successfully with all 621 public project declarations audited. The final
unconditional module and the auxiliary division module are both imported by
`Atiyah.lean`. The allowed axiom set remains exactly the three standard
foundations above. The enclosing commit records this checked source tree.
