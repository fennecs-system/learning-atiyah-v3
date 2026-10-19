# Formal verification of the 84-point planar singular configuration

Status: the end-to-end Lean theorem is assembled and compiled. The session
record reports the complete build and axiom-audit result.
Source: Jan Eickhoff, *Singular Atiyah Configurations*, v3, 28 September 2026,
https://zenodo.org/records/23024340. We verify a concrete m=1 specialization,
not the entire arbitrary-cardinality asymptotic family.

## Target

For a=52, b=30 and R=32, set

- L_j(t)=((j−51)t(1−t),0), j=0,…,51;
- A(t)=(31,t);
- B(t)=(32,32t);
- U_j(t)=(33−t+jt(1−t),0), j=0,…,29.

The proved existence theorem gives some t strictly between 0 and 1 with
84 distinct planar points and dependent complex homogeneous Atiyah forms.
The final theorem concludes `¬ Configuration.C1 84`.
The witness t need not be rational or computable. No endpoint is presented as
a distinct-point counterexample: many axial points coincide at t=0 or t=1.

## SG1 — Geometry and normalization

The heights are strictly increasing for 0<t<1, hence all points are distinct.
For every ordered pair with positive height difference δ and transverse
difference w, define s=w/(δ+sqrt(δ²+w²)). The normalized forward and reverse
factors are 1−sT and T+s in the paper. Actual Hopf incidence requires a nonzero
scale sqrt(δ+sqrt(δ²+w²)). The repository uses a plus-sign binary-form convention;
a common variable sign change, or a consistently reflected planar embedding,
is required. Prove this bridge, rather than silently treating conventions as equal.

## SG2 — Polynomial path and its initial endpoint

The 84 normalized univariate rows have the product formulas of manuscript
Section 2, with no cyclic Fourier transform needed for m=1. Each coefficient
extends continuously to [0,1]. At t=0, in point order L,A,B,U, they are exactly
1,T,…,T^83, so their coefficient determinant is +1.

## SG3 — Boundary elimination

At t=1 let x=y=sqrt(2)−1, alpha=sqrt(962)−31, tau=(sqrt(962)−1)/31.
The lower rows are T^j L(T), L=(1−alpha T)(1−xT); the upper rows are
T^(52+j) U(T), U=(T−y)(T−1). The two special rows are
A=(T+alpha)^52(1+yT)^30(1−tau T) and
B=(T+x)^52(1+T)^30(T+tau).

Divide out the lower rows by truncated series: D_C=trunc_<52(C/L),
W_C=(C−L D_C)/T^52. The determinant equals

    (W_A(y)W_B(1)−W_A(1)W_B(y))/(1−y).

Prove the full coefficient-matrix identity, including row order, degree bounds,
and the unit determinant of the intermediate basis. An isolated 2×2 identity
is not yet the geometric determinant formula.

## SG4 — Kernel-checked arithmetic

The numerator is negative and 1−y positive. The existing Python interval script
is an audit reference only; it is not accepted as a Lean premise. Use exact
integer/rational computation with proved interpretation in the real algebraic
field Q(sqrt(2),sqrt(962)), or a verified interval evaluator. Every generated
certificate must be checked by Lean's kernel; no `native_decide` or untrusted
numerical oracle is allowed.

## SG5 — Interior crossing

The real determinant is continuous on [0,1], positive at 0 and negative at 1.
The intermediate value theorem yields t in (0,1) with zero determinant.
Strict endpoint signs ensure the witness is interior.

## SG6 — Return to actual C1

Use degree bounds to convert coefficient singularity to dependence of the
univariate rows. Transfer across the real-to-complex coefficient embedding,
fixed-degree homogenization, the common sign convention change, and nonzero
column scales. Obtain an actual `Config 84` and an actual `LiftFamily` whose
binary point forms are dependent. This refutes universal C1 at that size.
Gauge invariance may additionally transfer dependence to every lift family.

## Ledger

| Step | Module | Status |
| --- | --- | --- |
| SG1 | `SingularGeometry`, `SingularPathFactors` | Actual interior configurations, lifts, nonzero scales and slope identities checked |
| SG2 | `SingularRows`, `SingularRowBridge`, `SingularGroupedRows`, `SingularEndpoint` | Exact geometric row identification, continuity, degree bounds and determinant at zero checked |
| SG3 | `SingularElimination`, `SingularIndex`, `SingularBoundary` | Full coefficient-matrix elimination and positive scaling by 31² |
| SG4 | `SingularCertificate`, `SingularCertificateBridge`, `SingularBoundary` | Kernel-checked arithmetic, list semantics and actual negative endpoint determinant |
| SG5 | `SingularCrossing`, `SingularFamily` | Strictly interior determinant zero by the intermediate value theorem |
| SG6 | `HomogeneousBridge`, `SingularFamily`, `SingularCounterexample` | Actual configuration, dependence for every lift family, and `¬ Configuration.C1 84` |

The final entry points are `SingularCounterexample.exists_singular_config`,
`SingularCounterexample.exists_singular_parameter`, and
`SingularCounterexample.not_C1_84`. They have no endpoint-sign or
singularity hypothesis. The generic endpoint theorem in `SingularFamily`
retains a sign argument deliberately; the final module supplies the proved
sign from `SingularBoundary`.

The arithmetic certificate scales each special row by 31. Thus its numerator
is 31² times the unscaled numerator, and `SingularBoundary.scaled_det` proves
the corresponding factor 961 in the full determinant. This positive factor
does not change the sign.

The independent reviewer must check statements as well as compilation: no
assumption may hide a boundary sign, determinant identity, or singularity of
an actual finite-parameter configuration.
