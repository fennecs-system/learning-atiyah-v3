# Singular path and row audit

Review date: 2026-10-19. This is a source-level mathematical review of the
m=1 specialization against the supplied `singular.txt`, sections 1.2–3.2.
The reviewer implemented `SingularRows`; this is not an independent authorship
review or a substitute for the final kernel audit. Several bridge files were
still being completed when reviewed.

## Formula ledger

For a=52, b=30, R=32, u=d=1, v=0 the points are
L_j=((j−51)t(1−t),0), A=(31,t), B=(32,32t),
U_j=(33−t+jt(1−t),0). These agree with (2.1).
The height order is strict for 0<t<1. In particular U_0 has height 33−t>32;
the equality at t=1 is not an interior collision.

With s(δ,r)=r/(δ+sqrt(δ²+r²)), the five slope families are:

| Family | Height gap | Transverse magnitude |
| --- | --- | --- |
| alpha_j | 31−(j−51)t(1−t) | t |
| chi_j | 32−(j−51)t(1−t) | 32t |
| gamma_j | 2−t+jt(1−t) | t |
| beta_j | 1−t+jt(1−t) | 32t |
| tau | 1 | 31t |

All denominators are positive on [0,1]. The only height gap that can vanish
there is beta's gap at t=1, where its transverse magnitude is 32. Thus beta
really has value 1 at that endpoint. All five slopes vanish at t=0.
The total division convention in Lean alone would not justify continuity at
an arbitrary simultaneous zero; the explicit positivity proof is essential.

The m=1 internal polynomial J is 1. The coupling factors are 1−tau X and
X+tau. The ring rows are respectively products of X+alpha_j and
1+gamma_j X, and products of X+chi_j and 1+beta_j X, times these coupling
factors. The lower row is X^j(1−alpha_j X)(1−chi_j X), and the upper row is
X^(52+j)(X−gamma_j)(X−beta_j). These exactly match (2.12)–(2.13).

At zero the ascending rows are X^0 through X^83. In particular upper rows
start at degree 54, not 52: the two quadratic factors become X². The generic
`matrix_zero` proof correctly gives identity, hence determinant +1. The
checked degree bound is ≤a+b+1, or ≤83 here, so an 84-coordinate coefficient
matrix loses no terms.

At one the slopes are alpha=sqrt(962)−31, chi=gamma=sqrt(2)−1,
beta=1, tau=(sqrt(962)−1)/31. Thus beta−gamma=2−sqrt(2)>0.

## Convention and sign checks

The repository uses homogeneous factors a X0+b X1. Its forward normalized
factor is 1+sX, and reverse normalized factor is X−s. Substitution X↦−X
changes these to 1−sX and −(X+s). Therefore the paper factors are obtained
by a single invertible variable substitution, and a nonzero minus sign on
each reversed factor. `SingularRowBridge.reflect_dehom_edge` states exactly
this identity. Replacing this bridge by literal equality of the two row
conventions would be incorrect.

For row i the reverse-edge sign is (-1)^i. For all 84 rows the product is
(-1)^(84*83/2)=+1; the coefficient substitution has determinant with the same
sign. The proofs only require independence equivalence, so neither sign
calculation needs to be assumed. Positive physical scales from square roots
are nonzero at every interior point. They can vanish at collision endpoints;
no endpoint physical lift assertion should be made.

`SingularRows.matrix` stores rows, whereas `Algebraic.coefficientMatrix`
stores columns. They are transposes. Their determinants coincide; an explicit
transpose identity is still required wherever these interfaces are connected.

The arithmetic certificate uses c=sqrt(962)−1 and k=31. Its coupling factors
are k−cX and c+kX, each k times the normalized coupling factor. Consequently
its eliminated evaluation numerator is k² times the normalized numerator.
The corresponding normalized determinant is certificateNumerator /
(k²*(1−gamma)). The omitted factors are strictly positive, but this scaling
identity must be proved, not inferred merely from the certificate's sign.

## Remaining obligations at review time

1. Finish the exact product identity between `paperRow` and the complex map
   of `SingularRows.row` for every point index. The inspected RowBridge
   already handles reflection and independence, but its group-product proof
   was still in progress.
2. Connect the list recurrence `SingularCertificate.eliminated` to the lower
   polynomial elimination D and W used by `SingularElimination`. Verify the
   list length, tail starting at a+2, and ascending coefficient ordering.
   Mathematically the recurrence yields W_0=d_a and W_1=c_(a+1)−alpha*chi*d_(a−1),
   consistent with the code; the required Lean equality was not yet present.
3. Reindex the sum-type axial determinant to Fin 84 in identical row and
   column order. A simultaneous reindex has no determinant sign; a one-sided
   permutation can change the sign and must not be silently discarded.
4. Instantiate continuity and endpoint positivity for the actual path, prove
   the endpoint determinant is negative via the previous identities, and
   apply IVT on the closed interval. The obtained zero must lie strictly
   inside it before invoking the actual distinct-point configuration.
5. Use the homogeneous degree-83 dehomogenization equivalence and the
   nonzero lift scalings to conclude failure of the repository's full C1
   statement. An arithmetic negative numerator alone is not that conclusion.

No mathematical mismatch was found in the inspected m=1 row formulas,
endpoint constants, or convention transformation. A final refutation claim
remains contingent on the complete checked bridge chain above. This review
makes no claim about the general-m Fourier argument or the paper's
hyperbolic extension.

## Final theorem review

After completion of `SingularCounterexample.lean`, the reviewer inspected the
final theorem and its imported `SingularFamily` / `SingularBoundary` chain.
The previous remaining-obligation list describes the earlier review snapshot;
these obligations are now discharged in the final chain.

Verdict: **accepted for the stated 84-point planar counterexample within the
repository's full physical Hopf-lift definition of C1**.

* `Config 84` includes `Function.Injective point`. The chosen parameter lies
  strictly in (0,1), and the path's height-strict-monotonicity proof supplies
  this distinctness. Endpoint collisions are not used as configurations.
* `LiftFamily p` requires the unnormalized physical Hopf equation for every
  directed off-diagonal displacement. This is not an abstract polynomial
  family or a list of arbitrary complex roots.
* `exists_singular_planar_config` explicitly includes `Nonempty (LiftFamily p)`
  and quantifies dependence over **every** such lift family. The statement is
  neither vacuous nor tied only to convenient normalized representatives.
* Its explicit planarity condition is `(p.point i).2.im = 0` for every index,
  placing all points in the real plane inside ℝ×ℂ.
* The degree bound is 83<84. The final family proof explicitly identifies its
  coefficient matrix as the transpose of `pathMatrix`; the determinant
  equality is proved using `Matrix.det_transpose`.
* `SingularBoundary.scaled_det` proves the exact positive factor 961 between
  the certificate's scaled boundary determinant and the path determinant.
  Its list-elimination bridge and axial determinant theorem supply the
  actual endpoint sign; the final counterexample theorem has no residual
  endpoint-sign hypothesis.
* `not_C1_84` separately gives failure of the repository's original C1
  proposition. The stronger planar existence theorem is the reviewed result.

A fresh scratch import (no full rebuild) ran:

```lean
#check Atiyah.SingularCounterexample.exists_singular_planar_config
#print axioms Atiyah.SingularCounterexample.exists_singular_planar_config
```

Lean printed the existential planar configuration, lift existence, and
arbitrary-lift dependence statement above. Its complete transitive axiom list
was exactly `[propext, Classical.choice, Quot.sound]`. No admitted proof,
custom axiom, or native evaluation axiom appears in this final theorem.
The repository-wide `scripts/check.sh` run remains the root agent's separate
release gate; this review does not report that run's result or a final commit.
