# Exact arithmetic boundary certificate

This is a checked arithmetic component, not an end-to-end singular configuration.

## Formal English statement

For α = √962 − 31, x = √2 − 1, c = √962 − 1 and k = 31, let
A(T) = (α+T)^52 (1+xT)^30 (k−cT) and
B(T) = (x+T)^52 (1+T)^30 (c+kT).
For each coefficient list C, set d₋₂=d₋₁=0 and
 dⱼ = Cⱼ +(α+x)dⱼ₋₁ − αx dⱼ₋₂ for j=0,…,52.
Define the list W(C) by its first coefficient d₅₂, second coefficient
C₅₃−αx d₅₁, and remaining coefficients C₅₄,C₅₅,….
The precisely implemented list expression
W(A)(x)W(B)(1)−W(A)(1)W(B)(x) is strictly negative.

The interpretation of this recurrence as polynomial elimination, and the
identification with a geometric determinant, are separate bridges.

## Checked correspondence ledger

| Step | Obligation | Lean declaration |
|---|---|---|
| SC-C1 | Integer quadruple arithmetic evaluates correctly at √2 and √962. | `Quad.eval_add`, `Quad.eval_neg`, `Quad.eval_mul` |
| SC-C2 | Coefficient multiplication, elimination recurrence and evaluation commute with the real evaluation map. | `map_linear`, `map_eliminated`, `map_evaluate`, `map_numerator` |
| SC-C3 | The full quadruple computation equals four explicit integer coefficients. | `computedQuad_eq` |
| SC-C4 | Rational bounds on √2, √962 and √1924 imply the quadruple evaluates negatively. | `boundaryQuad_negative` |
| SC-C5 | The real list expression above is negative. | `boundary_numerator_negative` |

All declarations are in `Atiyah.SingularCertificate`. SC-C3 uses Lean's
`decide +kernel`, which asks the kernel to reduce a decidable integer equality;
it does not use native compilation or an external arithmetic oracle. SC-C4 uses
1024-bit rational square-root enclosures, verified from squared inequalities.
`scripts/check_boundary_quad.py` regenerates the four coefficients for inspection;
the theorem does not trust that script or its output.
