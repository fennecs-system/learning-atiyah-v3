import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Algebraic component of the raw-D reflection-positivity obstruction.
See docs/reviews/PHYSICS_REVIEW.md, RP1–RP3. No configuration or QFT claim
is made by this module. -/

open scoped Matrix

namespace Atiyah.ReflectionObstruction

/-- The real three-observable candidate Gram matrix. -/
def kernel (t s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; 1, 1, t; 1, t, s]

/-- RP1: the determinant is independent of the final diagonal entry. -/
theorem det_kernel (t s : ℝ) : (kernel t s).det = -(t - 1)^2 := by
  simp [kernel, Matrix.det_fin_three]
  ring

/-- An explicit direction with negative quadratic form when t ≠ 1. -/
def witness (t s : ℝ) : Fin 3 → ℝ := ![s + 1, -(s + 1), 2 * (t - 1)]

/-- RP2: no estimate or bound on s is needed. -/
theorem negative_witness_identity (t s : ℝ) :
    dotProduct (star (witness t s)) (kernel t s *ᵥ witness t s) =
      -4 * (t - 1)^2 := by
  simp [kernel, witness, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- RP3: the matrix cannot be positive semidefinite unless t = 1. -/
theorem not_posSemidef (t s : ℝ) (ht : t ≠ 1) :
    ¬ (kernel t s).PosSemidef := by
  intro h
  have hnonneg := h.2 (witness t s)
  rw [negative_witness_identity] at hnonneg
  have hsq : 0 < (t - 1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ht)
  nlinarith

end Atiyah.ReflectionObstruction
