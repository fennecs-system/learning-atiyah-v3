import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficient matrices and their determinant divisor

The coefficient matrix has polynomial columns and ascending degree rows.
Its determinant is a multihomogeneous equation in the column coefficients:
rescaling each column multiplies it by the product of the scale factors.
Consequently its zero locus descends to a product of projective spaces.
The statements below establish the underlying algebra; they do not construct
schemes or prove that the Atiyah configuration map avoids this divisor.
-/

namespace Atiyah.Algebraic

open Polynomial Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The first `n` coefficients of each of `n` polynomials, as columns.
No degree bound is imposed here; geometric applications must supply one. -/
def coefficientMatrix (p : Fin n → K[X]) : Matrix (Fin n) (Fin n) K :=
  fun i j => (p j).coeff i.val

/-- Independent column rescaling gives the weight `(1,...,1)` character. -/
theorem det_coefficientMatrix_rescale (p : Fin n → K[X]) (c : Fin n → K) :
    (coefficientMatrix (fun j => C (c j) * p j)).det =
      (∏ j, c j) * (coefficientMatrix p).det := by
  have hmat : coefficientMatrix (fun j => C (c j) * p j) =
      Matrix.of (fun i j => c j * coefficientMatrix p i j) := by
    ext i j
    exact Polynomial.coeff_C_mul (p j)
  rw [hmat, Matrix.det_mul_row]

/-- Monomials provide a point outside the universal determinant divisor. -/
theorem coefficientMatrix_monomials :
    coefficientMatrix (fun j : Fin n => (X : K[X]) ^ j.val) = 1 := by
  ext i j
  simp [coefficientMatrix, Polynomial.coeff_X_pow, Matrix.one_apply, Fin.ext_iff]

/-- The ordered monomial basis has determinant one, including dimension zero. -/
theorem det_coefficientMatrix_monomials :
    (coefficientMatrix (fun j : Fin n => (X : K[X]) ^ j.val)).det = 1 := by
  rw [coefficientMatrix_monomials, Matrix.det_one]

/-- The scaled monomial determinant is exactly the product of its scales. -/
theorem det_coefficientMatrix_scaled_monomials (c : Fin n → K) :
    (coefficientMatrix (fun j => C (c j) * X ^ j.val)).det = ∏ j, c j := by
  rw [det_coefficientMatrix_rescale, det_coefficientMatrix_monomials, mul_one]

section Domain

variable [IsDomain K]

/-- Nonzero rescaling preserves the complement of the determinant divisor. -/
theorem det_coefficientMatrix_rescale_ne_zero_iff (p : Fin n → K[X])
    (c : Fin n → K) (hc : ∀ j, c j ≠ 0) :
    (coefficientMatrix (fun j => C (c j) * p j)).det ≠ 0 ↔
      (coefficientMatrix p).det ≠ 0 := by
  rw [det_coefficientMatrix_rescale]
  have hprod : (∏ j, c j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  exact mul_ne_zero_iff.trans (and_iff_right hprod)

/-- Algebraic baseline for a future geometric collinear normal-form proof.
This theorem does not identify any configuration with these monomials. -/
theorem det_coefficientMatrix_scaled_monomials_ne_zero
    (c : Fin n → K) (hc : ∀ j, c j ≠ 0) :
    (coefficientMatrix (fun j => C (c j) * X ^ j.val)).det ≠ 0 := by
  rw [det_coefficientMatrix_scaled_monomials]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)

end Domain
end Atiyah.Algebraic
