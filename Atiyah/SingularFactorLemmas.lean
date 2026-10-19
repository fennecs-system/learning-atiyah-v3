import Atiyah.SingularRowBridge

/-! SG4: Every off-diagonal factor of the actual geometric path is identified
with its corresponding factor in the four explicit paper rows. -/
noncomputable section
namespace Atiyah.SingularRowBridge
open Polynomial SingularGeometry SingularPathFactors

lemma factor_of_lt (t : ℝ) {i j : Fin 84} (h : i < j) :
    factor t i j = 1 - C (directedSlope t i j : ℂ) * X := by
  simp only [factor, paperEdge, if_neg (ne_of_gt h), if_pos h, directedSlope]
lemma factor_of_gt (t : ℝ) {i j : Fin 84} (h : j < i) :
    factor t i j = X + C (directedSlope t j i : ℂ) := by
  simp only [factor, paperEdge, if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le), directedSlope]

@[simp] lemma factor_lower_A (t : ℝ) (i : Fin 52) :
    factor t (lowerIdx i) 52 = 1 - C (SingularRows.alpha i t : ℂ) * X := by
  rw [factor_of_lt t (lowerIdx_lt_A i), slope_lower_A]
@[simp] lemma factor_lower_B (t : ℝ) (i : Fin 52) :
    factor t (lowerIdx i) 53 = 1 - C (SingularRows.chi i t : ℂ) * X := by
  rw [factor_of_lt t (lowerIdx_lt_B i), slope_lower_B]
@[simp] lemma factor_lower_upper (t : ℝ) (i : Fin 52) (j : Fin 30) :
    factor t (lowerIdx i) (upperIdx j) = 1 := by
  rw [factor_of_lt t (lowerIdx_lt_upperIdx i j), slope_lower_upper]
  simp
@[simp] lemma factor_A_lower (t : ℝ) (j : Fin 52) :
    factor t 52 (lowerIdx j) = X + C (SingularRows.alpha j t : ℂ) := by
  rw [factor_of_gt t (lowerIdx_lt_A j), slope_lower_A]
@[simp] lemma factor_B_lower (t : ℝ) (j : Fin 52) :
    factor t 53 (lowerIdx j) = X + C (SingularRows.chi j t : ℂ) := by
  rw [factor_of_gt t (lowerIdx_lt_B j), slope_lower_B]
@[simp] lemma factor_A_B (t : ℝ) :
    factor t 52 53 = 1 - C (SingularRows.tau t : ℂ) * X := by
  rw [factor_of_lt t (by decide : (52 : Fin 84) < 53), slope_A_B]
@[simp] lemma factor_B_A (t : ℝ) :
    factor t 53 52 = X + C (SingularRows.tau t : ℂ) := by
  rw [factor_of_gt t (by decide : (52 : Fin 84) < 53), slope_A_B]
@[simp] lemma factor_A_upper (t : ℝ) (j : Fin 30) :
    factor t 52 (upperIdx j) = 1 + C (SingularRows.gamma j t : ℂ) * X := by
  rw [factor_of_lt t (A_lt_upperIdx j), slope_A_upper]
  simp
@[simp] lemma factor_B_upper (t : ℝ) (j : Fin 30) :
    factor t 53 (upperIdx j) = 1 + C (SingularRows.beta j t : ℂ) * X := by
  rw [factor_of_lt t (B_lt_upperIdx j), slope_B_upper]
  simp
@[simp] lemma factor_upper_lower (t : ℝ) (i : Fin 30) (j : Fin 52) :
    factor t (upperIdx i) (lowerIdx j) = X := by
  rw [factor_of_gt t (lowerIdx_lt_upperIdx j i), slope_lower_upper]
  simp
@[simp] lemma factor_upper_A (t : ℝ) (i : Fin 30) :
    factor t (upperIdx i) 52 = X - C (SingularRows.gamma i t : ℂ) := by
  rw [factor_of_gt t (A_lt_upperIdx i), slope_A_upper]
  simp [sub_eq_add_neg]
@[simp] lemma factor_upper_B (t : ℝ) (i : Fin 30) :
    factor t (upperIdx i) 53 = X - C (SingularRows.beta i t : ℂ) := by
  rw [factor_of_gt t (B_lt_upperIdx i), slope_B_upper]
  simp [sub_eq_add_neg]

@[simp] lemma factor_self (t : ℝ) (i : Fin 84) : factor t i i = 1 := by simp [factor]

end Atiyah.SingularRowBridge
