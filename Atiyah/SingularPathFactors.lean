import Atiyah.SingularGeometry
import Atiyah.SingularRows

/-!
SG3: The ordered edge slopes of the actual 84-point path are precisely the
five slope families used in the paper's row formulas. These identities hold
as total functions, including the endpoints; physical distinctness is only
asserted for interior parameters by SingularGeometry.
-/
noncomputable section
namespace Atiyah.SingularPathFactors
open SingularGeometry

def lowerIdx (j : Fin 52) : Fin 84 := ⟨j.val, by omega⟩
def upperIdx (j : Fin 30) : Fin 84 := ⟨54+j.val, by omega⟩

def directedSlope (t : ℝ) (i j : Fin 84) : ℝ :=
  SingularGeometry.slope ((path t j).1-(path t i).1) ((path t j).2-(path t i).2)

@[simp] theorem path_lowerIdx (t : ℝ) (j : Fin 52) :
    path t (lowerIdx j) = (((j.val : ℝ)-51)*t*(1-t), 0) := path_lower t j
@[simp] theorem path_upperIdx (t : ℝ) (j : Fin 30) :
    path t (upperIdx j) = (33-t+(j.val : ℝ)*t*(1-t), 0) := path_upper t j

@[simp] theorem lowerIdx_lt_A (j : Fin 52) : lowerIdx j < 52 := by
  change j.val < 52
  exact j.isLt
@[simp] theorem lowerIdx_lt_B (j : Fin 52) : lowerIdx j < 53 := by
  change j.val < 53
  omega
@[simp] theorem A_lt_upperIdx (j : Fin 30) : (52 : Fin 84) < upperIdx j := by
  change 52 < 54+j.val
  omega
@[simp] theorem B_lt_upperIdx (j : Fin 30) : (53 : Fin 84) < upperIdx j := by
  change 53 < 54+j.val
  omega
@[simp] theorem lowerIdx_lt_upperIdx (i : Fin 52) (j : Fin 30) :
    lowerIdx i < upperIdx j := by
  change i.val < 54+j.val
  omega

@[simp] theorem slope_lower_lower (t : ℝ) (i j : Fin 52) :
    directedSlope t (lowerIdx i) (lowerIdx j) = 0 := by
  simp [directedSlope]
@[simp] theorem slope_upper_upper (t : ℝ) (i j : Fin 30) :
    directedSlope t (upperIdx i) (upperIdx j) = 0 := by
  simp [directedSlope]
@[simp] theorem slope_lower_upper (t : ℝ) (i : Fin 52) (j : Fin 30) :
    directedSlope t (lowerIdx i) (upperIdx j) = 0 := by
  simp [directedSlope]

@[simp] theorem slope_lower_A (t : ℝ) (j : Fin 52) :
    directedSlope t (lowerIdx j) 52 = SingularRows.alpha j t := by
  simp [directedSlope, SingularRows.alpha, SingularRows.slope,
    SingularGeometry.slope, denominator]
@[simp] theorem slope_lower_B (t : ℝ) (j : Fin 52) :
    directedSlope t (lowerIdx j) 53 = SingularRows.chi j t := by
  simp [directedSlope, SingularRows.chi, SingularRows.slope,
    SingularGeometry.slope, denominator]
@[simp] theorem slope_A_B (t : ℝ) :
    directedSlope t 52 53 = SingularRows.tau t := by
  simp only [directedSlope, path_A, path_B, SingularRows.tau]
  change SingularGeometry.slope (32-31) (32*t-t) = SingularRows.slope 1 (31*t)
  have h : 32*t-t = 31*t := by ring
  rw [h]
  norm_num [SingularGeometry.slope, denominator, SingularRows.slope]
@[simp] theorem slope_A_upper (t : ℝ) (j : Fin 30) :
    directedSlope t 52 (upperIdx j) = -SingularRows.gamma j t := by
  simp only [directedSlope, path_A, path_upperIdx]
  have h : 33-t+(j.val : ℝ)*t*(1-t)-31 = 2-t+(j.val : ℝ)*t*(1-t) := by ring
  rw [h, zero_sub, slope_neg]
  rfl
@[simp] theorem slope_B_upper (t : ℝ) (j : Fin 30) :
    directedSlope t 53 (upperIdx j) = -SingularRows.beta j t := by
  simp only [directedSlope, path_B, path_upperIdx]
  have h : 33-t+(j.val : ℝ)*t*(1-t)-32 = 1-t+(j.val : ℝ)*t*(1-t) := by ring
  rw [h, zero_sub, slope_neg]
  rfl

end Atiyah.SingularPathFactors
