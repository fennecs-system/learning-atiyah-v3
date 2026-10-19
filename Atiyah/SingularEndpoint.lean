import Atiyah.SingularRows

/-! Exact simplifications of the endpoint slopes. -/
noncomputable section
namespace Atiyah.SingularEndpoint
attribute [local irreducible] Matrix.detRowAlternating
open SingularRows
set_option maxHeartbeats 40000
set_option maxRecDepth 1000
set_option Elab.async false

theorem slope_31_1 : SingularRows.slope 31 1 = Real.sqrt 962 - 31 := by
  have hs : (Real.sqrt 962)^2 = 962 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (962 : ℝ)
  unfold SingularRows.slope
  norm_num
  rw [← one_div]
  apply (div_eq_iff (by positivity : (31 : ℝ) + Real.sqrt 962 ≠ 0)).2
  nlinarith

theorem slope_1_1 : SingularRows.slope 1 1 = Real.sqrt 2 - 1 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold SingularRows.slope
  norm_num
  rw [← one_div]
  apply (div_eq_iff (by positivity : (1 : ℝ) + Real.sqrt 2 ≠ 0)).2
  nlinarith

theorem slope_32_32 : SingularRows.slope 32 32 = Real.sqrt 2 - 1 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : Real.sqrt (2048 : ℝ) = 32 * Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2048)
    have hn := Real.sqrt_nonneg (2048 : ℝ)
    have hn2 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold SingularRows.slope
  norm_num
  rw [he]
  apply (div_eq_iff (by positivity : (32 : ℝ) + 32 * Real.sqrt 2 ≠ 0)).2
  nlinarith

theorem slope_1_31 : SingularRows.slope 1 31 = (Real.sqrt 962 - 1) / 31 := by
  have hs : (Real.sqrt 962)^2 = 962 := Real.sq_sqrt (by norm_num)
  unfold SingularRows.slope
  norm_num
  apply (div_eq_iff (by positivity : (1 : ℝ) + Real.sqrt 962 ≠ 0)).2
  nlinarith

theorem one_sub_root_pos : 0 < 1 - (Real.sqrt 2 - 1) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith


theorem pathMatrix_zero : pathMatrix 0 = 1 := by
  unfold pathMatrix
  convert matrix_zero 52 30 using 1 <;>
    simp only [alpha, chi, gamma, beta, tau, mul_zero, slope_zero]

private theorem det_one_helper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (h : M = 1) : M.det = 1 := h ▸ Matrix.det_one

theorem pathDet_zero : pathDet 0 = 1 :=
  det_one_helper (pathMatrix 0) pathMatrix_zero



theorem pathMatrix_continuous : Continuous (fun t : Interval => pathMatrix t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact @row_continuous Interval _ 52 30
    (fun j t => alpha j t) (fun j t => chi j t)
    (fun j t => gamma j t) (fun j t => beta j t)
    (fun t => tau t) alpha_continuous chi_continuous gamma_continuous beta_continuous tau_continuous i k.val


theorem pathMatrix_continuousOn : ContinuousOn pathMatrix (Set.Icc 0 1) :=
  continuousOn_iff_continuous_restrict.mpr pathMatrix_continuous

end Atiyah.SingularEndpoint
