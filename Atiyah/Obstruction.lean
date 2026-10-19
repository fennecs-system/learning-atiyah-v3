import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Atiyah.Cells

/-!
# The dual-incidence obstruction

For a square coefficient matrix, the determinant vanishes exactly when a
nonzero dual vector annihilates every column. This is the linear-algebraic
bridge from the Atiyah coefficient construction to the cell approach.

These results apply to arbitrary matrices. They do not assert that matrices
coming from point configurations avoid the determinant divisor.
-/

namespace Atiyah

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- A nonzero covector incident with every coefficient column. Over a field,
its projective class is a point of the dual-incidence obstruction locus. -/
def DualObstruction (A : Matrix ι ι K) : Prop :=
  ∃ v : ι → K, v ≠ 0 ∧ A.transpose.mulVec v = 0

/-- Nonvanishing is equivalent to injectivity of the dual evaluation map. -/
theorem det_ne_zero_iff_dual_injective (A : Matrix ι ι K) :
    A.det ≠ 0 ↔ Function.Injective A.transpose.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_transpose, isUnit_iff_ne_zero]

/-- No nonzero covector annihilates every column exactly when the determinant
is nonzero. The statement includes the empty matrix convention. -/
theorem det_ne_zero_iff_no_dual_kernel (A : Matrix ι ι K) :
    A.det ≠ 0 ↔ ∀ v : ι → K, A.transpose.mulVec v = 0 → v = 0 := by
  rw [det_ne_zero_iff_dual_injective]
  change Function.Injective A.transpose.mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]

/-- The determinant divisor is precisely the projection of dual incidence. -/
theorem det_eq_zero_iff_dual_obstruction (A : Matrix ι ι K) :
    A.det = 0 ↔ DualObstruction A := by
  classical
  have h := det_ne_zero_iff_no_dual_kernel A
  unfold DualObstruction
  constructor
  · intro hz
    have hn : ¬ ∀ v : ι → K, A.transpose.mulVec v = 0 → v = 0 := by
      intro hk
      exact (h.mpr hk) hz
    push_neg at hn
    obtain ⟨v, hv, hne⟩ := hn
    exact ⟨v, hne, hv⟩
  · rintro ⟨v, hne, hv⟩
    by_contra hz
    exact hne (h.mp hz v hv)

/-- Independence of coefficient columns is another presentation of the same
obstruction. -/
theorem columns_independent_iff_no_dual_obstruction (A : Matrix ι ι K) :
    LinearIndependent K A.col ↔ ¬ DualObstruction A := by
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, ← det_eq_zero_iff_dual_obstruction]

/-- In the real planar case every nonzero direction has a strictly positive
absolute evaluation on at least one column. This is a pointwise statement;
it is not a configuration-uniform margin bound. -/
theorem det_ne_zero_iff_positive_evaluation (A : Matrix ι ι ℝ) :
    A.det ≠ 0 ↔ ∀ v : ι → ℝ, v ≠ 0 → ∃ i : ι, 0 < |A.transpose.mulVec v i| := by
  classical
  rw [det_ne_zero_iff_no_dual_kernel]
  constructor
  · intro hk v hv
    by_contra hn
    push_neg at hn
    have hz : A.transpose.mulVec v = 0 := by
      funext i
      exact abs_eq_zero.mp (le_antisymm (hn i) (abs_nonneg _))
    exact hv (hk v hz)
  · intro hp v hz
    by_contra hv
    obtain ⟨i, hi⟩ := hp v hv
    simp [hz] at hi

/-- Cells use row-indexed coefficient vectors; this identifies their score
with matrix evaluation. -/
theorem cell_score_eq_mulVec {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (v : Fin n → ℝ) :
    Cells.score ρ i v = ρ.mulVec v i := by
  simp [Cells.score, Matrix.mulVec, dotProduct, mul_comm]

/-- For any chosen signed cell, pointedness is exactly nonsingularity.
This is the cell reformulation of C1 once the geometric coefficients are
substituted for `ρ`. The substantive geometric claim remains to be proved. -/
theorem det_ne_zero_iff_signedCell_pointed {n : ℕ}
    (ρ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (s : Bool) :
    ρ.det ≠ 0 ↔ ∀ v : Fin n → ℝ,
      v ∈ Cells.signedCell ρ i s → -v ∈ Cells.signedCell ρ i s → v = 0 := by
  have hkernel : ρ.det ≠ 0 ↔ ∀ v : Fin n → ℝ, ρ.mulVec v = 0 → v = 0 := by
    simpa using det_ne_zero_iff_no_dual_kernel ρ.transpose
  rw [hkernel]
  constructor
  · intro hk v hv hn
    apply hk v
    funext j
    have hz := (Cells.signedCell_lineality_iff ρ i s v).mp ⟨hv, hn⟩ j
    simpa only [cell_score_eq_mulVec] using hz
  · intro hp v hv
    have ha : v ∈ Cells.commonAnnihilator ρ := by
      intro j
      rw [cell_score_eq_mulVec, hv]
      rfl
    have hc := (Cells.signedCell_lineality_iff ρ i s v).mpr ha
    exact hp v hc.1 hc.2

end Atiyah
