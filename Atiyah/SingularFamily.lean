import Atiyah.SingularGroupedRows
import Atiyah.SingularCrossing
import Atiyah.SingularEndpoint

/-!
SF1: A negative endpoint determinant forces an interior zero because the
normalized coefficient determinant is continuous and equals one at zero.
SF2: At that interior parameter, the explicit path is a distinct configuration,
and the exact geometric row identities turn the determinant zero into complex
point-form dependence for every physical Hopf lift family.

The endpoint sign is an explicit hypothesis of every conclusion in this file.
No endpoint configuration or endpoint distinctness is assumed.
-/
noncomputable section
namespace Atiyah.SingularFamily
open SingularRows SingularGeometry Configuration

/-- The exact real normalized row family on the 84-point path. -/
def rows (t : ℝ) (i : Fin 84) : Polynomial ℝ :=
  SingularRows.row (fun j => alpha j t) (fun j => chi j t)
    (fun j => gamma j t) (fun j => beta j t) (tau t) i

theorem rows_degree (t : ℝ) (i : Fin 84) : (rows t i).natDegree < 84 := by
  have h := row_natDegree_le (fun j => alpha j t) (fun j => chi j t)
    (fun j => gamma j t) (fun j => beta j t) (tau t) i
  exact lt_of_le_of_lt h (by norm_num)

theorem coefficientMatrix_eq (t : ℝ) :
    Algebraic.coefficientMatrix (rows t) = (pathMatrix t).transpose := rfl

/-- An interior determinant zero is a genuine failure of independence of the
point forms of the actual path, independent of all choices of physical lifts. -/
theorem dependent_at_zero {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hz : pathDet t = 0) (L : LiftFamily (config t ht ht1)) :
    ¬ LinearIndependent ℂ (pointForm L) := by
  have hz' : (Algebraic.coefficientMatrix (rows t)).det = 0 := by
    rw [coefficientMatrix_eq, Matrix.det_transpose]
    exact hz
  have hdep := SingularCrossing.complex_dependent_of_det_zero (rows t) (rows_degree t) hz'
  intro hi
  apply hdep
  have hnorm := (independent_iff_normalized t ht ht1 L).mp hi
  have hpaper := (SingularRowBridge.independent_iff_paperRow t).mp hnorm
  change LinearIndependent ℂ (fun i => SingularRowBridge.paperRow t i) at hpaper
  simpa only [SingularRowBridge.paperRow_eq_map_row, rows] using hpaper

/-- The intermediate-value argument is proved at an abstract matrix size,
so specializing it never unfolds a concrete permutation determinant. -/
theorem matrix_interior_zero {n : ℕ} (M : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hc : ContinuousOn M (Set.Icc 0 1))
    (h0 : 0 < (M 0).det) (h1 : (M 1).det < 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, (M t).det = 0 := by
  have hd : ContinuousOn (fun t => (M t).det) (Set.Icc 0 1) :=
    continuous_id.matrix_det.comp_continuousOn hc
  exact SingularCrossing.interior_zero hd h0 h1

/-- Conditional endpoint-to-interior theorem for the specified 84-point path. -/
theorem exists_singular_parameter (hneg : pathDet 1 < 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∀ (ht : 0 < t) (ht1 : t < 1)
      (L : LiftFamily (config t ht ht1)), ¬ LinearIndependent ℂ (pointForm L) := by
  have h0 : 0 < pathDet 0 := by
    rw [SingularEndpoint.pathDet_zero]
    norm_num
  obtain ⟨t, ht, hz⟩ := matrix_interior_zero pathMatrix
    SingularEndpoint.pathMatrix_continuousOn h0 hneg
  exact ⟨t, ht, fun ht' ht1 L => dependent_at_zero ht' ht1 hz L⟩

/-- The remaining endpoint-sign obligation suffices for an actual distinct
84-point counterexample, with dependence for every Hopf lift family. -/
theorem exists_singular_config (hneg : pathDet 1 < 0) :
    ∃ p : Config 84, Nonempty (LiftFamily p) ∧
      ∀ L : LiftFamily p, ¬ LinearIndependent ℂ (pointForm L) := by
  obtain ⟨t, ht, h⟩ := exists_singular_parameter hneg
  exact ⟨config t ht.1 ht.2, liftFamily_nonempty _, h ht.1 ht.2⟩

/-- This is conditional only on the explicitly named real endpoint sign. -/
theorem not_c1_of_endpoint_neg (hneg : pathDet 1 < 0) : ¬ C1 84 := by
  obtain ⟨p, ⟨L⟩, hdep⟩ := exists_singular_config hneg
  intro hC1
  exact hdep L ((hC1 p).2 L)

end Atiyah.SingularFamily
