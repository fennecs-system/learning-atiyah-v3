import Atiyah.SpikeLimit
import Atiyah.DeterminantStability
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Matrix

/-! SG5: a sign change of the real coefficient determinant gives dependence
at a strictly interior parameter. This is a generic analytic bridge; applying
it to the actual geometric path requires the separately proved row identities. -/
noncomputable section
namespace Atiyah.SingularCrossing
open Polynomial Set

theorem interior_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (h0 : 0 < f 0) (h1 : f 1 < 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f t = 0 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hf ⟨h1.le, h0.le⟩
  refine ⟨t, ⟨?_, ?_⟩, he⟩
  · have hn : t ≠ 0 := by intro h; subst t; linarith
    exact lt_of_le_of_ne ht.1 (Ne.symm hn)
  · have hn : t ≠ 1 := by intro h; subst t; linarith
    exact lt_of_le_of_ne ht.2 hn

theorem exists_dependent_rows {n : ℕ} (p : ℝ → Fin n → ℝ[X])
    (hc : ∀ i j : Fin n, ContinuousOn (fun t => (p t j).coeff i.val) (Icc 0 1))
    (hdeg : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ j, (p t j).natDegree < n)
    (h0 : 0 < (Algebraic.coefficientMatrix (p 0)).det)
    (h1 : (Algebraic.coefficientMatrix (p 1)).det < 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ¬ LinearIndependent ℝ (p t) := by
  have hmat : ContinuousOn (fun t => Algebraic.coefficientMatrix (p t)) (Icc 0 1) := by
    apply continuousOn_pi.mpr
    intro i
    exact continuousOn_pi.mpr (hc i)
  have hd := (continuous_id.matrix_det).comp_continuousOn hmat
  obtain ⟨t, ht, he⟩ := interior_zero hd h0 h1
  exact ⟨t, ht, fun h => SpikeLimit.coefficientMatrix_det_ne_zero _ h (hdeg t ht) he⟩


/-- A real coefficient singularity remains a complex polynomial dependence.
The degree bound excludes loss of information in coefficient truncation. -/
theorem complex_dependent_of_det_zero {n : ℕ} (p : Fin n → ℝ[X])
    (hdeg : ∀ i, (p i).natDegree < n)
    (hz : (Algebraic.coefficientMatrix p).det = 0) :
    ¬ LinearIndependent ℂ (fun i => (p i).map Complex.ofRealHom) := by
  intro hi
  have hn := SpikeLimit.coefficientMatrix_det_ne_zero _ hi
    (fun i => lt_of_le_of_lt Polynomial.natDegree_map_le (hdeg i))
  apply hn
  have hm : Algebraic.coefficientMatrix (fun i => (p i).map Complex.ofRealHom) =
      (Algebraic.coefficientMatrix p).map Complex.ofRealHom := by
    ext i j
    simp [Algebraic.coefficientMatrix]
  rw [hm]
  have he := Complex.ofRealHom.map_det (Algebraic.coefficientMatrix p)
  rw [hz, map_zero] at he
  exact he.symm

end Atiyah.SingularCrossing
