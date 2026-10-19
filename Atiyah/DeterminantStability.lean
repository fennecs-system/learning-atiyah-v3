import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Separation.Basic
import Atiyah.Obstruction

/-!
# Stability away from the determinant divisor

If a matrix family converges to a nonsingular matrix, it is eventually
nonsingular. For a real parameter tending to infinity this gives an existential
threshold, not a computable numerical bound. In the planar setting the signed
winner cones are consequently eventually pointed.

These are analytic bridges only. Applying them to a distant point requires
separate geometric proofs of matrix convergence and nonsingularity of its
limit, with the normalization of the polynomial columns specified.
-/

namespace Atiyah

open Filter Topology

section General

variable {ι K T : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

/-- The complement of the determinant divisor is stable under convergence.
No continuity of the whole parameterized family is required. -/
theorem eventually_det_ne_zero_of_tendsto
    {A : T → Matrix ι ι K} {A₀ : Matrix ι ι K} {l : Filter T}
    (hA : Tendsto A l (𝓝 A₀)) (h₀ : A₀.det ≠ 0) :
    ∀ᶠ t in l, (A t).det ≠ 0 := by
  have hd : Continuous (fun B : Matrix ι ι K => B.det) :=
    continuous_id.matrix_det
  exact (hd.continuousAt.tendsto.comp hA).eventually_ne h₀

/-- A convergent real-parameter family has a nonsingular tail if its limit is
nonsingular. The threshold is existential and may depend on the entire family. -/
theorem exists_threshold_det_ne_zero
    {A : ℝ → Matrix ι ι K} {A₀ : Matrix ι ι K}
    (hA : Tendsto A atTop (𝓝 A₀)) (h₀ : A₀.det ≠ 0) :
    ∃ R : ℝ, ∀ t ≥ R, (A t).det ≠ 0 := by
  exact Filter.eventually_atTop.mp (eventually_det_ne_zero_of_tendsto hA h₀)

end General

/-- Planar signed winner cones become pointed whenever their row matrices
converge to a nonsingular limit. This does not supply geometric convergence. -/
theorem eventually_signedCells_pointed_of_tendsto
    {T : Type*} {n : ℕ} {ρ : T → Matrix (Fin n) (Fin n) ℝ}
    {ρ₀ : Matrix (Fin n) (Fin n) ℝ} {l : Filter T}
    (hρ : Tendsto ρ l (𝓝 ρ₀)) (h₀ : ρ₀.det ≠ 0) :
    ∀ᶠ t in l, ∀ (i : Fin n) (s : Bool) (v : Fin n → ℝ),
      v ∈ Cells.signedCell (ρ t) i s →
      -v ∈ Cells.signedCell (ρ t) i s → v = 0 := by
  filter_upwards [eventually_det_ne_zero_of_tendsto hρ h₀] with t ht
  intro i s
  exact (det_ne_zero_iff_signedCell_pointed (ρ t) i s).mp ht

end Atiyah
