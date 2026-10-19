import Atiyah.PlanarLift
import Atiyah.Algebraic
import Atiyah.Obstruction
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# From planar configurations to the coefficient determinant

Each unoriented pair receives one real Hopf lift; the reverse pair receives
its antipodal lift. Polynomial products give a map to the coefficient space.
The nonvanishing assertion below is an open proposition, not an axiom.
The two-point geometric case is proved.
-/
namespace Atiyah.PlanarConfiguration

open Polynomial PlanarLift

/-- Ordered configurations of distinct real planar points. -/
structure Configuration (n : ℕ) where
  point : Fin n → ℝ × ℝ
  distinct : Function.Injective point

/-- The index ordering chooses one lift per unoriented edge. -/
noncomputable def pairLift {n : ℕ} (p : Fin n → ℝ × ℝ) (i j : Fin n) : ℝ × ℝ :=
  if i < j then canonicalLift ((p j).1 - (p i).1) ((p j).2 - (p i).2)
  else J (canonicalLift ((p i).1 - (p j).1) ((p i).2 - (p j).2))

theorem pairLift_incidence {n : ℕ} (p : Fin n → ℝ × ℝ) (i j : Fin n) :
    Incidence ((p j).1 - (p i).1) ((p j).2 - (p i).2)
      (pairLift p i j).1 (pairLift p i j).2 := by
  unfold pairLift
  split_ifs
  · exact canonicalLift_incidence _ _
  · have h := incidence_antipodal
      (canonicalLift_incidence ((p i).1 - (p j).1) ((p i).2 - (p j).2))
    simpa only [neg_sub, J] using h

noncomputable def pointPolynomial {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) : ℝ[X] :=
  ∏ j, if j = i then 1 else C (pairLift p i j).1 + C (pairLift p i j).2 * X

/-- Each point polynomial has at most one linear factor per other point. -/
theorem pointPolynomial_natDegree_le {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) :
    (pointPolynomial p i).natDegree ≤ n - 1 := by
  let f : Fin n → ℝ[X] := fun j =>
    if j = i then 1 else C (pairLift p i j).1 + C (pairLift p i j).2 * X
  have heq : pointPolynomial p i = ∏ j ∈ Finset.univ.erase i, f j := by
    exact (Finset.prod_erase Finset.univ (f := f) (by simp [f])).symm
  rw [heq]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (f j).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      dsimp [f]
      rw [if_neg hji]
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by simp)
    _ = n - 1 := by simp

noncomputable def coefficientMatrix {n : ℕ} (p : Fin n → ℝ × ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Algebraic.coefficientMatrix (pointPolynomial p)

/-- The planar determinant-avoidance problem. No proof is assumed. -/
def PlanarNonvanishing (n : ℕ) : Prop :=
  ∀ p : Configuration n, (coefficientMatrix p.point).det ≠ 0

/-- The geometric coefficient columns define pointed signed cells exactly
when their determinant is nonzero. Note the transpose for row-based scores. -/
theorem nonvanishing_iff_pointed {n : ℕ} (p : Configuration n) (i : Fin n) (s : Bool) :
    (coefficientMatrix p.point).det ≠ 0 ↔ ∀ v : Fin n → ℝ,
      v ∈ Cells.signedCell (coefficientMatrix p.point).transpose i s →
      -v ∈ Cells.signedCell (coefficientMatrix p.point).transpose i s → v = 0 := by
  simpa only [Matrix.det_transpose] using
    det_ne_zero_iff_signedCell_pointed (coefficientMatrix p.point).transpose i s

/-- Two points produce the antipodal pair of linear forms, so the coefficient
matrix determinant is the positive squared norm of their chosen lift. -/
theorem two_point_det_pos (p : Configuration 2) : 0 < (coefficientMatrix p.point).det := by
  let q := canonicalLift ((p.point 1).1 - (p.point 0).1)
    ((p.point 1).2 - (p.point 0).2)
  have hinc : Incidence ((p.point 1).1 - (p.point 0).1)
      ((p.point 1).2 - (p.point 0).2) q.1 q.2 := canonicalLift_incidence _ _
  have hne : ((p.point 1).1 - (p.point 0).1,
      (p.point 1).2 - (p.point 0).2) ≠ (0, 0) := by
    intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    have heq : p.point 1 = p.point 0 := by
      apply Prod.ext <;> dsimp at * <;> linarith
    have h10 := p.distinct heq
    norm_num at h10
  have hpos := antipodal_determinant_pos hinc hne
  simpa [coefficientMatrix, Algebraic.coefficientMatrix, Matrix.det_fin_two,
    pointPolynomial, Fin.prod_univ_two, pairLift, J, q] using hpos

theorem planarNonvanishing_two : PlanarNonvanishing 2 := by
  intro p
  exact ne_of_gt (two_point_det_pos p)

/-- The two-point configuration cells have no nonzero lineality. -/
theorem two_point_cells_pointed (p : Configuration 2) (i : Fin 2) (s : Bool)
    (v : Fin 2 → ℝ)
    (hv : v ∈ Cells.signedCell (coefficientMatrix p.point).transpose i s)
    (hnv : -v ∈ Cells.signedCell (coefficientMatrix p.point).transpose i s) : v = 0 :=
  (nonvanishing_iff_pointed p i s).mp (ne_of_gt (two_point_det_pos p)) v hv hnv

end Atiyah.PlanarConfiguration
