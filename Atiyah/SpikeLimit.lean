import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Atiyah.Algebraic

/-!
# The algebraic boundary model for an isolated distant point

For an independent cluster family `qᵢ`, adjoining a distant point formally
produces the limiting family `L qᵢ` together with a polynomial `r` not vanishing
at the zero of `L`. Evaluation separates the new column from the cluster
columns, so the limiting family is independent.

This file proves that algebraic statement. It does not identify a geometric
configuration limit, establish convergence of chosen Hopf lifts, or assert a
separation threshold for finite configurations. Those are separate obligations.
-/

namespace Atiyah.SpikeLimit

open Polynomial

section Linear

variable {K V W ι : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An injective map into a functional's kernel preserves independence;
a vector outside that kernel supplies an additional independent column. -/
theorem independent_extension
    (q : ι → V) (hq : LinearIndependent K q)
    (T : V →ₗ[K] W) (hT : Function.Injective T)
    (φ : W →ₗ[K] K) (hφ : ∀ v, φ (T v) = 0)
    (r : W) (hr : φ r ≠ 0) :
    LinearIndependent K (fun o : Option ι => o.elim r (fun i => T (q i))) := by
  have hmap : LinearIndependent K (fun i => T (q i)) :=
    hq.map_injOn T hT.injOn
  have hspan : Submodule.span K (Set.range (fun i => T (q i))) ≤ LinearMap.ker φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hφ (q i)
  have hout : r ∉ Submodule.span K (Set.range (fun i => T (q i))) := by
    intro h
    exact hr (hspan h)
  simpa only [Option.casesOn'_eq_elim] using hmap.option hout

end Linear

section Polynomial

variable {K ι : Type*} [Field K]

/-- Algebraic model of the boundary family. `none` is the isolated point,
and `some i` is the cluster point indexed by `i`. -/
noncomputable def boundaryFamily (a : K) (q : ι → K[X]) (r : K[X]) :
    Option ι → K[X] :=
  fun o => o.elim r (fun i => (X - C a) * q i)

/-- Evaluation at the common cluster root certifies independence of the
boundary family. No geometric separation or convergence hypothesis is hidden. -/
theorem boundaryFamily_independent (a : K) (q : ι → K[X])
    (hq : LinearIndependent K q) (r : K[X]) (hr : r.eval a ≠ 0) :
    LinearIndependent K (boundaryFamily a q r) := by
  apply independent_extension q hq (LinearMap.mulLeft K (X - C a))
      (mul_right_injective₀ (X_sub_C_ne_zero a)) (Polynomial.leval a) ?_ r hr
  intro v
  simp [LinearMap.mulLeft_apply, Polynomial.leval_apply]

/-- Opposite limiting directions have distinct affine roots `a` and `b`.
The isolated-point column `(X-C b)^m` is therefore separated by evaluation. -/
theorem boundaryFamily_pow_independent (a b : K) (hab : a ≠ b)
    (q : ι → K[X]) (hq : LinearIndependent K q) (m : ℕ) :
    LinearIndependent K (boundaryFamily a q ((X - C b) ^ m)) := by
  apply boundaryFamily_independent a q hq
  simpa using pow_ne_zero m (sub_ne_zero.mpr hab)

/-- Finite indexing of the same boundary family, with the isolated column first. -/
theorem fin_cons_boundary_independent {n : ℕ} (a : K) (q : Fin n → K[X])
    (hq : LinearIndependent K q) (r : K[X]) (hr : r.eval a ≠ 0) :
    LinearIndependent K (Fin.cons r (fun i => (X - C a) * q i)) := by
  apply linearIndependent_fin_cons.mpr
  have h := boundaryFamily_independent a q hq r hr
  rw [linearIndependent_option] at h
  exact h

/-- Truncation to all possibly nonzero coefficients preserves independence.
The degree hypothesis is necessary: truncating high coefficients arbitrarily
would not preserve the information contained in a polynomial family. -/
theorem coefficientMatrix_det_ne_zero {n : ℕ} (p : Fin n → K[X])
    (hp : LinearIndependent K p) (hdeg : ∀ i, (p i).natDegree < n) :
    (Algebraic.coefficientMatrix p).det ≠ 0 := by
  classical
  have hcols : LinearIndependent K (Algebraic.coefficientMatrix p).col := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    apply Fintype.linearIndependent_iff.mp hp c
    ext k
    by_cases hk : k < n
    · have he := congrFun hc (⟨k, hk⟩ : Fin n)
      simpa [Algebraic.coefficientMatrix, Matrix.col, Polynomial.finset_sum_coeff,
        Polynomial.coeff_smul] using he
    · simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, Polynomial.coeff_zero]
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_le (Nat.le_of_not_gt hk))]
      exact smul_zero _
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hcols))

/-- The exact algebraic boundary lies outside the coefficient determinant
hypersurface when the cluster is independent and has the expected degree. -/
theorem fin_cons_boundary_det_ne_zero {n : ℕ} (a : K) (q : Fin n → K[X])
    (hq : LinearIndependent K q) (hdeg : ∀ i, (q i).natDegree < n)
    (r : K[X]) (hr : r.eval a ≠ 0) (hrdeg : r.natDegree ≤ n) :
    (Algebraic.coefficientMatrix (Fin.cons r (fun i => (X - C a) * q i))).det ≠ 0 := by
  apply coefficientMatrix_det_ne_zero _ (fin_cons_boundary_independent a q hq r hr)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using Nat.lt_succ_of_le hrdeg
  · simp only [Fin.cons_succ]
    have hmul : ((X - C a) * q j).natDegree ≤
        (X - C a).natDegree + (q j).natDegree := Polynomial.natDegree_mul_le
    have hlin : (X - C a).natDegree = 1 := Polynomial.natDegree_X_sub_C a
    rw [hlin] at hmul
    exact hmul.trans_lt (by have hj := hdeg j; omega)

/-- In the two-direction boundary model the isolated-point polynomial is the
power of the opposite linear factor. This is the determinant certificate used
by a future geometric distant-point limit argument. -/
theorem fin_cons_boundary_pow_det_ne_zero {n : ℕ} (a b : K) (hab : a ≠ b)
    (q : Fin n → K[X]) (hq : LinearIndependent K q)
    (hdeg : ∀ i, (q i).natDegree < n) :
    (Algebraic.coefficientMatrix
      (Fin.cons ((X - C b) ^ n) (fun i => (X - C a) * q i))).det ≠ 0 := by
  apply fin_cons_boundary_det_ne_zero a q hq hdeg
  · simpa using pow_ne_zero n (sub_ne_zero.mpr hab)
  · calc
      ((X - C b) ^ n).natDegree ≤ n * (X - C b).natDegree := natDegree_pow_le
      _ = n := by rw [natDegree_X_sub_C]; exact Nat.mul_one n

end Polynomial
end Atiyah.SpikeLimit
