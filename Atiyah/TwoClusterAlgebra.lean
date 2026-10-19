import Atiyah.GeometricLimit
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
TC-A1. An invertible linear change of the two variables sends two transverse
linear forms to the coordinate variables and preserves independence.
TC-A2. Each transformed point form has degree in the second variable at most
its number of factors, namely n−1.
TC-A3. In a relation X₀^k Q + X₁^m R=0, deg₁ Q<m forces Q=0 by
coefficient comparison. Then R=0, and independence inside each cluster finishes.
These steps prove the two-cluster boundary family without an affine chart.
-/
noncomputable section
namespace Atiyah.TwoClusterAlgebra
open Configuration MvPolynomial

private theorem separated_zero (m k : ℕ) (Q R : BinaryForm)
    (hQ : Q.degreeOf 1 < m)
    (h : X 0 ^ k * Q + X 1 ^ m * R = 0) : Q = 0 := by
  classical
  ext d
  by_cases hd : d 1 < m
  · have he := congrArg (coeff (Finsupp.single 0 k + d)) h
    have hn : ¬ Finsupp.single 1 m ≤ Finsupp.single 0 k + d := by
      intro hh
      have hh' := hh 1
      simp at hh'
      omega
    simpa [X_pow_eq_monomial, coeff_monomial_mul, coeff_monomial_mul', hn] using he
  · have hn : d ∉ Q.support := by
      intro hh
      have := monomial_le_degreeOf 1 hh
      omega
    exact not_mem_support_iff.mp hn

private def change (v w : Spinor) : BinaryForm →ₐ[ℂ] BinaryForm :=
  aeval ![linearForm (w.2 / (v.1*w.2-v.2*w.1), -v.2 / (v.1*w.2-v.2*w.1)),
    linearForm (-w.1 / (v.1*w.2-v.2*w.1), v.1 / (v.1*w.2-v.2*w.1))]

private theorem change_linearForm (v w z : Spinor) :
    change v w (linearForm z) = linearForm
      ((z.1*w.2-z.2*w.1)/(v.1*w.2-v.2*w.1),
       (-z.1*v.2+z.2*v.1)/(v.1*w.2-v.2*w.1)) := by
  simp [change, linearForm, map_add, map_mul, map_div₀, sub_eq_add_neg, div_eq_mul_inv]
  ring

private theorem change_left (v w : Spinor) (hd : v.1*w.2-v.2*w.1 ≠ 0) :
    change v w (linearForm v) = X 0 := by
  rw [change_linearForm]
  have h : -v.1*v.2+v.2*v.1 = 0 := by ring
  simp only [h, div_self hd, zero_div, linearForm]
  simp

private theorem change_right (v w : Spinor) (hd : v.1*w.2-v.2*w.1 ≠ 0) :
    change v w (linearForm w) = X 1 := by
  rw [change_linearForm]
  have h : -w.1*v.2+w.2*v.1 = v.1*w.2-v.2*w.1 := by ring
  have h0 : w.1*w.2-w.2*w.1 = 0 := by ring
  rw [h, h0]
  simp [hd, linearForm]

private theorem change_injective (v w : Spinor) (hd : v.1*w.2-v.2*w.1 ≠ 0) :
    Function.Injective (change v w) := by
  let T : BinaryForm →ₐ[ℂ] BinaryForm := aeval ![linearForm v, linearForm w]
  have comb (a b : ℂ) : C a * linearForm v + C b * linearForm w =
      linearForm (a*v.1+b*w.1, a*v.2+b*w.2) := by
    simp [linearForm, map_add, map_mul]; ring
  have hT (z : Spinor) : T (linearForm z) = C z.1 * linearForm v + C z.2 * linearForm w := by
    simp [T, linearForm]
  have hcomp : T.comp (change v w) = AlgHom.id ℂ BinaryForm := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp only [AlgHom.comp_apply, change, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, hT, AlgHom.id_apply]
    · change T (linearForm (w.2 / (v.1*w.2-v.2*w.1), -v.2 / (v.1*w.2-v.2*w.1))) = X 0
      rw [hT]
      change C (w.2 / (v.1*w.2-v.2*w.1)) * linearForm v +
        C (-v.2 / (v.1*w.2-v.2*w.1)) * linearForm w = X 0
      rw [comb]
      have ha : w.2 / (v.1*w.2-v.2*w.1) * v.1 +
          -v.2 / (v.1*w.2-v.2*w.1) * w.1 = 1 := by field_simp [hd]; ring
      have hb : w.2 / (v.1*w.2-v.2*w.1) * v.2 +
          -v.2 / (v.1*w.2-v.2*w.1) * w.2 = 0 := by ring
      rw [ha, hb]; simp [linearForm]
    · change T (linearForm (-w.1 / (v.1*w.2-v.2*w.1), v.1 / (v.1*w.2-v.2*w.1))) = X 1
      rw [hT]
      change C (-w.1 / (v.1*w.2-v.2*w.1)) * linearForm v +
        C (v.1 / (v.1*w.2-v.2*w.1)) * linearForm w = X 1
      rw [comb]
      have ha : -w.1 / (v.1*w.2-v.2*w.1) * v.1 +
          v.1 / (v.1*w.2-v.2*w.1) * w.1 = 0 := by ring
      have hb : -w.1 / (v.1*w.2-v.2*w.1) * v.2 +
          v.1 / (v.1*w.2-v.2*w.1) * w.2 = 1 := by field_simp [hd]; ring
      rw [ha, hb]; simp [linearForm]
  exact Function.LeftInverse.injective (f := change v w) (g := T)
    (fun p => DFunLike.congr_fun hcomp p)

private theorem linearForm_degreeOf (z : Spinor) (i : Fin 2) :
    (linearForm z).degreeOf i ≤ 1 := by
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · exact (degreeOf_C_mul_le _ _ _).trans (by simp [degreeOf_X]; split <;> omega)
  · exact (degreeOf_C_mul_le _ _ _).trans (by simp [degreeOf_X]; split <;> omega)

private theorem change_pointForm_degree {n : ℕ} {p : Config n}
    (L : LiftFamily p) (i : Fin n) (v w : Spinor) :
    (change v w (pointForm L i)).degreeOf 1 < n := by
  classical
  unfold pointForm
  rw [map_prod]
  apply lt_of_le_of_lt (degreeOf_prod_le _ _ _)
  calc
    ∑ j ∈ Finset.univ.erase i, (change v w (linearForm (L.lift i j))).degreeOf 1
      ≤ ∑ j ∈ Finset.univ.erase i, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [change_linearForm]
        exact linearForm_degreeOf _ _
    _ < n := by simp; exact Nat.zero_lt_of_lt i.isLt

private theorem coordinate_independent {m k : ℕ}
    (q : Fin m → BinaryForm) (r : Fin k → BinaryForm)
    (hq : LinearIndependent ℂ q) (hr : LinearIndependent ℂ r)
    (hd : ∀ i, (q i).degreeOf 1 < m) :
    LinearIndependent ℂ (Sum.elim (fun i => X 0 ^ k * q i)
      (fun j => X 1 ^ m * r j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hrel : X 0 ^ k * (∑ i, c (.inl i) • q i) +
      X 1 ^ m * (∑ j, c (.inr j) • r j) = 0 := by
    simpa [Fintype.sum_sum_type, Finset.mul_sum, mul_smul_comm] using hc
  have hzero : (∑ i, c (.inl i) • q i) = 0 := by
    by_cases hm : m = 0
    · subst m; simp
    apply separated_zero m k _ _ ?_ hrel
    apply lt_of_le_of_lt (degreeOf_sum_le _ _ _)
    apply (Finset.sup_lt_iff (show 0 < m by omega)).mpr
    intro i hi
    apply lt_of_le_of_lt _ (hd i)
    simpa [Algebra.smul_def] using degreeOf_C_mul_le (q i) 1 (c (.inl i))
  have hzero' : (∑ j, c (.inr j) • r j) = 0 := by
    rw [hzero, mul_zero, zero_add] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ (X_ne_zero 1))
  intro i
  cases i with
  | inl i => exact Fintype.linearIndependent_iff.mp hq _ hzero i
  | inr j => exact Fintype.linearIndependent_iff.mp hr _ hzero' j

/-- TC-A1–A3: the homogeneous boundary of two independent clusters is independent. -/
theorem boundary_independent {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B)
    (hA : LinearIndependent ℂ (pointForm LA))
    (hB : LinearIndependent ℂ (pointForm LB)) (v : Spinor) (hv : v ≠ 0) :
    LinearIndependent ℂ (Sum.elim (fun i => linearForm v ^ k * pointForm LA i)
      (fun j => linearForm (ContinuousLift.antipode v) ^ m * pointForm LB j)) := by
  let w := ContinuousLift.antipode v
  have hd : v.1*w.2-v.2*w.1 ≠ 0 :=
    ContinuousLift.antipodal_determinant_ne_zero v hv
  have hinj := change_injective v w hd
  have hA' := hA.map' (change v w).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have hB' := hB.map' (change v w).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have hh := coordinate_independent _ _ hA' hB'
    (fun i => change_pointForm_degree LA i v w)
  have hmapped : LinearIndependent ℂ (fun i => change v w
      (Sum.elim (fun i => linearForm v ^ k * pointForm LA i)
        (fun j => linearForm w ^ m * pointForm LB j) i)) := by
    convert hh using 1
    ext i
    cases i <;> simp [change_left v w hd, change_right v w hd]
  exact hmapped.of_comp (change v w).toLinearMap

end Atiyah.TwoClusterAlgebra
