import Atiyah.TwoClusterGeometry

noncomputable section
namespace Atiyah.TwoCluster
open Configuration ContinuousLift

/-- Directed lifts on the disjoint union, keeping both internal families. -/
def sumLift {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B)
    (b c : Fin m → Fin k → Spinor) :
    (Fin m ⊕ Fin k) → (Fin m ⊕ Fin k) → Spinor :=
  Sum.elim (fun i => Sum.elim (LA.lift i) (b i))
    (fun j => Sum.elim (fun i => c i j) (LB.lift j))

def glueLift {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (x : Space)
    (hx : ∀ i j, A.point i ≠ x + B.point j)
    (b c : Fin m → Fin k → Spinor)
    (hb : ∀ i j, hopf (b i j) = x + B.point j - A.point i)
    (hc : ∀ i j, hopf (c i j) = A.point i - (x + B.point j)) :
    LiftFamily (glue A B x hx) where
  lift i j := sumLift LA LB b c (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  incidence := by
    intro i j hij
    have hne : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
      fun he => hij (finSumFinEquiv.symm.injective he)
    change hopf (sumLift LA LB b c (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
      points A B x (finSumFinEquiv.symm j) - points A B x (finSumFinEquiv.symm i)
    generalize finSumFinEquiv.symm i = a at *
    generalize finSumFinEquiv.symm j = d at *
    cases a with
    | inl a =>
      cases d with
      | inl d => exact LA.incidence a d (fun he => hne (congrArg Sum.inl he))
      | inr d => exact hb a d
    | inr a =>
      cases d with
      | inl d => exact hc d a
      | inr d =>
        simpa [sumLift, points] using LB.incidence a d (fun he => hne (congrArg Sum.inr he))

private theorem prod_erase_eq_ite {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (f : ι → M) (i : ι) :
    ∏ j ∈ Finset.univ.erase i, f j = ∏ j, if j = i then 1 else f j := by
  rw [← Finset.prod_erase _ (f := fun j => if j = i then 1 else f j) (a := i) (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem pointForm_glueLift {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (x : Space)
    (hx : ∀ i j, A.point i ≠ x + B.point j)
    (b c : Fin m → Fin k → Spinor)
    (hb : ∀ i j, hopf (b i j) = x + B.point j - A.point i)
    (hc : ∀ i j, hopf (c i j) = A.point i - (x + B.point j))
    (a : Fin m ⊕ Fin k) :
    pointForm (glueLift LA LB x hx b c hb hc) (finSumFinEquiv a) =
      Sum.elim (fun i => (∏ j, linearForm (b i j)) * pointForm LA i)
        (fun j => (∏ i, linearForm (c i j)) * pointForm LB j) a := by
  classical
  rw [pointForm, prod_erase_eq_ite, ← finSumFinEquiv.prod_comp]
  simp only [Equiv.apply_eq_iff_eq, glueLift, Equiv.symm_apply_apply]
  rw [Fintype.prod_sum_type]
  cases a <;> simp [sumLift, pointForm, prod_erase_eq_ite, mul_comm]

/-- Restore the actual displacement scale on every cross-cluster edge. -/
def physicalLift {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i j, A.point i ≠ R • u + B.point j)
    (b : Fin m → Fin k → Spinor)
    (hb : ∀ i j, hopf (b i j) = u - R⁻¹ • (A.point i - B.point j)) :
    LiftFamily (glue A B (R • u) hx) :=
  glueLift LA LB (R • u) hx
    (fun i j => (Real.sqrt R : ℂ) • b i j)
    (fun i j => (Real.sqrt R : ℂ) • antipode (b i j))
    (by
      intro i j
      rw [hopf_sqrt_smul R hR.le, hb i j, smul_sub, smul_smul,
        mul_inv_cancel₀ hR.ne', one_smul]
      abel)
    (by
      intro i j
      rw [hopf_sqrt_smul R hR.le, hopf_antipode, hb i j, smul_neg,
        smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel)

theorem pointForm_physicalLift {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i j, A.point i ≠ R • u + B.point j)
    (b : Fin m → Fin k → Spinor)
    (hb : ∀ i j, hopf (b i j) = u - R⁻¹ • (A.point i - B.point j))
    (a : Fin m ⊕ Fin k) :
    pointForm (physicalLift LA LB u R hR hx b hb) (finSumFinEquiv a) =
      (Sum.elim (fun _ : Fin m => (Real.sqrt R : ℂ)^k)
        (fun _ : Fin k => (Real.sqrt R : ℂ)^m) a) • clusterForms LA LB b a := by
  rw [physicalLift, pointForm_glueLift]
  cases a <;>
    simp only [clusterForms, Sum.elim_inl, Sum.elim_inr, linearForm_smul,
      MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, map_pow, mul_assoc]

theorem independent_glue {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i j, A.point i ≠ R • u + B.point j)
    (b : Fin m → Fin k → Spinor)
    (hb : ∀ i j, hopf (b i j) = u - R⁻¹ • (A.point i - B.point j))
    (hind : LinearIndependent ℂ (clusterForms LA LB b)) :
    ∀ K : LiftFamily (glue A B (R • u) hx), LinearIndependent ℂ (pointForm K) := by
  intro K
  apply (linearIndependent_pointForm_iff (physicalLift LA LB u R hR hx b hb) K).mp
  have he : LinearIndependent ℂ (fun a : Fin m ⊕ Fin k =>
      pointForm (physicalLift LA LB u R hR hx b hb) (finSumFinEquiv a)) := by
    simp_rw [pointForm_physicalLift]
    apply (linearIndependent_smul_iff _ _ ?_).mpr hind
    have hs : (Real.sqrt R : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hR))
    intro a
    cases a <;> exact pow_ne_zero _ hs
  exact (linearIndependent_equiv finSumFinEquiv).mp he

end Atiyah.TwoCluster
