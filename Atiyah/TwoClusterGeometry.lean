import Atiyah.DistantPoint
import Mathlib.Logic.Equiv.Fin.Basic

/-! TC1–TC3: separated translated configurations, convergent cross-edge Hopf
lifts, and coefficientwise convergence of their normalized point forms. -/
noncomputable section
namespace Atiyah.TwoCluster
open Configuration ContinuousLift Filter Topology

/-- The left core is fixed and the right core translated by `x`. -/
def points {m k : ℕ} (A : Config m) (B : Config k) (x : Space) :
    Fin m ⊕ Fin k → Space := Sum.elim A.point (fun j => x + B.point j)

theorem points_injective {m k : ℕ} (A : Config m) (B : Config k) (x : Space)
    (h : ∀ i j, A.point i ≠ x + B.point j) : Function.Injective (points A B x) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (A.distinct he)
    | inr j => exact (h i j he).elim
  | inr i =>
    cases j with
    | inl j => exact (h j i he.symm).elim
    | inr j => exact congrArg Sum.inr (B.distinct (add_left_cancel he))

/-- TC1: package the separated cores as an ordinary finite configuration. -/
def glue {m k : ℕ} (A : Config m) (B : Config k) (x : Space)
    (h : ∀ i j, A.point i ≠ x + B.point j) : Config (m+k) where
  point := points A B x ∘ finSumFinEquiv.symm
  distinct := (points_injective A B x h).comp finSumFinEquiv.symm.injective

/-- TC1: a nonzero separating ray eventually excludes all cross collisions. -/
theorem eventually_separated {m k : ℕ} (A : Config m) (B : Config k)
    (u : Space) (hu : u ≠ 0) :
    ∀ᶠ R : ℝ in atTop, ∀ i j, A.point i ≠ R • u + B.point j := by
  have h := DistantPoint.eventually_ray_avoids u hu
    (fun ij : Fin (m*k) => A.point (finProdFinEquiv.symm ij).1 -
      B.point (finProdFinEquiv.symm ij).2)
  filter_upwards [h] with R h i j he
  apply h (finProdFinEquiv (i,j))
  simpa using (eq_sub_iff_add_eq.mpr he.symm)

/-- TC2: a single local chart yields convergent normalized cross-edge lifts. -/
theorem exists_cross_lifts {m k : ℕ} (A : Config m) (B : Config k)
    (u : Space) (hu : u ≠ 0) :
    ∃ v : Spinor, v ≠ 0 ∧ ∃ b : ℝ → Fin m → Fin k → Spinor,
      (∀ i j, Tendsto (fun R => b R i j) atTop (𝓝 v)) ∧
      ∀ᶠ R in atTop, ∀ i j,
        hopf (b R i j) = u - R⁻¹ • (A.point i - B.point j) := by
  obtain ⟨s, hs, hsu, he⟩ := exists_local_hopf_section u hu
  have hv : s u ≠ 0 := by
    intro h
    apply hu
    rw [← hsu, h]
    exact hopf_zero
  have ht (i : Fin m) (j : Fin k) :
      Tendsto (fun R : ℝ => u - R⁻¹ • (A.point i - B.point j)) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).smul_const (A.point i - B.point j))
  refine ⟨s u, hv, fun R i j => s (u - R⁻¹ • (A.point i - B.point j)), ?_, ?_⟩
  · intro i j
    exact hs.tendsto.comp (ht i j)
  · exact eventually_all.mpr (fun i => eventually_all.mpr (fun j => (ht i j).eventually he))

/-- TC3: normalized forms retain internal factors and cross-edge directions. -/
def clusterForms {m k : ℕ} {A : Config m} {B : Config k}
    (LA : LiftFamily A) (LB : LiftFamily B) (b : Fin m → Fin k → Spinor) :
    Fin m ⊕ Fin k → BinaryForm :=
  Sum.elim (fun i => (∏ j, linearForm (b i j)) * pointForm LA i)
    (fun j => (∏ i, linearForm (antipode (b i j))) * pointForm LB j)

/-- TC3: every coefficient tends to the appropriate two-cluster boundary form. -/
theorem clusterForms_tendsto {T : Type*} {l : Filter T} {m k : ℕ}
    {A : Config m} {B : Config k} (LA : LiftFamily A) (LB : LiftFamily B)
    (v : Spinor) (b : T → Fin m → Fin k → Spinor)
    (hb : ∀ i j, Tendsto (fun t => b t i j) l (𝓝 v))
    (ij : Fin m ⊕ Fin k) (d) :
    Tendsto (fun t => MvPolynomial.coeff d (clusterForms LA LB (b t) ij)) l
      (𝓝 (MvPolynomial.coeff d (Sum.elim
        (fun i => linearForm v ^ k * pointForm LA i)
        (fun j => linearForm (antipode v) ^ m * pointForm LB j) ij))) := by
  cases ij with
  | inl i =>
    apply GeometricLimit.coeff_tendsto_mul _ (fun _ => tendsto_const_nhds)
    intro d
    simpa using GeometricLimit.coeff_tendsto_prod Finset.univ
      (fun j _ d => GeometricLimit.coeff_tendsto_linearForm (hb i j) d) d
  | inr j =>
    apply GeometricLimit.coeff_tendsto_mul _ (fun _ => tendsto_const_nhds)
    intro d
    simpa using GeometricLimit.coeff_tendsto_prod Finset.univ
      (fun i _ d => GeometricLimit.coeff_tendsto_linearForm
        (continuous_antipode.continuousAt.tendsto.comp (hb i j)) d) d

end Atiyah.TwoCluster
