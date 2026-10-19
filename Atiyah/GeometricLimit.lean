import Atiyah.Configuration
import Atiyah.ContinuousLift
import Atiyah.SpikeLimit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! DP3–DP5: coefficientwise convergence of binary forms and stability of finite
independent families. Finite coefficient witnesses avoid a choice of affine chart. -/
noncomputable section
namespace Atiyah.GeometricLimit
open Configuration Filter Topology

/-- DP5: finitely many coefficients witness independence, even in the ambient
infinite-dimensional polynomial ring. -/
theorem eventually_independent_of_coeff_tendsto {T ι : Type*} [Fintype ι]
    {l : Filter T} {f : T → ι → BinaryForm} {f₀ : ι → BinaryForm}
    (h₀ : LinearIndependent ℂ f₀)
    (h : ∀ i d, Tendsto (fun t => MvPolynomial.coeff d (f t i)) l
      (𝓝 (MvPolynomial.coeff d (f₀ i)))) :
    ∀ᶠ t in l, LinearIndependent ℂ (f t) := by
  classical
  let S := Finset.univ.biUnion (fun i => (f₀ i).support)
  let C : BinaryForm →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun p d => MvPolynomial.coeff d.val p
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hC : LinearIndependent ℂ (fun i => C (f₀ i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    apply Fintype.linearIndependent_iff.mp h₀ c
    ext d
    by_cases hd : d ∈ S
    · have hh := congrFun hc (⟨d, hd⟩ : S)
      simpa [C, MvPolynomial.coeff_sum] using hh
    · simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
        MvPolynomial.coeff_zero]
      apply Finset.sum_eq_zero
      intro i hi
      have hdi : d ∉ (f₀ i).support := by
        intro hdi
        exact hd (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hdi⟩)
      simp [MvPolynomial.not_mem_support_iff.mp hdi]
  have hlim : Tendsto (fun t i => C (f t i)) l (𝓝 (fun i => C (f₀ i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro d
    exact h i d.val
  filter_upwards [hlim.eventually hC.eventually] with t ht
  exact ht.of_comp C

/-- DP3: multiplication is continuous coefficient by coefficient. -/
theorem coeff_tendsto_mul {T : Type*} {l : Filter T}
    {p q : T → BinaryForm} {p₀ q₀ : BinaryForm}
    (hp : ∀ d, Tendsto (fun t => MvPolynomial.coeff d (p t)) l
      (𝓝 (MvPolynomial.coeff d p₀)))
    (hq : ∀ d, Tendsto (fun t => MvPolynomial.coeff d (q t)) l
      (𝓝 (MvPolynomial.coeff d q₀))) (d) :
    Tendsto (fun t => MvPolynomial.coeff d (p t * q t)) l
      (𝓝 (MvPolynomial.coeff d (p₀ * q₀))) := by
  simp only [MvPolynomial.coeff_mul]
  exact tendsto_finset_sum _ (fun a _ => (hp a.1).mul (hq a.2))

/-- DP3: finite products inherit coefficientwise convergence. -/
theorem coeff_tendsto_prod {T ι : Type*} {l : Filter T}
    (s : Finset ι) {p : T → ι → BinaryForm} {p₀ : ι → BinaryForm}
    (hp : ∀ i ∈ s, ∀ d, Tendsto (fun t => MvPolynomial.coeff d (p t i)) l
      (𝓝 (MvPolynomial.coeff d (p₀ i)))) (d) :
    Tendsto (fun t => MvPolynomial.coeff d (∏ i ∈ s, p t i)) l
      (𝓝 (MvPolynomial.coeff d (∏ i ∈ s, p₀ i))) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa using tendsto_const_nhds
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact coeff_tendsto_mul (hp i (Finset.mem_insert_self _ _))
        (fun d => ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)) d) d

/-- DP3: the binary linear form depends continuously on its two coefficients. -/
theorem coeff_tendsto_linearForm {T : Type*} {l : Filter T}
    {v : T → Spinor} {v₀ : Spinor} (hv : Tendsto v l (𝓝 v₀)) (d) :
    Tendsto (fun t => MvPolynomial.coeff d (linearForm (v t))) l
      (𝓝 (MvPolynomial.coeff d (linearForm v₀))) := by
  simp only [linearForm, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
  exact ((continuous_fst.tendsto _ |>.comp hv).mul_const _).add
    ((continuous_snd.tendsto _ |>.comp hv).mul_const _)

/-- DP4 in homogeneous coordinates, valid at both poles: the antipodal form
is nonzero at a zero of the outgoing form. -/
theorem boundary_independent {ι : Type*} (q : ι → BinaryForm)
    (hq : LinearIndependent ℂ q) (v : Spinor) (hv : v ≠ 0) (m : ℕ) :
    LinearIndependent ℂ (fun o : Option ι => o.elim
      (linearForm (ContinuousLift.antipode v) ^ m) (fun i => linearForm v * q i)) := by
  let w : Fin 2 → ℂ := ![-v.2, v.1]
  have hL : linearForm v ≠ 0 := by
    exact fun h => hv ((linearForm_eq_zero_iff v).mp h)
  have hM : MvPolynomial.eval w (linearForm (ContinuousLift.antipode v)) ≠ 0 := by
    have hdet := ContinuousLift.antipodal_determinant_ne_zero v hv
    simpa [w, linearForm, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm] using hdet
  apply SpikeLimit.independent_extension q hq (LinearMap.mulLeft ℂ (linearForm v))
    (mul_right_injective₀ hL) (MvPolynomial.aeval w).toLinearMap ?_
    (linearForm (ContinuousLift.antipode v) ^ m) ?_
  · intro p
    simp [LinearMap.mulLeft_apply, w, linearForm, mul_comm]
  · simpa using pow_ne_zero m hM

/-- DP3–DP5: converging outgoing spinors give an eventually independent
geometric product family. This does not assume a matrix limit or independence
of any finite-parameter family. -/
theorem eventually_spike_independent {T : Type*} {n : ℕ} {l : Filter T}
    (q : Fin n → BinaryForm) (hq : LinearIndependent ℂ q)
    (v : Spinor) (hv : v ≠ 0) (s : T → Fin n → Spinor)
    (hs : ∀ i, Tendsto (fun t => s t i) l (𝓝 v)) :
    ∀ᶠ t in l, LinearIndependent ℂ (fun o : Option (Fin n) => o.elim
      (∏ i, linearForm (ContinuousLift.antipode (s t i)))
      (fun i => linearForm (s t i) * q i)) := by
  apply eventually_independent_of_coeff_tendsto (boundary_independent q hq v hv n)
  intro o d
  cases o with
  | none =>
      have hh := coeff_tendsto_prod Finset.univ
        (p := fun t i => linearForm (ContinuousLift.antipode (s t i)))
        (p₀ := fun _ => linearForm (ContinuousLift.antipode v))
        (fun i _ d => coeff_tendsto_linearForm
          (ContinuousLift.continuous_antipode.continuousAt.tendsto.comp (hs i)) d) d
      simpa using hh
  | some i =>
      exact coeff_tendsto_mul (coeff_tendsto_linearForm (hs i))
        (fun _ => tendsto_const_nhds) d

/-- Finite-indexed form of the geometric product stability theorem. -/
theorem eventually_spike_independent_fin {T : Type*} {n : ℕ} {l : Filter T}
    (q : Fin n → BinaryForm) (hq : LinearIndependent ℂ q)
    (v : Spinor) (hv : v ≠ 0) (s : T → Fin n → Spinor)
    (hs : ∀ i, Tendsto (fun t => s t i) l (𝓝 v)) :
    ∀ᶠ t in l, LinearIndependent ℂ (Fin.cons
      (∏ i, linearForm (ContinuousLift.antipode (s t i)))
      (fun i => linearForm (s t i) * q i)) := by
  filter_upwards [eventually_spike_independent q hq v hv s hs] with t ht
  apply linearIndependent_fin_cons.mpr
  rw [linearIndependent_option] at ht
  exact ht

end Atiyah.GeometricLimit
