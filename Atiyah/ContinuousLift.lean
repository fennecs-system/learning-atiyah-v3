import Atiyah.Configuration
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic

/-!
DP2a: at each nonzero displacement there exists a section continuous at that
point and satisfying Hopf incidence throughout a neighborhood. The chart is
chosen once at the base point; no global continuous section is asserted.
DP2b: antipodal conjugation is continuous and its determinant with a nonzero
spinor is nonzero. These are the two independent limiting linear factors.
-/
noncomputable section
open Filter Topology
namespace Atiyah.ContinuousLift
open Configuration

def antipode (v : Spinor) : Spinor := (-star v.2, star v.1)

theorem hopf_antipode (v : Spinor) : hopf (antipode v) = -hopf v := by
  apply Prod.ext
  · simp [hopf, antipode, Complex.normSq_neg, Complex.normSq_conj]
    ring
  · simp [hopf, antipode, mul_comm]

theorem continuous_antipode : Continuous antipode := by
  unfold antipode
  fun_prop

def radius (p : Space) : ℝ := Real.sqrt (p.1 ^ 2 + Complex.normSq p.2)
def north (p : Space) : Spinor :=
  ((Real.sqrt (radius p + p.1) : ℂ), star p.2 / (Real.sqrt (radius p + p.1) : ℂ))

theorem continuous_radius : Continuous radius := by
  unfold radius
  fun_prop

theorem north_incidence (p : Space) (hp : 0 < radius p + p.1) : hopf (north p) = p := by
  rcases p with ⟨x, z⟩
  let r := radius (x, z)
  let a := Real.sqrt (r + x)
  have hr2 : r ^ 2 = x ^ 2 + Complex.normSq z := Real.sq_sqrt (add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  have ha : 0 < a := Real.sqrt_pos.2 hp
  have ha2 : a ^ 2 = r + x := Real.sq_sqrt (le_of_lt hp)
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  change hopf ((a : ℂ), star z / (a : ℂ)) = (x, z)
  apply Prod.ext
  · dsimp [hopf]
    simp only [Complex.normSq_div, Complex.normSq_ofReal]
    rw [Complex.normSq_conj]
    have he : Complex.normSq z = (r - x) * (a * a) := by nlinarith
    rw [he, mul_div_cancel_right₀ _ (mul_ne_zero (ne_of_gt ha) (ne_of_gt ha))]
    nlinarith
  · dsimp [hopf]
    simp only [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    exact mul_div_cancel₀ z hac

theorem north_continuousAt (p : Space) (hp : 0 < radius p + p.1) :
    ContinuousAt north p := by
  have ha : (Real.sqrt (radius p + p.1) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp)
  unfold north
  apply ContinuousAt.prodMk
  · exact (Complex.continuous_ofReal.comp ((continuous_radius.add continuous_fst).sqrt)).continuousAt
  · apply ContinuousAt.div
    · fun_prop
    · exact (Complex.continuous_ofReal.comp ((continuous_radius.add continuous_fst).sqrt)).continuousAt
    · exact ha

theorem chart_covers (p : Space) (hp : p ≠ 0) :
    0 < radius p + p.1 ∨ 0 < radius (-p) + (-p).1 := by
  have hr : 0 ≤ radius p := Real.sqrt_nonneg _
  have he : radius (-p) = radius p := by simp [radius]
  have hsq : radius p ^ 2 = p.1 ^ 2 + Complex.normSq p.2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  have hn := Complex.normSq_nonneg p.2
  by_cases h₁ : 0 < radius p + p.1
  · exact Or.inl h₁
  by_cases h₂ : 0 < radius (-p) + (-p).1
  · exact Or.inr h₂
  have h := And.intro (le_of_not_gt h₁) (le_of_not_gt h₂)
  exfalso
  simp only [he, Prod.fst_neg] at h
  have hx : p.1 = 0 := by nlinarith [h.1, h.2]
  have hz : p.2 = 0 := Complex.normSq_eq_zero.mp (by nlinarith [h.1, h.2])
  exact hp (Prod.ext hx hz)

theorem exists_local_hopf_section (p : Space) (hp : p ≠ 0) :
    ∃ s : Space → Spinor, ContinuousAt s p ∧ hopf (s p) = p ∧
      ∀ᶠ q in 𝓝 p, hopf (s q) = q := by
  rcases chart_covers p hp with h | h
  · refine ⟨north, north_continuousAt p h, north_incidence p h, ?_⟩
    have he : ∀ᶠ q in 𝓝 p, 0 < radius q + q.1 :=
      (continuous_radius.add continuous_fst).continuousAt.eventually (lt_mem_nhds h)
    exact he.mono fun q hq => north_incidence q hq
  · refine ⟨fun q => antipode (north (-q)), ?_, ?_, ?_⟩
    · exact continuous_antipode.continuousAt.comp
        ((north_continuousAt (-p) h).comp continuous_neg.continuousAt)
    · rw [hopf_antipode, north_incidence (-p) h, neg_neg]
    · have he : ∀ᶠ q in 𝓝 p, 0 < radius (-q) + (-q).1 :=
        ((continuous_radius.comp continuous_neg).add (continuous_fst.comp continuous_neg)).continuousAt.eventually
          (lt_mem_nhds h)
      filter_upwards [he] with q hq
      rw [hopf_antipode, north_incidence (-q) hq, neg_neg]

/-- Antipodal spinors span the coefficient plane, including both pole cases. -/
theorem antipodal_determinant (v : Spinor) :
    v.1 * (antipode v).2 - v.2 * (antipode v).1 =
      ((Complex.normSq v.1 + Complex.normSq v.2 : ℝ) : ℂ) := by
  simp [antipode, sub_neg_eq_add, Complex.mul_conj]

theorem antipodal_determinant_ne_zero (v : Spinor) (hv : v ≠ 0) :
    v.1 * (antipode v).2 - v.2 * (antipode v).1 ≠ 0 := by
  rw [antipodal_determinant]
  apply Complex.ofReal_ne_zero.mpr
  intro h
  have h₁ := Complex.normSq_nonneg v.1
  have h₂ := Complex.normSq_nonneg v.2
  apply hv
  exact Prod.ext (Complex.normSq_eq_zero.mp (by linarith))
    (Complex.normSq_eq_zero.mp (by linarith))

/-- DP2 along a fixed ray: one local chart works eventually for every point of
any finite core. No unit-length hypothesis on the nonzero axis is needed. -/
theorem exists_ray_lifts {n : ℕ} (u : Space) (hu : u ≠ 0)
    (a : Fin n → Space) :
    ∃ v : Spinor, v ≠ 0 ∧ ∃ b : ℝ → Fin n → Spinor,
      (∀ i, Tendsto (fun R => b R i) atTop (𝓝 v)) ∧
      ∀ᶠ R in atTop, ∀ i, hopf (b R i) = u - R⁻¹ • a i := by
  obtain ⟨s, hs, hsu, he⟩ := exists_local_hopf_section u hu
  have hv : s u ≠ 0 := by
    intro h
    apply hu
    rw [← hsu, h]
    exact hopf_zero
  have ht (i : Fin n) :
      Tendsto (fun R : ℝ => u - R⁻¹ • a i) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).smul_const (a i))
  refine ⟨s u, hv, fun R i => s (u - R⁻¹ • a i), ?_, ?_⟩
  · intro i
    exact hs.tendsto.comp (ht i)
  · exact eventually_all.mpr (fun i => (ht i).eventually he)

end Atiyah.ContinuousLift
