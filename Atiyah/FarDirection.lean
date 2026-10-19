import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Directions towards a distant point

This proves the analytic direction limit, without assuming a limit of Hopf lifts
or coefficient matrices. It is one geometric input to the distant-point argument.
-/

namespace Atiyah.FarDirection

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit-direction normalization, with value zero at the zero vector. -/
noncomputable def direction (x : E) : E := ‖x‖⁻¹ • x

/-- Normalization is continuous away from the origin. -/
theorem continuousAt_direction {x : E} (hx : x ≠ 0) :
    ContinuousAt (direction : E → E) x := by
  exact (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

/-- In the inverse-distance coordinate, the direction converges to the unit axis. -/
theorem tendsto_direction_sub (u a : E) (hu : ‖u‖ = 1) :
    Tendsto (fun t : ℝ => direction (u - t • a)) (𝓝 0) (𝓝 u) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h : Tendsto (fun t : ℝ => u - t • a) (𝓝 0) (𝓝 u) := by
    simpa using (tendsto_const_nhds.sub ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).smul_const a))
  simpa [direction, hu] using (continuousAt_direction hu0).tendsto.comp h

/-- The near-limit displacement is eventually nonzero. -/
theorem eventually_sub_ne_zero (u a : E) (hu : ‖u‖ = 1) :
    ∀ᶠ t : ℝ in 𝓝 0, u - t • a ≠ 0 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h : Tendsto (fun t : ℝ => u - t • a) (𝓝 0) (𝓝 u) := by
    simpa using (tendsto_const_nhds.sub ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).smul_const a))
  exact h.eventually_ne hu0

/-- Positive scaling does not affect the normalized direction. -/
theorem direction_pos_smul (r : ℝ) (hr : 0 < r) (x : E) :
    direction (r • x) = direction x := by
  simp only [direction, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mul_inv_rev, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), mul_one]

/-- Physical distance and inverse-distance coordinates give the same direction. -/
theorem direction_far_eq (R : ℝ) (hR : 0 < R) (u a : E) :
    direction (R • u - a) = direction (u - R⁻¹ • a) := by
  have h : R • u - a = R • (u - R⁻¹ • a) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  rw [h, direction_pos_smul R hR]

/-- A point escaping along a ray has asymptotically the ray's direction from any
fixed point. This is the actual geometric limit used in a one-outlier argument. -/
theorem tendsto_direction_far (u a : E) (hu : ‖u‖ = 1) :
    Tendsto (fun R : ℝ => direction (R • u - a)) atTop (𝓝 u) := by
  have h := (tendsto_direction_sub u a hu).comp
    (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (direction_far_eq R hR u a).symm

/-- The escaping point eventually avoids any fixed point. -/
theorem eventually_far_ne_zero (u a : E) (hu : ‖u‖ = 1) :
    ∀ᶠ R : ℝ in atTop, R • u - a ≠ 0 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  filter_upwards [(tendsto_direction_far u a hu).eventually_ne hu0] with R hR
  intro h
  exact hR (by simp [direction, h])

/-- A distant point eventually avoids every point of a fixed finite cluster. -/
theorem eventually_far_avoids_cluster {ι : Type*} [Fintype ι]
    (u : E) (a : ι → E) (hu : ‖u‖ = 1) :
    ∀ᶠ R : ℝ in atTop, ∀ i, R • u ≠ a i := by
  have h : ∀ i, ∀ᶠ R : ℝ in atTop, R • u ≠ a i := by
    intro i
    filter_upwards [eventually_far_ne_zero u (a i) hu] with R hR
    exact sub_ne_zero.mp hR
  exact eventually_all.mpr h

end Atiyah.FarDirection
