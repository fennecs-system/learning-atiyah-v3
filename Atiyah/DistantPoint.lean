import Atiyah.GeometricLimit
import Atiyah.Gauge
import Atiyah.ContinuousLift
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace Atiyah.DistantPoint
open Atiyah.Configuration

/-- Add a distinguished point, indexed by zero, to a fixed core. -/
def extend {n : ℕ} (p : Config n) (x : Space)
    (hx : ∀ i, x ≠ p.point i) : Config (n + 1) where
  point := Fin.cons x p.point
  distinct := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro h
        exact (hx j (by simpa using h)).elim
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact (hx i (by simpa using h.symm)).elim
      · intro h
        exact congrArg Fin.succ (p.distinct (by simpa using h))

/-- Glue actual directed lifts on the new edges to the core lift family. -/
def extendLift {n : ℕ} {p : Config n} (L : LiftFamily p)
    (x : Space) (hx : ∀ i, x ≠ p.point i)
    (b c : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = x - p.point i)
    (hc : ∀ i, hopf (c i) = p.point i - x) : LiftFamily (extend p x hx) where
  lift := Fin.cons (Fin.cons (0, 0) c) (fun i => Fin.cons (b i) (L.lift i))
  incidence := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro _
        simpa [extend] using hc j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        simpa [extend] using hb i
      · intro hij
        simpa [extend] using L.incidence i j (fun h => hij (congrArg Fin.succ h))

private theorem prod_erase_eq_ite {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (f : ι → M) (i : ι) :
    ∏ j ∈ Finset.univ.erase i, f j = ∏ j, if j = i then 1 else f j := by
  rw [← Finset.prod_erase _ (f := fun j => if j = i then 1 else f j) (a := i) (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem pointForm_extend_zero {n : ℕ} {p : Config n} (L : LiftFamily p)
    (x : Space) (hx : ∀ i, x ≠ p.point i) (b c : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = x - p.point i)
    (hc : ∀ i, hopf (c i) = p.point i - x) :
    pointForm (extendLift L x hx b c hb hc) 0 = ∏ i, linearForm (c i) := by
  classical
  rw [pointForm, prod_erase_eq_ite, Fin.prod_univ_succ]
  simp [extendLift]

theorem pointForm_extend_succ {n : ℕ} {p : Config n} (L : LiftFamily p)
    (x : Space) (hx : ∀ i, x ≠ p.point i) (b c : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = x - p.point i)
    (hc : ∀ i, hopf (c i) = p.point i - x) (i : Fin n) :
    pointForm (extendLift L x hx b c hb hc) i.succ =
      linearForm (b i) * pointForm L i := by
  classical
  rw [pointForm, prod_erase_eq_ite, Fin.prod_univ_succ]
  simp only [Fin.succ_ne_zero, Fin.succ_ne_zero i |>.symm, ↓reduceIte, extendLift,
    Fin.cons_succ, Fin.cons_zero, Fin.succ_inj]
  rw [pointForm, prod_erase_eq_ite]


open ContinuousLift Filter Topology

/-- Rescale the local directional lifts to the actual far-point displacements. -/
def rayLift {n : ℕ} {p : Config n} (L : LiftFamily p)
    (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i, R • u ≠ p.point i) (b : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = u - R⁻¹ • p.point i) :
    LiftFamily (extend p (R • u) hx) :=
  extendLift L (R • u) hx
    (fun i => (Real.sqrt R : ℂ) • b i)
    (fun i => (Real.sqrt R : ℂ) • antipode (b i))
    (by
      intro i
      rw [hopf_sqrt_smul R hR.le, hb i, smul_sub, smul_smul,
        mul_inv_cancel₀ hR.ne', one_smul])
    (by
      intro i
      rw [hopf_sqrt_smul R hR.le, hopf_antipode, hb i, smul_neg,
        smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, neg_sub])

/-- The normalized point forms, before restoring displacement-sized lifts. -/
def rayForms {n : ℕ} {p : Config n} (L : LiftFamily p) (b : Fin n → Spinor) :
    Fin (n+1) → BinaryForm :=
  Fin.cons (∏ i, linearForm (antipode (b i)))
    (fun i => linearForm (b i) * pointForm L i)

theorem pointForm_rayLift {n : ℕ} {p : Config n} (L : LiftFamily p)
    (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i, R • u ≠ p.point i) (b : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = u - R⁻¹ • p.point i) :
    pointForm (rayLift L u R hR hx b hb) =
      fun i => (Fin.cons ((Real.sqrt R : ℂ)^n) (fun _ : Fin n => (Real.sqrt R : ℂ)) : Fin (n+1) → ℂ) i •
        rayForms L b i := by
  classical
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [rayLift, pointForm_extend_zero]
    simp only [linearForm_smul, rayForms, Fin.cons_zero,
      MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, map_pow]
  · rw [rayLift, pointForm_extend_succ]
    simp only [rayForms, Fin.cons_succ, linearForm_smul, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem independent_rayLift {n : ℕ} {p : Config n} (L : LiftFamily p)
    (u : Space) (R : ℝ) (hR : 0 < R)
    (hx : ∀ i, R • u ≠ p.point i) (b : Fin n → Spinor)
    (hb : ∀ i, hopf (b i) = u - R⁻¹ • p.point i)
    (hind : LinearIndependent ℂ (rayForms L b)) :
    ∀ K : LiftFamily (extend p (R • u) hx), LinearIndependent ℂ (pointForm K) := by
  intro K
  apply (linearIndependent_pointForm_iff (rayLift L u R hR hx b hb) K).mp
  rw [pointForm_rayLift]
  apply (linearIndependent_smul_iff _ _ ?_).mpr hind
  intro i
  have hs : (Real.sqrt R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hR))
  exact Fin.cases (pow_ne_zero n hs) (fun _ => hs) i


/-- A nonzero ray eventually avoids every point of a finite core. -/
theorem eventually_ray_avoids {n : ℕ} (u : Space) (hu : u ≠ 0)
    (a : Fin n → Space) : ∀ᶠ R : ℝ in atTop, ∀ i, R • u ≠ a i := by
  have ht (i : Fin n) : Tendsto (fun R : ℝ => u - R⁻¹ • a i) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).smul_const (a i))
  have hn : ∀ᶠ R : ℝ in atTop, ∀ i, u - R⁻¹ • a i ≠ 0 :=
    eventually_all.mpr (fun i => (ht i).eventually_ne hu)
  filter_upwards [hn, eventually_gt_atTop (0 : ℝ)] with R hn hR
  intro i he
  apply hn i
  rw [← he, smul_smul, inv_mul_cancel₀ hR.ne', one_smul, sub_self]


/-- DP: an independent fixed core remains independent after adding a point
sufficiently far along any fixed nonzero ray. The conclusion quantifies over
all actual displacement lift families, not merely the chosen local section. -/
theorem distant_point_extension {n : ℕ} (p : Config n)
    (hcore : ∀ L : LiftFamily p, LinearIndependent ℂ (pointForm L))
    (u : Space) (hu : u ≠ 0) :
    ∃ R₀ : ℝ, ∀ R > R₀, ∃ pR : Config (n + 1),
      pR.point = Fin.cons (R • u) p.point ∧ Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) := by
  classical
  obtain ⟨L⟩ := liftFamily_nonempty p
  obtain ⟨v, hv, b, hb, he⟩ := exists_ray_lifts u hu p.point
  have hi : ∀ᶠ R in atTop, LinearIndependent ℂ (rayForms L (b R)) :=
    GeometricLimit.eventually_spike_independent_fin (pointForm L) (hcore L) v hv b hb
  have ht : ∀ᶠ R : ℝ in atTop, ∃ pR : Config (n + 1),
      pR.point = Fin.cons (R • u) p.point ∧ Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) := by
    filter_upwards [hi, he, eventually_ray_avoids u hu p.point,
      eventually_gt_atTop (0 : ℝ)] with R hi he hx hR
    exact ⟨extend p (R • u) hx, rfl, liftFamily_nonempty _,
      independent_rayLift L u R hR hx (b R) he hi⟩
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp ht
  exact ⟨R₀, fun R hR => hR₀ R hR.le⟩

/-- If C1 is known for n points, its distant-point extension holds for every
n-point core. This does not assert C1 for all (n+1)-point configurations. -/
theorem distant_point_extension_of_c1 {n : ℕ} (hn : C1 n)
    (p : Config n) (u : Space) (hu : u ≠ 0) :
    ∃ R₀ : ℝ, ∀ R > R₀, ∃ pR : Config (n + 1),
      pR.point = Fin.cons (R • u) p.point ∧ Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) :=
  distant_point_extension p (hn p).2 u hu

end Atiyah.DistantPoint
