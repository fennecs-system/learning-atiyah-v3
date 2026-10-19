import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The real planar Hopf incidence cover

The equations `a² - b² = 2*x`, `a*b = y` give a polynomial incidence
presentation of planar lifts. Square roots select local real branches; they
are not regular functions on the base. The antipodal involution acts on
lifts by `J(a,b)=(-b,a)`, with `J²=-1`.
-/
namespace Atiyah.PlanarLift

/-- Real slice of the Hopf map, in the convention of the research notes. -/
noncomputable def hopf (a b : ℝ) : ℝ × ℝ := ((a ^ 2 - b ^ 2) / 2, a * b)

/-- Polynomial equations for the incidence cover. -/
def Incidence (x y a b : ℝ) : Prop := a ^ 2 - b ^ 2 = 2 * x ∧ a * b = y

theorem incidence_iff_hopf (x y a b : ℝ) :
    Incidence x y a b ↔ hopf a b = (x, y) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · dsimp [hopf]
      linarith
    · exact h₂
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp [hopf] at h₁ h₂
    exact ⟨by linarith, h₂⟩

/-- Rotation of a lift represents the antipodal displacement. -/
theorem hopf_antipodal (a b : ℝ) :
    hopf (-b) a = (-(hopf a b).1, -(hopf a b).2) := by
  apply Prod.ext <;> dsimp [hopf] <;> ring

theorem incidence_antipodal {x y a b : ℝ} (h : Incidence x y a b) :
    Incidence (-x) (-y) (-b) a := by
  rcases h with ⟨h₁, h₂⟩
  constructor <;> nlinarith

/-- The deck transformation fixes the represented displacement. -/
theorem hopf_deck (a b : ℝ) : hopf (-a) (-b) = hopf a b := by
  apply Prod.ext <;> dsimp [hopf] <;> ring

/-- Antipodal operation on homogeneous coordinates. -/
def J (q : ℝ × ℝ) : ℝ × ℝ := (-q.2, q.1)

/-- Applying the antipodal operation twice gives the deck transformation. -/
theorem antipodal_twice (a b : ℝ) : J (J (a, b)) = (-a, -b) := rfl

/-- Nonzero displacements cannot have the zero lift. -/
theorem lift_nonzero {x y a b : ℝ} (h : Incidence x y a b)
    (hne : (x, y) ≠ (0, 0)) : (a, b) ≠ (0, 0) := by
  intro hab
  have ha : a = 0 := congrArg Prod.fst hab
  have hb : b = 0 := congrArg Prod.snd hab
  rcases h with ⟨h₁, h₂⟩
  apply hne
  apply Prod.ext <;> dsimp at * <;> nlinarith

/-- The radial identity is polynomial, before choosing any square roots. -/
theorem radial_identity {x y a b : ℝ} (h : Incidence x y a b) :
    (a ^ 2 + b ^ 2) ^ 2 = 4 * (x ^ 2 + y ^ 2) := by
  rcases h with ⟨h₁, h₂⟩
  have hx : x = (a ^ 2 - b ^ 2) / 2 := by linarith
  rw [hx, ← h₂]
  ring

/-- The two antipodal lifts form a basis whenever the displacement is nonzero. -/
theorem antipodal_determinant_pos {x y a b : ℝ} (h : Incidence x y a b)
    (hne : (x, y) ≠ (0, 0)) : 0 < a * a - (-b) * b := by
  have hab := lift_nonzero h hne
  have ha := sq_nonneg a
  have hb := sq_nonneg b
  by_contra hn
  have ha0 : a = 0 := by nlinarith
  have hb0 : b = 0 := by nlinarith
  exact hab (Prod.ext ha0 hb0)

/-- On the upper half-plane, both square-root coordinates are nonnegative. -/
theorem upper_sqrt_incidence {x y r : ℝ} (hplus : 0 ≤ r + x)
    (hminus : 0 ≤ r - x) (hrad : r ^ 2 = x ^ 2 + y ^ 2) (hy : 0 ≤ y) :
    Incidence x y (Real.sqrt (r + x)) (Real.sqrt (r - x)) := by
  have hp := Real.sq_sqrt hplus
  have hm := Real.sq_sqrt hminus
  constructor
  · nlinarith
  · have hproduct : (r + x) * (r - x) = y ^ 2 := by nlinarith
    rw [← Real.sqrt_mul hplus, hproduct, Real.sqrt_sq_eq_abs, abs_of_nonneg hy]

/-- Correct lower branch: the radicals do NOT exchange positions.

Equivalently, apply `J` to the upper lift of `(-x,-y)`.
-/
theorem lower_sqrt_incidence {x y r : ℝ} (hplus : 0 ≤ r + x)
    (hminus : 0 ≤ r - x) (hrad : r ^ 2 = x ^ 2 + y ^ 2) (hy : y ≤ 0) :
    Incidence x y (-Real.sqrt (r + x)) (Real.sqrt (r - x)) := by
  have hp := Real.sq_sqrt hplus
  have hm := Real.sq_sqrt hminus
  constructor
  · nlinarith
  · have hproduct : (r + x) * (r - x) = y ^ 2 := by nlinarith
    rw [neg_mul, ← Real.sqrt_mul hplus, hproduct, Real.sqrt_sq_eq_abs,
      abs_of_nonpos hy, neg_neg]

/-- Regression: the exchanged-radical formula reflects the x coordinate. -/
theorem exchanged_lower_branch {x y r : ℝ} (hplus : 0 ≤ r + x)
    (hminus : 0 ≤ r - x) (hrad : r ^ 2 = x ^ 2 + y ^ 2) (hy : y ≤ 0) :
    Incidence (-x) y (-Real.sqrt (r - x)) (Real.sqrt (r + x)) := by
  have h := lower_sqrt_incidence (x := -x) (y := y) (r := r)
    (by linarith : 0 ≤ r + -x) (by linarith : 0 ≤ r - -x)
    (by nlinarith : r ^ 2 = (-x) ^ 2 + y ^ 2) hy
  simpa using h

/-- A total real branch, including horizontal displacements. It need not be
continuous across its branch cut; the incidence equations are global. -/
noncomputable def canonicalLift (x y : ℝ) : ℝ × ℝ :=
  let r := Real.sqrt (x ^ 2 + y ^ 2)
  if 0 ≤ y then (Real.sqrt (r + x), Real.sqrt (r - x))
  else (-Real.sqrt (r + x), Real.sqrt (r - x))

theorem canonicalLift_incidence (x y : ℝ) :
    Incidence x y (canonicalLift x y).1 (canonicalLift x y).2 := by
  have hrad : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg x, sq_nonneg y])
  have hb := abs_le.mp (Real.abs_le_sqrt (show x ^ 2 ≤ x ^ 2 + y ^ 2 by nlinarith [sq_nonneg y]))
  have hp : 0 ≤ Real.sqrt (x ^ 2 + y ^ 2) + x := by linarith [hb.1]
  have hm : 0 ≤ Real.sqrt (x ^ 2 + y ^ 2) - x := by linarith [hb.2]
  unfold canonicalLift
  split_ifs with hy
  · exact upper_sqrt_incidence hp hm hrad hy
  · exact lower_sqrt_incidence hp hm hrad (le_of_lt (lt_of_not_ge hy))

end Atiyah.PlanarLift
