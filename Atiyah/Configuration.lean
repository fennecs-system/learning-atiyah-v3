import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Configurations, the Hopf incidence space, and C1

We use `ℝ × ℂ` for Euclidean three-space. A lift `(a,b)` represents a
projective direction in `ℙ¹(ℂ)`; its associated binary linear form is
`a X₀ + b X₁`. Products give points of `ℙ(Symⁿ⁻¹ ℂ²)`.

These definitions are original code. The standard mathematical construction
is due to Atiyah and Sutcliffe. C1 is recorded as a proposition, not assumed
as an axiom and not asserted as a theorem. Choosing coefficients rather than
roots changes the projective convention by a common duality, which does not
change linear independence. No algebraicity of square-root sections is claimed.
-/

noncomputable section

namespace Atiyah.Configuration

abbrev Space := ℝ × ℂ
abbrev Spinor := ℂ × ℂ
abbrev BinaryForm := MvPolynomial (Fin 2) ℂ

/-- Ordered configuration of pairwise distinct points. -/
structure Config (n : ℕ) where
  point : Fin n → Space
  distinct : Function.Injective point

/-- The quadratic real Hopf map, without division by the displacement length. -/
def hopf (u : Spinor) : Space :=
  ((Complex.normSq u.1 - Complex.normSq u.2) / 2, u.1 * star u.2)

/-- A family of lifts of all directed displacements. Diagonal entries are ignored.
The equations define a real algebraic incidence locus over configuration space.
-/
structure LiftFamily {n : ℕ} (p : Config n) where
  lift : Fin n → Fin n → Spinor
  incidence : ∀ i j, i ≠ j → hopf (lift i j) = p.point j - p.point i

/-- The linear form corresponding to a nonzero spinor. -/
def linearForm (u : Spinor) : BinaryForm :=
  MvPolynomial.C u.1 * MvPolynomial.X 0 +
  MvPolynomial.C u.2 * MvPolynomial.X 1

/-- The product of the outgoing directed factors, of homogeneous degree `n-1`.
We retain it in the ambient polynomial ring rather than a degree subtype.
-/
noncomputable def pointForm {n : ℕ} {p : Config n} (L : LiftFamily p)
    (i : Fin n) : BinaryForm :=
  ∏ j ∈ Finset.univ.erase i, linearForm (L.lift i j)

/-- Original linear-independence conjecture C1, with arbitrary Hopf lift choices.
Existence is included explicitly, so configurations without a lift family cannot
satisfy this proposition vacuously. Independence of lift choices remains a lemma
to formalize; universal quantification expresses the usual choice-free claim.
-/
def C1 (n : ℕ) : Prop :=
  ∀ (p : Config n), Nonempty (LiftFamily p) ∧
    ∀ (L : LiftFamily p), LinearIndependent ℂ (pointForm L)

@[simp] theorem hopf_zero : hopf (0, 0) = 0 := by
  simp [hopf]

/-- Distinctness rules out the zero lift. -/
theorem lift_ne_zero {n : ℕ} {p : Config n} (L : LiftFamily p)
    (i j : Fin n) (hij : i ≠ j) : L.lift i j ≠ (0, 0) := by
  intro h
  have he := L.incidence i j hij
  rw [h, hopf_zero] at he
  have hp : p.point j = p.point i := sub_eq_zero.mp he.symm
  exact hij (p.distinct hp).symm

/-- A binary linear form vanishes only when both its coefficients vanish. -/
theorem linearForm_eq_zero_iff (u : Spinor) : linearForm u = 0 ↔ u = (0, 0) := by
  constructor
  · intro h
    have ha := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) h
    have hb := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) h
    simp [linearForm] at ha hb
    exact Prod.ext ha hb
  · rintro rfl
    simp [linearForm]

/-- Every off-diagonal factor is nonzero. -/
theorem factor_ne_zero {n : ℕ} {p : Config n} (L : LiftFamily p)
    (i j : Fin n) (hij : i ≠ j) : linearForm (L.lift i j) ≠ 0 := by
  intro h
  exact lift_ne_zero L i j hij ((linearForm_eq_zero_iff _).mp h)

/-- Products define genuine projective points: none is the zero binary form. -/
theorem pointForm_ne_zero {n : ℕ} {p : Config n} (L : LiftFamily p)
    (i : Fin n) : pointForm L i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact factor_ne_zero L i j (Finset.mem_erase.mp hj).1.symm

/-- At one point the empty product is the constant binary form 1. -/
@[simp] theorem pointForm_one {p : Config 1} (L : LiftFamily p) (i : Fin 1) :
    pointForm L i = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [pointForm]

/-- The one-point instance of C1 is verified. -/
theorem c1_one : C1 1 := by
  intro p
  constructor
  · refine ⟨⟨fun _ _ => (0, 0), ?_⟩⟩
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro L
    apply (linearIndependent_unique_iff (R := ℂ) (pointForm L)).mpr
    rw [pointForm_one]
    exact one_ne_zero

/-- The quadratic Hopf map covers all of three-space, including both poles. -/
theorem hopf_surjective : Function.Surjective hopf := by
  rintro ⟨x, z⟩
  let r := Real.sqrt (x ^ 2 + Complex.normSq z)
  have hn : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = x ^ 2 + Complex.normSq z :=
    Real.sq_sqrt (by positivity)
  have hrx : 0 ≤ r + x := by nlinarith
  by_cases hpos : 0 < r + x
  · let a := Real.sqrt (r + x)
    have ha : 0 < a := Real.sqrt_pos.2 hpos
    have ha2 : a ^ 2 = r + x := Real.sq_sqrt hrx
    have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    refine ⟨((a : ℂ), star z / (a : ℂ)), ?_⟩
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
  · have hrx0 : r + x = 0 := le_antisymm (le_of_not_gt hpos) hrx
    have hz : Complex.normSq z = 0 := by nlinarith
    have hz0 : z = 0 := Complex.normSq_eq_zero.mp hz
    have hx : 0 ≤ -2 * x := by linarith
    refine ⟨(0, (Real.sqrt (-2 * x) : ℂ)), ?_⟩
    apply Prod.ext
    · simp only [hopf, Complex.normSq_zero, Complex.normSq_ofReal]
      have hh := Real.sq_sqrt hx
      nlinarith
    · simp [hopf, hz0]

/-- Every distinct configuration admits a family of directed Hopf lifts. -/
theorem liftFamily_nonempty {n : ℕ} (p : Config n) : Nonempty (LiftFamily p) := by
  classical
  choose u hu using hopf_surjective
  exact ⟨⟨fun i j => u (p.point j - p.point i), fun i j _ => hu _⟩⟩

/-- With existence discharged, C1 reduces to its linear-independence assertion. -/
theorem c1_iff (n : ℕ) : C1 n ↔
    ∀ (p : Config n) (L : LiftFamily p), LinearIndependent ℂ (pointForm L) := by
  constructor
  · intro h p L
    exact (h p).2 L
  · intro h p
    exact ⟨liftFamily_nonempty p, h p⟩

end Atiyah.Configuration
