import Atiyah.Configuration
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Coeff

/-!
HB1: Dehomogenization sends X₀ to 1 and X₁ to T.
HB2: Degree-d homogenization sends T^k to X₀^(d-k) X₁^k. On a
homogeneous degree-d binary form this is a left inverse of HB1, since every
supported exponent pair sums to d.
HB3: Consequently a linear relation among dehomogenized degree-d forms
is precisely a relation among the forms. Point forms have degree n-1.
Correspondence ledger: HB1 `dehom`; HB2 `homogen_dehom`; HB3
`linearIndependent_dehom_iff`, `pointForm_homogeneous`.
-/
noncomputable section
namespace Atiyah.HomogeneousBridge
open Atiyah.Configuration MvPolynomial

def dehom : BinaryForm →ₐ[ℂ] Polynomial ℂ := aeval ![1, Polynomial.X]

def homogen (d : ℕ) : Polynomial ℂ →ₗ[ℂ] BinaryForm :=
  Polynomial.lsum fun k => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    (X 0 ^ (d-k) * X 1 ^ k)

@[simp] theorem dehom_linearForm (u : Spinor) :
    dehom (linearForm u) = Polynomial.C u.1 + Polynomial.C u.2 * Polynomial.X := by
  simp [dehom, linearForm]

lemma dehom_monomial (m : Fin 2 →₀ ℕ) (c : ℂ) :
    dehom (monomial m c) = Polynomial.monomial (m 1) c := by
  simp [dehom, aeval_def, eval₂_monomial, Finsupp.prod_fintype,
    Fin.prod_univ_two, Polynomial.C_mul_X_pow_eq_monomial]

lemma homogen_monomial (d k : ℕ) (c : ℂ) :
    homogen d (Polynomial.monomial k c) = c • (X 0 ^ (d-k) * X 1 ^ k) := by
  simp [homogen, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

lemma degree_pair (m : Fin 2 →₀ ℕ) : m.degree = m 0 + m 1 := by
  change m.sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Fin.sum_univ_two]

lemma binary_monomial (m : Fin 2 →₀ ℕ) (c : ℂ) :
    monomial m c = c • (X 0 ^ m 0 * X 1 ^ m 1) := by
  rw [MvPolynomial.monomial_eq]
  simp [Finsupp.prod_fintype, Fin.prod_univ_two, smul_eq_C_mul]

theorem homogen_dehom {d : ℕ} {p : BinaryForm} (hp : p.IsHomogeneous d) :
    homogen d (dehom p) = p := by
  conv_rhs => rw [p.as_sum]
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dehom_monomial, homogen_monomial, binary_monomial]
  have hd := hp (mem_support_iff.mp hm)
  have hd' : m.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  rw [degree_pair] at hd'
  congr 3
  omega

theorem linearIndependent_dehom_iff {ι : Type*} {d : ℕ} (p : ι → BinaryForm)
    (hp : ∀ i, (p i).IsHomogeneous d) :
    LinearIndependent ℂ (fun i => dehom (p i)) ↔ LinearIndependent ℂ p := by
  constructor
  · exact LinearIndependent.of_comp dehom.toLinearMap
  · intro h
    apply LinearIndependent.of_comp (homogen d)
    simpa only [Function.comp_def, homogen_dehom (hp _)] using h

theorem linearForm_homogeneous (u : Spinor) : (linearForm u).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X u.1 0).add (isHomogeneous_C_mul_X u.2 1)

theorem pointForm_homogeneous {n : ℕ} {p : Config n} (L : LiftFamily p) (i : Fin n) :
    (pointForm L i).IsHomogeneous (n-1) := by
  classical
  have h := IsHomogeneous.prod (Finset.univ.erase i)
    (fun j => linearForm (L.lift i j)) (fun _ => 1)
    (fun j _ => linearForm_homogeneous (L.lift i j))
  simpa [pointForm] using h

theorem linearIndependent_dehom_pointForm_iff {n : ℕ} {p : Config n}
    (L : LiftFamily p) :
    LinearIndependent ℂ (fun i => dehom (pointForm L i)) ↔
      LinearIndependent ℂ (pointForm L) :=
  linearIndependent_dehom_iff _ (pointForm_homogeneous L)

end Atiyah.HomogeneousBridge
