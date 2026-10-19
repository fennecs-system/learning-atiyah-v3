import Mathlib

/-!
Formal-English ledger:
SD1: If L has constant coefficient one, E=Σ(k<a)(1-L)^k is an inverse
modulo X^a. D=(C*E) mod X^a has degree below a and C-LD is divisible by X^a.
SD2: For a,q>0, deg L≤2 and deg C<a+q+2, W=(C-LD)/X^a has degree<q+2.
Dividing W by the monic quadratic U=(X-γ)(X-β) yields V+US with deg V<2,
deg S<q. Thus C=LD+X^a(V+US). No condition γ≠β is needed for division.
SD3: A polynomial of degree<2 is C(v0)+C(v1)X. This gives the affine
coordinates used in the determinant elimination module.
The finite inverse formula is constructive but is not yet identified with the
list recurrence in SingularCertificate.
-/
noncomputable section
namespace Atiyah.SingularDivision
open Polynomial

/-- Finite inverse modulo X^a, valid when the constant coefficient is one. -/
def inverseTrunc (L : ℝ[X]) (a : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range a, (1-L)^k

def lowerPart (C L : ℝ[X]) (a : ℕ) : ℝ[X] :=
  (C * inverseTrunc L a) %ₘ (X^a)

theorem lowerPart_divisible (C L : ℝ[X]) (a : ℕ) (hL : L.coeff 0 = 1) :
    X^a ∣ C-L*lowerPart C L a := by
  have hx : X ∣ (1-L) := X_dvd_iff.mpr (by simp [hL])
  have hp : X^a ∣ (1-L)^a := pow_dvd_pow_of_dvd hx a
  have hg : L * inverseTrunc L a = 1-(1-L)^a := by
    simpa only [inverseTrunc, sub_sub_cancel] using mul_neg_geom_sum (1-L) a
  have he : C-L*(C*inverseTrunc L a) = C*(1-L)^a := by
    calc
      _ = C*(1-L*inverseTrunc L a) := by ring
      _ = _ := by rw [hg]; ring
  have hf : C*inverseTrunc L a = lowerPart C L a +
      X^a*((C*inverseTrunc L a) /ₘ (X^a)) := by
    exact (modByMonic_add_div _ (monic_X.pow a)).symm
  have hd : X^a ∣ C-L*(C*inverseTrunc L a) := by
    rw [he]
    exact dvd_mul_of_dvd_right hp C
  have hadd : X^a ∣ L*(X^a*((C*inverseTrunc L a) /ₘ (X^a))) := by
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) L
  convert dvd_add hd hadd using 1
  linear_combination L * hf

theorem lowerPart_degree (C L : ℝ[X]) (a : ℕ) (ha : 0<a) :
    (lowerPart C L a).natDegree < a := by
  have hn : (X^a : ℝ[X]) ≠ 1 := by
    intro h
    have hh := congrArg Polynomial.natDegree h
    simp at hh
    omega
  simpa [lowerPart] using natDegree_modByMonic_lt (C*inverseTrunc L a) (monic_X.pow a) hn

/-- Constructive lower-axis elimination followed by monic quadratic division. -/
theorem exists_axial_decomposition (C L : ℝ[X]) (a q : ℕ) (γ β : ℝ)
    (ha : 0<a) (hq : 0<q) (hL : L.coeff 0 = 1) (hLd : L.natDegree ≤ 2)
    (hC : C.natDegree < a+q+2) :
    ∃ D V S : ℝ[X], D.natDegree < a ∧ V.natDegree < 2 ∧ S.natDegree < q ∧
      C = L*D + X^a*(V+((X-Polynomial.C γ)*(X-Polynomial.C β))*S) := by
  let D := lowerPart C L a
  let F := C-L*D
  let W := F /ₘ (X^a)
  let U : ℝ[X] := (X-Polynomial.C γ)*(X-Polynomial.C β)
  have hDm : D.natDegree < a := lowerPart_degree C L a ha
  have hFm : F.natDegree < a+q+2 := by
    have hm : (L*D).natDegree ≤ L.natDegree+D.natDegree := natDegree_mul_le
    have hs := natDegree_sub_le C (L*D)
    dsimp [F]
    omega
  have hWm : W.natDegree < q+2 := by
    dsimp [W]
    rw [natDegree_divByMonic _ (monic_X.pow a)]
    simp only [natDegree_X_pow]
    omega
  have hUm : U.Monic := (monic_X_sub_C γ).mul (monic_X_sub_C β)
  have hUd : U.natDegree = 2 := by
    dsimp [U]
    rw [natDegree_mul (monic_X_sub_C γ).ne_zero (monic_X_sub_C β).ne_zero]
    simp
  have hUn : U ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [hUd] at this
  have hVm : (W%ₘU).natDegree < 2 := by
    simpa only [hUd] using natDegree_modByMonic_lt W hUm hUn
  have hSm : (W/ₘU).natDegree < q := by
    rw [natDegree_divByMonic W hUm, hUd]
    omega
  have hFW : F = X^a*W := by
    have hd := lowerPart_divisible C L a hL
    have hz : F%ₘ(X^a) = 0 := (modByMonic_eq_zero_iff_dvd (monic_X.pow a)).mpr hd
    have hh := modByMonic_add_div F (monic_X.pow a)
    rw [hz, zero_add] at hh
    exact hh.symm
  refine ⟨D,W%ₘU,W/ₘU,hDm,hVm,hSm,?_⟩
  rw [modByMonic_add_div W hUm, ← hFW]
  dsimp [F]
  ring

theorem affine_of_natDegree_lt_two (V : ℝ[X]) (hV : V.natDegree < 2) :
    V = Polynomial.C (V.coeff 0) + Polynomial.C (V.coeff 1)*X := by
  ext n
  by_cases h0 : n=0
  · subst n; simp
  by_cases h1 : n=1
  · subst n; simp
  have hz : V.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_add, coeff_C_mul, coeff_C, coeff_X, h0, h1, Ne.symm h1, hz]

theorem exists_axial_affine_decomposition (C L : ℝ[X]) (a q : ℕ) (γ β : ℝ)
    (ha : 0<a) (hq : 0<q) (hL : L.coeff 0 = 1) (hLd : L.natDegree ≤ 2)
    (hC : C.natDegree < a+q+2) :
    ∃ (D S : ℝ[X]) (v₀ v₁ : ℝ), D.natDegree < a ∧ S.natDegree < q ∧
      C = L*D + X^a*(Polynomial.C v₀+Polynomial.C v₁*X+
        ((X-Polynomial.C γ)*(X-Polynomial.C β))*S) := by
  obtain ⟨D,V,S,hD,hV,hS,h⟩ := exists_axial_decomposition C L a q γ β ha hq hL hLd hC
  refine ⟨D,S,V.coeff 0,V.coeff 1,hD,hS,?_⟩
  rw [affine_of_natDegree_lt_two V hV] at h
  exact h

end Atiyah.SingularDivision
