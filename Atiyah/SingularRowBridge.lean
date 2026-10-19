import Atiyah.SingularPathFactors
import Atiyah.HomogeneousBridge

/-!
SRB1: Substituting -X in each dehomogenized form is an invertible linear
operation. SRB2: Each reversed edge contributes a constant minus sign;
thus row i contributes (-1)^i. SRB3: Grouping edges by the lower, two
ring, and upper groups gives the explicit SingularRows polynomials.
-/
noncomputable section
namespace Atiyah.SingularRowBridge
open Configuration HomogeneousBridge Polynomial SingularGeometry SingularPathFactors

def reflect : ℂ[X] →ₐ[ℂ] ℂ[X] := Polynomial.aeval (-Polynomial.X)

@[simp] theorem reflect_apply (p : ℂ[X]) : reflect p = p.comp (-X) := by
  rfl

@[simp] theorem reflect_reflect (p : ℂ[X]) : reflect (reflect p) = p := by
  simp only [reflect_apply, Polynomial.comp_neg_X_comp_neg_X]

theorem linearIndependent_reflect_iff {ι : Type*} (p : ι → ℂ[X]) :
    LinearIndependent ℂ (fun i => reflect (p i)) ↔ LinearIndependent ℂ p := by
  constructor
  · exact LinearIndependent.of_comp reflect.toLinearMap
  · intro h
    apply LinearIndependent.of_comp reflect.toLinearMap
    change LinearIndependent ℂ (fun i => reflect (reflect (p i)))
    simpa only [reflect_reflect] using h

def paperEdge (t : ℝ) (i j : Fin 84) : ℂ[X] :=
  if i < j then 1 - C (slope ((path t j).1-(path t i).1)
    ((path t j).2-(path t i).2) : ℂ) * X
  else X + C (slope ((path t i).1-(path t j).1)
    ((path t i).2-(path t j).2) : ℂ)

theorem reflect_dehom_edge (t : ℝ) (i j : Fin 84) :
    reflect (dehom (linearForm (normalizedSpinor t i j))) =
      (if i < j then 1 else -1) * paperEdge t i j := by
  unfold normalizedSpinor paperEdge
  split_ifs <;> simp [dehom_linearForm, reflect, map_add, map_mul] <;> ring

def paperRow (t : ℝ) (i : Fin 84) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, paperEdge t i j

def rowSign (i : Fin 84) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, if i < j then 1 else -1

theorem rowSign_ne_zero (i : Fin 84) : rowSign i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs <;> norm_num

theorem reflect_dehom_normalized (t : ℝ) (i : Fin 84) :
    reflect (dehom (normalizedPointForm t i)) = rowSign i • paperRow t i := by
  classical
  simp only [normalizedPointForm, map_prod, reflect_dehom_edge,
    Finset.prod_mul_distrib, paperRow, rowSign, Polynomial.smul_eq_C_mul,
    map_prod, apply_ite, map_one, map_neg]

theorem normalized_homogeneous (t : ℝ) (i : Fin 84) :
    (normalizedPointForm t i).IsHomogeneous 83 := by
  classical
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i)
    (fun j => linearForm (normalizedSpinor t i j)) (fun _ => 1)
    (fun j _ => linearForm_homogeneous (normalizedSpinor t i j))
  simpa [normalizedPointForm] using h

theorem independent_iff_paperRow (t : ℝ) :
    LinearIndependent ℂ (normalizedPointForm t) ↔ LinearIndependent ℂ (paperRow t) := by
  rw [← linearIndependent_dehom_iff _ (normalized_homogeneous t)]
  rw [← linearIndependent_reflect_iff]
  simp_rw [reflect_dehom_normalized]
  exact Configuration.linearIndependent_smul_iff _ _ rowSign_ne_zero

theorem prod_blocks {M : Type*} [CommMonoid M] (f : Fin 84 → M) :
    (∏ i, f i) = (∏ j : Fin 52, f ⟨j.val, by omega⟩) *
      f 52 * f 53 * (∏ j : Fin 30, f ⟨54+j.val, by omega⟩) := by
  rw [show (∏ i, f i) = (∏ j : Fin 52, f (Fin.castAdd 32 j)) *
    ∏ j : Fin 32, f (Fin.natAdd 52 j) from Fin.prod_univ_add (a := 52) (b := 32) f]
  conv_lhs => rhs; rw [Fin.prod_univ_succ]; rhs; rw [Fin.prod_univ_succ]
  simp only [Fin.natAdd, Fin.castAdd, Fin.val_zero, Fin.val_succ]
  simp only [mul_assoc]
  congr 3

theorem prod_before {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin n) (x : M) :
    (∏ j : Fin n, if j < k then x else 1) = x ^ k.val := by
  classical
  simp [Finset.prod_ite, Finset.filter_gt_eq_Iio]

def factor (t : ℝ) (i j : Fin 84) : ℂ[X] := if j = i then 1 else paperEdge t i j

lemma paperRow_eq (t : ℝ) (i : Fin 84) : paperRow t i = ∏ j, factor t i j := by
  classical
  unfold paperRow factor
  rw [← Finset.prod_erase _ (f := fun j => if j = i then 1 else paperEdge t i j) (a := i) (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

lemma factor_lower_lower (t : ℝ) (i j : Fin 52) :
    factor t (lowerIdx i) (lowerIdx j) = if j < i then X else 1 := by
  unfold factor paperEdge
  change (if lowerIdx j = lowerIdx i then 1 else
    if lowerIdx i < lowerIdx j then 1 - C (directedSlope t (lowerIdx i) (lowerIdx j) : ℂ) * X
    else X + C (directedSlope t (lowerIdx j) (lowerIdx i) : ℂ)) = _
  have he : lowerIdx j = lowerIdx i ↔ j = i := by simp [lowerIdx, Fin.ext_iff]
  have hl : lowerIdx i < lowerIdx j ↔ i < j := Iff.rfl
  simp only [he, hl, slope_lower_lower, Complex.ofReal_zero, map_zero, zero_mul, sub_zero, add_zero]
  split_ifs <;> simp_all <;> omega

lemma factor_upper_upper (t : ℝ) (i j : Fin 30) :
    factor t (upperIdx i) (upperIdx j) = if j < i then X else 1 := by
  unfold factor paperEdge
  change (if upperIdx j = upperIdx i then 1 else
    if upperIdx i < upperIdx j then 1 - C (directedSlope t (upperIdx i) (upperIdx j) : ℂ) * X
    else X + C (directedSlope t (upperIdx j) (upperIdx i) : ℂ)) = _
  have he : upperIdx j = upperIdx i ↔ j = i := by simp [upperIdx, Fin.ext_iff]
  have hl : upperIdx i < upperIdx j ↔ i < j := by
    change 54+i.val < 54+j.val ↔ i.val < j.val
    omega
  simp only [he, hl, slope_upper_upper, Complex.ofReal_zero, map_zero, zero_mul, sub_zero, add_zero]
  split_ifs <;> simp_all <;> omega

end Atiyah.SingularRowBridge
