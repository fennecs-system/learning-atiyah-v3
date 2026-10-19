import Atiyah.SingularFactorLemmas
set_option maxRecDepth 2000

/-!
SGR1: Partition the 84 edges into 52 lower, two ring, and 30 upper indices.
SGR2: Collinear factors contribute X exactly at earlier indices, yielding
X^j or X^(52+j). The remaining factors are the explicit four row formulas.
SGR3: The full indexed family is the complex scalar extension of SingularRows.row.
-/
noncomputable section
namespace Atiyah.SingularRowBridge
open Polynomial SingularPathFactors

lemma paperRow_blocks (t : ℝ) (i : Fin 84) :
    paperRow t i = (∏ j : Fin 52, factor t i (lowerIdx j)) *
      factor t i 52 * factor t i 53 * (∏ j : Fin 30, factor t i (upperIdx j)) := by
  rw [paperRow_eq, prod_blocks]
  rfl

lemma paperRow_lower (t : ℝ) (i : Fin 52) :
    paperRow t (lowerIdx i) =
      (SingularRows.lower i.val (SingularRows.alpha i t) (SingularRows.chi i t)).map
        Complex.ofRealHom := by
  rw [paperRow_blocks]
  simp only [factor_lower_lower, factor_lower_A, factor_lower_B, factor_lower_upper,
    Finset.prod_const_one, mul_one, prod_before]
  simp [SingularRows.lower, mul_assoc]

lemma paperRow_A (t : ℝ) :
    paperRow t 52 =
      (SingularRows.ringA (fun j => SingularRows.alpha j t)
        (fun j => SingularRows.gamma j t) (SingularRows.tau t)).map Complex.ofRealHom := by
  rw [paperRow_blocks]
  simp only [factor_A_lower, factor_self, factor_A_B, factor_A_upper, mul_one]
  simp only [SingularRows.ringA, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one, Complex.ofRealHom_eq_coe]
  ring

lemma paperRow_B (t : ℝ) :
    paperRow t 53 =
      (SingularRows.ringB (fun j => SingularRows.chi j t)
        (fun j => SingularRows.beta j t) (SingularRows.tau t)).map Complex.ofRealHom := by
  rw [paperRow_blocks]
  simp only [factor_B_lower, factor_B_A, factor_self, factor_B_upper, mul_one]
  simp only [SingularRows.ringB, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one, Complex.ofRealHom_eq_coe]
  ring

lemma paperRow_upper (t : ℝ) (i : Fin 30) :
    paperRow t (upperIdx i) =
      (SingularRows.upper 52 i.val (SingularRows.gamma i t) (SingularRows.beta i t)).map
        Complex.ofRealHom := by
  rw [paperRow_blocks]
  simp only [factor_upper_lower, factor_upper_A, factor_upper_B, factor_upper_upper,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, prod_before]
  simp [SingularRows.upper, pow_add, mul_comm, mul_left_comm, mul_assoc]

lemma paperRow_eq_map_row (t : ℝ) (i : Fin 84) :
    paperRow t i =
      (SingularRows.row (fun j => SingularRows.alpha j t) (fun j => SingularRows.chi j t)
        (fun j => SingularRows.gamma j t) (fun j => SingularRows.beta j t)
        (SingularRows.tau t) i).map Complex.ofRealHom := by
  unfold SingularRows.row
  split_ifs with h hA hB
  · have he : i = lowerIdx ⟨i.val, h⟩ := by rfl
    exact paperRow_lower t ⟨i.val,h⟩
  · have he : i = 52 := Fin.ext hA
    subst i
    exact paperRow_A t
  · have he : i = 53 := Fin.ext hB
    subst i
    exact paperRow_B t
  · have hi : i.val - 52 - 2 < 30 := by omega
    have he : i = upperIdx ⟨i.val-52-2,hi⟩ := by
      apply Fin.ext
      dsimp [upperIdx]
      omega
    exact (congrArg (paperRow t) he).trans (paperRow_upper t ⟨i.val-52-2,hi⟩)

end Atiyah.SingularRowBridge
