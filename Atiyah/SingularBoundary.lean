import Atiyah.SingularEndpoint
import Atiyah.SingularIndex
import Atiyah.SingularCertificateBridge

/-!
SB1: At t=1 the endpoint slope identities identify the lower/upper axial rows
and two nonaxial rows with the constant-slope boundary polynomials.
SB2: Multiplying each nonaxial row by 31 multiplies the determinant by 961.
SB3: The checked coefficient-list recurrence supplies lower-axis decompositions;
the generic determinant theorem transfers the negative certificate numerator
to the complete scaled coefficient determinant since 1-(sqrt 2-1)>0.
SB4: Positive scaling transfers this to pathDet 1 < 0.
All four obligations are discharged below. This file identifies the coefficient
endpoint; interior configurations and their Hopf forms are handled separately.
-/
noncomputable section
set_option maxRecDepth 200
set_option maxHeartbeats 1000000
namespace Atiyah.SingularBoundary
open Polynomial SingularRows SingularEndpoint SingularElimination
set_option Elab.async false
attribute [local irreducible] Matrix.detRowAlternating

abbrev al : ℝ := Real.sqrt 962 - 31
abbrev xx : ℝ := Real.sqrt 2 - 1
abbrev cc : ℝ := Real.sqrt 962 - 1

def L : ℝ[X] := (1 - C al * X) * (1 - C xx * X)
abbrev U : ℝ[X] := (X - C xx) * (X - C 1)
def A : ℝ[X] := (X+C al)^52 * (1+C xx*X)^30 * (C 31-C cc*X)
def B : ℝ[X] := (X+C xx)^52 * (1+X)^30 * (C cc+C 31*X)
def rings : Fin 2 → ℝ[X] := ![A, B]
def unscaledRings : Fin 2 → ℝ[X] :=
  ![ringA (fun _ : Fin 52 => al) (fun _ : Fin 30 => xx) (cc/31),
    ringB (fun _ : Fin 52 => xx) (fun _ : Fin 30 => 1) (cc/31)]

theorem rings_scaled (i : Fin 2) : rings i = C 31 * unscaledRings i := by
  have hc : (C 31 : ℝ[X]) * C (cc/31) = C cc := by
    rw [← map_mul]
    congr 1
    ring
  have ha : (C 31-C cc*X : ℝ[X]) = C 31 * (1-C (cc/31)*X) := by
    rw [mul_sub, mul_one, ← mul_assoc, hc]
  have hb : (C cc+C 31*X : ℝ[X]) = C 31 * (X+C (cc/31)) := by
    rw [mul_add, hc, add_comm]
  fin_cases i
  · change A = C 31 * ringA (fun _ : Fin 52 => al) (fun _ : Fin 30 => xx) (cc/31)
    simp only [A, ringA, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ha]
    ac_rfl
  · change B = C 31 * ringB (fun _ : Fin 52 => xx) (fun _ : Fin 30 => 1) (cc/31)
    simp only [B, ringB, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_one, one_mul]
    rw [hb]
    ac_rfl

theorem endpoint_row (i : SingularIndex.Index) :
    row (fun j => alpha j 1) (fun j => chi j 1) (fun j => gamma j 1)
      (fun j => beta j 1) (tau 1) (SingularIndex.equiv i) =
      boundaryRow 52 30 L U unscaledRings i := by
  simp only [alpha_one, chi_one, gamma_one, beta_one, tau_one,
    slope_31_1, slope_32_32, slope_1_1, slope_1_31]
  rcases i with i | (i | i)
  · simp only [row, SingularIndex.equiv_val, degreeIndex]
    rw [dif_pos i.isLt]
    rfl
  · fin_cases i <;> norm_num [row, SingularIndex.equiv_val, degreeIndex, boundaryRow, unscaledRings]
  · have h : ¬ 52+2+i.val < 52 := by omega
    have h1 : ¬ 52+2+i.val = 52 := by omega
    have h2 : ¬ 52+2+i.val = 52+1 := by omega
    simp only [row, SingularIndex.equiv_val, degreeIndex, dif_neg h, dif_neg h1, dif_neg h2]
    simp only [upper, boundaryRow, U]
    rw [show 52 + 2 + i.val - 52 - 2 = i.val by omega]

theorem endpoint_matrix :
    boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) unscaledRings =
      (pathMatrix 1).submatrix SingularIndex.equiv SingularIndex.equiv := by
  ext i j
  simp only [boundaryMatrix, Matrix.submatrix_apply, pathMatrix, matrix, endpoint_row, SingularIndex.equiv_val]

private theorem det_of_reindex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (h : P = Q.submatrix e e) :
    P.det = Q.det := by
  rw [h]
  exact Matrix.det_submatrix_equiv_self e Q

theorem endpoint_det : (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) unscaledRings).det = pathDet 1 := by
  unfold pathDet
  exact det_of_reindex (m := Fin 52 ⊕ (Fin 2 ⊕ Fin 30)) SingularIndex.equiv (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) unscaledRings) (pathMatrix 1) endpoint_matrix

def rowScale : Fin 52 ⊕ (Fin 2 ⊕ Fin 30) → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 31
  | .inr (.inr _) => 1

theorem scaled_matrix : boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) rings =
    Matrix.diagonal rowScale * boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) unscaledRings := by
  ext i j
  rw [Matrix.diagonal_mul]
  rcases i with i | (i | i)
  · simp [boundaryMatrix, boundaryRow, rowScale]
  · simp [boundaryMatrix, boundaryRow, rowScale, rings_scaled, coeff_C_mul]
  · simp [boundaryMatrix, boundaryRow, rowScale]

private theorem det_diag_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (P Q : Matrix n n ℝ) (h : P = Matrix.diagonal d * Q) :
    P.det = (∏ i, d i) * Q.det := by rw [h, Matrix.det_mul, Matrix.det_diagonal]

theorem scaled_det : (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) rings).det = 961 * pathDet 1 := by
  have h := det_diag_of_eq rowScale (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) rings) (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) unscaledRings) scaled_matrix
  have hp : (∏ i, rowScale i) = 961 := by
    norm_num [rowScale, Fintype.prod_sum_type, Fin.prod_univ_two]
  rw [hp] at h
  exact h.trans (congrArg (fun z => 961*z) endpoint_det)

open SingularCertificate SingularCertificateBridge
attribute [local irreducible] listA listB eliminated ofList numerator

theorem boundary_scaled_negative :
    (boundaryMatrix 52 30 L ((X-C xx)*(X-C (1:ℝ))) rings).det < 0 := by
  let pa := listA al xx cc 31
  let pb := listB al xx cc 31
  let WA := ofList (eliminated pa 52 al xx)
  let WB := ofList (eliminated pb 52 al xx)
  have hpa : pa.length = 84 := length_listA al xx cc 31
  have hpb : pb.length = 84 := length_listB al xx cc 31
  obtain ⟨DA,hDA,hA⟩ := eliminated_decomposition pa 52 al xx (by omega)
  obtain ⟨DB,hDB,hB⟩ := eliminated_decomposition pb 52 al xx (by omega)
  have hAA : A = L*DA + X^52*WA := by
    change ofList (listA al xx cc 31) = _ at hA
    rw [ofList_listA] at hA
    exact hA
  have hBB : B = L*DB + X^52*WB := by
    change ofList (listB al xx cc 31) = _ at hB
    rw [ofList_listB] at hB
    exact hB
  have hneg : WA.eval xx * WB.eval 1 - WA.eval 1 * WB.eval xx < 0 := by
    have h := boundary_numerator_negative
    rw [numerator_eq_list_evaluations] at h
    exact h
  have hd : ∀ r : Fin 2, (![DA, DB] r).degree < (52 : WithBot ℕ) := by
    intro r; fin_cases r <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero] <;> assumption
  have hw : ∀ r : Fin 2, (![WA, WB] r).natDegree < 30+2 := by
    intro r; fin_cases r <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero]
    · exact eliminated_natDegree pa hpa al xx
    · exact eliminated_natDegree pb hpb al xx
  have hab : ∀ r : Fin 2, rings r = L * ![DA, DB] r + X^52 * ![WA, WB] r := by
    intro r; fin_cases r <;> simp only [rings, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero]
    · exact hAA
    · exact hBB
  have horder : xx < 1 := by have h := one_sub_root_pos; dsimp [xx]; linarith only [h]
  have hl : L.coeff 0 = 1 := by simp [L]
  have hn := det_boundaryMatrix_neg 52 30 L xx 1 rings ![DA, DB] ![WA, WB]
    (by norm_num) horder hl hd hw hab
    (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hneg)
  exact hn

/-- The actual collapsed endpoint coefficient determinant is strictly negative. -/
theorem pathDet_one_negative : pathDet 1 < 0 := by
  have h : 961 * pathDet 1 < 0 := lt_of_eq_of_lt scaled_det.symm boundary_scaled_negative
  exact neg_of_mul_neg_right h (by norm_num)

end Atiyah.SingularBoundary
