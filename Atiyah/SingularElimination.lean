import Mathlib

/-!
# The algebraic core of axial elimination

Formal-English ledger:
* SE1: In coordinates ordered lower axes, two residual coordinates, upper axes,
  a matrix fixing the axial coordinates has determinant equal to its central
  two by two block. The residual rows may have arbitrary axial coordinates.
* SE2: Multiplication by a coefficient basis of determinant one preserves that
  determinant. This is conditional on the explicitly supplied basis identity;
  the polynomial construction of that basis is a separate obligation.
* SE3: Evaluation of two affine polynomials at distinct gamma,beta multiplies
  their coefficient determinant by beta-gamma.
* SE4: Adding a multiple of (X-gamma)(X-beta) preserves these evaluations.
* SE5: The actual polynomial axial basis has determinant one: its lower
  coefficient block is upper triangular with diagonal one, and its upper
  coefficient block is lower triangular with diagonal one.
* SE6: Finite coefficient reconstruction identifies explicitly decomposed ring
  rows with the coordinate matrix times this basis matrix.
* SE7: Monic quadratic division converts a lower-axis residual W of degree
  below q+2 to the affine residual. Consequently the full boundary determinant
  times beta-gamma is the residual evaluation numerator. For gamma<beta a
  negative numerator gives a negative full coefficient determinant.

These are checked algebraic components, not yet the coefficient-matrix theorem
for the 84-point geometric boundary.
-/
namespace Atiyah.SingularElimination
open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- Coordinates of two arbitrary rows among fixed lower and upper axial rows. -/
def eliminationCoordinates (p q : ℕ)
    (D : Matrix (Fin 2 ⊕ Fin q) (Fin p) R)
    (V : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin 2) (Fin q) R) :
    Matrix (Fin p ⊕ (Fin 2 ⊕ Fin q)) (Fin p ⊕ (Fin 2 ⊕ Fin q)) R :=
  Matrix.fromBlocks 1 0 D (Matrix.fromBlocks V S 0 1)

/-- SE1: axial-coordinate elimination, with no restrictions on the coefficients. -/
theorem det_eliminationCoordinates (p q : ℕ)
    (D : Matrix (Fin 2 ⊕ Fin q) (Fin p) R)
    (V : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin 2) (Fin q) R) :
    (eliminationCoordinates p q D V S).det = V.det := by
  simp [eliminationCoordinates, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁]

/-- SE2: the coefficient determinant after a determinant-one basis change. -/
theorem det_elimination_mul_basis (p q : ℕ)
    (D : Matrix (Fin 2 ⊕ Fin q) (Fin p) R)
    (V : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin 2) (Fin q) R)
    (B : Matrix (Fin p ⊕ (Fin 2 ⊕ Fin q)) (Fin p ⊕ (Fin 2 ⊕ Fin q)) R)
    (hB : B.det = 1) :
    (eliminationCoordinates p q D V S * B).det = V.det := by
  rw [Matrix.det_mul, det_eliminationCoordinates, hB, mul_one]

/-- SE3: evaluation at two points, in ascending monomial order. -/
theorem affine_evaluation_determinant (a₀ a₁ b₀ b₁ γ β : R) :
    (a₀ + a₁ * γ) * (b₀ + b₁ * β) -
      (a₀ + a₁ * β) * (b₀ + b₁ * γ) =
      (β - γ) * (a₀ * b₁ - a₁ * b₀) := by ring

/-- SE4: quotient multiples vanish at each of the two evaluation points. -/
theorem eval_quadratic_remainder (W S : R[X]) (a₀ a₁ γ β : R)
    (hW : W = C a₀ + C a₁ * X + ((X - C γ) * (X - C β)) * S) :
    W.eval γ = a₀ + a₁ * γ ∧ W.eval β = a₀ + a₁ * β := by
  rw [hW]
  simp

/-- Evaluation formula for any two explicitly decomposed quadratic remainders. -/
theorem remainder_evaluation_determinant (WA WB SA SB : R[X])
    (a₀ a₁ b₀ b₁ γ β : R)
    (hA : WA = C a₀ + C a₁ * X + ((X - C γ) * (X - C β)) * SA)
    (hB : WB = C b₀ + C b₁ * X + ((X - C γ) * (X - C β)) * SB) :
    WA.eval γ * WB.eval β - WA.eval β * WB.eval γ =
      (β - γ) * (a₀ * b₁ - a₁ * b₀) := by
  obtain ⟨hAγ, hAβ⟩ := eval_quadratic_remainder WA SA a₀ a₁ γ β hA
  obtain ⟨hBγ, hBβ⟩ := eval_quadratic_remainder WB SB b₀ b₁ γ β hB
  rw [hAγ, hAβ, hBγ, hBβ]
  exact affine_evaluation_determinant a₀ a₁ b₀ b₁ γ β

/-- The negative numerator yields a negative central determinant when gamma < beta. -/
theorem affine_determinant_neg_of_evaluations
    (a₀ a₁ b₀ b₁ γ β : ℝ) (hγβ : γ < β)
    (hneg : (a₀ + a₁ * γ) * (b₀ + b₁ * β) -
      (a₀ + a₁ * β) * (b₀ + b₁ * γ) < 0) :
    a₀ * b₁ - a₁ * b₀ < 0 := by
  rw [affine_evaluation_determinant] at hneg
  have hpos : 0 < β - γ := sub_pos.mpr hγβ
  nlinarith

/-- SE5: the mixed upper/lower triangular basis has determinant one.
The off-diagonal blocks record the quadratic overlap into the central degrees. -/
theorem det_axial_basis_blocks (p q : ℕ)
    (L : Matrix (Fin p) (Fin p) R) (U : Matrix (Fin q) (Fin q) R)
    (C : Matrix (Fin p) (Fin 2 ⊕ Fin q) R)
    (E : Matrix (Fin q) (Fin 2) R)
    (hL : L.BlockTriangular id) (hU : U.BlockTriangular OrderDual.toDual)
    (hLd : ∀ i, L i i = 1) (hUd : ∀ i, U i i = 1) :
    (Matrix.fromBlocks L C 0 (Matrix.fromBlocks 1 0 E U)).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, one_mul, Matrix.det_of_upperTriangular hL,
    Matrix.det_of_lowerTriangular U hU]
  simp [hLd, hUd]

/-- Low-degree coefficient block of the lower axial rows. -/
noncomputable def lowerCoefficientBlock (p : ℕ) (L : Fin p → R[X]) : Matrix (Fin p) (Fin p) R :=
  fun i j => (X ^ i.val * L i).coeff j.val

 theorem lowerCoefficientBlock_triangular (p : ℕ) (L : Fin p → R[X]) :
    (lowerCoefficientBlock p L).BlockTriangular id := by
  intro i j hij
  simp only [lowerCoefficientBlock, coeff_X_pow_mul']
  rw [if_neg]
  exact Nat.not_le.mpr hij

 theorem lowerCoefficientBlock_diagonal (p : ℕ) (L : Fin p → R[X])
    (h : ∀ i, (L i).coeff 0 = 1) (i : Fin p) :
    lowerCoefficientBlock p L i i = 1 := by
  simpa [lowerCoefficientBlock, coeff_X_pow_mul'] using h i

/-- High-degree coefficient block of the upper axial rows. -/
noncomputable def upperCoefficientBlock (q : ℕ) (U : Fin q → R[X]) : Matrix (Fin q) (Fin q) R :=
  fun i j => (X ^ i.val * U i).coeff (j.val + 2)

 theorem upperCoefficientBlock_triangular (q : ℕ) (U : Fin q → R[X])
    (h : ∀ i k, 2 < k → (U i).coeff k = 0) :
    (upperCoefficientBlock q U).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  simp only [upperCoefficientBlock, coeff_X_pow_mul']
  split_ifs with hij'
  · exact h i _ (by omega)
  · rfl

 theorem upperCoefficientBlock_diagonal (q : ℕ) (U : Fin q → R[X])
    (h : ∀ i, (U i).coeff 2 = 1) (i : Fin q) :
    upperCoefficientBlock q U i i = 1 := by
  simp only [upperCoefficientBlock, coeff_X_pow_mul']
  rw [if_pos (by omega), show i.val + 2 - i.val = 2 by omega]
  exact h i

/-- The polynomial axial basis blocks have determinant one. -/
theorem det_polynomial_axial_basis_blocks (p q : ℕ)
    (L : Fin p → R[X]) (U : Fin q → R[X])
    (C : Matrix (Fin p) (Fin 2 ⊕ Fin q) R)
    (E : Matrix (Fin q) (Fin 2) R)
    (hL : ∀ i, (L i).coeff 0 = 1)
    (hU₂ : ∀ i, (U i).coeff 2 = 1)
    (hU : ∀ i k, 2 < k → (U i).coeff k = 0) :
    (Matrix.fromBlocks (lowerCoefficientBlock p L) C 0
      (Matrix.fromBlocks 1 0 E (upperCoefficientBlock q U))).det = 1 := by
  exact det_axial_basis_blocks p q _ _ C E
    (lowerCoefficientBlock_triangular p L) (upperCoefficientBlock_triangular q U hU)
    (lowerCoefficientBlock_diagonal p L hL) (upperCoefficientBlock_diagonal q U hU₂)

def degreeIndex (p q : ℕ) : Fin p ⊕ (Fin 2 ⊕ Fin q) → ℕ
  | .inl i => i.val
  | .inr (.inl i) => p + i.val
  | .inr (.inr i) => p + 2 + i.val

noncomputable def axialBasisRow (p q : ℕ) (L : Fin p → R[X]) (U : Fin q → R[X]) :
    Fin p ⊕ (Fin 2 ⊕ Fin q) → R[X]
  | .inl i => X ^ i.val * L i
  | .inr (.inl i) => X ^ (p + i.val)
  | .inr (.inr i) => X ^ (p + i.val) * U i

noncomputable def axialBasisMatrix (p q : ℕ) (L : Fin p → R[X]) (U : Fin q → R[X]) :
    Matrix (Fin p ⊕ (Fin 2 ⊕ Fin q)) (Fin p ⊕ (Fin 2 ⊕ Fin q)) R :=
  fun i j => (axialBasisRow p q L U i).coeff (degreeIndex p q j)

 theorem axialBasisMatrix_blocks (p q : ℕ) (L : Fin p → R[X]) (U : Fin q → R[X]) :
    axialBasisMatrix p q L U = Matrix.fromBlocks (lowerCoefficientBlock p L)
      (fun i j => (X^i.val * L i).coeff (degreeIndex p q (.inr j))) 0
      (Matrix.fromBlocks 1 0 (fun i j => (X^i.val * U i).coeff j.val)
        (upperCoefficientBlock q U)) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · rfl
  · rfl
  · rfl
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, coeff_X_pow]
    rw [if_neg (by omega)]
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₂,
      Matrix.fromBlocks_apply₁₁, coeff_X_pow, Matrix.one_apply]
    congr 1
    simp [Fin.ext_iff, eq_comm]
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₂,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, coeff_X_pow]
    rw [if_neg (by omega)]
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, coeff_X_pow_mul']
    rw [if_neg (by omega)]
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₂,
      Matrix.fromBlocks_apply₂₁, coeff_X_pow_mul']
    simp only [Nat.add_le_add_iff_left, Nat.add_sub_add_left]
  · simp only [axialBasisMatrix, axialBasisRow, degreeIndex, Matrix.fromBlocks_apply₂₂,
      upperCoefficientBlock, coeff_X_pow_mul']
    rw [show p + 2 + j.val = p + (j.val + 2) by omega]
    simp only [Nat.add_le_add_iff_left, Nat.add_sub_add_left]
/-- The actual coefficient matrix of the ordered polynomial axial basis is unimodular. -/
theorem det_axialBasisMatrix (p q : ℕ) (L : Fin p → R[X]) (U : Fin q → R[X])
    (hL : ∀ i, (L i).coeff 0 = 1) (hU₂ : ∀ i, (U i).coeff 2 = 1)
    (hU : ∀ i k, 2 < k → (U i).coeff k = 0) :
    (axialBasisMatrix p q L U).det = 1 := by
  rw [axialBasisMatrix_blocks]
  exact det_polynomial_axial_basis_blocks p q L U _ _ hL hU₂ hU

/-- Finite coefficient reconstruction, including the zero polynomial. -/
theorem polynomial_eq_sum_fin (n : ℕ) (P : R[X]) (hP : P.degree < n) :
    (∑ i : Fin n, C (P.coeff i.val) * X ^ i.val) = P := by
  rw [Polynomial.sum_fin (fun i c => C c * X ^ i) (by simp) hP,
    Polynomial.sum_C_mul_X_pow_eq]

/-- Coordinates of an explicitly decomposed row in the axial basis. -/
def decompositionCoordinates (p q : ℕ) (D V S : R[X]) :
    Fin p ⊕ (Fin 2 ⊕ Fin q) → R
  | .inl i => D.coeff i.val
  | .inr (.inl i) => V.coeff i.val
  | .inr (.inr i) => S.coeff i.val

 theorem decomposition_as_basis_sum (p q : ℕ) (L U D V S : R[X])
    (hD : D.degree < p) (hV : V.degree < 2) (hS : S.degree < q) :
    (∑ i, C (decompositionCoordinates p q D V S i) *
      axialBasisRow p q (fun _ => L) (fun _ => U) i) =
      L * D + X ^ p * (V + U * S) := by
  simp only [Fintype.sum_sum_type, decompositionCoordinates, axialBasisRow]
  have hlo : (∑ i : Fin p, C (D.coeff i.val) * (X^i.val * L)) = D * L := by
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [polynomial_eq_sum_fin p D hD]
  have hmid : (∑ i : Fin 2, C (V.coeff i.val) * X^(p+i.val)) = V * X^p := by
    simp_rw [pow_add]
    conv_lhs => arg 2; ext i; rw [mul_comm (X^p), ← mul_assoc]
    rw [← Finset.sum_mul, polynomial_eq_sum_fin 2 V hV]
  have hup : (∑ i : Fin q, C (S.coeff i.val) * (X^(p+i.val) * U)) = S * (X^p * U) := by
    have heq : ∀ i : Fin q, C (S.coeff i.val) * (X^(p+i.val) * U) =
        (C (S.coeff i.val) * X^i.val) * (X^p * U) := by
      intro i; rw [pow_add]; ring
    simp_rw [heq, ← Finset.sum_mul]
    rw [polynomial_eq_sum_fin q S hS]
  rw [hlo, hmid, hup]
  ring

noncomputable def boundaryCoordinates (p q : ℕ) (D V S : Fin 2 → R[X]) :=
  eliminationCoordinates p q
    (Sum.elim (fun r j => (D r).coeff j.val) (fun _ _ => 0))
    (fun r j => (V r).coeff j.val) (fun r j => (S r).coeff j.val)

noncomputable def boundaryRow (p q : ℕ) (L U : R[X]) (A : Fin 2 → R[X]) :
    Fin p ⊕ (Fin 2 ⊕ Fin q) → R[X]
  | .inl i => X^i.val * L
  | .inr (.inl i) => A i
  | .inr (.inr i) => X^(p+i.val) * U

noncomputable def boundaryMatrix (p q : ℕ) (L U : R[X]) (A : Fin 2 → R[X]) :
    Matrix (Fin p ⊕ (Fin 2 ⊕ Fin q)) (Fin p ⊕ (Fin 2 ⊕ Fin q)) R :=
  fun i j => (boundaryRow p q L U A i).coeff (degreeIndex p q j)

 theorem boundary_row_decomposition (p q : ℕ) (L U : R[X]) (A D V S : Fin 2 → R[X])
    (hD : ∀ r, (D r).degree < p) (hV : ∀ r, (V r).degree < 2)
    (hS : ∀ r, (S r).degree < q)
    (hA : ∀ r, A r = L * D r + X^p * (V r + U * S r))
    (i : Fin p ⊕ (Fin 2 ⊕ Fin q)) :
    (∑ j, C (boundaryCoordinates p q D V S i j) *
      axialBasisRow p q (fun _ => L) (fun _ => U) j) = boundaryRow p q L U A i := by
  rcases i with i | (i | i)
  · simp [boundaryCoordinates, eliminationCoordinates, Fintype.sum_sum_type,
      axialBasisRow, boundaryRow, Matrix.one_apply, Matrix.fromBlocks]
  · have hc : ∀ j, boundaryCoordinates p q D V S (Sum.inr (Sum.inl i)) j =
        decompositionCoordinates p q (D i) (V i) (S i) j := by
      intro j
      rcases j with j | (j | j) <;> rfl
    simp_rw [hc]
    change (∑ j, C (decompositionCoordinates p q (D i) (V i) (S i) j) *
      axialBasisRow p q (fun _ => L) (fun _ => U) j) = A i
    rw [decomposition_as_basis_sum p q L U (D i) (V i) (S i) (hD i) (hV i) (hS i), hA i]
  · simp [boundaryCoordinates, eliminationCoordinates, Fintype.sum_sum_type,
      axialBasisRow, boundaryRow, Matrix.one_apply, Matrix.fromBlocks]

 theorem boundaryMatrix_eq_product (p q : ℕ) (L U : R[X]) (A D V S : Fin 2 → R[X])
    (hD : ∀ r, (D r).degree < p) (hV : ∀ r, (V r).degree < 2)
    (hS : ∀ r, (S r).degree < q)
    (hA : ∀ r, A r = L * D r + X^p * (V r + U * S r)) :
    boundaryMatrix p q L U A = boundaryCoordinates p q D V S *
      axialBasisMatrix p q (fun _ => L) (fun _ => U) := by
  ext i j
  simp only [boundaryMatrix, Matrix.mul_apply, axialBasisMatrix]
  rw [← boundary_row_decomposition p q L U A D V S hD hV hS hA i]
  simp only [finset_sum_coeff, coeff_C_mul]

/-- Full coefficient determinant reduction for explicitly decomposed ring rows. -/
theorem det_boundaryMatrix (p q : ℕ) (L U : R[X]) (A D V S : Fin 2 → R[X])
    (hL : L.coeff 0 = 1) (hU₂ : U.coeff 2 = 1)
    (hU : ∀ k, 2 < k → U.coeff k = 0)
    (hD : ∀ r, (D r).degree < p) (hV : ∀ r, (V r).degree < 2)
    (hS : ∀ r, (S r).degree < q)
    (hA : ∀ r, A r = L * D r + X^p * (V r + U * S r)) :
    (boundaryMatrix p q L U A).det =
      (V 0).coeff 0 * (V 1).coeff 1 - (V 0).coeff 1 * (V 1).coeff 0 := by
  rw [boundaryMatrix_eq_product p q L U A D V S hD hV hS hA,
    Matrix.det_mul, det_axialBasisMatrix p q _ _ (fun _ => hL) (fun _ => hU₂)
      (fun _ => hU), mul_one]
  rw [boundaryCoordinates, det_eliminationCoordinates, Matrix.det_fin_two]
  norm_num

theorem affine_of_degree_lt_two (V : R[X]) (hV : V.degree < 2) :
    V = C (V.coeff 0) + C (V.coeff 1) * X := by
  rw [← polynomial_eq_sum_fin 2 V hV]
  simp [Fin.sum_univ_two]

 theorem quadratic_coeff_two (γ β : R) :
    ((X - C γ) * (X - C β)).coeff 2 = 1 := by
  have he : (X - C γ) * (X - C β) = X^2 - C (γ+β)*X + C (γ*β) := by
    simp only [map_add, map_mul]; ring
  rw [he]
  simp

 theorem quadratic_coeff_above (γ β : R) (k : ℕ) (hk : 2 < k) :
    ((X - C γ) * (X - C β)).coeff k = 0 := by
  have he : (X - C γ) * (X - C β) = X^2 - C (γ+β)*X + C (γ*β) := by
    simp only [map_add, map_mul]; ring
  rw [he, coeff_add, coeff_sub, coeff_C_mul]
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C,
    show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega,
    show 1 ≠ k by omega, show 2 ≠ k by omega]

/-- The exact numerator identity, with the residual polynomial supplied explicitly. -/
theorem det_boundaryMatrix_evaluation_identity (p q : ℕ) (L : R[X]) (γ β : R)
    (A D V S W : Fin 2 → R[X])
    (hL : L.coeff 0 = 1) (hD : ∀ r, (D r).degree < p)
    (hV : ∀ r, (V r).degree < 2) (hS : ∀ r, (S r).degree < q)
    (hA : ∀ r, A r = L * D r + X^p * W r)
    (hW : ∀ r, W r = V r + ((X-C γ)*(X-C β))*S r) :
    (W 0).eval γ * (W 1).eval β - (W 0).eval β * (W 1).eval γ =
      (β-γ) * (boundaryMatrix p q L ((X-C γ)*(X-C β)) A).det := by
  rw [det_boundaryMatrix p q L ((X-C γ)*(X-C β)) A D V S hL
    (quadratic_coeff_two γ β) (quadratic_coeff_above γ β) hD hV hS
    (fun r => by rw [hA r, hW r])]
  apply remainder_evaluation_determinant (W 0) (W 1) (S 0) (S 1)
  · rw [hW 0, affine_of_degree_lt_two (V 0) (hV 0)]
    simp
  · rw [hW 1, affine_of_degree_lt_two (V 1) (hV 1)]
    simp

 theorem quadratic_division (W : ℝ[X]) (q : ℕ) (hq : 0 < q) (γ β : ℝ)
    (hW : W.natDegree < q+2) :
    ∃ V S : ℝ[X], V.degree < 2 ∧ S.degree < q ∧
      W = V + ((X-C γ)*(X-C β))*S := by
  let U : ℝ[X] := (X-C γ)*(X-C β)
  have hm : U.Monic := (monic_X_sub_C γ).mul (monic_X_sub_C β)
  have hd : U.natDegree = 2 := by
    dsimp [U]
    rw [natDegree_mul (monic_X_sub_C γ).ne_zero (monic_X_sub_C β).ne_zero]
    simp
  have hn : U ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [hd] at this
  have hv : (W %ₘ U).natDegree < 2 := by
    simpa only [hd] using natDegree_modByMonic_lt W hm hn
  have hs : (W /ₘ U).natDegree < q := by
    rw [natDegree_divByMonic W hm, hd]
    omega
  refine ⟨W%ₘU,W/ₘU,?_,?_,(modByMonic_add_div W hm).symm⟩
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast hv)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast hs)

/-- Axial elimination formula requiring only a lower-axis polynomial decomposition. -/
theorem det_boundaryMatrix_from_lower_elimination (p q : ℕ) (L : ℝ[X]) (γ β : ℝ)
    (A D W : Fin 2 → ℝ[X]) (hq : 0 < q)
    (hL : L.coeff 0 = 1) (hD : ∀ r, (D r).degree < p)
    (hWdeg : ∀ r, (W r).natDegree < q+2)
    (hA : ∀ r, A r = L * D r + X^p * W r) :
    (W 0).eval γ * (W 1).eval β - (W 0).eval β * (W 1).eval γ =
      (β-γ) * (boundaryMatrix p q L ((X-C γ)*(X-C β)) A).det := by
  choose V S hV hS hW using fun r => quadratic_division (W r) q hq γ β (hWdeg r)
  exact det_boundaryMatrix_evaluation_identity p q L γ β A D V S W hL hD hV hS hA hW

/-- Strict sign transfer from the two residual evaluations to the full determinant. -/
theorem det_boundaryMatrix_neg (p q : ℕ) (L : ℝ[X]) (γ β : ℝ)
    (A D W : Fin 2 → ℝ[X]) (hq : 0 < q) (hγβ : γ < β)
    (hL : L.coeff 0 = 1) (hD : ∀ r, (D r).degree < p)
    (hWdeg : ∀ r, (W r).natDegree < q+2)
    (hA : ∀ r, A r = L * D r + X^p * W r)
    (hneg : (W 0).eval γ * (W 1).eval β - (W 0).eval β * (W 1).eval γ < 0) :
    (boundaryMatrix p q L ((X-C γ)*(X-C β)) A).det < 0 := by
  rw [det_boundaryMatrix_from_lower_elimination p q L γ β A D W hq hL hD hWdeg hA] at hneg
  have hp : 0 < β-γ := sub_pos.mpr hγβ
  nlinarith

end Atiyah.SingularElimination
