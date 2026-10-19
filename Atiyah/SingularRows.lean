import Mathlib
set_option maxHeartbeats 100000
set_option maxRecDepth 1000

/-!
SR1: For m=1 the four groups of normalized rows are the products below.
SR2: Coefficientwise continuity is inherited from the five slope families.
SR3: If every slope vanishes at zero, the coefficient matrix is the identity.
These are algebraic statements; identification with geometric lifts is separate.
-/
namespace Atiyah.SingularRows
open Polynomial

noncomputable def lower (j : ℕ) (α x : ℝ) : ℝ[X] :=
  X ^ j * ((1 - C α * X) * (1 - C x * X))
noncomputable def upper (a j : ℕ) (y z : ℝ) : ℝ[X] :=
  X ^ (a+j) * ((X - C y) * (X - C z))
noncomputable def ringA {a b : ℕ} (α : Fin a → ℝ) (y : Fin b → ℝ) (τ : ℝ) : ℝ[X] :=
  (∏ j, (X + C (α j))) * (∏ j, (1 + C (y j) * X)) * (1 - C τ * X)
noncomputable def ringB {a b : ℕ} (x : Fin a → ℝ) (z : Fin b → ℝ) (τ : ℝ) : ℝ[X] :=
  (∏ j, (X + C (x j))) * (∏ j, (1 + C (z j) * X)) * (X + C τ)

noncomputable def row {a b : ℕ} (α x : Fin a → ℝ) (y z : Fin b → ℝ)
    (τ : ℝ) (i : Fin (a+b+2)) : ℝ[X] :=
  if h : i.val < a then lower i.val (α ⟨i.val,h⟩) (x ⟨i.val,h⟩)
  else if h₁ : i.val = a then ringA α y τ
  else if h₂ : i.val = a+1 then ringB x z τ
  else upper a (i.val-a-2) (y ⟨i.val-a-2, by omega⟩) (z ⟨i.val-a-2, by omega⟩)

noncomputable def matrix {a b : ℕ} (α x : Fin a → ℝ) (y z : Fin b → ℝ)
    (τ : ℝ) : Matrix (Fin (a+b+2)) (Fin (a+b+2)) ℝ :=
  fun i k => (row α x y z τ i).coeff k.val

@[simp] theorem lower_zero (j : ℕ) : lower j 0 0 = X^j := by simp [lower]
@[simp] theorem upper_zero (a j : ℕ) : upper a j 0 0 = X^(a+j+2) := by
  simp [upper, pow_add, pow_two, mul_assoc]
@[simp] theorem ringA_zero (a b : ℕ) : ringA (fun _ : Fin a => 0) (fun _ : Fin b => 0) 0 = X^a := by simp [ringA]
@[simp] theorem ringB_zero (a b : ℕ) : ringB (fun _ : Fin a => 0) (fun _ : Fin b => 0) 0 = X^(a+1) := by simp [ringB, pow_succ]

 theorem row_zero (a b : ℕ) (i : Fin (a+b+2)) :
    row (fun _ : Fin a => 0) (fun _ => 0) (fun _ : Fin b => 0) (fun _ => 0) 0 i = X^i.val := by
  unfold row
  split_ifs with h h₁ h₂
  · simp
  · simpa [h₁]
  · simpa [h₂]
  · rw [upper_zero]
    congr 1
    omega

 theorem matrix_zero (a b : ℕ) :
    matrix (fun _ : Fin a => 0) (fun _ => 0) (fun _ : Fin b => 0) (fun _ => 0) 0 = 1 := by
  ext i k
  simp only [matrix, row_zero, Polynomial.coeff_X_pow, Matrix.one_apply]
  congr 1
  exact propext (by simp [Fin.ext_iff, eq_comm])

 theorem det_zero (a b : ℕ) :
    (matrix (fun _ : Fin a => 0) (fun _ => 0) (fun _ : Fin b => 0) (fun _ => 0) 0).det = 1 := by
  rw [matrix_zero, Matrix.det_one]

 def CoeffContinuous {T : Type*} [TopologicalSpace T] (p : T → ℝ[X]) : Prop :=
  ∀ k, Continuous (fun t => (p t).coeff k)
 theorem cc_const {T : Type*} [TopologicalSpace T] (p : ℝ[X]) : CoeffContinuous (fun _ : T => p) := fun _ => continuous_const
 theorem cc_C {T : Type*} [TopologicalSpace T] {f : T → ℝ} (h : Continuous f) : CoeffContinuous (fun t => C (f t)) := by
  intro k
  simp only [coeff_C]
  split_ifs <;> fun_prop
 theorem cc_add {T : Type*} [TopologicalSpace T] {p q : T → ℝ[X]}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun t => p t + q t) := by
  intro k
  simpa only [coeff_add] using (hp k).add (hq k)
 theorem cc_sub {T : Type*} [TopologicalSpace T] {p q : T → ℝ[X]}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun t => p t - q t) := by
  intro k
  simpa only [coeff_sub] using (hp k).sub (hq k)
 theorem cc_mul {T : Type*} [TopologicalSpace T] {p q : T → ℝ[X]}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun t => p t * q t) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finset_sum _ (fun ij _ => (hp ij.1).mul (hq ij.2))
 theorem cc_prod {T ι : Type*} [TopologicalSpace T] (s : Finset ι) {p : ι → T → ℝ[X]}
    (h : ∀ i ∈ s, CoeffContinuous (p i)) : CoeffContinuous (fun t => ∏ i ∈ s, p i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cc_const (1 : ℝ[X])
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using cc_mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

 theorem row_continuous {T : Type*} [TopologicalSpace T] {a b : ℕ}
    {α x : Fin a → T → ℝ} {y z : Fin b → T → ℝ} {τ : T → ℝ}
    (hα : ∀ j, Continuous (α j)) (hx : ∀ j, Continuous (x j))
    (hy : ∀ j, Continuous (y j)) (hz : ∀ j, Continuous (z j)) (hτ : Continuous τ)
    (i : Fin (a+b+2)) : CoeffContinuous (fun t => row (fun j => α j t) (fun j => x j t)
      (fun j => y j t) (fun j => z j t) (τ t) i) := by
  unfold row
  split_ifs
  · exact cc_mul (cc_const _) (cc_mul (cc_sub (cc_const _) (cc_mul (cc_C (hα _)) (cc_const _)))
      (cc_sub (cc_const _) (cc_mul (cc_C (hx _)) (cc_const _))))
  · exact cc_mul (cc_mul (cc_prod _ (fun j _ => cc_add (cc_const _) (cc_C (hα j))))
      (cc_prod _ (fun j _ => cc_add (cc_const _) (cc_mul (cc_C (hy j)) (cc_const _)))))
      (cc_sub (cc_const _) (cc_mul (cc_C hτ) (cc_const _)))
  · exact cc_mul (cc_mul (cc_prod _ (fun j _ => cc_add (cc_const _) (cc_C (hx j))))
      (cc_prod _ (fun j _ => cc_add (cc_const _) (cc_mul (cc_C (hz j)) (cc_const _)))))
      (cc_add (cc_const _) (cc_C hτ))
  · exact cc_mul (cc_const _) (cc_mul (cc_sub (cc_const _) (cc_C (hy _)))
      (cc_sub (cc_const _) (cc_C (hz _))))

 theorem det_continuous {T : Type*} [TopologicalSpace T] {a b : ℕ}
    {α x : Fin a → T → ℝ} {y z : Fin b → T → ℝ} {τ : T → ℝ}
    (hα : ∀ j, Continuous (α j)) (hx : ∀ j, Continuous (x j))
    (hy : ∀ j, Continuous (y j)) (hz : ∀ j, Continuous (z j)) (hτ : Continuous τ) :
    Continuous (fun t => (matrix (fun j => α j t) (fun j => x j t)
      (fun j => y j t) (fun j => z j t) (τ t)).det) := by
  apply Continuous.matrix_det
  exact continuous_pi (fun i => continuous_pi (fun k => row_continuous hα hx hy hz hτ i k.val))

noncomputable def slope (δ r : ℝ) : ℝ := r / (δ + Real.sqrt (δ^2+r^2))

theorem slope_den_pos {δ r : ℝ} (hδ : 0 ≤ δ) (h : δ ≠ 0 ∨ r ≠ 0) :
    0 < δ + Real.sqrt (δ^2+r^2) := by
  have hs : 0 < δ^2+r^2 := by
    rcases h with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg r]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg δ]
  have := Real.sqrt_pos.2 hs
  linarith

theorem slope_continuous {T : Type*} [TopologicalSpace T] {δ r : T → ℝ}
    (hδ : Continuous δ) (hr : Continuous r) (hn : ∀ t, 0 ≤ δ t)
    (hne : ∀ t, δ t ≠ 0 ∨ r t ≠ 0) : Continuous (fun t => slope (δ t) (r t)) := by
  apply hr.div (hδ.add (Real.continuous_sqrt.comp ((hδ.pow 2).add (hr.pow 2))))
  intro t
  exact ne_of_gt (slope_den_pos (hn t) (hne t))

@[simp] theorem slope_zero (δ : ℝ) : slope δ 0 = 0 := by simp [slope]

abbrev Interval := Set.Icc (0 : ℝ) 1
noncomputable def alpha (j : Fin 52) (t : ℝ) : ℝ :=
  slope (31 - ((j.val : ℝ)-51)*t*(1-t)) t
noncomputable def chi (j : Fin 52) (t : ℝ) : ℝ :=
  slope (32 - ((j.val : ℝ)-51)*t*(1-t)) (32*t)
noncomputable def gamma (j : Fin 30) (t : ℝ) : ℝ :=
  slope (2-t+(j.val : ℝ)*t*(1-t)) t
noncomputable def beta (j : Fin 30) (t : ℝ) : ℝ :=
  slope (1-t+(j.val : ℝ)*t*(1-t)) (32*t)
noncomputable def tau (t : ℝ) : ℝ := slope 1 (31*t)

theorem lower_gap_pos (j : Fin 52) (t : Interval) :
    0 < 31 - ((j.val : ℝ)-51)*(t : ℝ)*(1-t) := by
  have hj : (j.val : ℝ) ≤ 51 := by exact_mod_cast (show j.val ≤ 51 by omega)
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hj)
    (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
  nlinarith

theorem upper_gap_nonneg (j : Fin 30) (t : Interval) :
    0 ≤ 1-(t : ℝ)+(j.val : ℝ)*t*(1-t) := by
  have hp := mul_nonneg (Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val)
    (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
  nlinarith [t.property.2]

theorem alpha_continuous (j : Fin 52) : Continuous (fun t : Interval => alpha j t) := by
  unfold alpha
  apply slope_continuous (by fun_prop) (by fun_prop)
  · exact fun t => (lower_gap_pos j t).le
  · exact fun t => Or.inl (ne_of_gt (lower_gap_pos j t))
theorem chi_continuous (j : Fin 52) : Continuous (fun t : Interval => chi j t) := by
  unfold chi
  apply slope_continuous (by fun_prop) (by fun_prop)
  · intro t; have := lower_gap_pos j t; linarith
  · intro t; left; have := lower_gap_pos j t; linarith
theorem gamma_continuous (j : Fin 30) : Continuous (fun t : Interval => gamma j t) := by
  unfold gamma
  apply slope_continuous (by fun_prop) (by fun_prop)
  · intro t; have := upper_gap_nonneg j t; linarith
  · intro t; left; have := upper_gap_nonneg j t; linarith
theorem beta_continuous (j : Fin 30) : Continuous (fun t : Interval => beta j t) := by
  unfold beta
  apply slope_continuous (by fun_prop) (by fun_prop) (upper_gap_nonneg j)
  intro t
  by_cases h : (t : ℝ) = 0
  · left; simp [h]
  · right; exact mul_ne_zero (by norm_num) h
theorem tau_continuous : Continuous (fun t : Interval => tau t) := by
  unfold tau
  apply slope_continuous (by fun_prop) (by fun_prop)
  · intro; norm_num
  · intro; left; norm_num


noncomputable def pathMatrix (t : ℝ) : Matrix (Fin 84) (Fin 84) ℝ :=
  matrix (fun j => alpha j t) (fun j => chi j t) (fun j => gamma j t) (fun j => beta j t) (tau t)
noncomputable def pathDet (t : ℝ) : ℝ := (pathMatrix t).det



theorem row_natDegree_le {a b : ℕ} (α x : Fin a → ℝ) (y z : Fin b → ℝ)
    (τ : ℝ) (i : Fin (a+b+2)) : (row α x y z τ i).natDegree ≤ a+b+1 := by
  have hlin₁ (r : ℝ) : (X + C r : ℝ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le <;> simp
  have hlin₂ (r : ℝ) : (1 + C r * X : ℝ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have hlin₃ (r : ℝ) : (1 - C r * X : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
  have hlin₄ (r : ℝ) : (X - C r : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have hp₁ {n : ℕ} (f : Fin n → ℝ) : (∏ j, (X + C (f j))).natDegree ≤ n := by
    exact (natDegree_prod_le _ _).trans (by simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlin₁ (f j)))
  have hp₂ {n : ℕ} (f : Fin n → ℝ) : (∏ j, (1 + C (f j) * X)).natDegree ≤ n := by
    exact (natDegree_prod_le _ _).trans (by simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlin₂ (f j)))
  unfold row
  split_ifs with h h₁ h₂
  · exact (natDegree_mul_le.trans (Nat.add_le_add (show (X ^ i.val : ℝ[X]).natDegree ≤ i.val by simp) (natDegree_mul_le.trans (Nat.add_le_add (hlin₃ _) (hlin₃ _))))).trans (by omega)
  · exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add (hp₁ α) (hp₂ y))) (hlin₃ τ)))
  · exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add (hp₁ x) (hp₂ z))) (hlin₁ τ)))
  · exact (natDegree_mul_le.trans (Nat.add_le_add (show (X ^ (a+(i.val-a-2)) : ℝ[X]).natDegree ≤ a+(i.val-a-2) by simp) (natDegree_mul_le.trans (Nat.add_le_add (hlin₄ _) (hlin₄ _))))).trans (by omega)

@[simp] theorem alpha_one (j : Fin 52) : alpha j 1 = slope 31 1 := by simp [alpha]
@[simp] theorem chi_one (j : Fin 52) : chi j 1 = slope 32 32 := by simp [chi]
@[simp] theorem gamma_one (j : Fin 30) : gamma j 1 = slope 1 1 := by norm_num [gamma]
@[simp] theorem beta_one (j : Fin 30) : beta j 1 = 1 := by norm_num [beta, slope]
@[simp] theorem tau_one : tau 1 = slope 1 31 := by simp [tau]


end Atiyah.SingularRows
