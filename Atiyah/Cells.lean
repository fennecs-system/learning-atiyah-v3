import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Signed winner cones of a polynomial coefficient configuration

The vectors in this file are arbitrary real coefficient vectors. The results
are linear-algebraic infrastructure, not a proof that Atiyah's geometric
coefficient vectors are independent. The signed cones are the normal cones
at the labelled points of the centrally symmetric convex hull `conv {±ρᵢ}`.
Labels need not be distinct or exposed, and ties are deliberately retained.
-/

namespace Atiyah.Cells

variable {n d : ℕ}

/-- Evaluation of a coefficient vector against a dual coordinate vector. -/
def score (ρ : Fin n → Fin d → ℝ) (i : Fin n) (v : Fin d → ℝ) : ℝ :=
  ∑ k, v k * ρ i k

@[simp] theorem score_add (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (v w : Fin d → ℝ) : score ρ i (v + w) = score ρ i v + score ρ i w := by
  simp [score, add_mul, Finset.sum_add_distrib]

@[simp] theorem score_smul (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (a : ℝ) (v : Fin d → ℝ) : score ρ i (a • v) = a * score ρ i v := by
  simp [score, mul_assoc, Finset.mul_sum]

@[simp] theorem score_zero (ρ : Fin n → Fin d → ℝ) (i : Fin n) :
    score ρ i 0 = 0 := by simp [score]

/-- `true` labels `ρᵢ`; `false` labels `-ρᵢ`. -/
def signedScore (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (positive : Bool) (v : Fin d → ℝ) : ℝ :=
  if positive then score ρ i v else -score ρ i v

@[simp] theorem signedScore_add (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (s : Bool) (v w : Fin d → ℝ) :
    signedScore ρ i s (v + w) = signedScore ρ i s v + signedScore ρ i s w := by
  cases s <;> simp [signedScore, neg_add, add_comm]

@[simp] theorem signedScore_smul (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (s : Bool) (a : ℝ) (v : Fin d → ℝ) :
    signedScore ρ i s (a • v) = a * signedScore ρ i s v := by
  cases s <;> simp [signedScore]

/-- The closed signed winner cell, as an intersection of homogeneous half-spaces. -/
def signedCell (ρ : Fin n → Fin d → ℝ) (i : Fin n) (s : Bool) :
    Set (Fin d → ℝ) :=
  {v | ∀ j, score ρ j v ≤ signedScore ρ i s v ∧
      -score ρ j v ≤ signedScore ρ i s v}

/-- The classifier which forgets the sign of the winning coefficient vector. -/
def absoluteCell (ρ : Fin n → Fin d → ℝ) (i : Fin n) : Set (Fin d → ℝ) :=
  {v | ∀ j, |score ρ j v| ≤ |score ρ i v|}

theorem mem_signedCell_iff (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (s : Bool) (v : Fin d → ℝ) :
    v ∈ signedCell ρ i s ↔ ∀ j, |score ρ j v| ≤ signedScore ρ i s v := by
  simp only [signedCell, Set.mem_setOf_eq, abs_le]
  constructor
  · intro h j
    constructor <;> have hj := h j <;> linarith
  · intro h j
    constructor <;> have hj := h j <;> linarith

/-- Each signed cell is a cone: nonnegative linear combinations remain inside. -/
theorem signedCell_nonneg_combination (ρ : Fin n → Fin d → ℝ)
    (i : Fin n) (s : Bool) {v w : Fin d → ℝ}
    (hv : v ∈ signedCell ρ i s) (hw : w ∈ signedCell ρ i s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • v + b • w ∈ signedCell ρ i s := by
  intro j
  have hvj := hv j
  have hwj := hw j
  have hpv := mul_le_mul_of_nonneg_left hvj.1 ha
  have hpw := mul_le_mul_of_nonneg_left hwj.1 hb
  have hnv := mul_le_mul_of_nonneg_left hvj.2 ha
  have hnw := mul_le_mul_of_nonneg_left hwj.2 hb
  simp only [score_add, score_smul, signedScore_add, signedScore_smul]
  constructor <;> nlinarith

theorem signedCell_convex (ρ : Fin n → Fin d → ℝ) (i : Fin n) (s : Bool) :
    Convex ℝ (signedCell ρ i s) := by
  intro v hv w hw a b ha hb _
  exact signedCell_nonneg_combination ρ i s hv hw ha hb

/-- Forgetting the sign gives a union of two cones, not generally one convex cone. -/
theorem absoluteCell_eq_union (ρ : Fin n → Fin d → ℝ) (i : Fin n) :
    absoluteCell ρ i = signedCell ρ i true ∪ signedCell ρ i false := by
  ext v
  simp only [Set.mem_union, mem_signedCell_iff, signedScore, Bool.false_eq_true,
    ↓reduceIte, absoluteCell, Set.mem_setOf_eq]
  constructor
  · intro h
    by_cases hi : 0 ≤ score ρ i v
    · left
      simpa only [abs_of_nonneg hi] using h
    · right
      simpa only [abs_of_nonpos (le_of_lt (lt_of_not_ge hi))] using h
  · intro h j
    rcases h with h | h
    · exact (h j).trans (le_abs_self _)
    · exact (h j).trans (neg_le_abs _)

/-- The common annihilator is the lineality direction invisible to all scores. -/
def commonAnnihilator (ρ : Fin n → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {w | ∀ i, score ρ i w = 0}

theorem score_add_annihilator (ρ : Fin n → Fin d → ℝ)
    {w : Fin d → ℝ} (hw : w ∈ commonAnnihilator ρ)
    (i : Fin n) (v : Fin d → ℝ) : score ρ i (v + w) = score ρ i v := by
  simp [hw i]

/-- Cells descend to the quotient of the dual space by the common annihilator. -/
theorem signedCell_add_annihilator_iff (ρ : Fin n → Fin d → ℝ)
    {w : Fin d → ℝ} (hw : w ∈ commonAnnihilator ρ)
    (i : Fin n) (s : Bool) (v : Fin d → ℝ) :
    v + w ∈ signedCell ρ i s ↔ v ∈ signedCell ρ i s := by
  simp only [signedCell, Set.mem_setOf_eq, signedScore,
    score_add_annihilator ρ hw]

theorem absoluteCell_add_annihilator_iff (ρ : Fin n → Fin d → ℝ)
    {w : Fin d → ℝ} (hw : w ∈ commonAnnihilator ρ)
    (i : Fin n) (v : Fin d → ℝ) :
    v + w ∈ absoluteCell ρ i ↔ v ∈ absoluteCell ρ i := by
  simp only [absoluteCell, Set.mem_setOf_eq, score_add_annihilator ρ hw]

@[simp] theorem score_neg (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (v : Fin d → ℝ) : score ρ i (-v) = -score ρ i v := by
  simp [score, Finset.sum_neg_distrib]

@[simp] theorem signedScore_neg (ρ : Fin n → Fin d → ℝ) (i : Fin n)
    (s : Bool) (v : Fin d → ℝ) :
    signedScore ρ i s (-v) = -signedScore ρ i s v := by
  cases s <;> simp [signedScore]

/-- Exact lineality: a vector and its opposite lie in a signed cell precisely
when every coefficient vector annihilates that vector. This holds for each
label, including labels that are not vertices of the convex hull. -/
theorem signedCell_lineality_iff (ρ : Fin n → Fin d → ℝ)
    (i : Fin n) (s : Bool) (v : Fin d → ℝ) :
    (v ∈ signedCell ρ i s ∧ -v ∈ signedCell ρ i s) ↔
      v ∈ commonAnnihilator ρ := by
  constructor
  · rintro ⟨hv, hn⟩ j
    have hvj := hv j
    have hnj := hn j
    simp only [score_neg, signedScore_neg, neg_neg] at hnj
    linarith
  · intro h
    constructor
    · intro j
      simp [signedScore, h i, h j]
    · intro j
      simp [signedScore, h i, h j]

/-- The intersection of dual strips is the polar of the symmetric coefficient
polytope. No boundedness or independence is assumed in this definition. -/
def dualStrips (ρ : Fin n → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {v | ∀ i, |score ρ i v| ≤ 1}

theorem dualStrips_add_annihilator_iff (ρ : Fin n → Fin d → ℝ)
    {w : Fin d → ℝ} (hw : w ∈ commonAnnihilator ρ)
    (v : Fin d → ℝ) :
    v + w ∈ dualStrips ρ ↔ v ∈ dualStrips ρ := by
  simp only [dualStrips, Set.mem_setOf_eq, score_add_annihilator ρ hw]

/-- Every real multiple of a common null direction lies in the dual strips. -/
theorem annihilator_line_mem_dualStrips (ρ : Fin n → Fin d → ℝ)
    {w : Fin d → ℝ} (hw : w ∈ commonAnnihilator ρ) (t : ℝ) :
    t • w ∈ dualStrips ρ := by
  intro i
  simp [hw i]

/-- A whole line through the origin lies in the dual strips exactly when its
 direction is annihilated by every coefficient vector. -/
theorem line_mem_dualStrips_iff (ρ : Fin n → Fin d → ℝ)
    (w : Fin d → ℝ) :
    (∀ t : ℝ, t • w ∈ dualStrips ρ) ↔ w ∈ commonAnnihilator ρ := by
  constructor
  · intro h i
    by_contra hi
    have ht := h (2 / score ρ i w) i
    simp only [score_smul] at ht
    have heq : (2 / score ρ i w) * score ρ i w = 2 := by
      field_simp [hi]
    rw [heq] at ht
    norm_num at ht
  · intro h t
    exact annihilator_line_mem_dualStrips ρ h t

end Atiyah.Cells
