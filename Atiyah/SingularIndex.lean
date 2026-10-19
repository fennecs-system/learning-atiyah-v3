import Atiyah.SingularElimination
import Atiyah.SingularRows

namespace Atiyah.SingularIndex
open SingularElimination
abbrev Index := Fin 52 ⊕ (Fin 2 ⊕ Fin 30)

def toFin : Index → Fin 84
  | .inl i => ⟨i.val, by omega⟩
  | .inr (.inl i) => ⟨52+i.val, by omega⟩
  | .inr (.inr i) => ⟨54+i.val, by omega⟩

def ofFin (i : Fin 84) : Index :=
  if h : i.val < 52 then .inl ⟨i.val,h⟩
  else if h' : i.val < 54 then .inr (.inl ⟨i.val-52,by omega⟩)
  else .inr (.inr ⟨i.val-54,by omega⟩)

def equiv : Index ≃ Fin 84 where
  toFun := toFin
  invFun := ofFin
  left_inv := by
    intro i
    rcases i with i | (i | i)
    · simp [ofFin,toFin,i.isLt]
    · simp only [ofFin,toFin]
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 3
      omega
    · simp only [ofFin,toFin]
      rw [dif_neg (by omega), dif_neg (by omega)]
      congr 3
      omega
  right_inv := by
    intro i
    unfold ofFin
    split_ifs with h h'
    · rfl
    · apply Fin.ext; simp [toFin]; omega
    · apply Fin.ext; simp [toFin]; omega

@[simp] theorem equiv_val (i : Index) : (equiv i).val = degreeIndex 52 30 i := by
  rcases i with i | (i | i) <;> rfl

theorem det_reindexed (M : Matrix (Fin 84) (Fin 84) ℝ) :
    Matrix.det (M.submatrix equiv equiv) = M.det :=
  Matrix.det_submatrix_equiv_self equiv M

end Atiyah.SingularIndex
