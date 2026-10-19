import Atiyah.SingularCertificate
/-!
Formal-English ledger:
SCB1: Interpret ascending coefficient lists as polynomials; list multiplication
by a linear factor and Horner evaluation agree with polynomial operations.
SCB2: A prefix fold gives quotient coefficients for the quadratic with constant
coefficient one. The exact remainder of the prefix is recorded by its last two
state entries; induction by appending one coefficient proves the invariant.
SCB3: Splitting a list after a coefficients and using SCB2 gives
P=L*D+X^a*W, where D.degree<a and W is exactly the certificate's eliminated list.
SCB4: The concrete ring lists have length 84 and the advertised product formulas.
Their eliminated lists have length 32, hence polynomial degree below 32.
SCB5: The certificate numerator equals the determinant of the two evaluation
rows. Identification of this with the full coefficient determinant remains in
the boundary elimination module.
-/
noncomputable section
namespace Atiyah.SingularCertificateBridge
open Polynomial SingularCertificate

def ofList : List ℝ → ℝ[X]
| [] => 0
| c::p => Polynomial.C c + X*ofList p

@[simp] theorem ofList_nil : ofList [] = 0 := rfl
@[simp] theorem ofList_cons (c : ℝ) (p : List ℝ) :
    ofList (c::p)=Polynomial.C c+X*ofList p := rfl

theorem ofList_append (p q : List ℝ) :
    ofList (p++q)=ofList p+X^p.length*ofList q := by
  induction p with
  | nil => simp
  | cons c p ih => simp only [List.cons_append, ofList_cons, List.length_cons, ih, pow_succ]; ring

theorem ofList_map_mul (p : List ℝ) (c : ℝ) :
    ofList (p.map (·*c)) = Polynomial.C c*ofList p := by
  induction p with
  | nil => simp
  | cons d p ih => simp only [List.map_cons, ofList_cons, ih, map_mul]; ring

theorem ofList_zipWith (p q : List ℝ) (h : p.length=q.length) :
    ofList (List.zipWith (·+·) p q)=ofList p+ofList q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all
  | cons c p ih =>
    cases q with
    | nil => simp_all
    | cons d q =>
      have hh : p.length=q.length := by simpa using h
      simp only [List.zipWith_cons_cons, ofList_cons, ih q hh, map_add]
      ring

theorem ofList_multiplyLinear (p : List ℝ) (c l : ℝ) :
    ofList (multiplyLinear p c l)=ofList p*(Polynomial.C c+Polynomial.C l*X) := by
  unfold multiplyLinear
  rw [ofList_zipWith _ _ (by simp), ofList_append, ofList_cons]
  simp only [ofList_cons, ofList_nil, map_zero, mul_zero, add_zero, zero_add, ofList_map_mul]
  ring

theorem eval_ofList (p : List ℝ) (x : ℝ) :
    (ofList p).eval x=evaluate p x := by
  induction p with
  | nil => simp [evaluate]
  | cons c p ih => simp [evaluate, ih, add_comm, mul_comm]

def state (p : List ℝ) (α x : ℝ) : ℝ×ℝ :=
  p.foldl (fun s c => (s.2,c+(α+x)*s.2-α*x*s.1)) (0,0)

def lowerQuad (α x : ℝ) : ℝ[X] :=
  (1-Polynomial.C α*X)*(1-Polynomial.C x*X)

theorem prefix_decomposition (p : List ℝ) (α x : ℝ) :
    ∃ D : ℝ[X], D.degree < (p.length : WithBot ℕ) ∧
    ofList p = lowerQuad α x*D + X^p.length *
      (Polynomial.C ((α+x)*(state p α x).2-α*x*(state p α x).1) -
       Polynomial.C (α*x*(state p α x).2)*X) := by
  induction p using List.reverseRecOn with
  | nil => refine ⟨0,?_,?_⟩ <;> simp [state, lowerQuad]
  | @append_singleton p c ih =>
    obtain ⟨D,hD,h⟩ := ih
    let d := c+(α+x)*(state p α x).2-α*x*(state p α x).1
    refine ⟨D+Polynomial.C d*X^p.length,?_,?_⟩
    · have hh := degree_add_le D (Polynomial.C d*X^p.length)
      have hm := degree_C_mul_X_pow_le p.length d
      have hn : (p.length : WithBot ℕ) < ↑(p.length+1) := by exact_mod_cast Nat.lt_succ_self p.length
      simp only [List.length_append, List.length_singleton]
      exact lt_of_le_of_lt (hh.trans (max_le hD.le hm)) hn
    · simp only [ofList_append, ofList_cons, ofList_nil, mul_zero, add_zero,
        List.length_append, List.length_singleton, pow_succ]
      have hs : state (p++[c]) α x = ((state p α x).2,d) := by
        simp [state, List.foldl_append, d, sub_eq_add_neg]
      rw [hs,h]
      simp only [Prod.fst, Prod.snd]
      dsimp [lowerQuad,d]
      simp only [map_add,map_sub,map_mul]
      ring

theorem eliminated_append (p q : List ℝ) (c d α x : ℝ) :
    eliminated (p++c::d::q) p.length α x =
      [(c+(α+x)*(state p α x).2-α*x*(state p α x).1),
       d-α*x*(state p α x).2]++q := by
  simp [eliminated, state, List.take_append, List.drop_append, List.foldl_append,
    List.getElem?_append, sub_eq_add_neg]

theorem eliminated_append_decomposition (p q : List ℝ) (c d α x : ℝ) :
    ∃ D : ℝ[X], D.degree < (p.length : WithBot ℕ) ∧
      ofList (p++c::d::q) = lowerQuad α x*D + X^p.length *
        ofList (eliminated (p++c::d::q) p.length α x) := by
  obtain ⟨D,hD,h⟩ := prefix_decomposition p α x
  refine ⟨D,hD,?_⟩
  rw [ofList_append, eliminated_append, h]
  simp only [List.cons_append, List.nil_append, ofList_cons, map_add, map_sub, map_mul]
  ring

theorem eliminated_decomposition (p : List ℝ) (a : ℕ) (α x : ℝ)
    (hlen : a+2 ≤ p.length) :
    ∃ D : ℝ[X], D.degree < (a : WithBot ℕ) ∧
      ofList p = lowerQuad α x*D + X^a * ofList (eliminated p a α x) := by
  have ht : (p.take a).length=a := by simp; omega
  have hdlen : (p.drop a).length = p.length-a := by simp
  have hp : p.take a ++ p.drop a = p := List.take_append_drop a p
  cases hd : p.drop a with
  | nil => simp only [hd, List.length_nil] at hdlen; omega
  | cons c r =>
    cases r with
    | nil => simp only [hd, List.length_cons, List.length_nil] at hdlen; omega
    | cons d q =>
      have hh := eliminated_append_decomposition (p.take a) q c d α x
      rw [ht, ← hd, hp] at hh
      exact hh

theorem ofList_coeff (p : List ℝ) (n : ℕ) :
    (ofList p).coeff n = p[n]?.getD 0 := by
  induction p generalizing n with
  | nil => simp
  | cons c p ih =>
    cases n <;> simp [ofList_cons, ih, coeff_X_mul]

theorem ofList_degree (p : List ℝ) : (ofList p).degree < (p.length : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  rw [ofList_coeff]
  simp [List.getElem?_eq_none hn]

theorem length_multiplyLinear (p : List ℝ) (c l : ℝ) :
    (multiplyLinear p c l).length = p.length+1 := by simp [multiplyLinear]

theorem length_eliminated (p : List ℝ) (a : ℕ) (α x : ℝ)
    (hlen : a+2 ≤ p.length) :
    (eliminated p a α x).length = p.length-a := by
  simp [eliminated]
  omega

theorem ofList_iterate_multiplyLinear (p : List ℝ) (c l : ℝ) (n : ℕ) :
    ofList (((multiplyLinear · c l)^[n]) p) =
      ofList p*(Polynomial.C c+Polynomial.C l*X)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ofList_multiplyLinear, ih, pow_succ]; ring

def listA (α x c k : ℝ) : List ℝ :=
  multiplyLinear ((multiplyLinear · 1 x)^[30]
    ((multiplyLinear · α 1)^[52] [1])) k (-c)

def listB (α x c k : ℝ) : List ℝ :=
  multiplyLinear ((multiplyLinear · 1 1)^[30]
    ((multiplyLinear · x 1)^[52] [1])) c k

theorem ofList_listA (α x c k : ℝ) :
    ofList (listA α x c k) =
      (X+Polynomial.C α)^52*(1+Polynomial.C x*X)^30*(Polynomial.C k-Polynomial.C c*X) := by
  simp only [listA, ofList_multiplyLinear, ofList_iterate_multiplyLinear,
    ofList_cons, ofList_nil, map_one, map_neg, mul_zero, add_zero, one_mul, mul_one]
  simp only [add_comm (Polynomial.C α) X, sub_eq_add_neg, neg_mul]

theorem ofList_listB (α x c k : ℝ) :
    ofList (listB α x c k) =
      (X+Polynomial.C x)^52*(1+X)^30*(Polynomial.C c+Polynomial.C k*X) := by
  simp only [listB, ofList_multiplyLinear, ofList_iterate_multiplyLinear,
    ofList_cons, ofList_nil, map_one, mul_zero, add_zero, one_mul, mul_one]
  rw [add_comm (Polynomial.C x) X]

theorem length_iterate_multiplyLinear (p : List ℝ) (c l : ℝ) (n : ℕ) :
    (((multiplyLinear · c l)^[n]) p).length = p.length+n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', length_multiplyLinear, ih]; omega

@[simp] theorem length_listA (α x c k : ℝ) : (listA α x c k).length=84 := by
  simp [listA, length_multiplyLinear, length_iterate_multiplyLinear]
@[simp] theorem length_listB (α x c k : ℝ) : (listB α x c k).length=84 := by
  simp [listB, length_multiplyLinear, length_iterate_multiplyLinear]

theorem eliminated_natDegree (p : List ℝ) (h : p.length=84) (α x : ℝ) :
    (ofList (eliminated p 52 α x)).natDegree < 32 := by
  by_cases hz : ofList (eliminated p 52 α x)=0
  · simp [hz]
  apply (natDegree_lt_iff_degree_lt hz).mpr
  have hh := ofList_degree (eliminated p 52 α x)
  simpa only [length_eliminated p 52 α x (by omega), h] using hh

theorem numerator_eq_list_evaluations (α x c k : ℝ) :
    numerator α x c k =
      (ofList (eliminated (listA α x c k) 52 α x)).eval x *
        (ofList (eliminated (listB α x c k) 52 α x)).eval 1 -
      (ofList (eliminated (listA α x c k) 52 α x)).eval 1 *
        (ofList (eliminated (listB α x c k) 52 α x)).eval x := by
  simp only [eval_ofList, listA, listB, numerator, sub_eq_add_neg]

end Atiyah.SingularCertificateBridge
