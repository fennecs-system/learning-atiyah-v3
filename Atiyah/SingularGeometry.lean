import Atiyah.Gauge
import Atiyah.PlanarLift

/-!
SG1: At each 0<t<1 the 84 points of the m=1, a=52, b=30, R=32
path have strictly increasing first coordinates, hence are distinct.
SG2: The normalized slope w/(δ+sqrt(δ²+w²)) gives an actual Hopf
lift after multiplication by sqrt(δ+sqrt(δ²+w²)). No endpoint
configuration or endpoint distinctness is asserted.
-/
noncomputable section
namespace Atiyah.SingularGeometry

/-- Actual real planar coordinates of Eickhoff's 84-point path. -/
def path (t : ℝ) (i : Fin 84) : ℝ × ℝ :=
  if i.val < 52 then (((i.val : ℝ) - 51) * t * (1-t), 0)
  else if i.val = 52 then (31, t)
  else if i.val = 53 then (32, 32*t)
  else (33-t + ((i.val : ℝ)-54)*t*(1-t), 0)

@[simp] theorem path_lower (t : ℝ) (j : Fin 52) :
    path t ⟨j.val, by omega⟩ = (((j.val : ℝ)-51)*t*(1-t), 0) := by
  simp [path, j.isLt]

@[simp] theorem path_A (t : ℝ) : path t 52 = (31,t) := by rfl
@[simp] theorem path_B (t : ℝ) : path t 53 = (32,32*t) := by rfl

@[simp] theorem path_upper (t : ℝ) (j : Fin 30) :
    path t ⟨54+j.val, by omega⟩ = (33-t+(j.val : ℝ)*t*(1-t), 0) := by
  have h1 : ¬54+j.val < 52 := by omega
  have h2 : ¬54+j.val = 52 := by omega
  have h3 : ¬54+j.val = 53 := by omega
  simp [path, h1, h2, h3, Nat.cast_add]

theorem path_height_strictMono {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    StrictMono (fun i : Fin 84 => (path t i).1) := by
  intro i j hij
  have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hmul : 0 < t * (1-t) := mul_pos ht (by linarith)
  have hprod := mul_lt_mul_of_pos_right hij' hmul
  have hleft (k : Fin 84) (hk : k.val < 52) :
      ((k.val : ℝ)-51)*t*(1-t) ≤ 0 := by
    have hb : (k.val : ℝ) ≤ 51 := by exact_mod_cast (show k.val ≤ 51 by omega)
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (le_of_lt hmul)
    nlinarith
  have hright (k : Fin 84) (hk : 54 ≤ k.val) :
      32 < 33-t+((k.val : ℝ)-54)*t*(1-t) := by
    have hb : (54 : ℝ) ≤ k.val := by exact_mod_cast hk
    have hh := mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hmul)
    nlinarith
  simp only [path]
  split_ifs <;> dsimp
  all_goals try omega
  all_goals try { have hh := hleft i (by omega); nlinarith }
  all_goals try { have hh := hright j (by omega); nlinarith }
  all_goals nlinarith

theorem path_injective {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Function.Injective (path t) := by
  intro i j h
  exact (path_height_strictMono ht ht1).injective (congrArg Prod.fst h)

/-- Embed the real planar path in the full complex three-dimensional model. -/
def config (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : Configuration.Config 84 where
  point i := ((path t i).1, ((path t i).2 : ℂ))
  distinct := by
    intro i j h
    apply path_injective ht ht1
    apply Prod.ext
    · exact congrArg (fun p : ℝ × ℂ => p.1) h
    · have hh := congrArg (fun p : ℝ × ℂ => p.2.re) h
      simpa using hh

/-- Half-angle denominator, used only where it is positive. -/
def denominator (δ w : ℝ) : ℝ := δ + Real.sqrt (δ^2+w^2)
def slope (δ w : ℝ) : ℝ := w / denominator δ w

@[simp] theorem slope_zero (δ : ℝ) : slope δ 0 = 0 := by simp [slope]
@[simp] theorem slope_neg (δ w : ℝ) : slope δ (-w) = -slope δ w := by
  simp only [slope, denominator, neg_sq, neg_div]

theorem denominator_pos {δ w : ℝ} (hδ : 0 < δ) : 0 < denominator δ w := by
  unfold denominator
  positivity

theorem normalized_incidence {δ w : ℝ} (hD : 0 < denominator δ w) :
    PlanarLift.Incidence δ w (Real.sqrt (denominator δ w))
      (Real.sqrt (denominator δ w) * slope δ w) := by
  have hs : (Real.sqrt (denominator δ w))^2 = denominator δ w :=
    Real.sq_sqrt (le_of_lt hD)
  have hr : (Real.sqrt (δ^2+w^2))^2 = δ^2+w^2 :=
    Real.sq_sqrt (by positivity)
  have hD0 : denominator δ w ≠ 0 := ne_of_gt hD
  constructor
  · dsimp [slope]
    field_simp
    dsimp [denominator] at *
    nlinarith
  · dsimp [slope]
    field_simp
    calc
      _ = (Real.sqrt (denominator δ w))^2 * w := by ring
      _ = _ := by rw [hs]; ring

/-- The real incidence equations embed into the full complex Hopf map. -/
theorem complex_incidence {δ w a b : ℝ} (h : PlanarLift.Incidence δ w a b) :
    Configuration.hopf ((a : ℂ), (b : ℂ)) = (δ, (w : ℂ)) := by
  apply Prod.ext
  · simp only [Configuration.hopf, Complex.normSq_ofReal]
    rcases h with ⟨h₁, h₂⟩
    nlinarith
  · simp only [Configuration.hopf, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    exact congrArg Complex.ofReal h.2

/-- A physical lift of a positive-height displacement. -/
def forwardLift (δ w : ℝ) : Configuration.Spinor :=
  ((Real.sqrt (denominator δ w) : ℝ),
   (Real.sqrt (denominator δ w) * slope δ w : ℝ))

theorem forwardLift_hopf {δ w : ℝ} (hδ : 0 < δ) :
    Configuration.hopf (forwardLift δ w) = (δ, (w : ℂ)) :=
  complex_incidence (normalized_incidence (denominator_pos hδ))

/-- A physical lift of the reverse displacement. -/
def reverseLift (δ w : ℝ) : Configuration.Spinor :=
  ((-(Real.sqrt (denominator δ w) * slope δ w) : ℝ),
   (Real.sqrt (denominator δ w) : ℝ))

theorem reverseLift_hopf {δ w : ℝ} (hδ : 0 < δ) :
    Configuration.hopf (reverseLift δ w) = (-δ, ((-w : ℝ) : ℂ)) :=
  complex_incidence (PlanarLift.incidence_antipodal
    (normalized_incidence (denominator_pos hδ)))

def edgeLift (t : ℝ) (i j : Fin 84) : Configuration.Spinor :=
  if i < j then forwardLift ((path t j).1-(path t i).1) ((path t j).2-(path t i).2)
  else reverseLift ((path t i).1-(path t j).1) ((path t i).2-(path t j).2)

/-- Explicit physical Hopf lifts of every displacement on the interior path. -/
def lifts (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Configuration.LiftFamily (config t ht ht1) where
  lift := edgeLift t
  incidence := by
    intro i j hij
    dsimp [edgeLift]
    split_ifs with h
    · rw [forwardLift_hopf (sub_pos.mpr (path_height_strictMono ht ht1 h))]
      simp [config, Complex.ofReal_sub]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.symm
      rw [reverseLift_hopf (sub_pos.mpr (path_height_strictMono ht ht1 hji))]
      simp [config, Complex.ofReal_sub, neg_sub]

/-- In the repository convention, forward normalized factors are X₀+sX₁. -/
theorem forward_linearForm (δ w : ℝ) :
    Configuration.linearForm (forwardLift δ w) =
      MvPolynomial.C (Real.sqrt (denominator δ w) : ℂ) *
      Configuration.linearForm (1, (slope δ w : ℂ)) := by
  simp [Configuration.linearForm, forwardLift, Complex.ofReal_mul,
    map_mul, mul_add, mul_assoc]

/-- Reverse normalized factors are -sX₀+X₁. A common substitution X₁↦-X₁
recovers the paper convention, up to a constant sign on reverse factors. -/
theorem reverse_linearForm (δ w : ℝ) :
    Configuration.linearForm (reverseLift δ w) =
      MvPolynomial.C (Real.sqrt (denominator δ w) : ℂ) *
      Configuration.linearForm (-(slope δ w : ℂ), 1) := by
  simp [Configuration.linearForm, reverseLift, Complex.ofReal_mul,
    map_mul, mul_add, mul_assoc]

def edgeScale (t : ℝ) (i j : Fin 84) : ℝ :=
  if i < j then Real.sqrt (denominator ((path t j).1-(path t i).1)
    ((path t j).2-(path t i).2))
  else Real.sqrt (denominator ((path t i).1-(path t j).1)
    ((path t i).2-(path t j).2))

def normalizedSpinor (t : ℝ) (i j : Fin 84) : Configuration.Spinor :=
  if i < j then (1, (slope ((path t j).1-(path t i).1)
    ((path t j).2-(path t i).2) : ℂ))
  else (-(slope ((path t i).1-(path t j).1)
    ((path t i).2-(path t j).2) : ℂ), 1)

theorem edge_linearForm (t : ℝ) (i j : Fin 84) :
    Configuration.linearForm (edgeLift t i j) =
    MvPolynomial.C (edgeScale t i j : ℂ) *
      Configuration.linearForm (normalizedSpinor t i j) := by
  unfold edgeLift edgeScale normalizedSpinor
  split_ifs
  · exact forward_linearForm _ _
  · exact reverse_linearForm _ _

theorem edgeScale_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (i j : Fin 84) (hij : i ≠ j) : 0 < edgeScale t i j := by
  unfold edgeScale
  split_ifs with h
  · exact Real.sqrt_pos.mpr (denominator_pos
      (sub_pos.mpr (path_height_strictMono ht ht1 h)))
  · exact Real.sqrt_pos.mpr (denominator_pos
      (sub_pos.mpr (path_height_strictMono ht ht1
        (lt_of_le_of_ne (le_of_not_gt h) hij.symm))))

def normalizedPointForm (t : ℝ) (i : Fin 84) : Configuration.BinaryForm :=
  ∏ j ∈ Finset.univ.erase i, Configuration.linearForm (normalizedSpinor t i j)

def rowScale (t : ℝ) (i : Fin 84) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, edgeScale t i j

theorem rowScale_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (i : Fin 84) :
    0 < rowScale t i := by
  apply Finset.prod_pos
  intro j hj
  exact edgeScale_pos ht ht1 i j (Finset.mem_erase.mp hj).1.symm

/-- The normalized row products represent the actual configuration's point
forms, with explicit nonzero positive physical scales. -/
theorem pointForm_eq (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (i : Fin 84) :
    Configuration.pointForm (lifts t ht ht1) i =
      MvPolynomial.C (rowScale t i : ℂ) * normalizedPointForm t i := by
  classical
  simp only [Configuration.pointForm, lifts, edge_linearForm, normalizedPointForm,
    rowScale, Finset.prod_mul_distrib, Complex.ofReal_prod, map_prod]

/-- Independence of the actual point forms is exactly independence of the
normalized geometric rows, for every physical lift family. -/
theorem independent_iff_normalized (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (L : Configuration.LiftFamily (config t ht ht1)) :
    LinearIndependent ℂ (Configuration.pointForm L) ↔
      LinearIndependent ℂ (normalizedPointForm t) := by
  rw [Configuration.linearIndependent_pointForm_iff L (lifts t ht ht1)]
  have he : Configuration.pointForm (lifts t ht ht1) =
      fun i => (rowScale t i : ℂ) • normalizedPointForm t i := by
    funext i
    simpa only [MvPolynomial.smul_eq_C_mul] using pointForm_eq t ht ht1 i
  rw [he]
  apply Configuration.linearIndependent_smul_iff
  intro i
  exact_mod_cast (ne_of_gt (rowScale_pos ht ht1 i))

end Atiyah.SingularGeometry
