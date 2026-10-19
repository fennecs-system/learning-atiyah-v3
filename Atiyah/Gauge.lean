import Atiyah.Configuration

/-!
# DP2 / DP6: Hopf lift gauge independence

G1: equal Hopf images force equality of the squared norms of each component.
G2: any two nonzero lifts of the same displacement differ by a nonzero scalar.
G3: changing each factor by a nonzero scalar rescales each point form, hence
preserves independence. Diagonal entries are deliberately irrelevant.
-/
noncomputable section
namespace Atiyah.Configuration

 theorem hopf_eq_normSq_fst {u v : Spinor} (h : hopf u = hopf v) :
    Complex.normSq u.1 = Complex.normSq v.1 := by
  have hd := congrArg Prod.fst h
  have hp := congrArg (fun z : Space => Complex.normSq z.2) h
  simp only [hopf, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj] at hd hp
  have hu := Complex.normSq_nonneg u.1
  have hv := Complex.normSq_nonneg v.1
  have hub := Complex.normSq_nonneg u.2
  have hvb := Complex.normSq_nonneg v.2
  nlinarith [sq_nonneg (Complex.normSq u.1 - Complex.normSq v.1)]

 theorem hopf_eq_exists_smul (u v : Spinor) (hu : u ≠ (0, 0))
    (h : hopf u = hopf v) : ∃ c : ℂ, c ≠ 0 ∧ v = c • u := by
  have hn := hopf_eq_normSq_fst h
  have hz : u.1 * star u.2 = v.1 * star v.2 := congrArg Prod.snd h
  by_cases ha : u.1 = 0
  · have hc : v.1 = 0 := Complex.normSq_eq_zero.mp (by simpa [ha] using hn.symm)
    have hb : u.2 ≠ 0 := by intro hb; exact hu (Prod.ext ha hb)
    have hd : v.2 ≠ 0 := by
      intro hd
      have hh := congrArg Prod.fst h
      simp [hopf, ha, hc, hd] at hh
      exact hb hh
    refine ⟨v.2 / u.2, div_ne_zero hd hb, ?_⟩
    apply Prod.ext <;> simp [ha, hc, div_mul_cancel₀ _ hb]
  · have hc : v.1 ≠ 0 := by
      intro hc
      exact ha (Complex.normSq_eq_zero.mp (by simpa [hc] using hn))
    have he : star u.1 * u.1 = star v.1 * v.1 := by
      simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] using congrArg Complex.ofReal hn
    have hw : u.1 * v.2 = v.1 * u.2 := by
      have hz' := congrArg star hz
      simp only [star_mul, star_star] at hz'
      apply mul_left_cancel₀ (show star v.1 ≠ 0 by simpa using hc)
      calc
        star v.1 * (u.1 * v.2) = u.1 * (star v.1 * v.2) := by ring
        _ = u.1 * (star u.1 * u.2) := by congr 1; simpa [mul_comm] using hz'.symm
        _ = (star u.1 * u.1) * u.2 := by ring
        _ = (star v.1 * v.1) * u.2 := by rw [he]
        _ = star v.1 * (v.1 * u.2) := by ring
    refine ⟨v.1 / u.1, div_ne_zero hc ha, ?_⟩
    apply Prod.ext
    · simp [div_mul_cancel₀ _ ha]
    · change v.2 = v.1 / u.1 * u.2
      field_simp
      simpa [mul_comm] using hw

@[simp] theorem linearForm_smul (c : ℂ) (u : Spinor) :
    linearForm (c • u) = c • linearForm u := by
  simp [linearForm, MvPolynomial.smul_eq_C_mul, mul_add, map_mul, mul_assoc]

/-- G3: each outgoing point form changes by a nonzero column scalar. -/
theorem pointForm_exists_smul {n : ℕ} {p : Config n} (L K : LiftFamily p)
    (i : Fin n) : ∃ c : ℂ, c ≠ 0 ∧ pointForm K i = c • pointForm L i := by
  classical
  have hs : ∀ j, ∃ c : ℂ, c ≠ 0 ∧
      (j ≠ i → K.lift i j = c • L.lift i j) := by
    intro j
    by_cases hj : j = i
    · exact ⟨1, one_ne_zero, fun h => (h hj).elim⟩
    · obtain ⟨c, hc, he⟩ := hopf_eq_exists_smul (L.lift i j) (K.lift i j)
        (lift_ne_zero L i j (Ne.symm hj)) ((L.incidence i j (Ne.symm hj)).trans
          (K.incidence i j (Ne.symm hj)).symm)
      exact ⟨c, hc, fun _ => he⟩
  choose c hc he using hs
  refine ⟨∏ j ∈ Finset.univ.erase i, c j, Finset.prod_ne_zero_iff.mpr (fun j _ => hc j), ?_⟩
  simp only [pointForm, MvPolynomial.smul_eq_C_mul, map_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [he j (Finset.mem_erase.mp hj).1, linearForm_smul, MvPolynomial.smul_eq_C_mul]

/-- Independent rescaling by arbitrary nonzero complex numbers preserves independence. -/
theorem linearIndependent_smul_iff {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : ι → V) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) :
    LinearIndependent ℂ (fun i => c i • v i) ↔ LinearIndependent ℂ v := by
  simpa only [Units.smul_def, Units.val_mk0] using LinearIndependent.units_smul_iff (R := ℂ) v (fun i => Units.mk0 (c i) (hc i))

/-- DP6: the full binary-form assertion is independent of all Hopf lift choices. -/
theorem linearIndependent_pointForm_iff {n : ℕ} {p : Config n} (L K : LiftFamily p) :
    LinearIndependent ℂ (pointForm L) ↔ LinearIndependent ℂ (pointForm K) := by
  classical
  choose c hc he using pointForm_exists_smul L K
  have hf : pointForm K = fun i => (Units.mk0 (c i) (hc i)) • pointForm L i := by
    funext i
    simpa using he i
  rw [hf]
  exact (LinearIndependent.units_smul_iff _ _).symm

 theorem hopf_real_smul (r : ℝ) (v : Spinor) :
    hopf ((r : ℂ) • v) = r ^ 2 • hopf v := by
  apply Prod.ext
  · simp [hopf, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  · simp [hopf, star_mul, Complex.star_def]
    ring

 theorem hopf_sqrt_smul (r : ℝ) (hr : 0 ≤ r) (v : Spinor) :
    hopf ((Real.sqrt r : ℂ) • v) = r • hopf v := by
  rw [hopf_real_smul, Real.sq_sqrt hr]

end Atiyah.Configuration
