import Atiyah.TwoClusterGeometry
import Atiyah.TwoClusterAlgebra
import Atiyah.TwoClusterLift

/-! TC4–TC6: the two-cluster boundary family is independent, hence so are all
actual displacement lift families on one sufficiently separated tail. -/
noncomputable section
namespace Atiyah.TwoCluster
open Configuration ContinuousLift Filter Topology

theorem eventually_clusterForms_independent {T : Type*} {l : Filter T} {m k : ℕ}
    {A : Config m} {B : Config k} (LA : LiftFamily A) (LB : LiftFamily B)
    (hA : LinearIndependent ℂ (pointForm LA))
    (hB : LinearIndependent ℂ (pointForm LB))
    (v : Spinor) (hv : v ≠ 0) (b : T → Fin m → Fin k → Spinor)
    (hb : ∀ i j, Tendsto (fun t => b t i j) l (𝓝 v)) :
    ∀ᶠ t in l, LinearIndependent ℂ (clusterForms LA LB (b t)) := by
  exact GeometricLimit.eventually_independent_of_coeff_tendsto
    (TwoClusterAlgebra.boundary_independent LA LB hA hB v hv)
    (clusterForms_tendsto LA LB v b hb)

/-- Fixed C1 cores remain C1 after translating the second sufficiently far
along any nonzero ray. Both empty cores and both Hopf poles are included. -/
theorem two_cluster_extension {m k : ℕ} (A : Config m) (B : Config k)
    (hA : ∀ L : LiftFamily A, LinearIndependent ℂ (pointForm L))
    (hB : ∀ L : LiftFamily B, LinearIndependent ℂ (pointForm L))
    (u : Space) (hu : u ≠ 0) :
    ∃ R₀ : ℝ, ∀ R > R₀, ∃ pR : Config (m+k),
      pR.point = points A B (R • u) ∘ finSumFinEquiv.symm ∧
      Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) := by
  classical
  obtain ⟨LA⟩ := liftFamily_nonempty A
  obtain ⟨LB⟩ := liftFamily_nonempty B
  obtain ⟨v, hv, b, hb, he⟩ := exists_cross_lifts A B u hu
  have hi := eventually_clusterForms_independent LA LB (hA LA) (hB LB) v hv b hb
  have ht : ∀ᶠ R : ℝ in atTop, ∃ pR : Config (m+k),
      pR.point = points A B (R • u) ∘ finSumFinEquiv.symm ∧
      Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) := by
    filter_upwards [hi, he, eventually_separated A B u hu,
      eventually_gt_atTop (0 : ℝ)] with R hi he hx hR
    exact ⟨glue A B (R • u) hx, rfl, liftFamily_nonempty _,
      independent_glue LA LB u R hR hx (b R) he hi⟩
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp ht
  exact ⟨R₀, fun R hR => hR₀ R hR.le⟩

/-- A convenience corollary from universal C1 for the two separate sizes;
no universal C1 conclusion for their sum is asserted. -/
theorem two_cluster_extension_of_c1 {m k : ℕ} (hm : C1 m) (hk : C1 k)
    (A : Config m) (B : Config k) (u : Space) (hu : u ≠ 0) :
    ∃ R₀ : ℝ, ∀ R > R₀, ∃ pR : Config (m+k),
      pR.point = points A B (R • u) ∘ finSumFinEquiv.symm ∧
      Nonempty (LiftFamily pR) ∧
      ∀ K : LiftFamily pR, LinearIndependent ℂ (pointForm K) :=
  two_cluster_extension A B (hm A).2 (hk B).2 u hu

end Atiyah.TwoCluster
