import Atiyah.SingularBoundary
import Atiyah.SingularFamily

/-!
# A singular planar configuration of 84 points

This specializes the reported singular family to m=1, with 52 lower axial
points, two off-axis points, and 30 upper axial points. All geometric,
algebraic, arithmetic, and analytic premises are discharged by the imported
theorems. In particular, the endpoint sign is not a hypothesis here.
-/
noncomputable section
namespace Atiyah.SingularCounterexample
open Configuration

/-- An actual distinct 84-point configuration whose point forms are dependent
for every physical Hopf lift family. Lift existence is included explicitly. -/
theorem exists_singular_config :
    ∃ p : Config 84, Nonempty (LiftFamily p) ∧
      ∀ L : LiftFamily p, ¬ LinearIndependent ℂ (pointForm L) :=
  SingularFamily.exists_singular_config SingularBoundary.pathDet_one_negative

/-- The original independence assertion fails at n=84. -/
theorem not_C1_84 : ¬ C1 84 :=
  SingularFamily.not_c1_of_endpoint_neg SingularBoundary.pathDet_one_negative

/-- The singular configuration occurs at a strictly interior point of the
explicit planar path, so the limiting endpoint collisions are excluded. -/
theorem exists_singular_parameter :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∀ (ht : 0 < t) (ht1 : t < 1)
      (L : LiftFamily (SingularGeometry.config t ht ht1)),
      ¬ LinearIndependent ℂ (pointForm L) :=
  SingularFamily.exists_singular_parameter SingularBoundary.pathDet_one_negative

/-- The counterexample lies in the real planar slice of ℝ × ℂ. -/
theorem exists_singular_planar_config :
    ∃ p : Config 84, (∀ i, (p.point i).2.im = 0) ∧
      Nonempty (LiftFamily p) ∧
      ∀ L : LiftFamily p, ¬ LinearIndependent ℂ (pointForm L) := by
  obtain ⟨t, ht, h⟩ := exists_singular_parameter
  refine ⟨SingularGeometry.config t ht.1 ht.2, ?_, liftFamily_nonempty _, h ht.1 ht.2⟩
  intro i
  exact Complex.ofReal_im _

end Atiyah.SingularCounterexample
