import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57

/-!
# `dcylDBoundaryι`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

end DV

open DV

/-- The inclusion of the boundary into the derived double cylinder. -/
def dcylDBoundaryι {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    dcylDBoundary.{u} v ⟶ dcylD.{u} v :=
  Complex.Hom.toSemiSSet
    { f := id
      strictMonoOn := fun _ _ => strictMono_id.strictMonoOn _
      map_S := fun A hA => by simpa using hA.1 }
