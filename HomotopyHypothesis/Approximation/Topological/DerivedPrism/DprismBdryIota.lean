import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdry
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `dprismBdryι`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrism`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace PV

variable {k : ℕ}

end PV

open PV

/-- The inclusion of `dprismBdry k` into the derived cylinder. -/
def dprismBdryι (k : ℕ) : dprismBdry.{u} k ⟶ dprism.{u} k :=
  Complex.Hom.toSemiSSet
    { f := id
      strictMonoOn := fun _ _ => strictMono_id.strictMonoOn _
      map_S := fun A hA => by simpa using hA.1 }
