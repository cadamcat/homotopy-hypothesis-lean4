import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapS
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapStrictMonoOn

/-!
# `dprismHom`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The map of derived cylinders induced by a face map. -/
def dprismHom {k l : ℕ} {t : Fin (k + 1) → Fin (l + 1)} (ht : StrictMono t) :
    (dprismComplex k).Hom (dprismComplex l) where
  f := PV.map t
  strictMonoOn := PV.map_strictMonoOn ht
  map_S := PV.map_S ht
