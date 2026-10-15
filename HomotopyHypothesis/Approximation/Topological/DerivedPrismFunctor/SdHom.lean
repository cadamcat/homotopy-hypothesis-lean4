import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapS
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapStrictMonoOn
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex

/-!
# `sdHom`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The map of derived simplices induced by a face map. -/
def sdHom {k l : ℕ} {t : Fin (k + 1) → Fin (l + 1)} (ht : StrictMono t) :
    (sdComplex k).Hom (sdComplex l) where
  f := PV.map t
  strictMonoOn A hA := PV.map_strictMonoOn ht A hA.1
  map_S A hA := ⟨PV.map_S ht A hA.1, fun i h => by
    simp only [Finset.mem_image] at h
    obtain ⟨a, ha, he⟩ := h
    cases a with
    | top j => exact hA.2 j ha
    | mid S => cases he⟩
