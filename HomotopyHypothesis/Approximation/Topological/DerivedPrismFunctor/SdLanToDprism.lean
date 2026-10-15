import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos

/-!
# `sdLanToDprism`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived end `W' ⟶ D W`. -/
noncomputable def sdLanToDprism : sdLan.{u} ⟶ dprismLan.{u} :=
  sdLan.{u}.descOfIsLeftKanExtension (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
    dprismLan.{u}
    (sdToDprismCos.{u} ≫ Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
