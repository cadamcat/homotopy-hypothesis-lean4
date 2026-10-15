import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapComp
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapId
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdHom

/-!
# `sdCos`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived simplices, as a cosimplicial semi-simplicial set. -/
noncomputable def sdCos : Henry.SemiSimplexCategory ⥤ SemiSSet.{u} where
  obj x := (sdComplex x.obj.len).toSemiSSet
  map θ := (sdHom (SemiSimplexCategory.strictMono θ)).toSemiSSet
  map_id x := Complex.Hom.toSemiSSet_id _ (by
    change PV.map _ = id
    convert PV.map_id
    rfl)
  map_comp θ θ' := Complex.Hom.toSemiSSet_comp _ _ _ (by
    change PV.map _ = PV.map _ ∘ PV.map _
    rw [← PV.map_comp]
    rfl)
