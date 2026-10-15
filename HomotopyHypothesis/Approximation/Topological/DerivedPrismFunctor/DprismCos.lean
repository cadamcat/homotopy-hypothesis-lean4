import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapComp
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapId

/-!
# `dprismCos`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived cylinders of the simplices, as a cosimplicial semi-simplicial set. -/
noncomputable def dprismCos : Henry.SemiSimplexCategory ⥤ SemiSSet.{u} where
  obj x := dprism.{u} x.obj.len
  map θ := (dprismHom (SemiSimplexCategory.strictMono θ)).toSemiSSet
  map_id x := Complex.Hom.toSemiSSet_id _ (by
    change PV.map _ = id
    convert PV.map_id
    rfl)
  map_comp θ θ' := Complex.Hom.toSemiSSet_comp _ _ _ (by
    change PV.map _ = PV.map _ ∘ PV.map _
    rw [← PV.map_comp]
    rfl)
