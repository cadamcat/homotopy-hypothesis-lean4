import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapS
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapStrictMonoOn
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism

/-!
# `sdToDprismCos`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived end of the derived cylinders. -/
noncomputable def sdToDprismCos : sdCos.{u} ⟶ dprismCos.{u} where
  app x := (sdToDprism x.obj.len).toSemiSSet
  naturality _ _ θ := by
    let χ : (sdComplex _).Hom (dprismComplex _) :=
      { f := PV.map _
        strictMonoOn := fun A (hA : (sdComplex _).S A) =>
          PV.map_strictMonoOn (SemiSimplexCategory.strictMono θ) A hA.1
        map_S := fun A (hA : (sdComplex _).S A) =>
          PV.map_S (SemiSimplexCategory.strictMono θ) A hA.1 }
    change (Complex.Hom.toSemiSSet _) ≫ _ = _ ≫ Complex.Hom.toSemiSSet _
    rw [← Complex.Hom.toSemiSSet_comp _ _ χ rfl, ← Complex.Hom.toSemiSSet_comp _ _ χ rfl]
