import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopCos

/-!
# `dprismLanTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The top end `W ⟶ D W`. -/
noncomputable def dprismLanTop : Functor.id SemiSSet.{u} ⟶ dprismLan.{u} :=
  haveI : (Functor.id SemiSSet.{u}).IsLeftKanExtension
      (Iso.refl (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits.{u} (Functor.id SemiSSet.{u})
      (Iso.refl (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u}))
  (Functor.id SemiSSet.{u}).descOfIsLeftKanExtension
    (Iso.refl (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom
    dprismLan.{u}
    (dprismTopCos.{u} ≫ Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
