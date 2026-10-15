import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP

/-!
# `prismTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The end `W''` of the prism. -/
noncomputable def prismTop : sdLan.{u} ⋙ sdLan.{u} ⟶ prismP.{u} where
  app W := sdLanToDprism.app (sdLan.obj W) ≫ pushout.inr _ _
  naturality {W V} φ := by
    dsimp only [prismP, Functor.comp_map]
    rw [Category.assoc, pushout.inr_desc, ← Category.assoc, ← Category.assoc,
      sdLanToDprism.naturality (sdLan.map φ)]
