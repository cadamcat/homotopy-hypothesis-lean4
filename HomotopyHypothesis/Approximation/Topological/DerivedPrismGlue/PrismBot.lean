import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP

/-!
# `prismBot`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The end `W` of the prism. -/
noncomputable def prismBot : 𝟭 SemiSSet.{u} ⟶ prismP.{u} where
  app W := dprismLanTop.app W ≫ pushout.inl _ _
  naturality {W V} φ := by
    dsimp only [prismP]
    rw [Category.assoc, pushout.inl_desc, ← Category.assoc, ← Category.assoc,
      ← dprismLanTop.naturality φ]
