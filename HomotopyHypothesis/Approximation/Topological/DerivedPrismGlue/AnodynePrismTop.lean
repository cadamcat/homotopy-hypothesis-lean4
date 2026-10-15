import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismGluing.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismTop

/-!
# `anodyne_prismTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The prism collapses onto its end `W''` relative to the prism over `J`**: `W'' ⊔_{J''} P J ⟶ P W`
is anodyne. It is the composite of a pushout of `W'' ⊔_{J''} D J' ⟶ D W'` and a pushout of
`W' ⊔_{J'} D J ⟶ D W` (`anodyne_dprismLan_rel` for `J' ⊆ W'` and `J ⊆ W`). Frozen helper
statement. -/
theorem anodyne_prismTop (W : SemiSSet.{u}) (J : Subfunctor W) (hW : W.IsFinite) :
    anodyne (pushout.desc (prismTop.app W) (prismP.map J.ι) (prismTop.naturality J.ι) :
      pushout ((sdLan ⋙ sdLan).map J.ι) (prismTop.app J.toFunctor) ⟶ prismP.obj W) := by apply @_root_.HomotopyHypothesis.Approximation.PrismGluing.anodyne_prismTop_proof <;> assumption
