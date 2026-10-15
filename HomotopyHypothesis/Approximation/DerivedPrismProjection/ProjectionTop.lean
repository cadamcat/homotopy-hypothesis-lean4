import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.GlobalTopRestriction
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
/-!
# The top end of the derived-cylinder projections
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismProjection

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem dprismProjections_top_identities (V : SemiSSet.{u}) :
    realization.{u}.map (dprismLanTop.{u}.app V) ≫
        dprismLanLastVertexProjection.{u}.app V = 𝟙 _ ∧
      realization.{u}.map (dprismLanTop.{u}.app V) ≫
        dprismLanProjection.{u}.app V = 𝟙 _ := by
  exact ⟨dprismLanLastVertexProjection_top.{u} V, dprismLanProjection_top.{u} V⟩

end HomotopyHypothesis.Approximation.DerivedPrismProjection
