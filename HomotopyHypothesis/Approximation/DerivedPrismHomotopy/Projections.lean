import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.GlobalTopRestriction
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.DerivedPrismProjection.DerivedEndIso
import HomotopyHypothesis.Approximation.DerivedPrismProjection.PerSimplexProjection
import HomotopyHypothesis.Approximation.DerivedPrismHomotopy.RelativeHomotopy
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
/-!
# Projections of the derived cylinder
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismHomotopy

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Approximation.DerivedPrismProjection HomotopyHypothesis.Henry
  HomotopyHypothesis.Henry.SemiSSet

/-- The last-vertex and barycentric projections of the derived cylinder, with their natural
homotopy relative to the top end. -/
theorem exists_dprismProjections_proof :
    ∃ (pr πe : dprismLan.{u} ⋙ realization ⟶ realization)
      (K : ∀ V : SemiSSet.{u}, ContinuousMap.HomotopyRel (pr.app V).hom (πe.app V).hom
        (Set.range (realization.map (dprismLanTop.app V)).hom)),
      (∀ V : SemiSSet.{u}, realization.map (dprismLanTop.app V) ≫ pr.app V = 𝟙 _) ∧
      (∀ V : SemiSSet.{u}, realization.map (dprismLanTop.app V) ≫ πe.app V = 𝟙 _) ∧
      (∀ (V : SemiSSet.{u}) (n : ℕ)
        (z : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ dprismLan.obj V),
        ∃ (m : ℕ) (w : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ V)
          (v : Fin (n + 1) → Fin (m + 1)), simplexChar z ≫ pr.app V = vertexMap v ≫ simplexChar w) ∧
      (∀ (V : SemiSSet.{u}) (n : ℕ)
        (z : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ sdLan.obj V),
        ∃ (m : ℕ) (w : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ V)
          (le : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
            toTop.obj (Henry.SemiSimplexCategory.mk m))
          (v : Fin (n + 1) → Fin (m + 1)),
          IsLinearEmbedding le ∧
            simplexChar z ≫ realization.map (sdLanToDprism.app V) ≫ πe.app V =
              le ≫ simplexChar w ∧
            simplexChar z ≫ realization.map (sdLanToDprism.app V) ≫ pr.app V =
              vertexMap v ≫ simplexChar w) ∧
      (∀ V : SemiSSet.{u}, IsIso (realization.map (sdLanToDprism.app V) ≫ πe.app V)) ∧
      (∀ {V V' : SemiSSet.{u}} (φ : V ⟶ V') (t : unitInterval)
        (x : realization.obj (dprismLan.obj V)),
        K V' (t, (realization.map (dprismLan.map φ)).hom x) = (realization.map φ).hom (K V (t, x))) := by
  refine ⟨dprismLanLastVertexProjection.{u}, dprismLanProjection.{u},
    dprismProjectionHomotopy.{u}, dprismLanLastVertexProjection_top.{u},
    dprismLanProjection_top.{u}, ?_, ?_, ?_, ?_⟩
  · intro V n z
    exact exists_dprismLan_simplex_lastVertex z
  · intro V n z
    exact exists_sdLan_simplex_projections z
  · intro V
    exact sdLanBarycentricProjection_isIso V
  · intro V W f t x
    exact dprismProjectionHomotopy_naturality f t x

#print axioms exists_dprismProjections_proof

end HomotopyHypothesis.Approximation.DerivedPrismHomotopy
