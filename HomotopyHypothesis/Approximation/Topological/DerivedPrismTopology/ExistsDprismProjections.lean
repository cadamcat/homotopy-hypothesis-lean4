import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismHomotopy.Projections
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism

/-!
# `exists_dprismProjections`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismTopology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The projections of the derived cylinder.** Construction: on the derived cylinder of `Δ_k`,
the affine maps `‖D Δ_k‖ ⟶ ‖Δ_k‖` with vertex positions `top i ↦ i`, `mid S ↦ max S` (`pr`),
respectively `mid S ↦` barycentre of `S` (`πe`), and the straight line between them; they are
natural in face maps of `Δ_k`, hence glue over the simplices of `V` (the pointwise left Kan
extension along the Yoneda embedding, and the realization adjunction). On each derived simplex the
barycentric map is a homeomorphism `‖Δ_k'‖ ≅ ‖Δ_k‖`, natural in face maps; hence so is its glued
version. Frozen helper statement. -/
theorem exists_dprismProjections :
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
        K V' (t, (realization.map (dprismLan.map φ)).hom x) = (realization.map φ).hom (K V (t, x))) :=
  @_root_.HomotopyHypothesis.Approximation.DerivedPrismHomotopy.exists_dprismProjections_proof
