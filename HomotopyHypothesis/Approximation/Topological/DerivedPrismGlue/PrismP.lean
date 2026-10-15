import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism

/-!
# `prismP`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The prism `P W = D W ⊔_{W'} D W'`. -/
noncomputable def prismP : SemiSSet.{u} ⥤ SemiSSet.{u} where
  obj W := pushout (sdLanToDprism.app W) (dprismLanTop.app (sdLan.obj W))
  map {W V} φ := pushout.map _ _ _ _ (dprismLan.map φ) (dprismLan.map (sdLan.map φ))
    (sdLan.map φ) (sdLanToDprism.naturality φ).symm (dprismLanTop.naturality (sdLan.map φ)).symm
  map_id W := by
    apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    apply pushout.hom_ext <;>
      simp only [pushout.inl_desc, pushout.inr_desc, pushout.inl_desc_assoc,
        pushout.inr_desc_assoc, Functor.map_comp, Category.assoc]
