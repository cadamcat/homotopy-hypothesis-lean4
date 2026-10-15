import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.MixedDistributions
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativeHomeomorphism
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Projection of the mixed relative prism

The vertex-distribution embedding lifts mixed distributions to the original
realization. The lift restricts to the identity on the original end and to
the affine subdivision map on the derived end. Composing with the inverse
subdivision isomorphism gives the required prism projection.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Choose the original point represented by a mixed distribution. -/
noncomputable def mixedRealizationPoint {K : SemiSSet.{u}} (hK : K.IsFinite)
    (L : Subfunctor K) (z : realization.obj (mixedFlags K L)) : realization.obj K :=
  Classical.choose (mixedDistributionMap_mem_range hK L z)

/-- The chosen original point has the prescribed mixed distribution. -/
theorem mixedRealizationPoint_distribution {K : SemiSSet.{u}} (hK : K.IsFinite)
    (L : Subfunctor K) (z : realization.obj (mixedFlags K L)) :
    (vertexDistributionMap K).hom (mixedRealizationPoint hK L z) =
      (mixedDistributionMap hK L).hom z :=
  Classical.choose_spec (mixedDistributionMap_mem_range hK L z)

/-- The embedding of original distributions makes the lift continuous. -/
theorem mixedRealizationPoint_continuous {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    Continuous (mixedRealizationPoint hK L) := by
  have he := (Realization.ComplexTopology.complexRealizationTopologyStatement_proof K hK hKs).2
  apply he.isEmbedding.continuous_iff.mpr
  have hd : (vertexDistributionMap K).hom ∘ mixedRealizationPoint hK L =
      (mixedDistributionMap hK L).hom :=
    funext (mixedRealizationPoint_distribution hK L)
  rw [hd]
  exact (mixedDistributionMap hK L).hom.continuous

/-- The continuous geometric map from the mixed prism to the original realization. -/
noncomputable def mixedRealizationMap {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj (mixedFlags K L) ⟶ realization.obj K :=
  TopCat.ofHom ⟨mixedRealizationPoint hK L, mixedRealizationPoint_continuous hK hKs L⟩

/-- The affine distribution on the derived end is the previously defined derived distribution. -/
theorem mixedDistributionAffineMap_derived {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    mixedDistributionAffineMap
      ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n)) a) =
        relativeDistributionAffineMap a := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [mixedDistributionAffineMap, relativeDistributionAffineMap,
    StdSimplex.affineMapMk_single]
  exact mixedVertexDistribution_derived (a.val i)

/-- The affine distribution on an original simplex is its original vertex distribution. -/
theorem mixedDistributionAffineMap_original {K : SemiSSet.{u}}
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    mixedDistributionAffineMap
      ((mixedOriginalInclusion hKs L).app (op (Henry.SemiSimplexCategory.mk n)) x) =
        StdSimplex.affineMap (R := ℝ) (vertex x) := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [mixedDistributionAffineMap, StdSimplex.affineMapMk_single,
    StdSimplex.coe_affineMap, StdSimplex.map_single]
  exact mixedVertexDistribution_original (vertex x i)

/-- Mixed distributions restrict to the original distributions of the derived realization. -/
theorem mixedDistributionMap_derived {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedDerivedInclusion L) ≫ mixedDistributionMap hK L =
      relativeRealizationMap hKs L ≫ vertexDistributionMap K := by
  apply realization_hom_ext
  intro n a
  rw [← Category.assoc, simplexChar_postcomp]
  apply ConcreteCategory.hom_ext
  intro t
  change (mixedDistributionMap hK L).hom
    ((simplexChar (uliftYonedaEquiv.symm
      ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n)) a))).hom t) =
    (vertexDistributionMap K).hom ((relativeRealizationMap hKs L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom t))
  erw [mixedDistributionMap_simplex_apply, relativeRealizationMap_distribution_simplex_apply]
  exact DFunLike.congr_fun (mixedDistributionAffineMap_derived a) t.down

/-- Mixed distributions restrict to the original vertex-distribution map on the original end. -/
theorem mixedDistributionMap_original {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedOriginalInclusion hKs L) ≫ mixedDistributionMap hK L =
      vertexDistributionMap K := by
  apply realization_hom_ext
  intro n x
  rw [← Category.assoc, simplexChar_postcomp]
  apply ConcreteCategory.hom_ext
  intro t
  change (mixedDistributionMap hK L).hom
    ((simplexChar (uliftYonedaEquiv.symm
      ((mixedOriginalInclusion hKs L).app (op (Henry.SemiSimplexCategory.mk n)) x))).hom t) =
    (vertexDistributionMap K).hom ((simplexChar (uliftYonedaEquiv.symm x)).hom t)
  erw [mixedDistributionMap_simplex_apply, vertexDistributionMap_simplex_apply]
  exact DFunLike.congr_fun (mixedDistributionAffineMap_original hKs L x) t.down

/-- The geometric mixed map restricts to the affine subdivision map at the derived end. -/
theorem mixedRealizationMap_derived {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedDerivedInclusion L) ≫ mixedRealizationMap hK hKs L =
      relativeRealizationMap hKs L := by
  apply ConcreteCategory.hom_ext
  intro z
  apply vertexDistributionMap_injective hKs
  exact (mixedRealizationPoint_distribution hK L
    ((realization.map (mixedDerivedInclusion L)).hom z)).trans
      (congrArg (fun f => f.hom z) (mixedDistributionMap_derived hK hKs L))

/-- The geometric mixed map is the identity at the original end. -/
theorem mixedRealizationMap_original {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedOriginalInclusion hKs L) ≫ mixedRealizationMap hK hKs L = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro z
  apply vertexDistributionMap_injective hKs
  exact (mixedRealizationPoint_distribution hK L
    ((realization.map (mixedOriginalInclusion hKs L)).hom z)).trans
      (congrArg (fun f => f.hom z) (mixedDistributionMap_original hK hKs L))

/-- Project the mixed prism onto its derived end. -/
noncomputable def mixedPrismProjection {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj (mixedFlags K L) ⟶ realization.obj (relativeDerived K L) :=
  mixedRealizationMap hK hKs L ≫ (relativeRealizationIso hK hKs L).inv

/-- The prism projection is a retraction onto the derived end. -/
theorem mixedPrismProjection_derived {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedDerivedInclusion L) ≫ mixedPrismProjection hK hKs L = 𝟙 _ := by
  unfold mixedPrismProjection
  rw [← Category.assoc, mixedRealizationMap_derived]
  exact (relativeRealizationIso hK hKs L).hom_inv_id

/-- The original end projects by the inverse subdivision identification. -/
theorem mixedPrismProjection_original {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (mixedOriginalInclusion hKs L) ≫ mixedPrismProjection hK hKs L =
      (relativeRealizationIso hK hKs L).inv := by
  unfold mixedPrismProjection
  rw [← Category.assoc, mixedRealizationMap_original, Category.id_comp]

/-- An anodyne derived-end inclusion completes the relative subdivision data. -/
noncomputable def relativeDerivedSubdivisionOfCollapse {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K)
    (hc : anodyne (mixedDerivedInclusion L)) : RelSubdivision K L where
  Y' := relativeDerived K L
  finite := relativeDerived_isFinite hK L
  h := relativeRealizationIso hK hKs L
  linear := relativeRealizationIso_linear hK hKs L
  j := relativeDerivedInclusion hKs L
  mono_j := relativeDerivedInclusion_mono hKs L
  hj := relativeRealizationIso_retained hK hKs L
  C := mixedFlags K L
  c₀ := mixedDerivedInclusion L
  c₁ := mixedOriginalInclusion hKs L
  hc := mixedInclusions_agree hKs L
  anodyne_c₀ := hc
  ρ := mixedPrismProjection hK hKs L
  hρ₀ := mixedPrismProjection_derived hK hKs L
  hρ₁ := mixedPrismProjection_original hK hKs L

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedPrismProjection_derived
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedPrismProjection_original
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerivedSubdivisionOfCollapse
