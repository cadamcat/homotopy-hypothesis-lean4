import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Finite.AverageContraction.FiniteAverageContraction
import HomotopyHypothesis.Approximation.Zeeman.InducedRealization
import HomotopyHypothesis.Approximation.Zeeman.InducedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.ScalarMesh
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Iterated exterior subdivisions and scalar mesh

Subdivisions induced on an exterior subcomplex remain disjoint from the
retained image at every stage and realize to the original subcomplex.
The scalar mesh bound contracts at every step, giving a power of the
uniform dimension factor for each original vertex coordinate.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The subcomplex induced at each relative derived stage by an original subcomplex. -/
noncomputable def iteratedInducedSubdivision {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L A : Subfunctor K) :
    (r : ℕ) → Subfunctor (derivedSubdivisionIterate hK hKs L r).Y'
  | 0 => A
  | r + 1 => inducedRelativeSubdivision (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)
      (iteratedInducedSubdivision hK hKs L A r)

/-- An induced exterior subcomplex stays disjoint from the retained image. -/
theorem iteratedInducedSubdivision_inf_retained {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (r : ℕ) :
    iteratedInducedSubdivision hK hKs L A r ⊓
      Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j = ⊥ := by
  induction r with
  | zero =>
    change A ⊓ Subfunctor.range L.ι = ⊥
    rw [Subfunctor.range_ι]
    exact hAL
  | succ r ih =>
    change inducedRelativeSubdivision (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
        (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)
        (iteratedInducedSubdivision hK hKs L A r) ⊓
      Subfunctor.range (Subfunctor.toRange (derivedSubdivisionIterate hK hKs L r).j ≫
        relativeDerivedInclusion (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
          (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)) = ⊥
    rw [Subfunctor.range_comp, Subfunctor.range_toRange, Subfunctor.image_top]
    exact inducedRelativeSubdivision_inf_retained
      (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r) _ _ ih

/-- The iterated induced realization is the preimage of the original subcomplex. -/
theorem iteratedInducedSubdivision_range_eq_preimage {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K) (r : ℕ) :
    Set.range (realization.map (iteratedInducedSubdivision hK hKs L A r).ι).hom =
      (derivedSubdivisionIterate hK hKs L r).h.hom.hom ⁻¹'
        Set.range (realization.map A.ι).hom := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Set.range (realization.map (inducedRelativeSubdivision
      (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)
      (iteratedInducedSubdivision hK hKs L A r)).ι).hom = _
    rw [inducedRelativeSubdivision_range_eq_preimage, ih]
    rfl

/-- The subdivision identification maps every induced stage onto the original subcomplex. -/
theorem iteratedInducedSubdivision_image_realization {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K) (r : ℕ) :
    (derivedSubdivisionIterate hK hKs L r).h.hom.hom ''
        Set.range (realization.map (iteratedInducedSubdivision hK hKs L A r).ι).hom =
      Set.range (realization.map A.ι).hom := by
  let S := derivedSubdivisionIterate hK hKs L r
  have hpre := iteratedInducedSubdivision_range_eq_preimage hK hKs L A r
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact (Set.ext_iff.mp hpre y).mp hy
  · intro z hz
    have he : S.h.hom.hom (S.h.inv.hom z) = z :=
      congrArg (fun k => k.hom z) S.h.inv_hom_id
    have hmem : S.h.inv.hom z ∈ S.h.hom.hom ⁻¹' Set.range (realization.map A.ι).hom := by
      change S.h.hom.hom (S.h.inv.hom z) ∈ Set.range (realization.map A.ι).hom
      rw [he]
      exact hz
    exact ⟨S.h.inv.hom z, (Set.ext_iff.mp hpre _).mpr hmem, he⟩

/-- Scalar diameters contract by the dimension factor at every induced exterior stage. -/
theorem iteratedInducedSubdivision_scalarMesh {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (F : realization.obj K → ℝ) (hF : IsSimplexwiseScalarAffine F)
    (c : ℝ) (hc : ScalarStarDiameterBound A F c) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n)))) (r : ℕ) :
    ScalarStarDiameterBound (iteratedInducedSubdivision hK hKs L A r)
      (F ∘ (derivedSubdivisionIterate hK hKs L r).h.hom.hom)
        (((D : ℝ) / ((D : ℝ) + 1)) ^ r * c) := by
  induction r with
  | zero =>
    change ScalarStarDiameterBound A (F ∘ id) (((D : ℝ) / ((D : ℝ) + 1)) ^ 0 * c)
    simpa only [Function.comp_id, pow_zero, one_mul] using hc
  | succ r ih =>
    let d : ℝ := (D : ℝ) / ((D : ℝ) + 1)
    have hstep := scalarStarDiameterBound_relativeRealizationMap
      Finite.AverageContraction.finiteAverageContractionStatement_proof
      (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)
      (iteratedInducedSubdivision hK hKs L A r)
      (iteratedInducedSubdivision_inf_retained hK hKs L A hAL r)
      (F ∘ (derivedSubdivisionIterate hK hKs L r).h.hom.hom)
      (isSimplexwiseScalarAffine_subdivision (derivedSubdivisionIterate hK hKs L r) F hF)
      (d ^ r * c) ih D (derivedSubdivisionIterate_dimensionBound hK hKs L D hD r)
    have he : d * (d ^ r * c) = d ^ (r + 1) * c := by rw [pow_succ]; ring
    change ScalarStarDiameterBound _ _ (d * (d ^ r * c)) at hstep
    rw [he] at hstep
    exact hstep

/-- Each original vertex coordinate has the power mesh bound on the exterior tower. -/
theorem iteratedInducedSubdivision_vertexCoordinate_mesh {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n))))
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) (r : ℕ) :
    ScalarStarDiameterBound (iteratedInducedSubdivision hK hKs L A r)
      (vertexCoordinate K w ∘ (derivedSubdivisionIterate hK hKs L r).h.hom.hom)
        (((D : ℝ) / ((D : ℝ) + 1)) ^ r) := by
  simpa only [mul_one] using iteratedInducedSubdivision_scalarMesh hK hKs L A hAL
    (vertexCoordinate K w) (vertexCoordinate_isSimplexwiseScalarAffine K w) 1
    (vertexCoordinate_starDiameterBound K A w) D hD r

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.iteratedInducedSubdivision_inf_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.iteratedInducedSubdivision_range_eq_preimage
#print axioms HomotopyHypothesis.Approximation.Zeeman.iteratedInducedSubdivision_vertexCoordinate_mesh
