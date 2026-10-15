import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Topology.CarrierHomotopy.CarrierHomotopy
import HomotopyHypothesis.Approximation.PrismComposition.SubdivisionPrismComposition
import HomotopyHypothesis.Approximation.Zeeman.CollarHomotopy
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.DerivedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.GlobalStars
import HomotopyHypothesis.Approximation.Zeeman.PointwiseCarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.RelativeCollar
import HomotopyHypothesis.Approximation.Zeeman.RelativeComplex
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.SimplicialRestriction
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionComposition
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.VertexStarApproximationStatement
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Assembly of relative simplicial approximation

For a full subcomplex, the collar and exterior star choices combine with
simplicial star gluing. The collar homotopy compares this approximation
with the original map. An initial relative derived subdivision makes the
retained subcomplex full, reducing the general case to this construction.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The composite retained map projects to its retained map in the intermediate subdivision. -/
theorem compositeSubdivisionRetainedMap_realization_hom {K : SemiSSet.{u}} {L : Subfunctor K}
    (S₁ : RelSubdivision K L) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    realization.map (compositeSubdivisionRetainedMap S₁ S₂) ≫ S₂.h.hom = realization.map S₁.j := by
  unfold compositeSubdivisionRetainedMap
  calc
    realization.map (Subfunctor.toRange S₁.j ≫ S₂.j) ≫ S₂.h.hom =
        realization.map (Subfunctor.toRange S₁.j) ≫ (realization.map S₂.j ≫ S₂.h.hom) := by
      rw [Functor.map_comp, Category.assoc]
    _ = realization.map (Subfunctor.toRange S₁.j) ≫
        realization.map (Subfunctor.range S₁.j).ι := by rw [S₂.hj]
    _ = realization.map S₁.j := by rw [← Functor.map_comp, Subfunctor.toRange_ι]

/-- The composite retained map and the last retained map have the same realized image. -/
theorem compositeSubdivisionRetainedMap_realization_range {K : SemiSSet.{u}} {L : Subfunctor K}
    (S₁ : RelSubdivision K L) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    Set.range (realization.map (compositeSubdivisionRetainedMap S₁ S₂)).hom =
      Set.range (realization.map S₂.j).hom := by
  have : Mono (compositeSubdivisionRetainedMap S₁ S₂) := compositeSubdivisionRetainedMap_mono S₁ S₂
  have : Mono S₂.j := S₂.mono_j
  calc
    Set.range (realization.map (compositeSubdivisionRetainedMap S₁ S₂)).hom =
        Set.range (realization.map (Subfunctor.range (compositeSubdivisionRetainedMap S₁ S₂)).ι).hom :=
      realization_range_of_mono _
    _ = Set.range (realization.map (Subfunctor.range S₂.j).ι).hom := by
      rw [compositeSubdivisionRetainedMap_range]
    _ = Set.range (realization.map S₂.j).hom := (realization_range_of_mono S₂.j).symm

/-- A realized map factors through the range before any postcomposition. -/
theorem realization_toRange_factor {J W M : SemiSSet.{u}} (j : J ⟶ W)
    (F : realization.obj W ⟶ realization.obj M) :
    realization.map j ≫ F = realization.map (Subfunctor.toRange j) ≫
      (realization.map (Subfunctor.range j).ι ≫ F) := by
  rw [← Category.assoc, ← Functor.map_comp, Subfunctor.toRange_ι]

/-- Star gluing and pointwise carrier homotopies give relative approximation when L is full. -/
theorem exists_full_relSubdivision_simplicialApproximation
    (hSA : VertexStarApproximationStatement.{u}) (hPH : PointwiseCarrierHomotopyStatement.{u})
    {K M : SemiSSet.{u}} (hK : K.IsFinite) (hKs : K.IsSimplicialComplex)
    (hM : M.IsFinite) (hMs : M.IsSimplicialComplex) (L : Subfunctor K)
    (hfull : IsFullSubcomplex L) (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    ∃ (S : RelSubdivision K L) (g : realization.obj S.Y' ⟶ realization.obj M),
      IsSimplicial g ∧ realization.map S.j ≫ g = realization.map L.ι ≫ f ∧
        g.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) := by
  obtain ⟨r, q, hq⟩ := exists_relativeCollar_vertexStarMap hK hKs L hfull f hL
  let S₀ := derivedSubdivision hK hKs L
  let T := derivedSubdivisionIterate S₀.finite (derivedSubdivision_isSimplicialComplex hK hKs L)
    (Subfunctor.range S₀.j) r
  let S := composeRelSubdivision Approximation.PrismComposition.subdivisionPrismCompositionStatement_proof S₀ T
  let c : realization.obj S₀.Y' ⟶ realization.obj K := relativeCollarMap hKs L
  let F : realization.obj S.Y' ⟶ realization.obj M := T.h.hom ≫ c ≫ f
  have : Mono S.j := S.mono_j
  have hc : realization.map S₀.j ≫ c = realization.map L.ι := relativeCollarMap_retained hKs L
  have hintermediate : realization.map S.j ≫ T.h.hom = realization.map S₀.j :=
    compositeSubdivisionRetainedMap_realization_hom S₀ T
  have hFj : realization.map S.j ≫ F = realization.map L.ι ≫ f := by
    calc
      realization.map S.j ≫ F =
          (realization.map S.j ≫ T.h.hom) ≫ c ≫ f :=
        (Category.assoc (realization.map S.j) T.h.hom (c ≫ f)).symm
      _ = realization.map S₀.j ≫ c ≫ f := congrArg (fun p => p ≫ c ≫ f) hintermediate
      _ = realization.map L.ι ≫ f :=
        (Category.assoc (realization.map S₀.j) c f).symm.trans (congrArg (fun p => p ≫ f) hc)
  have hFJ : IsSimplicial (realization.map (Subfunctor.range S.j).ι ≫ F) :=
    isSimplicial_range_restriction S.j F (by rw [hFj]; exact hL)
  obtain ⟨g, hgs, hgJ, hgRel⟩ := hSA hPH (W := S.Y') hM hMs F q hq (Subfunctor.range S.j) hFJ
  have hgj : realization.map S.j ≫ g = realization.map L.ι ≫ f := by
    calc
      realization.map S.j ≫ g = realization.map (Subfunctor.toRange S.j) ≫
          (realization.map (Subfunctor.range S.j).ι ≫ g) := realization_toRange_factor S.j g
      _ = realization.map (Subfunctor.toRange S.j) ≫
          (realization.map (Subfunctor.range S.j).ι ≫ F) :=
        congrArg (fun p => realization.map (Subfunctor.toRange S.j) ≫ p) hgJ
      _ = realization.map S.j ≫ F := (realization_toRange_factor S.j F).symm
      _ = realization.map L.ι ≫ f := hFj
  have hgRel' : g.hom.HomotopicRel F.hom (Set.range (realization.map S.j).hom) :=
    (realization_range_of_mono S.j).symm ▸ hgRel
  have hcarrier := (relativeCollarMap_homotopicRel
    Topology.CarrierHomotopy.carrierHomotopyStatement_proof hK hKs L).symm
  have hmaps : Set.MapsTo T.h.hom.hom (Set.range (realization.map S.j).hom)
      (Set.range (realization.map (relativeDerivedInclusion hKs L)).hom) := by
    rintro z ⟨a, rfl⟩
    exact ⟨a, (congrArg (fun e => e.hom a) hintermediate).symm⟩
  have hpre := homotopicRel_precomp hcarrier T.h.hom.hom
    (Set.range (realization.map S.j).hom) hmaps
  have hcompare := hpre.comp_continuousMap f.hom
  change F.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) at hcompare
  exact ⟨S, g, hgs, hgj, hgRel'.trans hcompare⟩

/-- Star gluing and pointwise carrier homotopies give relative approximation for any subcomplex. -/
theorem zeeman_relativeApproximation_of_starApproximation
    (hSA : VertexStarApproximationStatement.{u}) (hPH : PointwiseCarrierHomotopyStatement.{u})
    {K M : SemiSSet.{u}} (hK : K.IsFinite) (hKs : K.IsSimplicialComplex)
    (hM : M.IsFinite) (hMs : M.IsSimplicialComplex) (L : Subfunctor K)
    (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    ∃ (S : RelSubdivision K L) (g : realization.obj S.Y' ⟶ realization.obj M),
      IsSimplicial g ∧ realization.map S.j ≫ g = realization.map L.ι ≫ f ∧
        g.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) := by
  let S₁ := derivedSubdivision hK hKs L
  have hfull := derivedSubdivision_retained_isFull hK hKs L
  have hF := isSimplicial_subdivision_retained S₁ f hL
  obtain ⟨S₂, g, hgs, hgj, hgRel⟩ := exists_full_relSubdivision_simplicialApproximation
    hSA hPH S₁.finite (derivedSubdivision_isSimplicialComplex hK hKs L) hM hMs
    (Subfunctor.range S₁.j) hfull (S₁.h.hom ≫ f) hF
  let S := composeRelSubdivision Approximation.PrismComposition.subdivisionPrismCompositionStatement_proof S₁ S₂
  have hgj' : realization.map S.j ≫ g = realization.map L.ι ≫ f := by
    calc
      realization.map S.j ≫ g = realization.map (Subfunctor.toRange S₁.j) ≫
          (realization.map S₂.j ≫ g) := by
        change realization.map (Subfunctor.toRange S₁.j ≫ S₂.j) ≫ g = _
        rw [Functor.map_comp, Category.assoc]
      _ = realization.map (Subfunctor.toRange S₁.j) ≫
          (realization.map (Subfunctor.range S₁.j).ι ≫ (S₁.h.hom ≫ f)) := by rw [hgj]
      _ = realization.map L.ι ≫ f := by
        simp only [← Category.assoc]
        rw [← Functor.map_comp, Subfunctor.toRange_ι, S₁.hj]
  have hrange : Set.range (realization.map S.j).hom = Set.range (realization.map S₂.j).hom :=
    compositeSubdivisionRetainedMap_realization_range S₁ S₂
  rw [← hrange] at hgRel
  change g.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) at hgRel
  exact ⟨S, g, hgs, hgj', hgRel⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_full_relSubdivision_simplicialApproximation
#print axioms HomotopyHypothesis.Approximation.Zeeman.zeeman_relativeApproximation_of_starApproximation
