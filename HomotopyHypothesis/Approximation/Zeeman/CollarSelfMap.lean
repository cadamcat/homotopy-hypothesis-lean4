import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.CollarHomotopy
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarNeighborhood
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeHomeomorphism
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# A collar map on the original realization

Transporting the collar vertex map along the subdivision identification
gives a self-map fixing the retained realization. For a full subcomplex,
it maps an open neighborhood into that subcomplex. A carrier homotopy
makes this self-map homotopic to the identity relative to the subcomplex.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The inverse subdivision identification takes L to its retained copy. -/
theorem relativeRealizationIso_inv_retained {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map L.ι ≫ (relativeRealizationIso hK hKs L).inv =
      realization.map (relativeDerivedInclusion hKs L) := by
  calc
    realization.map L.ι ≫ (relativeRealizationIso hK hKs L).inv =
        (realization.map (relativeDerivedInclusion hKs L) ≫
          (relativeRealizationIso hK hKs L).hom) ≫ (relativeRealizationIso hK hKs L).inv :=
      congrArg (fun e => e ≫ (relativeRealizationIso hK hKs L).inv)
        (relativeRealizationIso_retained hK hKs L).symm
    _ = realization.map (relativeDerivedInclusion hKs L) := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transport the collar vertex map to the original realization. -/
noncomputable def relativeCollarSelfMap {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj K ⟶ realization.obj K :=
  (relativeRealizationIso hK hKs L).inv ≫ relativeCollarMap hKs L

/-- The collar self-map fixes the original retained realization. -/
theorem relativeCollarSelfMap_retained {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map L.ι ≫ relativeCollarSelfMap hK hKs L = realization.map L.ι := by
  unfold relativeCollarSelfMap
  rw [← Category.assoc, relativeRealizationIso_inv_retained, relativeCollarMap_retained]

/-- A carrier homotopy makes the collar self-map homotopic to the identity relative to L. -/
theorem relativeCollarSelfMap_homotopicRel {K : SemiSSet.{u}}
    (hH : CarrierHomotopyStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (relativeCollarSelfMap hK hKs L).hom.HomotopicRel (ContinuousMap.id _)
      (Set.range (realization.map L.ι).hom) := by
  let e := relativeRealizationIso hK hKs L
  have hp : Set.MapsTo e.inv.hom (Set.range (realization.map L.ι).hom)
      (Set.range (realization.map (relativeDerivedInclusion hKs L)).hom) := by
    rintro z ⟨a, rfl⟩
    exact ⟨a, (congrArg (fun k => k.hom a)
      (relativeRealizationIso_inv_retained hK hKs L)).symm⟩
  have h := homotopicRel_precomp (relativeCollarMap_homotopicRel hH hK hKs L).symm
    e.inv.hom (Set.range (realization.map L.ι).hom) hp
  change (relativeCollarSelfMap hK hKs L).hom.HomotopicRel (e.inv ≫ e.hom).hom
    (Set.range (realization.map L.ι).hom) at h
  rw [e.inv_hom_id] at h
  exact h

/-- The collar self-map takes an open neighborhood of full L into L. -/
theorem relativeCollarSelfMap_exists_openNeighborhood {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K)
    (hL : IsFullSubcomplex L) :
    ∃ U : Set (realization.obj K), IsOpen U ∧
      Set.range (realization.map L.ι).hom ⊆ U ∧
        Set.MapsTo (relativeCollarSelfMap hK hKs L).hom U
          (Set.range (realization.map L.ι).hom) := by
  obtain ⟨U, hU, hsub, hmap⟩ := relativeCollarMap_exists_openNeighborhood hKs L hL
  let e := relativeRealizationIso hK hKs L
  refine ⟨e.inv.hom ⁻¹' U, hU.preimage e.inv.hom.continuous, ?_, ?_⟩
  · rintro z ⟨a, rfl⟩
    apply hsub
    exact ⟨a, (congrArg (fun k => k.hom a)
      (relativeRealizationIso_inv_retained hK hKs L)).symm⟩
  · intro z hz
    exact hmap hz

/-- A full finite subcomplex has a neighborhood retraction homotopic to the identity. -/
theorem exists_relativeCollarSelfMap {K : SemiSSet.{u}}
    (hH : CarrierHomotopyStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) :
    ∃ h : realization.obj K ⟶ realization.obj K,
      realization.map L.ι ≫ h = realization.map L.ι ∧
        h.hom.HomotopicRel (ContinuousMap.id _) (Set.range (realization.map L.ι).hom) ∧
          ∃ U : Set (realization.obj K), IsOpen U ∧
            Set.range (realization.map L.ι).hom ⊆ U ∧
              Set.MapsTo h.hom U (Set.range (realization.map L.ι).hom) :=
  ⟨relativeCollarSelfMap hK hKs L, relativeCollarSelfMap_retained hK hKs L,
    relativeCollarSelfMap_homotopicRel hH hK hKs L,
    relativeCollarSelfMap_exists_openNeighborhood hK hKs L hL⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSelfMap_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSelfMap_homotopicRel
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSelfMap_exists_openNeighborhood
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeCollarSelfMap
