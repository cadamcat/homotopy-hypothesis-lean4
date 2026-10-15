import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Topology.CarrierHomotopy.CarrierHomotopy
import HomotopyHypothesis.Approximation.Zeeman.CollarHomotopy
import HomotopyHypothesis.Approximation.Zeeman.CollarSelfMap
import HomotopyHypothesis.Approximation.Zeeman.DerivedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
/-!
# Relative neighborhood collars

The full retained subcomplex of a relative derived subdivision has a
neighborhood collar homotopic to the identity. Transporting it through
the subdivision identification gives such a collar for the original
subcomplex, without requiring that subcomplex to be full.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A monomorphism and its range inclusion have the same realized image. -/
theorem realization_range_of_mono {A B : SemiSSet.{u}} (f : A ⟶ B) [Mono f] :
    Set.range (realization.map f).hom =
      Set.range (realization.map (Subfunctor.range f).ι).hom := by
  let e := asIso (realization.map (Subfunctor.toRange f))
  have hf : realization.map f = e.hom ≫ realization.map (Subfunctor.range f).ι := by
    change realization.map f = realization.map (Subfunctor.toRange f) ≫
      realization.map (Subfunctor.range f).ι
    rw [← Functor.map_comp, Subfunctor.toRange_ι]
  rw [hf]
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨e.hom.hom x, rfl⟩
  · rintro z ⟨x, rfl⟩
    refine ⟨e.inv.hom x, ?_⟩
    exact congrArg (fun k => k.hom x) (e.inv_hom_id_assoc
      (realization.map (Subfunctor.range f).ι))

/-- The inverse subdivision identification carries the original retained inclusion to its copy. -/
theorem subdivision_inv_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) :
    realization.map L.ι ≫ S.h.inv = realization.map S.j := by
  calc
    realization.map L.ι ≫ S.h.inv = (realization.map S.j ≫ S.h.hom) ≫ S.h.inv :=
      congrArg (fun k => k ≫ S.h.inv) S.hj.symm
    _ = realization.map S.j := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The subdivision identification maps the full retained image into the original subcomplex. -/
theorem subdivision_hom_maps_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) :
    Set.MapsTo S.h.hom.hom (Set.range (realization.map (Subfunctor.range S.j).ι).hom)
      (Set.range (realization.map L.ι).hom) := by
  have : Mono S.j := S.mono_j
  rw [← realization_range_of_mono S.j]
  rintro z ⟨x, rfl⟩
  exact ⟨x, (congrArg (fun k => k.hom x) S.hj).symm⟩

/-- The inverse identification maps the original retained realization into its full image. -/
theorem subdivision_inv_maps_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) :
    Set.MapsTo S.h.inv.hom (Set.range (realization.map L.ι).hom)
      (Set.range (realization.map (Subfunctor.range S.j).ι).hom) := by
  have : Mono S.j := S.mono_j
  rw [← realization_range_of_mono S.j]
  rintro z ⟨x, rfl⟩
  exact ⟨x, (congrArg (fun k => k.hom x) (subdivision_inv_retained S)).symm⟩

/-- Conjugate the full-subcomplex collar by a subdivision identification. -/
noncomputable def subdivisionCollarSelfMap {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) (hS : S.Y'.IsSimplicialComplex) :
    realization.obj K ⟶ realization.obj K :=
  S.h.inv ≫ relativeCollarSelfMap S.finite hS (Subfunctor.range S.j) ≫ S.h.hom

/-- The transported collar fixes the original retained inclusion. -/
theorem subdivisionCollarSelfMap_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) (hS : S.Y'.IsSimplicialComplex) :
    realization.map L.ι ≫ subdivisionCollarSelfMap S hS = realization.map L.ι := by
  have hj : realization.map S.j ≫ relativeCollarSelfMap S.finite hS
      (Subfunctor.range S.j) = realization.map S.j := by
    calc
      realization.map S.j ≫ relativeCollarSelfMap S.finite hS (Subfunctor.range S.j) =
          realization.map (Subfunctor.toRange S.j) ≫
            (realization.map (Subfunctor.range S.j).ι ≫
              relativeCollarSelfMap S.finite hS (Subfunctor.range S.j)) := by
                rw [← Category.assoc, ← Functor.map_comp, Subfunctor.toRange_ι]
      _ = realization.map (Subfunctor.toRange S.j) ≫
          realization.map (Subfunctor.range S.j).ι := by rw [relativeCollarSelfMap_retained]
      _ = realization.map S.j := by rw [← Functor.map_comp, Subfunctor.toRange_ι]
  unfold subdivisionCollarSelfMap
  rw [← Category.assoc, subdivision_inv_retained, ← Category.assoc, hj]
  exact S.hj

/-- The transported collar is homotopic to the identity relative to the original subcomplex. -/
theorem subdivisionCollarSelfMap_homotopicRel {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) (hS : S.Y'.IsSimplicialComplex) :
    (subdivisionCollarSelfMap S hS).hom.HomotopicRel (ContinuousMap.id _)
      (Set.range (realization.map L.ι).hom) := by
  have h := relativeCollarSelfMap_homotopicRel Topology.CarrierHomotopy.carrierHomotopyStatement_proof
    S.finite hS (Subfunctor.range S.j)
  have hp := homotopicRel_precomp h S.h.inv.hom (Set.range (realization.map L.ι).hom)
    (subdivision_inv_maps_retained S)
  have hc := hp.comp_continuousMap S.h.hom.hom
  change (subdivisionCollarSelfMap S hS).hom.HomotopicRel (S.h.inv ≫ S.h.hom).hom
    (Set.range (realization.map L.ι).hom) at hc
  rw [S.h.inv_hom_id] at hc
  exact hc

/-- A full retained image gives an open neighborhood mapped into the original subcomplex. -/
theorem subdivisionCollarSelfMap_exists_openNeighborhood {K : SemiSSet.{u}}
    {L : Subfunctor K} (S : RelSubdivision K L) (hS : S.Y'.IsSimplicialComplex)
    (hfull : IsFullSubcomplex (Subfunctor.range S.j)) :
    ∃ U : Set (realization.obj K), IsOpen U ∧ Set.range (realization.map L.ι).hom ⊆ U ∧
      Set.MapsTo (subdivisionCollarSelfMap S hS).hom U (Set.range (realization.map L.ι).hom) := by
  obtain ⟨U, hU, hsub, hmap⟩ := relativeCollarSelfMap_exists_openNeighborhood
    S.finite hS (Subfunctor.range S.j) hfull
  refine ⟨S.h.inv.hom ⁻¹' U, hU.preimage S.h.inv.hom.continuous, ?_, ?_⟩
  · exact fun z hz => hsub (subdivision_inv_maps_retained S hz)
  · exact fun z hz => subdivision_hom_maps_retained S (hmap hz)

/-- Every subcomplex of a finite ordered complex has a relative neighborhood collar. -/
theorem exists_relativeNeighborhoodCollar {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    ∃ h : realization.obj K ⟶ realization.obj K,
      realization.map L.ι ≫ h = realization.map L.ι ∧
        h.hom.HomotopicRel (ContinuousMap.id _) (Set.range (realization.map L.ι).hom) ∧
          ∃ U : Set (realization.obj K), IsOpen U ∧ Set.range (realization.map L.ι).hom ⊆ U ∧
            Set.MapsTo h.hom U (Set.range (realization.map L.ι).hom) := by
  let S := derivedSubdivision hK hKs L
  have hS : S.Y'.IsSimplicialComplex := derivedSubdivision_isSimplicialComplex hK hKs L
  exact ⟨subdivisionCollarSelfMap S hS, subdivisionCollarSelfMap_retained S hS,
    subdivisionCollarSelfMap_homotopicRel S hS,
    subdivisionCollarSelfMap_exists_openNeighborhood S hS
      (derivedSubdivision_retained_isFull hK hKs L)⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.realization_range_of_mono
#print axioms HomotopyHypothesis.Approximation.Zeeman.subdivisionCollarSelfMap_homotopicRel
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeNeighborhoodCollar
