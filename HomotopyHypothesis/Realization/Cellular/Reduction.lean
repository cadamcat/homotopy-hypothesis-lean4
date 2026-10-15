import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Cellular.CellularTransport
noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

include adj

/-- Finitely cellular objects realize to finite cell complexes if the generators do. -/
theorem restricted_obj_mem
    (hI : ∀ n, Top.relativeFiniteCellComplexes (L.map (I C n))) (X : Afin C hC) :
    Top.IsFiniteCellComplex ((Afin.ι hC ⋙ L).obj X) := by
  letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have hm : Top.relativeFiniteCellComplexes (L.map (initial.to X.obj)) :=
    map_finiteCellMaps R L adj hI _ X.property
  have hinit : IsInitial (L.obj (⊥_ C.Model)) := initialIsInitial.isInitialObj L _
  let e : (⊥_ TopCat.{u}) ≅ L.obj (⊥_ C.Model) := initialIsInitial.uniqueUpToIso hinit
  change Top.relativeFiniteCellComplexes (initial.to (L.obj X.obj))
  rw [initialIsInitial.hom_ext (initial.to (L.obj X.obj)) (e.hom ≫ L.map (initial.to X.obj))]
  exact Top.relativeFiniteCellComplexes.comp_mem _ _
    (isomorphisms_le_relativeFiniteCellComplexes _ (inferInstance : IsIso e.hom)) hm

/-- The formal part of cellular realization reduces to its generating cells and weak equivalences.
-/
theorem cellularRealization_of_cells_and_weakEquivalences
    (hI : ∀ n, Top.relativeFiniteCellComplexes (L.map (I C n)))
    (hW : ∀ ⦃X Y : Afin C hC⦄ (f : X ⟶ Y), weakEquivalences (Afin C hC) f →
      Top.homotopyEquivalences ((Afin.ι hC ⋙ L).map f)) :
    IsCellularRealization (Afin.ι hC ⋙ L) where
  obj_mem := restricted_obj_mem hC R L adj hI
  map_cofibration := fun {_ _} f hf => map_finiteCellMaps R L adj hI _ hf
  map_weakEquivalence := hW
  map_initial := fun {_} h => restricted_map_initial R L adj hC h
  map_isPushout := fun {_ _ _ _} => restricted_map_isPushout R L adj hC

end HomotopyHypothesis.Realization.Cellular
