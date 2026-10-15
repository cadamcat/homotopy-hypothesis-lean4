import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint

theorem afin_ι_map_initial_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    ∀ ⦃I : Afin C hC⦄, IsInitial I → Nonempty (IsInitial ((Afin.ι hC).obj I)) := by
  intro I hI
  have hInitialFin : IsFinitelyCellular C (⊥_ C.Model) := by
    change finiteCellMaps C (initial.to (⊥_ C.Model))
    have hId : initial.to (⊥_ C.Model) = 𝟙 (⊥_ C.Model) :=
      initialIsInitial.hom_ext _ _
    rw [hId]
    change
      ((MorphismProperty.ofHoms (fun n : ℕ => OAI.Grothendieck.GlobularTheory.Model.I C n)).pushouts ⊔
        MorphismProperty.isomorphisms C.Model).multiplicativeClosure (𝟙 (⊥_ C.Model))
    exact MorphismProperty.multiplicativeClosure.id _
  let I0 : Afin C hC := ⟨⊥_ C.Model, hInitialFin⟩
  have hI0 : IsInitial I0 :=
    IsInitial.ofUniqueHom
      (fun X => ObjectProperty.homMk (initial.to X.1))
      (fun X f => by
        apply ObjectProperty.hom_ext
        exact initialIsInitial.hom_ext _ _)
  let e : I ≅ I0 := hI.uniqueUpToIso hI0
  refine ⟨?_⟩
  exact IsInitial.ofIso initialIsInitial ((Afin.ι hC).mapIso e).symm

#print axioms afin_ι_map_initial_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
