import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapInitial
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

universe v u

section Closure

variable {D : Type u} [Category.{v} D] [HasPushouts D]

/-- Finite composition preserves stability under cobase change. -/
theorem finiteClosure_cobaseChange (P : MorphismProperty D)
    [P.IsStableUnderCobaseChange] (hP : MorphismProperty.isomorphisms D ≤ P) :
    P.multiplicativeClosure.IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    induction hf generalizing B B' with
    | of f hf => exact .of _ (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
    | id A =>
        haveI : IsIso f' := sq.isIso_inl_of_isIso
        exact .of _ (hP _ (inferInstance : IsIso f'))
    | comp_of f h hf hh ih =>
        let mid := pushout g f
        let j : B ⟶ mid := pushout.inl g f
        let k : _ ⟶ mid := pushout.inr g f
        let t : mid ⟶ B' := pushout.desc f' (h ≫ g') (by simpa using sq.w)
        have first : IsPushout g f j k := IsPushout.of_hasPushout g f
        have outer : IsPushout g (f ≫ h) (j ≫ t) g' := by
          simpa only [j, t, pushout.inl_desc] using sq
        have second : IsPushout k h t g' :=
          outer.of_top (by simp only [k, t, pushout.inr_desc]) first
        have hj := ih first
        have ht := MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := P) second hh
        have H := P.multiplicativeClosure.comp_mem j t hj (.of _ ht)
        simpa only [j, t, pushout.inl_desc] using H

end Closure

instance relativeFiniteCellComplexes_multiplicative :
    Top.relativeFiniteCellComplexes.{u}.IsMultiplicative :=
  inferInstanceAs (Top.cellBoundaries.pushouts ⊔
    MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure.IsMultiplicative

/-- Relative finite cell maps contain all isomorphisms. -/
theorem isomorphisms_le_relativeFiniteCellComplexes :
    MorphismProperty.isomorphisms TopCat.{u} ≤ Top.relativeFiniteCellComplexes := by
  exact le_trans le_sup_right (MorphismProperty.le_multiplicativeClosure _)

instance relativeFiniteCellComplexes_respectsIso :
    Top.relativeFiniteCellComplexes.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    isomorphisms_le_relativeFiniteCellComplexes

instance cellSteps_cobaseChange :
    (Top.cellBoundaries.{u}.pushouts ⊔ MorphismProperty.isomorphisms TopCat).IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    rcases hf with hf | hf
    · exact Or.inl (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
    · haveI : IsIso f := hf
      exact Or.inr sq.isIso_inl_of_isIso

instance relativeFiniteCellComplexes_cobaseChange :
    Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
  finiteClosure_cobaseChange _ le_sup_right

section Adjunction

universe w
variable {C : GlobularTheory.{u}} (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

include adj

/-- A left adjoint preserves finite boundary-cell maps once it preserves the generating cells. -/
theorem map_finiteCellMaps
    (hI : ∀ n, Top.relativeFiniteCellComplexes (L.map (I C n))) :
    finiteCellMaps C ≤ Top.relativeFiniteCellComplexes.inverseImage L := by
  letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  change ((MorphismProperty.ofHoms (fun n => I C n)).pushouts ⊔
    MorphismProperty.isomorphisms C.Model).multiplicativeClosure ≤ _
  apply (MorphismProperty.multiplicativeClosure_le_iff
    ((MorphismProperty.ofHoms (fun n => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model)
    (Top.relativeFiniteCellComplexes.inverseImage L)).mpr
  intro X Y f hf
  change Top.relativeFiniteCellComplexes (L.map f)
  rcases hf with hf | hf
  · rcases hf with ⟨A, B, p, a, b, hp, sq⟩
    cases hp with
    | mk n =>
      exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout (sq.map L) (hI n)
  · haveI : IsIso f := hf
    exact isomorphisms_le_relativeFiniteCellComplexes _ (inferInstance : IsIso (L.map f))

/-- The restricted adjoint preserves initial objects. -/
theorem restricted_map_initial (hC : C.IsCoherator) {A : Afin C hC} (hA : IsInitial A) :
    Nonempty (IsInitial ((Afin.ι hC ⋙ L).obj A)) := by
  letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  obtain ⟨h⟩ := Blueprint.Packages.afin_ι_map_initial hC hA
  exact ⟨h.isInitialObj L _⟩

/-- The restricted adjoint preserves pushouts along cofibrations. -/
theorem restricted_map_isPushout (hC : C.IsCoherator) {A B X Q : Afin C hC}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (sq : IsPushout i f k j) (hi : cofibrations (Afin C hC) i) :
    IsPushout ((Afin.ι hC ⋙ L).map i) ((Afin.ι hC ⋙ L).map f)
      ((Afin.ι hC ⋙ L).map k) ((Afin.ι hC ⋙ L).map j) := by
  letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  exact (Blueprint.Packages.afin_ι_map_isPushout hC i f k j sq hi).map L

end Adjunction

end HomotopyHypothesis.Realization.Cellular
