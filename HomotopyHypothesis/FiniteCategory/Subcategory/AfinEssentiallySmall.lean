import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open OAI.Grothendieck
open OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

theorem afin_essentiallySmall_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    EssentiallySmall.{u} (Afin C hC) := by
  let P : ObjectProperty C.Model := ObjectProperty.ofObj
    (fun i : ℕ ⊕ Unit =>
      match i with
      | Sum.inl n => disk C n
      | Sum.inr _ => ⊥_ C.Model)
  let Q : ObjectProperty C.Model := P.colimitsClosure (fun _ : Unit => WalkingSpan)
  have hDisk (n : ℕ) : Q (disk C n) := by
    have hSeed : P (disk C n) := ⟨Sum.inl n⟩
    exact P.le_colimitsClosure (fun _ : Unit => WalkingSpan) (disk C n)
      hSeed
  have hInitial : Q (⊥_ C.Model) := by
    have hSeed : P (⊥_ C.Model) := ⟨Sum.inr ()⟩
    exact P.le_colimitsClosure (fun _ : Unit => WalkingSpan) (⊥_ C.Model)
      hSeed
  have hBoundary : ∀ n, Q (boundaryDisk C n) := by
    intro n
    induction n with
    | zero =>
        simpa [boundaryDisk, boundaryRepresentation, BoundaryRepresentation.zero] using hInitial
    | succ n ih =>
        change Q (pushout (I C n) (I C n))
        exact Q.prop_of_isColimit (pushout.isColimit (I C n) (I C n)) (by
          rintro (⟨⟩ | ⟨⟨⟩⟩)
          · exact ih
          · exact hDisk n
          · exact hDisk n)
  haveI : Small.{u} (ℕ ⊕ Unit) := inferInstance
  haveI : ObjectProperty.EssentiallySmall.{u} P := inferInstance
  haveI : LocallySmall.{u} C.Model := inferInstance
  haveI : Small.{u} (Unit) := inferInstance
  haveI : Small.{u} WalkingSpan := inferInstance
  haveI : LocallySmall.{u} WalkingSpan := inferInstance
  haveI : ObjectProperty.EssentiallySmall.{u} Q := inferInstance
  let G : MorphismProperty C.Model :=
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model
  have hGenerator : ∀ {X Y} (f : X ⟶ Y), G f → Q X → Q Y := by
    intro X Y f hf hX
    rcases hf with hp | hi
    · rcases hp with ⟨A, B, p, a, b, hp, sq⟩
      cases hp with
      | mk n =>
          exact Q.prop_of_isColimit sq.isColimit (by
            rintro (⟨⟩ | ⟨⟨⟩⟩)
            · exact hBoundary n
            · exact hX
            · exact hDisk n)
    · haveI : IsIso f := hi
      exact Q.prop_of_iso (asIso f) hX
  have hFinite : ∀ {X Y} (f : X ⟶ Y), finiteCellMaps C f → Q X → Q Y := by
    intro X Y f hf
    change G.multiplicativeClosure f at hf
    induction hf with
    | of f hf => exact hGenerator f hf
    | id X => exact fun hX => hX
    | comp_of f g hf hg ih => exact fun hX => hGenerator g hg (ih hX)
  have hFinitelyCellular : IsFinitelyCellular C ≤ Q := by
    intro X hX
    exact hFinite (initial.to X) hX hInitial
  have hSmall : ObjectProperty.EssentiallySmall.{u} (IsFinitelyCellular C) :=
    ObjectProperty.EssentiallySmall.of_le hFinitelyCellular
  letI : ObjectProperty.EssentiallySmall.{u} (IsFinitelyCellular C) := hSmall
  change EssentiallySmall.{u} (ObjectProperty.FullSubcategory (IsFinitelyCellular C))
  exact inferInstance

#print axioms afin_essentiallySmall_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
