import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelStructure.CellStep
import HomotopyHypothesis.Category.SemiModelStructure.Filtered
import HomotopyHypothesis.Category.SemiModelStructure.Flat
import HomotopyHypothesis.Category.SemiModelConstruction.TrivialFibrations
import HomotopyHypothesis.Category.SemiModelConstruction.WeakEquivalences
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Relative cell complexes starting from a flat object

A relative cell complex of the completion whose cells are images `y c` of cofibrations of `C`,
starting from a flat object, ends at a flat object; if the cells are trivial cofibrations, it is a
weak equivalence (transfinite induction: successor steps attach cells, limit steps are filtered
colimits).
-/

universe w v u t

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C] [EssentiallySmall.{w} C]

theorem completion_weakEquivalence_id (X : Completion.{w} C) :
    Completion.weakEquivalences C (𝟙 X) :=
  completion_trivialFibration_isWeakEquivalence _ (fun _ _ _ _ a b hab =>
    ⟨b, by simpa using hab.symm, rfl⟩)

theorem completion_weakEquivalence_of_isColimit_const {J : Type w} [SmallCategory J]
    [IsFiltered J] {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c)
    {X₀ : Completion.{w} C} (t : (Functor.const J).obj X₀ ⟶ F)
    (ht : ∀ j, Completion.weakEquivalences C (t.app j)) (u : X₀ ⟶ c.pt)
    (hu : ∀ j, u = t.app j ≫ c.ι.app j) : Completion.weakEquivalences C u :=
  have : IsConnected J := IsFiltered.isConnected J
  completion_weakEquivalence_of_isColimit t ht (isColimitConstCocone J X₀) hc u
    (fun j => by
      change 𝟙 X₀ ≫ u = _
      rw [Category.id_comp, hu j])

theorem relativeCellComplex_flat {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {α : J → Type t} {A B : (j : J) → α j → Completion.{w} C}
    {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} (P : Prop)
    (hcell : ∀ j i, ∃ (Cc Dd : C) (c : Cc ⟶ Dd), cofibrations C c ∧
      (P → weakEquivalences C c) ∧
      Nonempty (Arrow.mk (basicCell j i) ≅ Arrow.mk (completionSmallYoneda.{w}.map c)))
    {X Y : Completion.{w} C} {f : X ⟶ Y} (hf : RelativeCellComplex.{w} basicCell f)
    (hX : IsFlat X) :
    IsFlat Y ∧ (P → Completion.weakEquivalences C f) := by
  have := Completion.weakEquivalences_respectsIso.{w} C
  have key : ∀ j : J, IsFlat (hf.F.obj j) ∧
      (P → Completion.weakEquivalences C (hf.F.map (homOfLE bot_le : ⊥ ⟶ j))) := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl := hj.eq_bot
      refine ⟨isFlat_of_iso hf.isoBot.symm hX, fun _ => ?_⟩
      rw [show (homOfLE bot_le : (⊥ : J) ⟶ ⊥) = 𝟙 _ from rfl, hf.F.map_id]
      exact completion_weakEquivalence_id _
    | succ j hj ih =>
      have hstep := attachCells_flat (basicCell j) P (hcell j) (hf.attachCells j hj) ih.1
      refine ⟨hstep.1, fun hP => ?_⟩
      have e : (homOfLE bot_le : ⊥ ⟶ Order.succ j) =
          (homOfLE bot_le : ⊥ ⟶ j) ≫ homOfLE (Order.le_succ j) := rfl
      rw [e, hf.F.map_comp]
      exact completion_weakEquivalence_comp _ _ (ih.2 hP) (hstep.2 hP)
    | isSuccLimit j hj ih =>
      have hc := Functor.isColimitOfIsWellOrderContinuous hf.F j hj
      have : Nonempty (Set.Iio j) := ⟨⟨⊥, bot_lt_iff_ne_bot.mpr (fun h => hj.not_isMin (h ▸ isMin_bot))⟩⟩
      refine ⟨isFlat_of_isColimit hc (fun k => (ih k.1 k.2).1), fun hP => ?_⟩
      refine completion_weakEquivalence_of_isColimit_const hc
        { app := fun k => hf.F.map (homOfLE bot_le : ⊥ ⟶ k.1)
          naturality := fun k k' φ => by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.comp_map, ← hf.F.map_comp]
            rfl }
        (fun k => (ih k.1 k.2).2 hP) _ (fun k => ?_)
      simp only [PrincipalSeg.cocone_ι_app, ← hf.F.map_comp]
      rfl
  refine ⟨isFlat_of_isColimit hf.isColimit (fun j => (key j).1), fun hP => ?_⟩
  have hW : Completion.weakEquivalences C (hf.incl.app ⊥) :=
    completion_weakEquivalence_of_isColimit_const hf.isColimit
      { app := fun j => hf.F.map (homOfLE bot_le : ⊥ ⟶ j)
        naturality := fun k k' φ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            ← hf.F.map_comp]
          rfl }
      (fun j => (key j).2 hP) _ (fun j => by
        have := hf.incl.naturality (homOfLE bot_le : ⊥ ⟶ j)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this.symm)
  rw [← hf.fac]
  exact (MorphismProperty.RespectsIso.precomp _ _ _ hW)

end HomotopyHypothesis.Category.SemiModelStructure
