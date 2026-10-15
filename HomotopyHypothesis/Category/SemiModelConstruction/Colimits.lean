import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelConstruction.Reflection
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

theorem smallLocalObjects_locallyPresentable {D : Type u} [Category.{v} D]
    [IsLocallyPresentable.{w} D] (W : MorphismProperty D) [MorphismProperty.IsSmall.{w} W] :
    IsLocallyPresentable.{w} W.isLocal.FullSubcategory := by
  obtain ⟨κ₀, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} D
  let P := ObjectProperty.ofObj (fun (a : W.toSet) => a.val.left) ⊔
    ObjectProperty.ofObj (fun (a : W.toSet) => a.val.right)
  obtain ⟨κ, _, hP⟩ := ObjectProperty.le_isCardinalPresentable.{w} P
  let κ' := max κ₀ κ
  haveI : Fact κ'.IsRegular := ⟨by
    dsimp [κ']
    rcases le_total κ₀ κ with h | h
    · rw [max_eq_right h]; exact Fact.out
    · rw [max_eq_left h]; exact Fact.out⟩
  haveI : IsCardinalLocallyPresentable D κ' :=
    IsCardinalLocallyPresentable.of_le D (le_max_left κ₀ κ)
  refine ⟨κ', inferInstance, W.isLocallyPresentable_isLocal κ' ?_⟩
  intro X Y f hf
  let a : W.toSet := ⟨Arrow.mk f, hf⟩
  constructor
  · exact isCardinalPresentable_monotone D (le_max_right κ₀ κ) X
      (hP X (Or.inl (ObjectProperty.ofObj_apply (fun (b : W.toSet) => b.val.left) a)))
  · exact isCardinalPresentable_monotone D (le_max_right κ₀ κ) Y
      (hP Y (Or.inr (ObjectProperty.ofObj_apply (fun (b : W.toSet) => b.val.right) a)))

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

theorem presheaves_locallyPresentable [EssentiallySmall.{w} C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) := by
  let e : ((SmallModel.{w} C)ᵒᵖ ⥤ Type w) ≌ (Cᵒᵖ ⥤ Type w) :=
    (equivSmallModel.{w} C).op.congrLeft.symm
  exact e.isLocallyPresentable

theorem completion_locallyPresentable [IsCofibrationCategory C] [EssentiallySmall.{w} C] :
    IsLocallyPresentable.{w} (Completion.{w} C) := by
  haveI := presheaves_locallyPresentable.{w} (C := C)
  obtain ⟨W, _, hW⟩ := exists_small_completionTests.{w} (C := C)
  change IsLocallyPresentable (ObjectProperty.FullSubcategory (IsCompletionPresheaf.{w} C))
  rw [hW]
  exact smallLocalObjects_locallyPresentable W

theorem completion_hasColimits [IsCofibrationCategory C] [EssentiallySmall.{w} C] :
    HasColimitsOfSize.{w, w} (Completion.{w} C) := by
  haveI := completion_locallyPresentable.{w} (C := C)
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} (Completion.{w} C)
  infer_instance

theorem completion_hasFiniteColimits [IsCofibrationCategory C] [EssentiallySmall.{w} C] :
    HasFiniteColimits (Completion.{w} C) := by
  haveI := completion_hasColimits.{w} (C := C)
  exact hasFiniteColimits_of_hasColimitsOfSize.{w, w} (Completion.{w} C)

#print axioms completion_hasColimits
#print axioms completion_hasFiniteColimits

end HomotopyHypothesis.Category.SemiModelConstruction
