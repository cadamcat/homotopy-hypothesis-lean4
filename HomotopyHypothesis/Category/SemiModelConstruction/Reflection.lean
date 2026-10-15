import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelConstruction.Limits
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

def cofibrationCospans : ObjectProperty (WalkingCospan ⥤ Cᵒᵖ) := fun F =>
  ∃ (A B X : C) (i : A ⟶ B) (f : A ⟶ X), cofibrations C i ∧ F = cospan i.op f.op

theorem completion_iff_preservesTests [IsCofibrationCategory C] (P : Cᵒᵖ ⥤ Type w) :
    IsCompletionPresheaf C P ↔ PreservesLimit (Functor.empty.{0} Cᵒᵖ) P ∧
      ∀ F, cofibrationCospans F → PreservesLimit F P := by
  constructor
  · intro hP
    obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
    refine ⟨completionPresheaf_preservesTerminal P hP hI, ?_⟩
    rintro F ⟨A, B, X, i, f, hi, rfl⟩
    haveI := IsCofibrationCategory.hasPushout i f hi
    exact completionPresheaf_preservesCofibrationPushout P hP i f
      (pushout.inl i f) (pushout.inr i f) (IsPushout.of_hasPushout i f) hi
  · rintro ⟨h₀, h₁⟩
    refine ⟨fun I hI => ?_, fun A B X Q i f k j h hi => ?_⟩
    · exact ⟨Types.isTerminalEquivUnique _ (hI.op.isTerminalObj P _)⟩
    · haveI := h₁ (cospan i.op f.op) ⟨A, B, X, i, f, hi, rfl⟩
      exact h.op.flip.map P

theorem cofibrationCospans_essentiallySmall [EssentiallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (cofibrationCospans (C := C)) := by
  let e : (WalkingCospan ⥤ Cᵒᵖ) ≌ (WalkingCospan ⥤ SmallModel.{w} Cᵒᵖ) :=
    (equivSmallModel.{w} Cᵒᵖ).congrRight
  haveI : EssentiallySmall.{w} (WalkingCospan ⥤ Cᵒᵖ) :=
    (essentiallySmall_congr e).mpr inferInstance
  exact ObjectProperty.EssentiallySmall.of_le (show cofibrationCospans (C := C) ≤ ⊤ from le_top)

theorem exists_small_completionTests [IsCofibrationCategory C] [EssentiallySmall.{w} C] :
    ∃ (W : MorphismProperty (Cᵒᵖ ⥤ Type w)) (_ : MorphismProperty.IsSmall.{w} W),
      (IsCompletionPresheaf.{w} C : ObjectProperty (Cᵒᵖ ⥤ Type w)) = W.isLocal := by
  haveI := cofibrationCospans_essentiallySmall.{w} (C := C)
  obtain ⟨Q, _, hQ, hcover⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le.{w} (cofibrationCospans (C := C))
  haveI : Small.{w} (Option (Subtype Q)) :=
    small_of_injective (Equiv.optionEquivSumPUnit.{w} (Subtype Q)).injective
  let test (a : Option (Subtype Q)) : MorphismProperty (Cᵒᵖ ⥤ Type w) :=
    match a with
    | none => MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily (Functor.empty.{0} Cᵒᵖ))
    | some F => MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F.val)
  haveI (a : Option (Subtype Q)) : MorphismProperty.IsSmall.{w} (test a) := by
    cases a <;> dsimp [test] <;> exact MorphismProperty.isSmall_ofHoms.{w} _
  refine ⟨⨆ a, test a, MorphismProperty.isSmall_iSup.{w} test, ?_⟩
  ext P
  rw [MorphismProperty.isLocal_iSup]
  simp only [iInf_apply, iInf_Prop_eq]
  change IsCompletionPresheaf C P ↔ ∀ a, (test a).isLocal P
  rw [completion_iff_preservesTests]
  constructor
  · rintro ⟨h₀, h₁⟩ a
    cases a with
    | none =>
      change (MorphismProperty.ofHoms
        (Presheaf.preservesLimitHomFamily (Functor.empty.{0} Cᵒᵖ))).isLocal P
      rw [← Presheaf.preservesLimit_eq_isLocal]
      exact h₀
    | some F =>
      change (MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F.val)).isLocal P
      rw [← Presheaf.preservesLimit_eq_isLocal]
      exact h₁ F.val (hQ _ F.property)
  · intro h
    have h₀ := h none
    change (MorphismProperty.ofHoms
      (Presheaf.preservesLimitHomFamily (Functor.empty.{0} Cᵒᵖ))).isLocal P at h₀
    rw [← Presheaf.preservesLimit_eq_isLocal] at h₀
    refine ⟨h₀, fun F hF => ?_⟩
    obtain ⟨F', hF', ⟨e⟩⟩ := hcover _ hF
    have h' := h (some ⟨F', hF'⟩)
    change (MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F')).isLocal P at h'
    rw [← Presheaf.preservesLimit_eq_isLocal] at h'
    exact preservesLimit_of_iso_diagram P e.symm

#print axioms exists_small_completionTests

end HomotopyHypothesis.Category.SemiModelConstruction
