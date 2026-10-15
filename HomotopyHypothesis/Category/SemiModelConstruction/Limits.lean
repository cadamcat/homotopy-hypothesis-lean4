import HomotopyHypothesis.Blueprint.Henry.Completion
universe w v u v' u' v'' u''

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

theorem completionPresheaf_preservesTerminal (P : Cᵒᵖ ⥤ Type w)
    (hP : IsCompletionPresheaf C P) {I : C} (hI : IsInitial I) :
    PreservesLimit (Functor.empty.{0} Cᵒᵖ) P := by
  obtain ⟨hUnique⟩ := hP.1 hI
  exact preservesLimit_of_preserves_limit_cone hI.op
    ((isLimitMapConeEmptyConeEquiv P (op I)).symm
      ((Types.isTerminalEquivUnique _).symm hUnique))

theorem completionPresheaf_preservesCofibrationPushout
    (P : Cᵒᵖ ⥤ Type w) (hP : IsCompletionPresheaf C P)
    {A B X Q : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (h : IsPushout i f k j) (hi : cofibrations C i) :
    PreservesLimit (cospan i.op f.op) P := by
  exact preservesLimit_of_preserves_limit_cone h.op.flip.isLimit
    ((PullbackCone.isLimitMapConeEquiv _ P).symm (hP.2 i f k j h hi).isLimit)

theorem preservesLimit_closedLimits [LocallySmall.{w} C]
    {K : Type u''} [Category.{v''} K] [Small.{w} K]
    (F : K ⥤ Cᵒᵖ) (J : Type u') [Category.{v'} J] :
    (ObjectProperty.preservesLimit (C := Type w) F).IsClosedUnderLimitsOfShape J := by
  rw [Presheaf.preservesLimit_eq_isLocal F]
  infer_instance

theorem completionPresheaves_closedLimits [LocallySmall.{w} C]
    (J : Type u') [Category.{v'} J] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsCompletionPresheaf.{w} C) J := by
  constructor
  intro P ⟨p⟩
  refine ⟨fun I hI => ?_, fun A B X Q i f k j h hi => ?_⟩
  · haveI := preservesLimit_closedLimits (C := C) (Functor.empty.{0} Cᵒᵖ) J
    haveI : PreservesLimit (Functor.empty.{0} Cᵒᵖ) P :=
      (ObjectProperty.preservesLimit (Functor.empty.{0} Cᵒᵖ)).prop_of_isLimit p.isLimit
        (fun a => completionPresheaf_preservesTerminal _ (p.prop_diag_obj a) hI)
    exact ⟨Types.isTerminalEquivUnique _ (hI.op.isTerminalObj P _)⟩
  · haveI := preservesLimit_closedLimits (C := C) (cospan i.op f.op) J
    haveI : PreservesLimit (cospan i.op f.op) P :=
      (ObjectProperty.preservesLimit (cospan i.op f.op)).prop_of_isLimit p.isLimit
        (fun a => completionPresheaf_preservesCofibrationPushout _
          (p.prop_diag_obj a) i f k j h hi)
    exact h.op.flip.map P

theorem completion_hasFiniteLimits [LocallySmall.{w} C] :
    HasFiniteLimits (Completion.{w} C) := by
  constructor
  intro J hJ hF
  haveI := completionPresheaves_closedLimits (C := C) J
  infer_instance

#print axioms completion_hasFiniteLimits

end HomotopyHypothesis.Category.SemiModelConstruction
