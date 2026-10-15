import Mathlib
universe w v u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

theorem smallObjectArgument_of_locallyPresentable {D : Type u} [Category.{v} D]
    [IsLocallyPresentable.{w} D] (I : MorphismProperty D) [MorphismProperty.IsSmall.{w} I] :
    MorphismProperty.HasSmallObjectArgument.{w} I := by
  obtain ⟨κ₀, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} D
  let P := ObjectProperty.ofObj (fun (a : I.toSet) => a.val.left)
  obtain ⟨κ, _, hP⟩ := ObjectProperty.le_isCardinalPresentable.{w} P
  have : Nonempty κ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero (show κ.IsRegular from Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  refine ⟨κ, inferInstance, inferInstance, { preservesColimit := ?_ }⟩
  intro A B X Y i hi f hf
  have hA : IsCardinalPresentable A κ := by
    rw [← isCardinalPresentable_iff]
    let a : I.toSet := ⟨Arrow.mk i, hi⟩
    exact hP a.val.left (ObjectProperty.ofObj_apply (fun (b : I.toSet) => b.val.left) a)
  haveI := (coyoneda.obj (op A)).preservesColimitsOfShape_of_isCardinalAccessible
    κ κ.ord.ToType
  infer_instance

#print axioms smallObjectArgument_of_locallyPresentable

end HomotopyHypothesis.Category.SemiModelConstruction
