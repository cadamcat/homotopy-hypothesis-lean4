import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

theorem relativeCylinder_end_cofibrations {A B : C} (i : A ⟶ B)
    (hi : cofibrations C i) (cyl : RelativeCylinder i) :
    cofibrations C (cyl.j₀ ≫ cyl.c) ∧ cofibrations C (cyl.j₁ ≫ cyl.c) := by
  haveI := IsCofibrationCategory.isStableUnderCobaseChange (C := C)
  haveI := IsCofibrationCategory.isMultiplicative (C := C)
  exact ⟨(cofibrations C).comp_mem _ _
    ((cofibrations C).of_isPushout cyl.isPushout hi) cyl.c_mem,
    (cofibrations C).comp_mem _ _
      ((cofibrations C).of_isPushout cyl.isPushout.flip hi) cyl.c_mem⟩

theorem relativeCylinder_end_weakEquivalences {A B : C} {i : A ⟶ B}
    (cyl : RelativeCylinder i) :
    weakEquivalences C (cyl.j₀ ≫ cyl.c) ∧
      weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _ (by infer_instance)
  constructor
  · exact (IsCylinderCategory.twoOutOfSix (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
      (by simpa only [Category.assoc, cyl.j₀_c_p] using hid)
      (by simpa using cyl.p_mem)).1
  · exact (IsCylinderCategory.twoOutOfSix (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 B)
      (by simpa only [Category.assoc, cyl.j₁_c_p] using hid)
      (by simpa using cyl.p_mem)).1

theorem completion_trivialFibration_isWeakEquivalence {X Y : Completion.{w} C}
    (f : X ⟶ Y) (hf : Completion.trivialFibrations C f) :
    Completion.weakEquivalences C f := by
  intro A B i hi a b hab
  obtain ⟨l, hl, hfl⟩ := hf i hi a b hab
  obtain ⟨cyl, H, h₀, h₁⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).1.refl (𝟙 B)
  refine ⟨l, cyl, Y.obj.map cyl.p.op b, hl, ?_, ?_⟩
  · rw [hfl]
    change (Y.obj.map cyl.p.op ≫ Y.obj.map (cyl.j₀ ≫ cyl.c).op) b = b
    rw [← Y.obj.map_comp, ← op_comp, Category.assoc, cyl.j₀_c_p,
      op_id, Y.obj.map_id]
    rfl
  · change (Y.obj.map cyl.p.op ≫ Y.obj.map (cyl.j₁ ≫ cyl.c).op) b = b
    rw [← Y.obj.map_comp, ← op_comp, Category.assoc, cyl.j₁_c_p,
      op_id, Y.obj.map_id]
    rfl

theorem completion_fibration_weakEquivalence_isTrivialFibration
    {X Y : Completion.{w} C} (f : X ⟶ Y) (hf : Completion.fibrations C f)
    (hw : Completion.weakEquivalences C f) : Completion.trivialFibrations C f := by
  intro A B i hi a b hab
  obtain ⟨l, cyl, H, hl, h₀, h₁⟩ := hw i hi a b hab
  obtain ⟨L, hL₀, hfL⟩ := hf (cyl.j₀ ≫ cyl.c)
    (relativeCylinder_end_cofibrations i hi cyl).1
    (relativeCylinder_end_weakEquivalences cyl).1 l H h₀.symm
  have he : i ≫ (cyl.j₀ ≫ cyl.c) = i ≫ (cyl.j₁ ≫ cyl.c) := by
    simpa only [Category.assoc] using congrArg (fun t => t ≫ cyl.c) cyl.isPushout.w
  refine ⟨X.obj.map (cyl.j₁ ≫ cyl.c).op L, ?_, ?_⟩
  · calc
      X.obj.map i.op (X.obj.map (cyl.j₁ ≫ cyl.c).op L) =
          X.obj.map i.op (X.obj.map (cyl.j₀ ≫ cyl.c).op L) := by
        change (X.obj.map (cyl.j₁ ≫ cyl.c).op ≫ X.obj.map i.op) L =
          (X.obj.map (cyl.j₀ ≫ cyl.c).op ≫ X.obj.map i.op) L
        rw [← X.obj.map_comp, ← X.obj.map_comp, ← op_comp, ← op_comp, he]
      _ = a := by rw [hL₀, hl]
  · rw [NatTrans.naturality_apply, hfL, h₁]

theorem completion_trivialFibrations_eq :
    Completion.trivialFibrations.{w} C =
      Completion.fibrations C ⊓ Completion.weakEquivalences C := by
  ext X Y f
  constructor
  · intro hf
    exact ⟨fun _ _ i hi _ => hf i hi,
      completion_trivialFibration_isWeakEquivalence f hf⟩
  · rintro ⟨hf, hw⟩
    exact completion_fibration_weakEquivalence_isTrivialFibration f hf hw

theorem completion_lift_cof_trivFib :
    Completion.fibrations.{w} C ⊓ Completion.weakEquivalences C ≤
      (Completion.cofibrations C).rlp := by
  rw [← completion_trivialFibrations_eq]
  intro X Y p hp A B i hi
  exact hi p hp

#print axioms completion_trivialFibrations_eq
#print axioms completion_lift_cof_trivFib

end HomotopyHypothesis.Category.SemiModelConstruction
