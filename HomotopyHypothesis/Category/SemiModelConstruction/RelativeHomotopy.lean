import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Category.SemiModelConstruction.TrivialFibrations
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

def PresheafRelHomotopic {A B : C} (i : A ⟶ B) (X : Completion.{w} C)
    (a b : X.obj.obj (op B)) : Prop :=
  ∃ (cyl : RelativeCylinder i) (H : X.obj.obj (op cyl.I)),
    X.obj.map (cyl.j₀ ≫ cyl.c).op H = a ∧ X.obj.map (cyl.j₁ ≫ cyl.c).op H = b

theorem presheafRelHomotopic_symm {A B : C} {i : A ⟶ B} {X : Completion.{w} C}
    {a b : X.obj.obj (op B)} (h : PresheafRelHomotopic i X a b) :
    PresheafRelHomotopic i X b a := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  exact ⟨{ cyl with
    j₀ := cyl.j₁
    j₁ := cyl.j₀
    isPushout := cyl.isPushout.flip
    j₀_c_p := cyl.j₁_c_p
    j₁_c_p := cyl.j₀_c_p }, H, h₁, h₀⟩

theorem presheafRelHomotopic_map {A B : C} {i : A ⟶ B} {X Y : Completion.{w} C}
    (f : X ⟶ Y) {a b : X.obj.obj (op B)} (h : PresheafRelHomotopic i X a b) :
    PresheafRelHomotopic i Y (f.hom.app (op B) a) (f.hom.app (op B) b) := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  refine ⟨cyl, f.hom.app (op cyl.I) H, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply, h₀]
  · rw [← NatTrans.naturality_apply, h₁]

theorem presheafRelHomotopic_boundary {A B : C} {i : A ⟶ B} {X : Completion.{w} C}
    {a b : X.obj.obj (op B)} (h : PresheafRelHomotopic i X a b) :
    X.obj.map i.op a = X.obj.map i.op b := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  rw [← h₀, ← h₁]
  change (X.obj.map (cyl.j₀ ≫ cyl.c).op ≫ X.obj.map i.op) H =
    (X.obj.map (cyl.j₁ ≫ cyl.c).op ≫ X.obj.map i.op) H
  rw [← X.obj.map_comp, ← X.obj.map_comp, ← op_comp, ← op_comp,
    ← Category.assoc, ← Category.assoc, cyl.isPushout.w]

variable [IsCylinderCategory C]

theorem presheafRelHomotopic_refl {A B : C} (i : A ⟶ B) (hi : cofibrations C i)
    (X : Completion.{w} C) (a : X.obj.obj (op B)) : PresheafRelHomotopic i X a a := by
  obtain ⟨cyl, F, h₀, h₁⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).1.refl (𝟙 B)
  refine ⟨cyl, X.obj.map cyl.p.op a, ?_, ?_⟩
  · change (X.obj.map cyl.p.op ≫ X.obj.map (cyl.j₀ ≫ cyl.c).op) a = a
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, cyl.j₀_c_p, op_id, X.obj.map_id]
    rfl
  · change (X.obj.map cyl.p.op ≫ X.obj.map (cyl.j₁ ≫ cyl.c).op) a = a
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, cyl.j₁_c_p, op_id, X.obj.map_id]
    rfl

theorem presheafRelHomotopic_onCylinder {A B : C} {i : A ⟶ B}
    (hi : cofibrations C i) (given : RelativeCylinder i) {X : Completion.{w} C}
    {a b : X.obj.obj (op B)} (h : PresheafRelHomotopic i X a b) :
    ∃ H : X.obj.obj (op given.I), X.obj.map (given.j₀ ≫ given.c).op H = a ∧
      X.obj.map (given.j₁ ≫ given.c).op H = b := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  have hab : RelHomotopic i (cyl.j₀ ≫ cyl.c) (cyl.j₁ ≫ cyl.c) :=
    ⟨cyl, 𝟙 cyl.I, by simp, by simp⟩
  obtain ⟨F, hF₀, hF₁⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).2 given
    (cyl.j₀ ≫ cyl.c) (cyl.j₁ ≫ cyl.c) hab
  refine ⟨X.obj.map F.op H, ?_, ?_⟩
  · change (X.obj.map F.op ≫ X.obj.map (given.j₀ ≫ given.c).op) H = a
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₀, h₀]
  · change (X.obj.map F.op ≫ X.obj.map (given.j₁ ≫ given.c).op) H = b
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₁, h₁]

theorem presheafRelHomotopic_trans {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    {X : Completion.{w} C} {a b c : X.obj.obj (op B)}
    (hab : PresheafRelHomotopic i X a b) (hbc : PresheafRelHomotopic i X b c) :
    PresheafRelHomotopic i X a c := by
  obtain ⟨cyl₀, H₀, ha, hb₀⟩ := hab
  obtain ⟨cyl₁, H₁, hb₁, hc⟩ := hbc
  have hi₀ := (relativeCylinder_end_cofibrations i hi cyl₀).2
  haveI := IsCofibrationCategory.hasPushout (cyl₀.j₁ ≫ cyl₀.c) (cyl₁.j₀ ≫ cyl₁.c) hi₀
  let k₀ := pushout.inl (cyl₀.j₁ ≫ cyl₀.c) (cyl₁.j₀ ≫ cyl₁.c)
  let k₁ := pushout.inr (cyl₀.j₁ ≫ cyl₀.c) (cyl₁.j₀ ≫ cyl₁.c)
  have hs := IsPushout.of_hasPushout (cyl₀.j₁ ≫ cyl₀.c) (cyl₁.j₀ ≫ cyl₁.c)
  obtain ⟨H, hk₀, hk₁⟩ := Types.exists_of_isPullback
    (X.property.2 _ _ k₀ k₁ hs hi₀) H₀ H₁ (by rw [hb₀, hb₁])
  have h₀ : RelHomotopic i ((cyl₀.j₀ ≫ cyl₀.c) ≫ k₀) ((cyl₀.j₁ ≫ cyl₀.c) ≫ k₀) :=
    ⟨cyl₀, k₀, by simp, by simp⟩
  have h₁ : RelHomotopic i ((cyl₀.j₁ ≫ cyl₀.c) ≫ k₀) ((cyl₁.j₁ ≫ cyl₁.c) ≫ k₁) :=
    ⟨cyl₁, k₁, by simpa [k₀, k₁, Category.assoc] using hs.w.symm, by simp⟩
  obtain ⟨cyl, F, hF₀, hF₁⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).1.trans h₀ h₁
  refine ⟨cyl, X.obj.map F.op H, ?_, ?_⟩
  · change (X.obj.map F.op ≫ X.obj.map (cyl.j₀ ≫ cyl.c).op) H = a
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₀, op_comp, X.obj.map_comp]
    change X.obj.map (cyl₀.j₀ ≫ cyl₀.c).op (X.obj.map k₀.op H) = a
    rw [hk₀, ha]
  · change (X.obj.map F.op ≫ X.obj.map (cyl.j₁ ≫ cyl.c).op) H = c
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₁, op_comp, X.obj.map_comp]
    change X.obj.map (cyl₁.j₁ ≫ cyl₁.c).op (X.obj.map k₁.op H) = c
    rw [hk₁, hc]

theorem presheafRelHomotopic_equivalence {A B : C} (i : A ⟶ B) (hi : cofibrations C i)
    (X : Completion.{w} C) : Equivalence (PresheafRelHomotopic i X) :=
  ⟨presheafRelHomotopic_refl i hi X, presheafRelHomotopic_symm,
    presheafRelHomotopic_trans hi⟩

#print axioms presheafRelHomotopic_equivalence

end HomotopyHypothesis.Category.SemiModelConstruction
