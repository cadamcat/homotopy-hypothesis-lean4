import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelConstruction.RelativeHomotopy
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem completion_weakEquivalence_iff_homotopyLift {X Y : Completion.{w} C} (f : X ⟶ Y) :
    Completion.weakEquivalences C f ↔
      ∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i →
        ∀ (a : X.obj.obj (op A)) (b : Y.obj.obj (op B)),
          f.hom.app (op A) a = Y.obj.map i.op b →
            ∃ l : X.obj.obj (op B), X.obj.map i.op l = a ∧
              PresheafRelHomotopic i Y (f.hom.app (op B) l) b := by
  constructor
  · intro hf A B i hi a b hab
    obtain ⟨l, cyl, H, hl, h₀, h₁⟩ := hf i hi a b hab
    exact ⟨l, hl, cyl, H, h₀, h₁⟩
  · intro hf A B i hi a b hab
    obtain ⟨l, hl, cyl, H, h₀, h₁⟩ := hf i hi a b hab
    exact ⟨l, cyl, H, hl, h₀, h₁⟩

theorem completion_weakEquivalence_reflectsHomotopy {X Y : Completion.{w} C}
    (f : X ⟶ Y) (hf : Completion.weakEquivalences C f) {A B : C} {i : A ⟶ B}
    (hi : cofibrations C i) {a b : X.obj.obj (op B)}
    (hab : X.obj.map i.op a = X.obj.map i.op b)
    (h : PresheafRelHomotopic i Y (f.hom.app (op B) a) (f.hom.app (op B) b)) :
    PresheafRelHomotopic i X a b := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  obtain ⟨aP, ha₀, ha₁⟩ := Types.exists_of_isPullback
    (X.property.2 i i cyl.j₀ cyl.j₁ cyl.isPushout hi) a b hab
  have hs : f.hom.app (op cyl.P) aP = Y.obj.map cyl.c.op H := by
    apply Types.ext_of_isPullback (Y.property.2 i i cyl.j₀ cyl.j₁ cyl.isPushout hi)
    · rw [← NatTrans.naturality_apply, ha₀]
      change f.hom.app (op B) a = (Y.obj.map cyl.c.op ≫ Y.obj.map cyl.j₀.op) H
      rw [← Y.obj.map_comp, ← op_comp]
      exact h₀.symm
    · rw [← NatTrans.naturality_apply, ha₁]
      change f.hom.app (op B) b = (Y.obj.map cyl.c.op ≫ Y.obj.map cyl.j₁.op) H
      rw [← Y.obj.map_comp, ← op_comp]
      exact h₁.symm
  obtain ⟨L, cyl', H', hL, hL₀, hL₁⟩ := hf cyl.c cyl.c_mem aP H hs
  refine ⟨cyl, L, ?_, ?_⟩
  · rw [op_comp, X.obj.map_comp]
    change X.obj.map cyl.j₀.op (X.obj.map cyl.c.op L) = a
    rw [hL, ha₀]
  · rw [op_comp, X.obj.map_comp]
    change X.obj.map cyl.j₁.op (X.obj.map cyl.c.op L) = b
    rw [hL, ha₁]

variable [IsCylinderCategory C]

theorem completion_weakEquivalence_comp {X Y Z : Completion.{w} C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Completion.weakEquivalences C f)
    (hg : Completion.weakEquivalences C g) : Completion.weakEquivalences C (f ≫ g) := by
  apply (completion_weakEquivalence_iff_homotopyLift (f ≫ g)).mpr
  intro A B i hi a b hab
  obtain ⟨lY, hlY, hY⟩ := (completion_weakEquivalence_iff_homotopyLift g).mp hg
    i hi (f.hom.app (op A) a) b hab
  obtain ⟨lX, hlX, hX⟩ := (completion_weakEquivalence_iff_homotopyLift f).mp hf
    i hi a lY hlY.symm
  exact ⟨lX, hlX, presheafRelHomotopic_trans hi (presheafRelHomotopic_map g hX) hY⟩

theorem completion_weakEquivalence_of_postcomp {X Y Z : Completion.{w} C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : Completion.weakEquivalences C g)
    (hfg : Completion.weakEquivalences C (f ≫ g)) : Completion.weakEquivalences C f := by
  apply (completion_weakEquivalence_iff_homotopyLift f).mpr
  intro A B i hi a b hab
  have hs : (f ≫ g).hom.app (op A) a = Z.obj.map i.op (g.hom.app (op B) b) := by
    rw [← NatTrans.naturality_apply, ← hab]
    rfl
  obtain ⟨l, hl, h⟩ := (completion_weakEquivalence_iff_homotopyLift (f ≫ g)).mp hfg
    i hi a (g.hom.app (op B) b) hs
  refine ⟨l, hl, completion_weakEquivalence_reflectsHomotopy g hg hi ?_ h⟩
  rw [← NatTrans.naturality_apply, hl, hab]

#print axioms completion_weakEquivalence_comp
#print axioms completion_weakEquivalence_of_postcomp

end HomotopyHypothesis.Category.SemiModelConstruction
