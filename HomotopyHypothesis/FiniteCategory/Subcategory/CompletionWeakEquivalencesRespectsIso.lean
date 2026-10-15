import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

open CategoryTheory CategoryTheory.Limits Opposite
open HomotopicalAlgebra
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

universe u v w

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem presheafWeakEquivalences_respectsIso :
    (presheafWeakEquivalences.{w} (C := C)).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ ?_ ?_
  · intro X Y Z e f hf A B i hi a b hb
    have hsq : f.app (op A) (e.hom.app (op A) a) = Z.map i.op b := by
      simpa using hb
    obtain ⟨l, cyl, h, hl, h₀, h₁⟩ := hf i hi (e.hom.app (op A) a) b hsq
    refine ⟨e.inv.app (op B) l, cyl, h, ?_, ?_, h₁⟩
    · have hn := congrArg (fun g => g l) (e.inv.naturality i.op).symm
      calc
        X.map i.op (e.inv.app (op B) l) = e.inv.app (op A) (Y.map i.op l) := by
          simpa using hn.symm
        _ = e.inv.app (op A) (e.hom.app (op A) a) := by rw [hl]
        _ = a := by simp
    · simpa using h₀
  · intro X Y Z e f hf A B i hi a b hb
    have hsq : f.app (op A) a = Y.map i.op (e.inv.app (op B) b) := by
      have hb' : e.hom.app (op A) (f.app (op A) a) = Z.map i.op b := by
        simpa using hb
      calc
        f.app (op A) a = e.inv.app (op A) (e.hom.app (op A) (f.app (op A) a)) := by simp
        _ = e.inv.app (op A) (Z.map i.op b) := by rw [hb']
        _ = Y.map i.op (e.inv.app (op B) b) := by
          have hn := congrArg (fun g => g b) (e.inv.naturality i.op)
          simpa using hn.symm
    obtain ⟨l, cyl, h, hl, h₀, h₁⟩ := hf i hi a (e.inv.app (op B) b) hsq
    refine ⟨l, cyl, e.hom.app (op cyl.I) h, hl, ?_, ?_⟩
    · calc
        Z.map (cyl.j₀ ≫ cyl.c).op (e.hom.app (op cyl.I) h) =
            e.hom.app (op B) (Y.map (cyl.j₀ ≫ cyl.c).op h) :=
          by
            have hn := congrArg (fun g => g h)
              (e.hom.naturality (cyl.j₀ ≫ cyl.c).op)
            simpa using hn.symm
        _ = e.hom.app (op B) (f.app (op B) l) := by rw [h₀]
        _ = (f ≫ e.hom).app (op B) l := rfl
    · calc
        Z.map (cyl.j₁ ≫ cyl.c).op (e.hom.app (op cyl.I) h) =
            e.hom.app (op B) (Y.map (cyl.j₁ ≫ cyl.c).op h) :=
          by
            have hn := congrArg (fun g => g h)
              (e.hom.naturality (cyl.j₁ ≫ cyl.c).op)
            simpa using hn.symm
        _ = e.hom.app (op B) (e.inv.app (op B) b) := by rw [h₁]
        _ = b := by simp

theorem completion_weakEquivalences_respectsIso_proof
    {C : OAI.Grothendieck.GlobularTheory}
    (hC : C.IsCoherator) :
    (Completion.weakEquivalences.{u} (Afin C hC)).RespectsIso := by
  change ((presheafWeakEquivalences.{u} (C := Afin C hC)).inverseImage
    (ObjectProperty.ι (IsCompletionPresheaf (Afin C hC)))).RespectsIso
  letI : (presheafWeakEquivalences.{u} (C := Afin C hC)).RespectsIso :=
    presheafWeakEquivalences_respectsIso (C := Afin C hC)
  exact MorphismProperty.RespectsIso.inverseImage _ _

#print axioms completion_weakEquivalences_respectsIso_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
