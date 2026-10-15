import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem presheafWeakEquivalences_retracts :
    (presheafWeakEquivalences : MorphismProperty (Cᵒᵖ ⥤ Type w)).IsStableUnderRetracts := by
  constructor
  intro X Y Z W f g h hg A B i hi a b hab
  obtain ⟨l, cyl, H, hl, h₀, h₁⟩ :=
    hg i hi (h.i.left.app (op A) a) (h.i.right.app (op B) b) (by
      rw [← NatTrans.naturality_apply]
      change g.app (op A) (h.i.left.app (op A) a) =
        h.i.right.app (op A) (Y.map i.op b)
      rw [← hab]
      exact congrArg (fun t => t.app (op A) a) h.i_w)
  refine ⟨h.r.left.app (op B) l, cyl, h.r.right.app (op cyl.I) H, ?_, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply]
    change h.r.left.app (op A) (Z.map i.op l) = a
    rw [hl]
    exact congrArg (fun t => t.app (op A) a) h.retract_left
  · rw [← NatTrans.naturality_apply]
    change h.r.right.app (op B) (W.map (cyl.j₀ ≫ cyl.c).op H) = _
    rw [h₀]
    exact (congrArg (fun t => t.app (op B) l) h.r_w).symm
  · rw [← NatTrans.naturality_apply]
    change h.r.right.app (op B) (W.map (cyl.j₁ ≫ cyl.c).op H) = _
    rw [h₁]
    exact congrArg (fun t => t.app (op B) b) h.retract_right

theorem presheafFibrations_retracts :
    (presheafFibrations : MorphismProperty (Cᵒᵖ ⥤ Type w)).IsStableUnderRetracts := by
  constructor
  intro X Y Z W f g h hg A B i hi hwi a b hab
  obtain ⟨l, hl, hfl⟩ :=
    hg i hi hwi (h.i.left.app (op A) a) (h.i.right.app (op B) b) (by
      rw [← NatTrans.naturality_apply]
      change g.app (op A) (h.i.left.app (op A) a) =
        h.i.right.app (op A) (Y.map i.op b)
      rw [← hab]
      exact congrArg (fun t => t.app (op A) a) h.i_w)
  refine ⟨h.r.left.app (op B) l, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply]
    change h.r.left.app (op A) (Z.map i.op l) = a
    rw [hl]
    exact congrArg (fun t => t.app (op A) a) h.retract_left
  · have hr := congrArg (fun t => t.app (op B) l) h.r_w
    change f.app (op B) (h.r.left.app (op B) l) = h.r.right.app (op B) (g.app (op B) l) at hr
    rw [hr, hfl]
    exact congrArg (fun t => t.app (op B) b) h.retract_right

theorem presheafTrivialFibrations_retracts :
    (presheafTrivialFibrations : MorphismProperty (Cᵒᵖ ⥤ Type w)).IsStableUnderRetracts := by
  constructor
  intro X Y Z W f g h hg A B i hi a b hab
  obtain ⟨l, hl, hfl⟩ :=
    hg i hi (h.i.left.app (op A) a) (h.i.right.app (op B) b) (by
      rw [← NatTrans.naturality_apply]
      change g.app (op A) (h.i.left.app (op A) a) =
        h.i.right.app (op A) (Y.map i.op b)
      rw [← hab]
      exact congrArg (fun t => t.app (op A) a) h.i_w)
  refine ⟨h.r.left.app (op B) l, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply]
    change h.r.left.app (op A) (Z.map i.op l) = a
    rw [hl]
    exact congrArg (fun t => t.app (op A) a) h.retract_left
  · have hr := congrArg (fun t => t.app (op B) l) h.r_w
    change f.app (op B) (h.r.left.app (op B) l) = h.r.right.app (op B) (g.app (op B) l) at hr
    rw [hr, hfl]
    exact congrArg (fun t => t.app (op B) b) h.retract_right

theorem completion_weakEquivalences_retracts :
    (Completion.weakEquivalences.{w} C).IsStableUnderRetracts := by
  haveI := presheafWeakEquivalences_retracts.{w} (C := C)
  exact inferInstanceAs
    ((presheafWeakEquivalences.inverseImage (ObjectProperty.ι (IsCompletionPresheaf C))).IsStableUnderRetracts)

theorem completion_fibrations_retracts :
    (Completion.fibrations.{w} C).IsStableUnderRetracts := by
  haveI := presheafFibrations_retracts.{w} (C := C)
  exact inferInstanceAs
    ((presheafFibrations.inverseImage (ObjectProperty.ι (IsCompletionPresheaf C))).IsStableUnderRetracts)

theorem completion_trivialFibrations_retracts :
    (Completion.trivialFibrations.{w} C).IsStableUnderRetracts := by
  haveI := presheafTrivialFibrations_retracts.{w} (C := C)
  exact inferInstanceAs
    ((presheafTrivialFibrations.inverseImage (ObjectProperty.ι (IsCompletionPresheaf C))).IsStableUnderRetracts)

#print axioms completion_weakEquivalences_retracts
#print axioms completion_fibrations_retracts
#print axioms completion_trivialFibrations_retracts

end HomotopyHypothesis.Category.SemiModelConstruction
