import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
/-!
# Cofibrant globular face maps

If the adjacent maps of a globular frame are trivial cofibrations, so are all of its proper face
maps. These are the gluing maps in the finite realization of globular sums.
-/

universe u v

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]

set_option backward.isDefEq.respectTransparency false in
/-- Every proper face of a frame with trivial adjacent maps is a trivial cofibration. -/
theorem frameFace_trivial (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    {m n : ℕ} (h : m < n) (side : Bool) :
    cofibrations X (B.diagram.face h side) ∧ weakEquivalences X (B.diagram.face h side) := by
  revert h
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    by_cases e : m = n
    · subst m
      cases side
      · simpa only [CoGlobularObject.face_succ, CoGlobularObject.adjacent,
          Bool.false_eq_true, ↓reduceIte] using (hB n).1
      · simpa only [CoGlobularObject.face_succ, CoGlobularObject.adjacent,
          ↓reduceIte] using (hB n).2
    · rw [CoGlobularObject.face, dif_neg e]
      have hm : m < n := by omega
      exact ⟨(IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _ (ih hm).1 (hB n).1.1,
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).comp_mem _ _
          (ih hm).2 (hB n).1.2⟩

#print axioms frameFace_trivial

end HomotopyHypothesis.FiniteCategory.Lifting
