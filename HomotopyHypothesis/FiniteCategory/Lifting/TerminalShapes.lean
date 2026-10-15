import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Homotopy.Terminality.HTerminalInvariant
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
universe u v u₁

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]

/-- A finite frame shape is h-terminal when the frame's zero disk is h-terminal. -/
theorem finiteFrame_shape_hterminal (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (h₀ : IsHTerminal (B.obj 0)) (S : Shape) :
    IsHTerminal ((finiteFrameRealization B hB).obj S) := by
  obtain ⟨w, hw⟩ := finiteFrame_shape_from_zero B hB S
  exact ((Homotopy.Terminality.hTerminalInvariantStatement_proof X) w hw).1 h₀

/-- The shape arities and their images are h-terminal when both zero disks are h-terminal. -/
theorem finiteFrame_shapes_hterminal_over (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (p : X ⥤ Y) (hp : IsCylinderMorphism p) (h₀ : IsHTerminal (B.obj 0))
    (hp₀ : IsHTerminal (p.obj (B.obj 0))) (S : Shape) :
    IsHTerminal ((finiteFrameRealization B hB).obj S) ∧
      IsHTerminal (p.obj ((finiteFrameRealization B hB).obj S)) := by
  obtain ⟨w, hw⟩ := finiteFrame_shape_from_zero B hB S
  exact ⟨finiteFrame_shape_hterminal B hB h₀ S,
    ((Homotopy.Terminality.hTerminalInvariantStatement_proof Y) (p.map w)
      (hp.map_weakEquivalence w hw)).1 hp₀⟩

#print axioms finiteFrame_shapes_hterminal_over

end HomotopyHypothesis.FiniteCategory.Lifting
