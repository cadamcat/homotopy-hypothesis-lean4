import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CylinderCategory

/-!
# `afin_isCylinderCategory`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **`A_fin` is a cylinder category** (H:3084, Prop. 5.3.6, with the repairs of gap review A (R5)
and B §1.2: 2-out-of-6, pushout stability of trivial cofibrations from Cor. 4.1, relative
cylinders `Dⱼ ⊔_{∂Dⱼ} Dⱼ ⟶ Dⱼ₊₁ ⟶ Dⱼ` (OA:04:170–181) extended by finite cell induction,
retractions of trivial cofibrations from `trivialCofibration_lift` and `fibrant`). -/
theorem afin_isCylinderCategory {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCylinderCategory (Afin C hC) := _root_.HomotopyHypothesis.Blueprint.Packages.afin_isCylinderCategory_proof ..
