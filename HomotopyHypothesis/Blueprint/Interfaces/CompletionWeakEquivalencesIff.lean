import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Homotopy.WeakEquivalence.Proof

/-!
# `completion_weakEquivalences_iff`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Weak equivalences match** (H:3091–3108 with H:1444–1460, Prop. 2.4.19: Henry's weak
equivalences of the completion are detected by relative cylinders of the generating cofibrations
`∂Dⱼ ⟶ Dⱼ`, whose cylinder is `Dⱼ₊₁`; this is OpenAI's weak-equivalence test, OA:01:318). -/
theorem completion_weakEquivalences_iff {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {X Y : C.Model} (f : X ⟶ Y) :
    Completion.weakEquivalences (Afin C hC) ((restriction hC).map f) ↔ W hC f := _root_.HomotopyHypothesis.Blueprint.Packages.completion_weakEquivalences_iff_proof ..
