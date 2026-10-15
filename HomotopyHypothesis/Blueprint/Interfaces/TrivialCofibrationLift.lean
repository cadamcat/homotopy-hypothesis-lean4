import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.TrivialCofibration

/-!
# `trivialCofibration_lift`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Trivial cofibrations with cofibrant domain lift against fibrations** (OA:04:28–120,
Cor. `semimodel`: transfinite composites of elementary expansions, `elementary_expansion` extended
to cofibrant starts by retracts, the small object argument for `J`, and the retract argument). -/
theorem trivialCofibration_lift {C : GlobularTheory.{u}} (hC : C.IsCoherator) {X Y P Q : C.Model}
    (i : X ⟶ Y) (hi : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp i) (hwi : W hC i)
    (hX : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp (initial.to X))
    (p : P ⟶ Q) (hp : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp p) :
    HasLiftingProperty i p := by apply @_root_.HomotopyHypothesis.Blueprint.Packages.trivialCofibration_lift_proof <;> assumption
