import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.EndComparison

/-!
# `lifting_test`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Lifting test** (OA:01:411–441, Lemma `lifting-test`; OA:04:51):
`I-inj = W ∩ J-inj`. -/
theorem lifting_test {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp =
      W hC ⊓ (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp := _root_.HomotopyHypothesis.Blueprint.Packages.lifting_test_proof ..
