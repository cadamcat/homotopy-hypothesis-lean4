import HomotopyHypothesis.Blueprint.Bridge.FaceOfOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `globeOfOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

/-- OpenAI's globe category to the statement's. -/
def globeOfOAI : OAI.Grothendieck.Globe ⥤ HomotopyHypothesis.Grothendieck.Globe where
  obj n := ⟨n.dim⟩
  map f := faceOfOAI f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    obtain ⟨_⟩ := X; obtain ⟨_⟩ := Y; obtain ⟨_⟩ := Z
    change OAI.Grothendieck.Globe.Face _ _ at f g
    cases f <;> cases g <;> rfl
