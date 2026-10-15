import HomotopyHypothesis.Blueprint.Bridge.FaceToOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `globeToOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

/-- The statement's globe category to OpenAI's. -/
def globeToOAI : HomotopyHypothesis.Grothendieck.Globe ⥤ OAI.Grothendieck.Globe where
  obj n := ⟨n.dim⟩
  map f := faceToOAI f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    obtain ⟨_⟩ := X; obtain ⟨_⟩ := Y; obtain ⟨_⟩ := Z
    change HomotopyHypothesis.Grothendieck.Globe.Face _ _ at f g
    cases f <;> cases g <;> rfl
