import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `faceToOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

/-- Faces of the statement's globe category as faces of OpenAI's. -/
def faceToOAI : ∀ {m n : ℕ}, HomotopyHypothesis.Grothendieck.Globe.Face m n →
    OAI.Grothendieck.Globe.Face m n
  | _, _, .id n => .id n
  | _, _, .face h b => .face h b
