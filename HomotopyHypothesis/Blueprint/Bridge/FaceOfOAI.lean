import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `faceOfOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

/-- Faces of OpenAI's globe category as faces of the statement's. -/
def faceOfOAI : ∀ {m n : ℕ}, OAI.Grothendieck.Globe.Face m n →
    HomotopyHypothesis.Grothendieck.Globe.Face m n
  | _, _, .id n => .id n
  | _, _, .face h b => .face h b
