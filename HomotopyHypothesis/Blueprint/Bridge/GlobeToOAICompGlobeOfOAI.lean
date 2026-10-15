import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `globeToOAI_comp_globeOfOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

theorem globeToOAI_comp_globeOfOAI : globeToOAI ⋙ globeOfOAI = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
  obtain ⟨_⟩ := X; obtain ⟨_⟩ := Y
  change HomotopyHypothesis.Grothendieck.Globe.Face _ _ at f
  cases f <;> rfl
