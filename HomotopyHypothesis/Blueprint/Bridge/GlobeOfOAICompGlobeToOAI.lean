import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `globeOfOAI_comp_globeToOAI`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

theorem globeOfOAI_comp_globeToOAI : globeOfOAI ⋙ globeToOAI = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
  obtain ⟨_⟩ := X; obtain ⟨_⟩ := Y
  change OAI.Grothendieck.Globe.Face _ _ at f
  cases f <;> rfl
