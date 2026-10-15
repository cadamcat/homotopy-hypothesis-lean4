import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `topGlobes_eq`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

/-- The statement's topological globes are OpenAI-side globes along the isomorphism. -/
theorem topGlobes_eq : topGlobes.{u} = globeToOAI ⋙ oaiTopGlobes.{u} := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
  obtain ⟨_⟩ := X; obtain ⟨_⟩ := Y
  change HomotopyHypothesis.Grothendieck.Globe.Face _ _ at f
  cases f <;> rfl
