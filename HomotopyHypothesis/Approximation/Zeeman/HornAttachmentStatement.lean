import Mathlib.CategoryTheory.Subfunctor.Image
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Prism
/-!
# Attaching a simplex along a horn

A simplex embedded in a semi-simplicial set can be adjoined to a subcomplex
by a horn pushout when its intersection with that subcomplex is exactly
the horn. This is the elementary step in a finite relative collapse.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Adjoining an embedded simplex whose intersection is a horn is anodyne. -/
def HornAttachmentStatement : Prop :=
  ∀ {C : SemiSSet.{u}} (A : Subfunctor C) (n : ℕ) (k : Fin (n + 2))
    (σ : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶ C),
    Mono σ → A.preimage σ = horn (n + 1) k →
      anodyne (Subfunctor.homOfLe
        (show A ≤ A ⊔ Subfunctor.range σ from le_sup_left))

end HomotopyHypothesis.Approximation.Zeeman
