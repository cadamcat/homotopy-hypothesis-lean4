import HomotopyHypothesis.Blueprint.Henry.Approximation

/-!
# `HomotopyHypothesis.Blueprint.Henry.KanSimplices`, part 1

Lines 16–23 of `HomotopyHypothesis.Blueprint.Henry.KanSimplices`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits

namespace HomotopyHypothesis.Henry

/-- Precomposition of a homotopy relative to a subset. -/
theorem homotopicRel_comp_right {X' X Y : Type*} [TopologicalSpace X'] [TopologicalSpace X]
    [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {S : Set X} (h : f₀.HomotopicRel f₁ S) (g : C(X', X))
    {S' : Set X'} (hS : ∀ x ∈ S', g x ∈ S) : (f₀.comp g).HomotopicRel (f₁.comp g) S' := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy.comp (ContinuousMap.Homotopy.refl g)
           prop' := fun t x hx => by simpa using F.eq_fst t (hS x hx) }⟩
