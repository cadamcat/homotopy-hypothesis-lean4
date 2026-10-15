import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativePrism
/-!
# Composition of relative subdivision prisms

Successive relative subdivisions have pinched prisms that glue along the
intermediate complex. Their composite collapses onto the last derived end,
and its projection agrees with the inverse composite realization map on
the original end.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Glue two relative subdivision prisms along their intermediate complex. -/
def SubdivisionPrismCompositionStatement : Prop :=
  ∀ {Y : SemiSSet.{u}} (J : Subfunctor Y) (S₁ : RelSubdivision Y J)
    (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)),
    ∃ (C : SemiSSet.{u}) (a : S₂.Y' ⟶ C) (b : Y ⟶ C)
      (ρ : realization.obj C ⟶ realization.obj S₂.Y'),
      (Subfunctor.toRange S₁.j ≫ S₂.j) ≫ a = J.ι ≫ b ∧ anodyne a ∧
        realization.map a ≫ ρ = 𝟙 _ ∧
        realization.map b ≫ ρ = S₁.h.inv ≫ S₂.h.inv

end HomotopyHypothesis.Approximation.Zeeman
