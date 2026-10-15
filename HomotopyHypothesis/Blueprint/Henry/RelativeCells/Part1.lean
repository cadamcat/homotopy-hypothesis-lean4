import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial

/-!
# `HomotopyHypothesis.Blueprint.Henry.RelativeCells`, part 1

Lines 21–35 of `HomotopyHypothesis.Blueprint.Henry.RelativeCells`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

/-- The map between free algebraic Kan complexes induced by `∂Δ_n ↪ Δ_n` is a free cell
attachment, hence a cofibration of `C^Δ`. -/
theorem cofibration_of_isFreeOn_boundary {n : ℕ} {B D : CDelta.{u}}
    {ηB : (SemiSSet.boundary.{u} n).toFunctor ⟶ B.obj.X}
    {ηD : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ D.obj.X}
    (hB : B.obj.IsFreeOn ηB) (hD : D.obj.IsFreeOn ηD) (ι : B ⟶ D)
    (hι : ηB ≫ ι.hom.hom = (SemiSSet.boundary n).ι ≫ ηD) : cofibrations CDelta.{u} ι := by
  refine MorphismProperty.multiplicativeClosure.of _ (Or.inl ?_)
  refine ⟨n, ηB, ηD, hι.symm, fun Z g z hz => ?_⟩
  obtain ⟨g', hg', hu⟩ := hD Z z
  refine ⟨g', ⟨?_, hg'⟩, fun g'' h => hu g'' h.2⟩
  refine (hB Z (ηB ≫ g.hom)).unique ?_ rfl
  change ηB ≫ ι.hom.hom ≫ g'.hom = ηB ≫ g.hom
  rw [← Category.assoc, hι, Category.assoc, hg', hz]
