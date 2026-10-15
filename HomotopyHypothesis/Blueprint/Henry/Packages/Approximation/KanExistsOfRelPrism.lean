import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part2

/-!
# `kan_exists_of_relPrism`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Removing collapses and subdivisions in a Kan target** (Rourke–Sanderson, Thm. 5.3, cases 1–2,
for a given approximation). Let `X` satisfy the Kan condition, `J ⊆ Y`, `g : J ⟶ X`, `S` a relative
prism of `Y` relative to `J` and `f' : ‖Y'‖ ⟶ ‖X‖` simplicial with `f' = ‖g‖` on `J`. Then there is
a map `φ : Y ⟶ X` extending `g` whose realization is homotopic to `f'`, transported to `‖Y‖`
through the prism, relative to `‖J‖`. Proof: in the folded relative mapping cylinder of `f'`
(`exists_foldedMappingCylinder`, with `sharpMk_eq_of_vertexMap` on `J`) the identity of `X` extends
(`isKan_extension_of_anodyne`) to a semi-simplicial map `ψ : Y' ⟶ X` extending `g` and homotopic to
`f'` relative to `J`; extend `ψ` over the prism `C` and restrict to the end `Y`. All homotopies come
from the fact that realized collapses are strong deformation retractions
(`realization_anodyne_deformationRetract`). -/
theorem kan_exists_of_relPrism {X Y : SemiSSet.{u}} (hX : X.IsKan) (J : Subfunctor Y)
    (g : J.toFunctor ⟶ X) (S : RelPrism Y J) (f' : realization.obj S.Y' ⟶ realization.obj X)
    (hf' : IsSimplicial f') (hg : realization.map S.j ≫ f' = realization.map g) :
    ∃ φ : Y ⟶ X, J.ι ≫ φ = g ∧
      (realization.map φ).hom.HomotopicRel (realization.map S.c₁ ≫ S.ρ ≫ f').hom
        (Set.range (realization.map J.ι).hom) := by apply @_root_.HomotopyHypothesis.Henry.Packages.kan_exists_of_relPrism_proof <;> assumption
