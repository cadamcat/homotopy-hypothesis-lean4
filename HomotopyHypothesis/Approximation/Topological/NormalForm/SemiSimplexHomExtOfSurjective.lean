import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `semiSimplex_hom_ext_of_surjective`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A map of the semi-simplicial category is determined by its composite with a surjection. -/
theorem semiSimplex_hom_ext_of_surjective {k m m' : ℕ} (w : Fin (k + 1) → Fin (m' + 1))
    (hw : Function.Surjective w)
    {ι₁ ι₂ : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m}
    (h : ι₁.1.toOrderHom ∘ w = ι₂.1.toOrderHom ∘ w) : ι₁ = ι₂ := by
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext c
  obtain ⟨a, rfl⟩ := hw c
  exact congrFun h a
