import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.NormalForms.NormalForm
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `sharp_normalForm_face`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **Faces of normal forms** (frozen helper statement). If `(v', x')`, with `v'` surjective,
represents the face along `θ` of the simplex represented by `(v, x)`, then `v ∘ θ = ι ∘ v'` and
`x' = ι^* x` for an injective increasing `ι` (the enumeration of the image of `v ∘ θ`). -/
theorem sharp_normalForm_face {X : SemiSSet.{u}} {n n' m m' : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (v : Fin (n + 1) → Fin (m + 1)) (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (v' : Fin (n' + 1) → Fin (m' + 1)) (x' : X.obj (op (Henry.SemiSimplexCategory.mk m')))
    (hv' : Function.Surjective v')
    (h : (sharp X).map θ.op (sharpMk v x) = sharpMk v' x') :
    ∃ ι : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m,
      v ∘ θ.1.toOrderHom = ι.1.toOrderHom ∘ v' ∧ X.map ι.op x = x' := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Simplicial.NormalForms.sharp_normalForm_face_proof <;> assumption
