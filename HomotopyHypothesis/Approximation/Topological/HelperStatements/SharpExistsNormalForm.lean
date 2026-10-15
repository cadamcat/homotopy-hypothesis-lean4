import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.SharpNormalForms.NormalForms
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `sharp_exists_normalForm`

One declaration of `HomotopyHypothesis.Approximation.Topological.HelperStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Every simplex of `X♯` is represented by a vertex map onto (surjective) a simplex of `X`.
(Factor any representative `(v, x)` as `v = ι ∘ v'` with `v'` surjective onto the image and `ι`
the increasing enumeration of the image; then `(v, x)` and `(v', ι^* x)` represent the same
simplex.) -/
theorem sharp_exists_normalForm {X : SemiSSet.{u}} {n : ℕ}
    (e : (sharp X).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ (m : ℕ) (v : Fin (n + 1) → Fin (m + 1))
      (x : X.obj (op (Henry.SemiSimplexCategory.mk m))),
      Function.Surjective v ∧ sharpMk v x = e := _root_.HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_exists_normalForm_proof ..
