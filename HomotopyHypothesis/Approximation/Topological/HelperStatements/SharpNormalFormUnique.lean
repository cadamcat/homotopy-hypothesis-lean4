import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.SharpNormalForms.NormalForms
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `sharp_normalForm_unique`

One declaration of `HomotopyHypothesis.Approximation.Topological.HelperStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The representative with surjective vertex map is unique. (The image normalization
`(v, x) ↦ (v', ι^* x)` is constant on the equivalence classes of the pointwise colimit defining the
left Kan extension.) -/
theorem sharp_normalForm_unique {X : SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (v' : Fin (n + 1) → Fin (m' + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (x' : X.obj (op (Henry.SemiSimplexCategory.mk m')))
    (hv : Function.Surjective v) (hv' : Function.Surjective v')
    (h : sharpMk v x = sharpMk v' x') : m = m' ∧ HEq v v' ∧ HEq x x' := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_normalForm_unique_proof <;> assumption
