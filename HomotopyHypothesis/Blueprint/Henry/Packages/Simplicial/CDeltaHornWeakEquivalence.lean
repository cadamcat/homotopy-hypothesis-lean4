import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.HornWeq

/-!
# `cDelta_horn_weakEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Prop 5.2.3 (H:2850–2865): the free maps on the horn inclusions `Λ^{n+1}_k ↪ Δ_{n+1}` are
weak equivalences of `C^Δ` (induction on the dimension, filtering `Λ` through sub-objects obtained
by pushouts along lower-dimensional horn inclusions; the index at H:2859 should read `X_n`). -/
theorem cDelta_horn_weakEquivalence (n : ℕ) (k : Fin (n + 2)) {X Y : CDelta.{u}}
    (ηX : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ X.obj.X)
    (ηY : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk (n + 1)) ⟶ Y.obj.X)
    (hX : X.obj.IsFreeOn ηX) (hY : Y.obj.IsFreeOn ηY) (f : X ⟶ Y)
    (hf : ηX ≫ f.hom.hom = (SemiSSet.horn (n + 1) k).ι ≫ ηY) :
    weakEquivalences CDelta.{u} f := by apply @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.cDelta_horn_weakEquivalence_proof <;> assumption
