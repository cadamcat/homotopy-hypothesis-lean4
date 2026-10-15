import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.StdSimplex

/-!
# `stdSimplex_isFinite`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- The standard simplex `Δ_n` is a finite semi-simplicial set (its `m`-simplices are the injective
monotone maps `[m] ⟶ [n]`). -/
theorem stdSimplex_isFinite (n : ℕ) :
    (stdSimplex.{u}.obj (SemiSimplexCategory.mk n)).IsFinite := _root_.HomotopyHypothesis.Approximation.Anodyne.stdSimplex_isFinite_proof ..
