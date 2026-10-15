import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Comparison.FundamentalGroupoid.Comparison

/-!
# `pi_comparison`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Homotopy groups of `Π_∞`** (A:4309–4322, Cor. `charac_we`). For every realization `R`, a
continuous map `f` is a weak homotopy equivalence if and only if `Π_R f` is a weak equivalence of
models. Route: the `n`-cells of `Π_R X` are the maps `Dⁿ → X`; the base cells at a point `x` are
the constant maps (the units factor through the point `D⁰`); loops are maps `Dⁿ⁺¹ → X` sending the
boundary sphere to `x`, and `Joined` is homotopy relative to the boundary. This gives bijections
`Components (Π_R X) ≃ ZerothHomotopy X` and `HomotopyGroup (Π_R X) x n ≃ π_{n+1}(X, x)` natural in
`X` (Mathlib's cube model, through `Dⁿ⁺¹/Sⁿ ≅ Iⁿ⁺¹/∂Iⁿ⁺¹`). -/
theorem pi_comparison {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    W hC (R.Pi.map f) ↔ weakHomotopyEquivalences f := _root_.HomotopyHypothesis.Comparison.FundamentalGroupoid.pi_comparison_proof ..
