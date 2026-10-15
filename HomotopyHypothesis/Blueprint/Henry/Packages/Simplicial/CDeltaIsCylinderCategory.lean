import HomotopyHypothesis.Cylinder.SimplicialCategory.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial

/-!
# `cDelta_isCylinderCategory`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Prop 5.2.9 (H:2955–2983), repaired: `C^Δ` is a cylinder category. Henry's construction of
cylinders uses a relative cylinder for `∂Δ_n ↪ Δ_n` that is never constructed and a homotopy
`p ∘ b ≃ x` relative to the boundary that is never produced. Repair: with `M = Δ_n ⊔_{∂Δ_n} Δ_n`
and its semi-simplicial cone `CM`, the apex inclusion is a composite of horn pushouts (hence a
trivial cofibration by `cDelta_horn_weakEquivalence`), `M ↪ CM ⟶ Δ_n` is the needed relative
cylinder (extension over `CM` by `standardRealization_isHomotopyFullyFaithful`), and the map
`(p ∘ b, x) : M ⟶ X⁺` extends over `CM`, giving `IX⁺ = Z ⊔_{Δ_n} CM`. Retractions of trivial
cofibrations come from homotopy full faithfulness. -/
theorem cDelta_isCylinderCategory : IsCylinderCategory CDelta.{u} := @_root_.HomotopyHypothesis.Henry.Packages.cDelta_isCylinderCategory_proof
