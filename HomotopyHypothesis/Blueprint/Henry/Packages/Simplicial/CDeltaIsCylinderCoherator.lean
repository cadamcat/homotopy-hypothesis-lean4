import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Coherator.Comparison.Coherator

/-!
# `cDelta_isCylinderCoherator`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Prop 5.2.11 (H:2994–3000): `C^Δ` is a cylinder coherator at the free point `Δ₀`: the morphism
`F_* ⟶ C^Δ_0` is a trivial cofibration (lift the cells `∂Δ_n ↪ Δ_n ⥲ Δ_0` one dimension at a time
through the pre-fibration; "trivial fibration" at H:2998 should read "(pre-)fibration"), and
`C^Δ_0 ⟶ C^Δ` freely adds retractions of trivial cofibrations. -/
theorem cDelta_isCylinderCoherator (o : CDelta.{u})
    (η : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk 0) ⟶ o.obj.X) (hη : o.obj.IsFreeOn η) :
    IsCylinderCoherator.{u + 1, u} CDelta.{u} o := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Henry.Packages.cDelta_isCylinderCoherator_proof <;> assumption
