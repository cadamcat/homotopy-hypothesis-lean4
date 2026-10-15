import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCoherator.Main

/-!
# `isCylinderCoherator_of_liftsAtHTerminal`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Coherator`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

variable {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
  [CategoryWithWeakEquivalences 𝒜]

/-- H Cor 5.3.12 (H:3143–3177), generic form: a cylinder category `𝒜`, cofibrant at an h-terminal
object `o` and with the lifting property of H Lemma 5.3.9 at `o`, is a cylinder coherator at `o`.
Proof: given a square `(x, h)` against a pre-fibration `p : X ⥤ Y`, lift `h` to `Y^{p x}`
(`lift_to_sliceObj`), lift the cylinder of `p x` to a cylinder of `x` (`p` is a pre-fibration), and
apply the lifting property to the pre-fibration `X^x ⥤ Y^{p x}` (`sliceObj_map_isLiftingTarget`)
at the h-terminal objects `(x, I x)` and `(p x, I p x)` (`sliceObj_isHTerminal`). -/
theorem isCylinderCoherator_of_liftsAtHTerminal [IsCylinderCategory 𝒜] {o : 𝒜}
    (hcof : IsCofibrantAt.{u + 1, u} 𝒜 o) (ho : IsHTerminal o)
    (hlift : LiftsAtHTerminal.{u + 1, u} 𝒜 o) : IsCylinderCoherator.{u + 1, u} 𝒜 o := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Cylinder.SliceCoherator.isCylinderCoherator_of_liftsAtHTerminal_proof <;> assumption
