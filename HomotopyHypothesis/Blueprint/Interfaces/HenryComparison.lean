import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Assembly.Theorem.Assembly

/-!
# `henry_comparison`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Henry's comparison with spaces** (H:2765–2798, Thm. 5.1.2(5), for an arbitrary cellular
realization; H:1440, Prop. 2.4.18; H:1367, Prop. 2.4.16). Interface for the theorem
`HomotopyHypothesis.Henry.comparison_with_spaces` of the Henry blueprint, in its announced form. -/
theorem henry_comparison {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
    [CategoryWithWeakEquivalences 𝒜] [EssentiallySmall.{u} 𝒜] (o : 𝒜)
    (h𝒜 : IsCylinderCoherator.{u + 1, u} 𝒜 o)
    (G : 𝒜 ⥤ TopCat.{u}) (hG : IsCellularRealization G) (ho : ContractibleSpace (G.obj o)) :
    Henry.Top.weakEquivalences ≤ (Completion.weakEquivalences 𝒜).inverseImage (topRestriction hG) ∧
    ∀ {H₁ H₂ : Type*} [Category H₁] [Category H₂] (L₁ : TopCat.{u} ⥤ H₁)
      [L₁.IsLocalization Henry.Top.weakEquivalences] (L₂ : Completion.{u} 𝒜 ⥤ H₂)
      [L₂.IsLocalization (Completion.weakEquivalences 𝒜)] (Φ : H₁ ⥤ H₂),
      (L₁ ⋙ Φ ≅ topRestriction hG ⋙ L₂) → Φ.IsEquivalence := by apply @_root_.HomotopyHypothesis.Assembly.Theorem.henry_comparison_proof <;> assumption
