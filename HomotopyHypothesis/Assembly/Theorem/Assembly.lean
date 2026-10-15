import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part3
import HomotopyHypothesis.Blueprint.Henry.Packages.Coherator.IsCylinderCoheratorOfLiftsAtHTerminal
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCofibrantAt
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.AfinLiftsAtHTerminal
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Blueprint.Interfaces.Disk0IsHTerminal
/-!
# Assembly of two outer packages from their inputs

`afin_isCylinderCoherator` is the generic reduction (Henry, Cor. 5.3.12) applied to the cylinder
category `A_fin`; `henry_comparison` is the comparison theorem of the Henry tree.
-/

noncomputable section

universe u

namespace HomotopyHypothesis.Assembly.Theorem

open CategoryTheory HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

theorem afin_isCylinderCoherator_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCylinderCoherator.{u + 1, u} (Afin C hC) (Blueprint.Packages.disk0 hC) := by
  have := Blueprint.Packages.afin_isCylinderCategory hC
  exact Henry.Packages.isCylinderCoherator_of_liftsAtHTerminal
    (Blueprint.Packages.afin_isCofibrantAt hC) (Blueprint.Packages.disk0_isHTerminal hC)
    (Blueprint.Packages.afin_liftsAtHTerminal hC)

theorem henry_comparison_proof {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
    [CategoryWithWeakEquivalences 𝒜] [EssentiallySmall.{u} 𝒜] (o : 𝒜)
    (h𝒜 : IsCylinderCoherator.{u + 1, u} 𝒜 o)
    (G : 𝒜 ⥤ TopCat.{u}) (hG : IsCellularRealization G) (ho : ContractibleSpace (G.obj o)) :
    Henry.Top.weakEquivalences ≤ (Completion.weakEquivalences 𝒜).inverseImage (topRestriction hG) ∧
    ∀ {H₁ H₂ : Type*} [Category H₁] [Category H₂] (L₁ : TopCat.{u} ⥤ H₁)
      [L₁.IsLocalization Henry.Top.weakEquivalences] (L₂ : Completion.{u} 𝒜 ⥤ H₂)
      [L₂.IsLocalization (Completion.weakEquivalences 𝒜)] (Φ : H₁ ⥤ H₂),
      (L₁ ⋙ Φ ≅ topRestriction hG ⋙ L₂) → Φ.IsEquivalence :=
  Henry.comparison_with_spaces o h𝒜 G hG ho

end HomotopyHypothesis.Assembly.Theorem

#print axioms HomotopyHypothesis.Assembly.Theorem.afin_isCylinderCoherator_proof
#print axioms HomotopyHypothesis.Assembly.Theorem.henry_comparison_proof
