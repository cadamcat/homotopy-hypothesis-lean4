import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Counit
import HomotopyHypothesis.Completion.FinitelyCellular.Phi
import HomotopyHypothesis.Completion.FinitelyCellular.Unit
/-
# The completion of A_fin is the category of models.

The restriction functor `C.Model ⥤ Completion (Afin C hC)` is an equivalence
of categories (Ara, Henry Prop. 5.3.7).
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

universe u

namespace HomotopyHypothesis.Completion.FinitelyCellular

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- The equivalence between models of a globular theory and the completion of its
category of finitely cellular models. -/
def completionEquivalence :
    C.Model ≌ Completion.{u} (Afin C hC) :=
  CategoryTheory.Equivalence.mk (Packages.restriction hC) (Phi hC)
    (unitNatIso hC) (counitNatIso hC)

/-- The restriction functor is an equivalence. -/
theorem completion_isEquivalence_proof :
    (Packages.restriction hC).IsEquivalence :=
  Functor.IsEquivalence.mk' (Phi hC) (unitNatIso hC) (counitNatIso hC)

end HomotopyHypothesis.Completion.FinitelyCellular

open HomotopyHypothesis.Completion.FinitelyCellular

#print axioms completion_isEquivalence_proof
