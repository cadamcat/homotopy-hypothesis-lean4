import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

theorem fibrant_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) (X : C.Model) :
    (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp (terminal.from X) := by
  have hJ : ∀ n, HasLiftingProperty (J C n) (terminal.from X) := by
    intro n
    rw [hasLiftingProperty_J_iff]
    intro x y _hy
    refine ⟨X.unitCell hC n x, X.unitCell_source hC n x, ?_⟩
    apply (cellEquiv (⊤_ C.Model) (n + 1)).symm.injective
    exact terminal.hom_ext _ _
  rintro A B i ⟨n⟩
  exact hJ n

#print axioms fibrant_proof

end HomotopyHypothesis.Blueprint.Packages
