import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Category.SemiModelStructure.Factorization
import HomotopyHypothesis.Category.SemiModelStructure.LeftCancel
import HomotopyHypothesis.Category.SemiModelConstruction.Assembly
import HomotopyHypothesis.Category.SemiModelConstruction.WeakEquivalences
/-!
# The completion of a cylinder category is a semi-model category

Henry, *Algebraic models of homotopy types and the homotopy hypothesis*, Thm 2.4.14: the completion
of an essentially small cylinder category is a semi-model category in which every object is
fibrant.
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

/-- Weak equivalences of the completion satisfy two-out-of-three. -/
theorem completion_weakEquivalences_twoOutOfThree :
    (Completion.weakEquivalences.{w} C).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := completion_weakEquivalence_comp f g hf hg
  of_postcomp f g hg hfg := completion_weakEquivalence_of_postcomp f g hg hfg
  of_precomp f g hf hfg := completion_weakEquivalence_of_precomp f g hf hfg

end HomotopyHypothesis.Category.SemiModelStructure

namespace HomotopyHypothesis.Henry.Packages

open Category.SemiModelStructure Category.SemiModelConstruction

/-- Henry, Thm 2.4.14: the completion of an essentially small cylinder category is a semi-model
category in which every object is fibrant. -/
theorem completion_isSemiModelCategory_proof {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    [EssentiallySmall.{w} C] :
    IsSemiModelCategory (Completion.{w} C) (Completion.cofibrations C) (Completion.fibrations C)
      (Completion.weakEquivalences C) ∧
    ∀ X : Completion.{w} C, IsFibrantFor (Completion.fibrations C) X :=
  completion_isSemiModelCategory_of completion_weakEquivalences_twoOutOfThree
    (fun _ _ i hX hi => completion_weakEquivalence_of_llp_fibrations i hX hi)

#print axioms completion_isSemiModelCategory_proof

end HomotopyHypothesis.Henry.Packages
