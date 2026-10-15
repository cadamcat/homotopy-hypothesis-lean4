import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `isCylinderMorphism_toFinCell`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- A cellular realization is a morphism of cylinder categories into finite cell complexes
(pushouts and initial objects of spaces that lie in `FinCell` are pushouts and initial objects
there, since `FinCell ⥤ TopCat` is fully faithful). -/
theorem isCylinderMorphism_toFinCell {C : Type*} [Category C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] {G : C ⥤ TopCat.{u}} (hG : IsCellularRealization G) :
    IsCylinderMorphism hG.toFinCell := _root_.HomotopyHypothesis.CylinderCategoryTheory.isCylinderMorphism_toFinCell_proof ..
