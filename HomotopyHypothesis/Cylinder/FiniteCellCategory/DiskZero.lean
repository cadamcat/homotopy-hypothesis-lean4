import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

 theorem freeShape_terminal_rlp {C : GlobularTheory.{u}} (hC : C.IsCoherator) (S : Shape) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp
      (terminal.from (freeShape C S)) := by
  rintro _ _ _ ⟨n⟩
  apply (lifting_terminal_iff (I C n) (freeShape C S)).2
  intro a
  let R := boundaryRepresentation C n
  obtain ⟨z, hz⟩ := freeShape_hasFillers C hC S n (R.equiv (freeShape C S) a)
  refine ⟨(cellEquiv (freeShape C S) n).symm z, ?_⟩
  apply (R.equiv (freeShape C S)).injective
  rw [R.inclusion_boundary, Equiv.apply_symm_apply]
  exact hz

end HomotopyHypothesis.Cylinder.FiniteCellCategory

namespace HomotopyHypothesis.Blueprint.Packages

universe u

 theorem disk0_isHTerminal_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsHTerminal (disk0 hC) := by
  intro A B i hi a
  have hl : HasLiftingProperty i.hom (terminal.from (disk C 0)) :=
    Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C _ hi _
      (Cylinder.FiniteCellCategory.freeShape_terminal_rlp hC (Shape.globe 0))
  obtain ⟨b, hb⟩ := (lifting_terminal_iff i.hom (disk C 0)).1 hl a.hom
  refine ⟨ObjectProperty.homMk b, ?_⟩
  apply ObjectProperty.hom_ext
  exact hb

#print axioms disk0_isHTerminal_proof

end HomotopyHypothesis.Blueprint.Packages
