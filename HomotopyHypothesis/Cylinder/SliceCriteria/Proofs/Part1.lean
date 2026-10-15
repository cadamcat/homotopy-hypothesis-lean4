import Mathlib
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetPreFibration
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetRetraction
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Cylinder.SliceCategory.SliceAcyclicForward
import HomotopyHypothesis.Cylinder.SliceCategory.SliceCylinderCategory.Part1
import HomotopyHypothesis.Cylinder.SliceCategory.SliceInitialCofibration
import HomotopyHypothesis.Cylinder.SliceCategory.SlicePairPushout
import HomotopyHypothesis.Cylinder.SliceCategory.SlicePushout
import HomotopyHypothesis.Cylinder.SliceCategory.SliceWeakAxioms
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
import HomotopyHypothesis.Cylinder.SliceCriteria.HTerminal

/-!
# `HomotopyHypothesis.Cylinder.SliceCriteria.Proofs`, part 1

Lines 11–37 of `HomotopyHypothesis.Cylinder.SliceCriteria.Proofs`, split so that the modules of the development form an acyclic import graph.
-/

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCriteria

/-- Acyclicity of the slice forgetful functor forces its base to be h-terminal. -/
theorem isHTerminal_of_sliceForget_isAcyclic {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) (hac : IsAcyclic (SliceObj.forget X)) : IsHTerminal X := by
  letI : IsCylinderCategory (SliceObj X) := Cylinder.SliceCategory.slice_isCylinderCategory X
  obtain ⟨U, hU₀, hU⟩ := Cylinder.SliceCategory.exists_hTerminal_sliceCylinder X
  have h := isHTerminal_map_of_isAcyclic (Cylinder.SliceCategory.sliceForget_isCylinderMorphism X) hac hU
  change IsHTerminal U.A₀ at h
  simpa only [hU₀] using h

end HomotopyHypothesis.Cylinder.SliceCriteria

namespace HomotopyHypothesis.Henry.Packages

/-- H Proposition 4.4.1: a homotopy slice and its forgetful functor form a lifting target. -/
theorem sliceObj_isLiftingTarget_proof {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsLiftingTarget false (SliceObj X) C (SliceObj.forget X) :=
  Cylinder.SliceCategory.sliceObj_isLiftingTarget_proof X

/-- H Proposition 4.4.4: the homotopy-slice projection is acyclic exactly for h-terminal bases. -/
theorem sliceObj_forget_isAcyclic_iff_proof {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsAcyclic (SliceObj.forget X) ↔ IsHTerminal X :=
  ⟨Cylinder.SliceCriteria.isHTerminal_of_sliceForget_isAcyclic X,
    Cylinder.SliceCategory.sliceObj_forget_isAcyclic_of_hTerminal X⟩
