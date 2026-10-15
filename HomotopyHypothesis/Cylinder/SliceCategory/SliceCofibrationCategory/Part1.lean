import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.SliceLifting.Proofs.Part1
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Cylinder.SliceCategory.SliceCofibrationAxioms
import HomotopyHypothesis.Cylinder.SliceCategory.SliceInitialCofibration
import HomotopyHypothesis.Cylinder.SliceCategory.SlicePushout

/-!
# `HomotopyHypothesis.Cylinder.SliceCategory.SliceCofibrationCategory`, part 1

Lines 11–27 of `HomotopyHypothesis.Cylinder.SliceCategory.SliceCofibrationCategory`, split so that the modules of the development form an acyclic import graph.
-/

open CategoryTheory HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The Reedy cofibrations make a homotopy slice a cofibration category. -/
theorem slice_isCofibrationCategory {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsCofibrationCategory (SliceObj X) where
  isomorphisms_le := sliceCofibration_isomorphisms X
  isMultiplicative := sliceCofibration_multiplicative
  exists_initial := HomotopyHypothesis.Cylinder.SliceLifting.slice_exists_initial X
  initial_cofibration := sliceCofibration_initial
  hasPushout := by
    intro A B D f g hf
    obtain ⟨P, u, v, h, h₀, _, hv, _⟩ := slice_pushout_exists f g hf
    exact h.hasPushout
  isStableUnderCobaseChange := by
    constructor
    intro A A' B B' f g f' g' h hf
    exact sliceCofibration_cobaseChange f g g' f' h.flip hf
