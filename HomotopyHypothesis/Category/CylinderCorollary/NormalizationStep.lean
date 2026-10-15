import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.IteratedUnits
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}} {i h : ℕ} {hi : i < h} {anchor : Bool}

def liftedSourceCorrection (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor)
    (n : ℕ) (hn : h + 1 ≤ n) : C.Hom (Shape.globe n) (lowerPairShape i n (by omega)) :=
  C.comp (unitExtension hC (h + 1) n hn (normalizationCorrection hC A))
    (lowerPairMap C i h n hi (by omega) false)

def liftedTargetCorrection (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor)
    (n : ℕ) (hn : h + 1 ≤ n) : C.Hom (Shape.globe n) (lowerPairShape i n (by omega)) :=
  C.comp (unitExtension hC (h + 1) n hn (normalizationReverseCorrection hC A))
    (lowerPairMap C i h n hi (by omega) true)

theorem liftedSourceCorrection_boundary (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : h < n) side))
        (liftedSourceCorrection hC A n hn) =
      C.comp (if side then A.operation h le_rfl else C.base (lowerPairInclusion i h hi anchor))
        (lowerPairMap C i h n hi (by omega) false) := by
  dsimp only [liftedSourceCorrection]
  rw [← C.assoc, unitExtension_lowerFace hC h (h + 1) n (Nat.lt_succ_self h)
    hn side (normalizationCorrection hC A)]
  cases side
  · exact congrArg (fun q => C.comp q (lowerPairMap C i h n hi (by omega) false))
      (normalizationCorrection_source hC A)
  · exact congrArg (fun q => C.comp q (lowerPairMap C i h n hi (by omega) false))
      (normalizationCorrection_target hC A)

theorem liftedTargetCorrection_boundary (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : h < n) side))
        (liftedTargetCorrection hC A n hn) =
      C.comp (if side then C.base (lowerPairInclusion i h hi anchor) else A.operation h le_rfl)
        (lowerPairMap C i h n hi (by omega) true) := by
  dsimp only [liftedTargetCorrection]
  rw [← C.assoc, unitExtension_lowerFace hC h (h + 1) n (Nat.lt_succ_self h)
    hn side (normalizationReverseCorrection hC A)]
  cases side
  · exact congrArg (fun q => C.comp q (lowerPairMap C i h n hi (by omega) true))
      (normalizationReverseCorrection_source hC A)
  · exact congrArg (fun q => C.comp q (lowerPairMap C i h n hi (by omega) true))
      (normalizationReverseCorrection_target hC A)

theorem liftedSourceCorrection_source (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) :
    C.comp (C.base (Shape.face (by omega : h < n) false)) (liftedSourceCorrection hC A n hn) =
      C.comp (C.base (Shape.face (by omega : h < n) false))
        (C.base (lowerPairInclusion i n (by omega) anchor)) := by
  rw [liftedSourceCorrection_boundary hC A n hn false]
  exact (lowerPairMap_inclusion C i h n hi (by omega) anchor false).trans (C.base_comp _ _)

theorem liftedSourceCorrection_target (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) :
    C.comp (C.base (Shape.face (by omega : h < n) true)) (liftedSourceCorrection hC A n hn) =
      C.comp (C.base (Shape.face (by omega : h < n) false)) (A.operation n (by omega)) := by
  rw [liftedSourceCorrection_boundary hC A n hn true]
  exact (A.generalFace h n le_rfl (by omega) false).symm

theorem liftedTargetCorrection_source (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) :
    C.comp (C.base (Shape.face (by omega : h < n) false)) (liftedTargetCorrection hC A n hn) =
      C.comp (C.base (Shape.face (by omega : h < n) true)) (A.operation n (by omega)) := by
  rw [liftedTargetCorrection_boundary hC A n hn false]
  exact (A.generalFace h n le_rfl (by omega) true).symm

theorem liftedTargetCorrection_target (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) :
    C.comp (C.base (Shape.face (by omega : h < n) true)) (liftedTargetCorrection hC A n hn) =
      C.comp (C.base (Shape.face (by omega : h < n) true))
        (C.base (lowerPairInclusion i n (by omega) anchor)) := by
  rw [liftedTargetCorrection_boundary hC A n hn true]
  exact (lowerPairMap_inclusion C i h n hi (by omega) anchor true).trans (C.base_comp _ _)

theorem liftedSourceCorrection_face (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (liftedSourceCorrection hC A (n + 1) (Nat.le_trans hn (Nat.le_succ n))) =
      C.comp (liftedSourceCorrection hC A n hn) (lowerPairFace C i n (by omega) side) := by
  dsimp only [liftedSourceCorrection]
  rw [← C.assoc, unitExtension_face hC (h + 1) n hn side,
    C.assoc, ← lowerPairMap_succ C i n (by omega) side, lowerPairMap_comp]

theorem liftedTargetCorrection_face (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (liftedTargetCorrection hC A (n + 1) (Nat.le_trans hn (Nat.le_succ n))) =
      C.comp (liftedTargetCorrection hC A n hn) (lowerPairFace C i n (by omega) side) := by
  dsimp only [liftedTargetCorrection]
  rw [← C.assoc, unitExtension_face hC (h + 1) n hn side,
    C.assoc, ← lowerPairMap_succ C i n (by omega) side, lowerPairMap_comp]

def normalizationStepOperation (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor)
    (n : ℕ) (hn : h + 1 ≤ n) : C.Hom (Shape.globe n) (lowerPairShape i n (by omega)) :=
  operationCompositionAt hC h n (by omega) (liftedSourceCorrection hC A n hn)
    (operationCompositionAt hC h n (by omega) (A.operation n (by omega))
      (liftedTargetCorrection hC A n hn) (liftedTargetCorrection_source hC A n hn).symm)
    (by
      rw [operationCompositionAt_boundary hC h n (by omega) false]
      exact liftedSourceCorrection_target hC A n hn)

theorem normalizationStepOperation_boundary (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : h < n) side)) (normalizationStepOperation hC A n hn) =
      C.comp (C.base (Shape.face (by omega : h < n) side))
        (C.base (lowerPairInclusion i n (by omega) anchor)) := by
  dsimp only [normalizationStepOperation]
  rw [operationCompositionAt_boundary hC h n (by omega) side]
  cases side
  · exact liftedSourceCorrection_source hC A n hn
  · simp only [↓reduceIte]
    rw [operationCompositionAt_boundary hC h n (by omega) true]
    exact liftedTargetCorrection_target hC A n hn

theorem normalizationStepOperation_face (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (normalizationStepOperation hC A (n + 1) (Nat.le_trans hn (Nat.le_succ n))) =
      C.comp (normalizationStepOperation hC A n hn) (lowerPairFace C i n (by omega) side) := by
  dsimp only [normalizationStepOperation]
  rw [operationCompositionAt_face hC h n (by omega) side]
  simp only [liftedSourceCorrection_face hC A n hn side,
    operationCompositionAt_face hC h n (by omega) side, A.face n (by omega) side,
    liftedTargetCorrection_face hC A n hn side,
    operationCompositionAt_postcomp hC h n (by omega)]

def nextNormalizationFamily (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor) :
    NormalizationFamilyAt C i (h + 1) (by omega) anchor where
  operation := normalizationStepOperation hC A
  parallel := by
    constructor
    · exact normalizationStepOperation_boundary hC A (h + 1) le_rfl false
    · exact normalizationStepOperation_boundary hC A (h + 1) le_rfl true
  face := normalizationStepOperation_face hC A

#print axioms liftedSourceCorrection_face
#print axioms liftedTargetCorrection_face
#print axioms normalizationStepOperation_boundary
#print axioms normalizationStepOperation_face
#print axioms nextNormalizationFamily

end HomotopyHypothesis.Category.CylinderCorollary
