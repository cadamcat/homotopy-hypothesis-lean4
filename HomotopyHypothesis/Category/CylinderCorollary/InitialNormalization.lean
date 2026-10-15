import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerInverses
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
import HomotopyHypothesis.Category.CylinderCorollary.OperationFaces
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def initialNormalization (hC : C.IsCoherator) (i d : ℕ) :
    C.Hom (Shape.globe (i + 1 + d)) (lowerPairShape i (i + 1 + d) (by omega)) :=
  operationComposition hC i d
    (operationInverse hC i d (C.base (lowerPairLeft i (i + 1 + d) (by omega))))
    (lowerCompositionOp hC i d) (by
      rw [operationInverse_boundary, lowerCompositionOp_boundary]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, C.base_comp])

theorem initialNormalization_boundary (hC : C.IsCoherator) (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (initialNormalization hC i d) =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (C.base (lowerPairRight i (i + 1 + d) (by omega))) := by
  dsimp only [initialNormalization]
  rw [operationComposition_boundary]
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [operationInverse_boundary]
    simp only [Bool.not_false, ← C.base_comp]
    exact congrArg C.base (lowerPair_seam i (i + 1 + d) (by omega))
  · simp only [↓reduceIte]
    rw [lowerCompositionOp_boundary]
    exact C.base_comp _ _

theorem initialNormalization_face (hC : C.IsCoherator) (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
        (initialNormalization hC i (d + 1)) =
      C.comp (initialNormalization hC i d)
        (lowerPairFace C i (i + 1 + d) (by omega) side) := by
  have hg : C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
      (operationInverse hC i (d + 1)
        (C.base (lowerPairLeft i (i + 1 + (d + 1)) (by omega)))) =
      C.comp (operationInverse hC i d
        (C.base (lowerPairLeft i (i + 1 + d) (by omega))))
        (lowerPairFace C i (i + 1 + d) (by omega) side) := by
    rw [operationInverse_face]
    dsimp only [operationInverse]
    rw [C.assoc]
    exact congrArg (C.comp (lowerInverseOp hC i d))
      ((C.base_comp _ _).symm.trans (lowerPairFace_left C i (i + 1 + d) (by omega) side).symm)
  dsimp only [initialNormalization]
  rw [operationComposition_face]
  simp only [hg, lowerCompositionOp_face]
  symm
  apply operationComposition_postcomp

def initialCorrectionPair (hC : C.IsCoherator) (i : ℕ) : C.AdmissiblePair where
  n := i + 1
  arity := lowerPairShape i (i + 1) (Nat.lt_succ_self i)
  height := by
    change max (i + 1) (i + 1) ≤ i + 1 + 1
    omega
  source := C.base (lowerPairRight i (i + 1) (Nat.lt_succ_self i))
  target := initialNormalization hC i 0
  parallel := by
    constructor
    · exact (initialNormalization_boundary hC i 0 false).symm
    · exact (initialNormalization_boundary hC i 0 true).symm

def initialCorrection (hC : C.IsCoherator) (i : ℕ) :
    C.Hom (Shape.globe (i + 1 + 1)) (lowerPairShape i (i + 1) (Nat.lt_succ_self i)) :=
  (hC.2 (initialCorrectionPair hC i)).choose

theorem initialCorrection_source (hC : C.IsCoherator) (i : ℕ) :
    C.comp (C.base (Shape.source (i + 1))) (initialCorrection hC i) =
      C.base (lowerPairRight i (i + 1) (Nat.lt_succ_self i)) :=
  (hC.2 (initialCorrectionPair hC i)).choose_spec.1

theorem initialCorrection_target (hC : C.IsCoherator) (i : ℕ) :
    C.comp (C.base (Shape.target (i + 1))) (initialCorrection hC i) =
      initialNormalization hC i 0 :=
  (hC.2 (initialCorrectionPair hC i)).choose_spec.2

def initialReverseCorrection (hC : C.IsCoherator) (i : ℕ) :
    C.Hom (Shape.globe (i + 1 + 1)) (lowerPairShape i (i + 1) (Nat.lt_succ_self i)) :=
  operationInverse hC (i + 1) 0 (initialCorrection hC i)

theorem initialReverseCorrection_source (hC : C.IsCoherator) (i : ℕ) :
    C.comp (C.base (Shape.source (i + 1))) (initialReverseCorrection hC i) =
      initialNormalization hC i 0 :=
  (operationInverse_boundary hC (i + 1) 0 false (initialCorrection hC i)).trans
    (initialCorrection_target hC i)

theorem initialReverseCorrection_target (hC : C.IsCoherator) (i : ℕ) :
    C.comp (C.base (Shape.target (i + 1))) (initialReverseCorrection hC i) =
      C.base (lowerPairRight i (i + 1) (Nat.lt_succ_self i)) :=
  (operationInverse_boundary hC (i + 1) 0 true (initialCorrection hC i)).trans
    (initialCorrection_source hC i)

#print axioms initialNormalization_boundary
#print axioms initialNormalization_face
#print axioms initialCorrection_source
#print axioms initialCorrection_target
#print axioms initialReverseCorrection_source
#print axioms initialReverseCorrection_target

end HomotopyHypothesis.Category.CylinderCorollary
