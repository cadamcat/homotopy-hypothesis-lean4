import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.GenericNormalization
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationStep
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def pairCompositionAt (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe n) (lowerPairShape i n hi) :=
  operationCompositionAt hC i n hi (C.base (lowerPairLeft i n hi))
    (C.base (lowerPairRight i n hi))
    ((C.base_comp _ _).symm.trans ((congrArg C.base (lowerPair_seam i n hi)).trans (C.base_comp _ _)))

theorem pairCompositionAt_boundary (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (side : Bool) :
    C.comp (C.base (Shape.face hi side)) (pairCompositionAt hC i n hi) =
      C.comp (C.base (Shape.face hi side)) (C.base (lowerPairInclusion i n hi side)) := by
  dsimp only [pairCompositionAt]
  rw [operationCompositionAt_boundary]
  cases side <;> rfl

theorem pairCompositionAt_face (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (pairCompositionAt hC i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) =
      C.comp (pairCompositionAt hC i n hi) (lowerPairFace C i n hi side) := by
  have hl : C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
      (C.base (lowerPairLeft i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)))) =
      C.comp (C.base (lowerPairLeft i n hi)) (lowerPairFace C i n hi side) :=
    (C.base_comp _ _).symm.trans (lowerPairFace_left C i n hi side).symm
  have hr : C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
      (C.base (lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)))) =
      C.comp (C.base (lowerPairRight i n hi)) (lowerPairFace C i n hi side) :=
    (C.base_comp _ _).symm.trans (lowerPairFace_right C i n hi side).symm
  dsimp only [pairCompositionAt]
  rw [operationCompositionAt_face hC i n hi side]
  simp only [hl, hr, operationCompositionAt_postcomp hC i n hi]

def initialRightNormalizationAt (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe n) (lowerPairShape i n hi) :=
  operationCompositionAt hC i n hi (pairCompositionAt hC i n hi)
    (operationInverseAt hC i n hi (C.base (lowerPairRight i n hi))) (by
      rw [pairCompositionAt_boundary hC i n hi true,
        operationInverseAt_boundary hC i n hi false]
      rfl)

theorem initialRightNormalizationAt_boundary (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) :
    C.comp (C.base (Shape.face hi side)) (initialRightNormalizationAt hC i n hi) =
      C.comp (C.base (Shape.face hi side)) (C.base (lowerPairLeft i n hi)) := by
  dsimp only [initialRightNormalizationAt]
  rw [operationCompositionAt_boundary]
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [pairCompositionAt_boundary hC i n hi false]
    rfl
  · simp only [↓reduceIte]
    rw [operationInverseAt_boundary hC i n hi true]
    simp only [Bool.not_true, ← C.base_comp]
    exact congrArg C.base (lowerPair_seam i n hi).symm

theorem initialRightNormalizationAt_face (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (initialRightNormalizationAt hC i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) =
      C.comp (initialRightNormalizationAt hC i n hi) (lowerPairFace C i n hi side) := by
  have hr : C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
      (C.base (lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)))) =
      C.comp (C.base (lowerPairRight i n hi)) (lowerPairFace C i n hi side) :=
    (C.base_comp _ _).symm.trans (lowerPairFace_right C i n hi side).symm
  have hg : C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
      (operationInverseAt hC i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))
        (C.base (lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))))) =
      C.comp (operationInverseAt hC i n hi (C.base (lowerPairRight i n hi)))
        (lowerPairFace C i n hi side) := by
    rw [operationInverseAt_face hC i n hi side]
    simp only [hr, operationInverseAt_postcomp hC i n hi]
  dsimp only [initialRightNormalizationAt]
  rw [operationCompositionAt_face hC i n hi side]
  simp only [pairCompositionAt_face hC i n hi side, hg,
    operationCompositionAt_postcomp hC i n hi]

def initialRightNormalizationFamily (hC : C.IsCoherator) (i : ℕ) :
    NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) false where
  operation := fun n hn => initialRightNormalizationAt hC i n (by omega)
  parallel := by
    constructor
    · exact initialRightNormalizationAt_boundary hC i (i + 1) (Nat.lt_succ_self i) false
    · exact initialRightNormalizationAt_boundary hC i (i + 1) (Nat.lt_succ_self i) true
  face := fun n hn side => initialRightNormalizationAt_face hC i n (by omega) side

def rightNormalizedFamily (hC : C.IsCoherator) (i : ℕ) :
    (p : ℕ) → NormalizationFamilyAt C i (i + 1 + p) (by omega) false
  | 0 => initialRightNormalizationFamily hC i
  | p + 1 => nextNormalizationFamily hC (rightNormalizedFamily hC i p)

def rightNormalizedEndpoint (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe n) (lowerPairShape i n hi) := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => (hk : i < k) →
    C.Hom (Shape.globe k) (lowerPairShape i k hk))
    (fun _ => (rightNormalizedFamily hC i (n - (i + 1))).operation _ le_rfl) he) hi

theorem rightNormalizedEndpoint_add (hC : C.IsCoherator) (i d : ℕ) :
    rightNormalizedEndpoint hC i (i + 1 + d) (by omega) =
      (rightNormalizedFamily hC i d).operation (i + 1 + d) le_rfl := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => (hn : i < n) →
        C.Hom (Shape.globe n) (lowerPairShape i n hn))
        (fun _ => (rightNormalizedFamily hC i k).operation _ le_rfl) he) (by omega) =
        (rightNormalizedFamily hC i d).operation _ le_rfl := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold rightNormalizedEndpoint
  exact hcast _ _

theorem rightNormalizedEndpoint_parallel (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Parallel n (rightNormalizedEndpoint hC i n hi) (C.base (lowerPairLeft i n hi)) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [rightNormalizedEndpoint_add]
  exact (rightNormalizedFamily hC i d).parallel

def rightNormalizedEndpointPair (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.AdmissiblePair where
  n := n
  arity := lowerPairShape i n hi
  height := by
    change max n n ≤ n + 1
    omega
  source := rightNormalizedEndpoint hC i n hi
  target := C.base (lowerPairLeft i n hi)
  parallel := rightNormalizedEndpoint_parallel hC i n hi

def rightNormalizedEndpointHomotopy (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe (n + 1)) (lowerPairShape i n hi) :=
  (hC.2 (rightNormalizedEndpointPair hC i n hi)).choose

theorem rightNormalizedEndpointHomotopy_source (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) :
    C.comp (C.base (Shape.source n)) (rightNormalizedEndpointHomotopy hC i n hi) =
      rightNormalizedEndpoint hC i n hi :=
  (hC.2 (rightNormalizedEndpointPair hC i n hi)).choose_spec.1

theorem rightNormalizedEndpointHomotopy_target (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) :
    C.comp (C.base (Shape.target n)) (rightNormalizedEndpointHomotopy hC i n hi) =
      C.base (lowerPairLeft i n hi) :=
  (hC.2 (rightNormalizedEndpointPair hC i n hi)).choose_spec.2

#print axioms nextNormalizationFamily
#print axioms normalizedEndpoint_parallel
#print axioms normalizedEndpointHomotopy_source
#print axioms normalizedEndpointHomotopy_target
#print axioms initialRightNormalizationAt_boundary
#print axioms initialRightNormalizationAt_face
#print axioms rightNormalizedEndpoint_parallel
#print axioms rightNormalizedEndpointHomotopy_source
#print axioms rightNormalizedEndpointHomotopy_target

end HomotopyHypothesis.Category.CylinderCorollary
