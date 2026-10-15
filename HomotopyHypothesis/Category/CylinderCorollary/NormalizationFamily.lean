import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.IteratedUnits
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFaces
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

structure NormalizationFamilyAt (C : GlobularTheory.{u}) (i h : ℕ) (hi : i < h)
    (anchor : Bool) where
  operation : ∀ n (hn : h ≤ n),
    C.Hom (Shape.globe n) (lowerPairShape i n (Nat.lt_of_lt_of_le hi hn))
  parallel : C.Parallel h (operation h le_rfl) (C.base (lowerPairInclusion i h hi anchor))
  face : ∀ n (hn : h ≤ n) (side : Bool),
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (operation (n + 1) (Nat.le_trans hn (Nat.le_succ n))) =
      C.comp (operation n hn) (lowerPairFace C i n (Nat.lt_of_lt_of_le hi hn) side)

abbrev NormalizationFamily (C : GlobularTheory.{u}) (i h : ℕ) (hi : i < h) :=
  NormalizationFamilyAt C i h hi true

variable {C : GlobularTheory.{u}}

theorem NormalizationFamilyAt.generalFace {i h : ℕ} {hi : i < h} {anchor : Bool}
    (A : NormalizationFamilyAt C i h hi anchor) (m n : ℕ) (hm : h ≤ m) (hmn : m < n)
    (side : Bool) :
    C.comp (C.base (Shape.face hmn side))
        (A.operation n (Nat.le_trans hm (Nat.le_of_lt hmn))) =
      C.comp (A.operation m hm)
        (lowerPairMap C i m n (Nat.lt_of_lt_of_le hi hm) hmn side) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : m = n
    · subst m
      rw [lowerPairMap_succ]
      exact A.face n hm side
    · have hm' : m < n := by omega
      have hhn : h ≤ n := Nat.le_trans hm (Nat.le_of_lt hm')
      have hni : i < n := Nat.lt_of_lt_of_le hi hhn
      conv_lhs =>
        rw [← shape_face_comp hm' (Nat.lt_succ_self n) side false,
          C.base_comp, C.assoc, A.face n hhn false,
          ← lowerPairMap_succ C i n hni false, ← C.assoc, ih hm']
      rw [C.assoc, lowerPairMap_comp]

theorem NormalizationFamily.generalFace {i h : ℕ} {hi : i < h}
    (A : NormalizationFamily C i h hi) (m n : ℕ) (hm : h ≤ m) (hmn : m < n)
    (side : Bool) :
    C.comp (C.base (Shape.face hmn side))
        (A.operation n (Nat.le_trans hm (Nat.le_of_lt hmn))) =
      C.comp (A.operation m hm)
        (lowerPairMap C i m n (Nat.lt_of_lt_of_le hi hm) hmn side) :=
  NormalizationFamilyAt.generalFace A m n hm hmn side

def initialNormalizationFamily (hC : C.IsCoherator) (i : ℕ) :
    NormalizationFamily C i (i + 1) (Nat.lt_succ_self i) where
  operation := fun n hn => initialNormalizationAt hC i n (by omega)
  parallel := by
    constructor
    · exact initialNormalizationAt_boundary hC i (i + 1) (Nat.lt_succ_self i) false
    · exact initialNormalizationAt_boundary hC i (i + 1) (Nat.lt_succ_self i) true
  face := by
    intro n hn side
    exact (initialNormalizationAt_face hC i n (by omega) side).trans
      (congrArg (C.comp (initialNormalizationAt hC i n (by omega)))
        (lowerPairMap_succ C i n (by omega) side))

def normalizationCorrectionPair {i h : ℕ} {hi : i < h} {anchor : Bool}
    (A : NormalizationFamilyAt C i h hi anchor) : C.AdmissiblePair where
  n := h
  arity := lowerPairShape i h hi
  height := by
    change max h h ≤ h + 1
    omega
  source := C.base (lowerPairInclusion i h hi anchor)
  target := A.operation h le_rfl
  parallel := by
    cases h with
    | zero => trivial
    | succ h => exact ⟨A.parallel.1.symm, A.parallel.2.symm⟩

def normalizationCorrection {i h : ℕ} {hi : i < h} {anchor : Bool} (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) :
    C.Hom (Shape.globe (h + 1)) (lowerPairShape i h hi) :=
  (hC.2 (normalizationCorrectionPair A)).choose

theorem normalizationCorrection_source {i h : ℕ} {hi : i < h} {anchor : Bool} (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) :
    C.comp (C.base (Shape.source h)) (normalizationCorrection hC A) =
      C.base (lowerPairInclusion i h hi anchor) :=
  (hC.2 (normalizationCorrectionPair A)).choose_spec.1

theorem normalizationCorrection_target {i h : ℕ} {hi : i < h} {anchor : Bool} (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) :
    C.comp (C.base (Shape.target h)) (normalizationCorrection hC A) = A.operation h le_rfl :=
  (hC.2 (normalizationCorrectionPair A)).choose_spec.2

def normalizationReverseCorrection {i h : ℕ} {hi : i < h} {anchor : Bool} (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) :
    C.Hom (Shape.globe (h + 1)) (lowerPairShape i h hi) :=
  operationInverse hC h 0 (normalizationCorrection hC A)

theorem normalizationReverseCorrection_source {i h : ℕ} {hi : i < h} {anchor : Bool}
    (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor) :
    C.comp (C.base (Shape.source h)) (normalizationReverseCorrection hC A) =
      A.operation h le_rfl :=
  (operationInverse_boundary hC h 0 false (normalizationCorrection hC A)).trans
    (normalizationCorrection_target hC A)

theorem normalizationReverseCorrection_target {i h : ℕ} {hi : i < h} {anchor : Bool}
    (hC : C.IsCoherator) (A : NormalizationFamilyAt C i h hi anchor) :
    C.comp (C.base (Shape.target h)) (normalizationReverseCorrection hC A) =
      C.base (lowerPairInclusion i h hi anchor) :=
  (operationInverse_boundary hC h 0 true (normalizationCorrection hC A)).trans
    (normalizationCorrection_source hC A)

#print axioms unitExtension_postcomp
#print axioms unitExtension_face
#print axioms unitExtension_generalFace
#print axioms unitExtension_lowerFace
#print axioms NormalizationFamilyAt.generalFace
#print axioms initialNormalizationFamily
#print axioms normalizationCorrection_target
#print axioms normalizationReverseCorrection_source
#print axioms normalizationReverseCorrection_target

end HomotopyHypothesis.Category.CylinderCorollary
