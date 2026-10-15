import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerInverses
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

theorem operationTuple_postcomp {S T : Shape} (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b)
    (q : C.Hom S T) :
    C.comp (operationTuple i d a b hab) q =
      operationTuple i d (C.comp a q) (C.comp b q)
        (by rw [← C.assoc, ← C.assoc, hab]) := by
  apply lowerPair_hom_ext C
  · rw [← C.assoc, operationTuple_left, operationTuple_left]
  · rw [← C.assoc, operationTuple_right, operationTuple_right]

theorem operationComposition_postcomp {S T : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b)
    (q : C.Hom S T) :
    C.comp (operationComposition hC i d a b hab) q =
      operationComposition hC i d (C.comp a q) (C.comp b q)
        (by rw [← C.assoc, ← C.assoc, hab]) := by
  dsimp only [operationComposition]
  rw [C.assoc, operationTuple_postcomp]

theorem operationInverse_postcomp {S T : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a : C.Hom (Shape.globe (i + 1 + d)) S) (q : C.Hom S T) :
    C.comp (operationInverse hC i d a) q = operationInverse hC i d (C.comp a q) :=
  C.assoc _ _ _

theorem operationTuple_face {S : Shape} (i d : ℕ) (side : Bool)
    (a b : C.Hom (Shape.globe (i + 1 + (d + 1))) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + (d + 1)) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + (d + 1)) false)) b) :
    C.comp (lowerPairFace C i (i + 1 + d) (by omega) side)
        (operationTuple i (d + 1) a b hab) =
      operationTuple i d
        (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) a)
        (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) b)
        (by simp only [← C.assoc, ← C.base_comp, shape_face_comp]; exact hab) := by
  apply lowerPair_hom_ext C
  · rw [← C.assoc, lowerPairFace_left, C.base_comp, C.assoc, operationTuple_left i d]
    exact congrArg (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)))
      (operationTuple_left i (d + 1) a b hab)
  · rw [← C.assoc, lowerPairFace_right, C.base_comp, C.assoc, operationTuple_right i d]
    exact congrArg (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)))
      (operationTuple_right i (d + 1) a b hab)

theorem operationComposition_face {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (side : Bool) (a b : C.Hom (Shape.globe (i + 1 + (d + 1))) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + (d + 1)) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + (d + 1)) false)) b) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
        (operationComposition hC i (d + 1) a b hab) =
      operationComposition hC i d
        (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) a)
        (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) b)
        (by simp only [← C.assoc, ← C.base_comp, shape_face_comp]; exact hab) := by
  dsimp only [operationComposition]
  rw [← C.assoc, lowerCompositionOp_face, C.assoc, operationTuple_face]

theorem operationInverse_face {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (side : Bool) (a : C.Hom (Shape.globe (i + 1 + (d + 1))) S) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
        (operationInverse hC i (d + 1) a) =
      operationInverse hC i d
        (C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) a) := by
  dsimp only [operationInverse]
  rw [← C.assoc, lowerInverseOp_face, C.assoc]

#print axioms operationComposition_postcomp
#print axioms operationComposition_face
#print axioms operationInverse_face

end HomotopyHypothesis.Category.CylinderCorollary
