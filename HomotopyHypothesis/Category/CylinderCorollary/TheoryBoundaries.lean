import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerInverses
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

theorem lowerCompositionOp_boundary (hC : C.IsCoherator) (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (lowerCompositionOp hC i d) =
      C.base (Shape.face (by omega : i < i + 1 + d) side ≫
        if side then lowerPairRight i (i + 1 + d) (by omega)
        else lowerPairLeft i (i + 1 + d) (by omega)) := by
  induction d with
  | zero =>
    rw [lowerCompositionOp_zero]
    cases side
    · exact C.composition_source hC i
    · exact C.composition_target hC i
  | succ d ih =>
    change C.comp (C.base (Shape.face (by omega : i < i + 1 + d + 1) side))
      (lowerCompositionOp hC i (d + 1)) = _
    conv_lhs =>
      rw [← shape_face_comp (by omega : i < i + 1 + d)
        (Nat.lt_succ_self (i + 1 + d)) side false,
        C.base_comp, C.assoc, lowerCompositionOp_face, ← C.assoc, ih]
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [C.base_comp, C.assoc, lowerPairFace_left]
      simp only [← C.base_comp]
      with_unfolding_all simp only [← Category.assoc, shape_face_comp]
      rfl
    · simp only [↓reduceIte]
      rw [C.base_comp, C.assoc, lowerPairFace_right]
      simp only [← C.base_comp]
      with_unfolding_all simp only [← Category.assoc, shape_face_comp]
      rfl

theorem lowerInverseOp_boundary (hC : C.IsCoherator) (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (lowerInverseOp hC i d) =
      C.base (Shape.face (by omega : i < i + 1 + d) (!side)) := by
  induction d with
  | zero =>
    rw [lowerInverseOp_zero]
    cases side
    · exact C.inverse_source hC i
    · exact C.inverse_target hC i
  | succ d ih =>
    change C.comp (C.base (Shape.face (by omega : i < i + 1 + d + 1) side))
      (lowerInverseOp hC i (d + 1)) = _
    conv_lhs =>
      rw [← shape_face_comp (by omega : i < i + 1 + d)
        (Nat.lt_succ_self (i + 1 + d)) side false,
        C.base_comp, C.assoc, lowerInverseOp_face, ← C.assoc, ih,
        ← C.base_comp, shape_face_comp]

def operationTuple {S : Shape} (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    C.Hom (lowerPairShape i (i + 1 + d) (by omega)) S :=
  (C.sums (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)).desc a b (by
    exact (congrArg (fun q : Shape.globe i ⟶ Shape.globe (i + 1 + d) =>
      C.comp (C.base q) a) (Shape.globe_seam_general (i + 1 + d) i (by omega))).trans hab)

theorem operationTuple_left {S : Shape} (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    C.comp (C.base (lowerPairLeft i (i + 1 + d) (by omega)))
      (operationTuple i d a b hab) = a :=
  (C.sums (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)).inl_desc _ _ _

theorem operationTuple_right {S : Shape} (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    C.comp (C.base (lowerPairRight i (i + 1 + d) (by omega)))
      (operationTuple i d a b hab) = b :=
  (C.sums (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)).inr_desc _ _ _

def operationComposition {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    C.Hom (Shape.globe (i + 1 + d)) S :=
  C.comp (lowerCompositionOp hC i d) (operationTuple i d a b hab)

theorem operationComposition_boundary {S : Shape} (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (operationComposition hC i d a b hab) =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (if side then b else a) := by
  dsimp only [operationComposition]
  rw [← C.assoc, lowerCompositionOp_boundary]
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [C.base_comp, C.assoc, operationTuple_left]
  · simp only [↓reduceIte]
    rw [C.base_comp, C.assoc, operationTuple_right]

def operationInverse {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a : C.Hom (Shape.globe (i + 1 + d)) S) : C.Hom (Shape.globe (i + 1 + d)) S :=
  C.comp (lowerInverseOp hC i d) a

theorem operationInverse_boundary {S : Shape} (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) (a : C.Hom (Shape.globe (i + 1 + d)) S) :
    C.comp (C.base (Shape.face (by omega : i < i + 1 + d) side))
        (operationInverse hC i d a) =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) (!side))) a := by
  dsimp only [operationInverse]
  rw [← C.assoc, lowerInverseOp_boundary]

#print axioms lowerCompositionOp_boundary
#print axioms lowerInverseOp_boundary
#print axioms operationComposition_boundary
#print axioms operationInverse_boundary

end HomotopyHypothesis.Category.CylinderCorollary
