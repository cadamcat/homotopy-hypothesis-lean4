import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerInverses
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def lowerFace (X : C.Model) (i n : ℕ) (hi : i < n) (side : Bool)
    (a : X.underlying.Cell n) : X.underlying.Cell i :=
  X.eval (C.base (Shape.face hi side)) a

theorem lowerFace_face (X : C.Model) (i n k : ℕ) (hi : i < n) (hn : n < k)
    (side outer : Bool) (a : X.underlying.Cell k) :
    lowerFace X i n hi side (lowerFace X n k hn outer a) =
      lowerFace X i k (Nat.lt_trans hi hn) side a := by
  dsimp only [lowerFace]
  rw [← eval_comp, ← C.base_comp, shape_face_comp]

theorem map_lowerFace {X Y : C.Model} (f : X ⟶ Y) (i n : ℕ) (hi : i < n)
    (side : Bool) (a : X.underlying.Cell n) :
    (underlyingMap f).app i (lowerFace X i n hi side a) =
      lowerFace Y i n hi side ((underlyingMap f).app n a) :=
  map_eval f (C.base (Shape.face hi side)) a

def lowerTuple (X : C.Model) (i d : ℕ) (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    X.presheaf.obj (op (⟨lowerPairShape i (i + 1 + d) (by omega)⟩ : C.Obj)) :=
  X.sumTuple (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega) a b (by
    rw [Shape.globe_seam_general]
    exact hab)

theorem lowerTuple_left (X : C.Model) (i d : ℕ)
    (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    X.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega)))
      (lowerTuple X i d a b hab) = a :=
  X.sumTuple_left _ _ _ _ _ _ _ _

theorem lowerTuple_right (X : C.Model) (i d : ℕ)
    (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    X.eval (C.base (lowerPairRight i (i + 1 + d) (by omega)))
      (lowerTuple X i d a b hab) = b :=
  X.sumTuple_right _ _ _ _ _ _ _ _

theorem map_lowerTuple {X Y : C.Model} (f : X ⟶ Y) (i d : ℕ)
    (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    f.app (op (⟨lowerPairShape i (i + 1 + d) (by omega)⟩ : C.Obj))
        (lowerTuple X i d a b hab) =
      lowerTuple Y i d ((underlyingMap f).app (i + 1 + d) a)
        ((underlyingMap f).app (i + 1 + d) b)
        (by rw [← map_lowerFace, ← map_lowerFace, hab]) := by
  apply Y.sumTuple_ext (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)
  · change Y.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) (f.app _ _) =
      Y.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) _
    rw [← map_eval, lowerTuple_left, lowerTuple_left]
    rfl
  · change Y.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) (f.app _ _) =
      Y.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) _
    rw [← map_eval, lowerTuple_right, lowerTuple_right]
    rfl

def lowerCompositionCell (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) : X.underlying.Cell (i + 1 + d) :=
  X.eval (lowerCompositionOp hC i d) (lowerTuple X i d a b hab)

theorem map_lowerCompositionCell {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i d : ℕ) (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    (underlyingMap f).app (i + 1 + d) (lowerCompositionCell X hC i d a b hab) =
      lowerCompositionCell Y hC i d ((underlyingMap f).app (i + 1 + d) a)
        ((underlyingMap f).app (i + 1 + d) b)
        (by rw [← map_lowerFace, ← map_lowerFace, hab]) :=
  (map_eval f (lowerCompositionOp hC i d) (lowerTuple X i d a b hab)).trans
    (congrArg (Y.eval (lowerCompositionOp hC i d)) (map_lowerTuple f i d a b hab))

theorem lowerCompositionCell_zero (X : C.Model) (hC : C.IsCoherator) (i : ℕ)
    (a b : X.underlying.Cell (i + 1))
    (hab : lowerFace X i (i + 1) (Nat.lt_succ_self i) true a =
      lowerFace X i (i + 1) (Nat.lt_succ_self i) false b) :
    lowerCompositionCell X hC i 0 a b hab =
      X.compCell hC i a b (show X.underlying.target i a = X.underlying.source i b from hab) :=
  rfl

theorem lowerTuple_face (X : C.Model) (i d : ℕ) (side : Bool)
    (a b : X.underlying.Cell (i + 1 + (d + 1)))
    (hab : lowerFace X i (i + 1 + (d + 1)) (by omega) true a =
      lowerFace X i (i + 1 + (d + 1)) (by omega) false b) :
    X.eval (lowerPairFace C i (i + 1 + d) (by omega) side)
        (lowerTuple X i (d + 1) a b hab) =
      lowerTuple X i d
        (lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side a)
        (lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side b)
        (by rw [lowerFace_face, lowerFace_face]; exact hab) := by
  apply X.sumTuple_ext (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)
  · change X.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) (X.eval _ _) =
      X.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) _
    rw [← eval_comp, lowerPairFace_left, C.base_comp, eval_comp,
      lowerTuple_left X i d]
    exact congrArg (X.eval (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)))
      (lowerTuple_left X i (d + 1) a b hab)
  · change X.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) (X.eval _ _) =
      X.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) _
    rw [← eval_comp, lowerPairFace_right, C.base_comp, eval_comp,
      lowerTuple_right X i d]
    exact congrArg (X.eval (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)))
      (lowerTuple_right X i (d + 1) a b hab)

theorem lowerCompositionCell_face (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (side : Bool) (a b : X.underlying.Cell (i + 1 + (d + 1)))
    (hab : lowerFace X i (i + 1 + (d + 1)) (by omega) true a =
      lowerFace X i (i + 1 + (d + 1)) (by omega) false b) :
    lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side
        (lowerCompositionCell X hC i (d + 1) a b hab) =
      lowerCompositionCell X hC i d
        (lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side a)
        (lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side b)
        (by rw [lowerFace_face, lowerFace_face]; exact hab) := by
  dsimp only [lowerFace, lowerCompositionCell]
  rw [← eval_comp, lowerCompositionOp_face, eval_comp, lowerTuple_face]
  rfl

def lowerInverseCell (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (a : X.underlying.Cell (i + 1 + d)) : X.underlying.Cell (i + 1 + d) :=
  X.eval (lowerInverseOp hC i d) a

theorem map_lowerInverseCell {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i d : ℕ) (a : X.underlying.Cell (i + 1 + d)) :
    (underlyingMap f).app (i + 1 + d) (lowerInverseCell X hC i d a) =
      lowerInverseCell Y hC i d ((underlyingMap f).app (i + 1 + d) a) :=
  map_eval f (lowerInverseOp hC i d) a

theorem lowerInverseCell_zero (X : C.Model) (hC : C.IsCoherator) (i : ℕ)
    (a : X.underlying.Cell (i + 1)) :
    lowerInverseCell X hC i 0 a = X.inverseCell hC i a := rfl

theorem lowerInverseCell_face (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (side : Bool) (a : X.underlying.Cell (i + 1 + (d + 1))) :
    lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side
        (lowerInverseCell X hC i (d + 1) a) =
      lowerInverseCell X hC i d
        (lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side a) := by
  dsimp only [lowerFace, lowerInverseCell]
  rw [← eval_comp, lowerInverseOp_face, eval_comp]

#print axioms map_lowerCompositionCell
#print axioms lowerCompositionCell_face
#print axioms map_lowerInverseCell
#print axioms lowerInverseCell_face

end HomotopyHypothesis.Category.CylinderCorollary
