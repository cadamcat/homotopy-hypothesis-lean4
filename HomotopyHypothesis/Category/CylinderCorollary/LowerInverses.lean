import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

theorem theory_face_globular (C : GlobularTheory.{u}) (n : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (C.base (Shape.face (Nat.lt_succ_self (n + 1)) false)) =
      C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (C.base (Shape.face (Nat.lt_succ_self (n + 1)) true)) := by
  simp only [← C.base_comp, shape_face_comp]

def LowerInverseBoundary (C : GlobularTheory.{u}) (i : ℕ) :
    (d : ℕ) → C.Hom (Shape.globe (i + 1 + d)) (Shape.globe (i + 1 + d)) → Prop
  | 0, op =>
    C.comp (C.base (Shape.source i)) op = C.base (Shape.target i) ∧
      C.comp (C.base (Shape.target i)) op = C.base (Shape.source i)
  | d + 1, op =>
    ∃ p : C.Hom (Shape.globe (i + 1 + d)) (Shape.globe (i + 1 + d)),
      ∀ side : Bool,
        C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) op =
          C.comp p (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))

structure LowerInverseData (C : GlobularTheory.{u}) (i d : ℕ) where
  operation : C.Hom (Shape.globe (i + 1 + d)) (Shape.globe (i + 1 + d))
  boundary : LowerInverseBoundary C i d operation

def lowerInverseZero {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    LowerInverseData C i 0 where
  operation := C.inverse hC i
  boundary := ⟨C.inverse_source hC i, C.inverse_target hC i⟩

def lowerInverseNextPair {C : GlobularTheory.{u}} (i d : ℕ)
    (a : LowerInverseData C i d) : C.AdmissiblePair where
  n := i + 1 + d
  arity := Shape.globe (i + 1 + d + 1)
  height := le_rfl
  source := C.comp a.operation (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) false))
  target := C.comp a.operation (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) true))
  parallel := by
    cases d with
    | zero =>
      constructor
      · simp only [← C.assoc, a.boundary.1]
        simp only [← C.base_comp, Shape.target, shape_face_comp]
      · simp only [← C.assoc, a.boundary.2]
        simp only [← C.base_comp, Shape.source, shape_face_comp]
    | succ d =>
      obtain ⟨p, hp⟩ := a.boundary
      constructor
      · simp only [← C.assoc, Shape.source]
        rw [hp false]
        simp only [C.assoc]
        exact congrArg (C.comp p) (theory_face_globular C (i + 1 + d) false)
      · simp only [← C.assoc, Shape.target]
        rw [hp true]
        simp only [C.assoc]
        exact congrArg (C.comp p) (theory_face_globular C (i + 1 + d) true)

def lowerInverseData {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    (d : ℕ) → LowerInverseData C i d
  | 0 => lowerInverseZero hC i
  | d + 1 =>
    let a := lowerInverseData hC i d
    let p := lowerInverseNextPair i d a
    { operation := (hC.2 p).choose
      boundary := ⟨a.operation, by
        intro side
        cases side with
        | false => exact (hC.2 p).choose_spec.1
        | true => exact (hC.2 p).choose_spec.2⟩ }

def lowerInverseOp {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i d : ℕ) :
    C.Hom (Shape.globe (i + 1 + d)) (Shape.globe (i + 1 + d)) :=
  (lowerInverseData hC i d).operation

theorem lowerInverseOp_zero {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    lowerInverseOp hC i 0 = C.inverse hC i := rfl

theorem lowerInverseOp_face {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
        (lowerInverseOp hC i (d + 1)) =
      C.comp (lowerInverseOp hC i d)
        (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) := by
  cases side with
  | false => exact (hC.2 (lowerInverseNextPair i d (lowerInverseData hC i d))).choose_spec.1
  | true => exact (hC.2 (lowerInverseNextPair i d (lowerInverseData hC i d))).choose_spec.2

#print axioms lowerInverseOp_face

end HomotopyHypothesis.Category.CylinderCorollary
