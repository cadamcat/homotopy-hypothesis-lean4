import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

def LowerOpBoundary (C : GlobularTheory.{u}) (i : ℕ) :
    (d : ℕ) → C.Hom (Shape.globe (i + 1 + d))
      (lowerPairShape i (i + 1 + d) (by omega)) → Prop
  | 0, op =>
    C.comp (C.base (Shape.source i)) op =
      C.base (Shape.source i ≫ lowerPairLeft i (i + 1) (Nat.lt_succ_self i)) ∧
    C.comp (C.base (Shape.target i)) op =
      C.base (Shape.target i ≫ lowerPairRight i (i + 1) (Nat.lt_succ_self i))
  | d + 1, op =>
    ∃ p : C.Hom (Shape.globe (i + 1 + d))
        (lowerPairShape i (i + 1 + d) (by omega)),
      ∀ side : Bool,
        C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side)) op =
          C.comp p (lowerPairFace C i (i + 1 + d) (by omega) side)

structure LowerOpData (C : GlobularTheory.{u}) (i d : ℕ) where
  operation : C.Hom (Shape.globe (i + 1 + d))
    (lowerPairShape i (i + 1 + d) (by omega))
  boundary : LowerOpBoundary C i d operation

def lowerOpZero {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    LowerOpData C i 0 where
  operation := C.composition hC i
  boundary := ⟨C.composition_source hC i, C.composition_target hC i⟩

def lowerOpNextPair {C : GlobularTheory.{u}} (i d : ℕ) (a : LowerOpData C i d) :
    C.AdmissiblePair where
  n := i + 1 + d
  arity := lowerPairShape i (i + 1 + d + 1) (by omega)
  height := by
    change max (i + 1 + d + 1) (i + 1 + d + 1) ≤ i + 1 + d + 1
    simp only [Nat.max_self, le_refl]
  source := C.comp a.operation (lowerPairFace C i (i + 1 + d) (by omega) false)
  target := C.comp a.operation (lowerPairFace C i (i + 1 + d) (by omega) true)
  parallel := by
    cases d with
    | zero =>
      constructor
      · simp only [← C.assoc, a.boundary.1]
        simp only [C.base_comp, C.assoc, lowerPairFace_left]
        simp only [← C.base_comp]
        with_unfolding_all simp only [Shape.source, ← Category.assoc, shape_face_comp]
      · simp only [← C.assoc, a.boundary.2]
        simp only [C.base_comp, C.assoc, lowerPairFace_right]
        simp only [← C.base_comp]
        with_unfolding_all simp only [Shape.target, ← Category.assoc, shape_face_comp]
    | succ d =>
      obtain ⟨p, hp⟩ := a.boundary
      constructor
      · simp only [← C.assoc, Shape.source]
        rw [hp false]
        simp only [C.assoc]
        exact congrArg (C.comp p) (lowerPairFace_globular C i (i + 1 + d) (by omega) false)
      · simp only [← C.assoc, Shape.target]
        rw [hp true]
        simp only [C.assoc]
        exact congrArg (C.comp p) (lowerPairFace_globular C i (i + 1 + d) (by omega) true)

def lowerOpData {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    (d : ℕ) → LowerOpData C i d
  | 0 => lowerOpZero hC i
  | d + 1 =>
    let a := lowerOpData hC i d
    let p := lowerOpNextPair i d a
    { operation := (hC.2 p).choose
      boundary := ⟨a.operation, by
        intro side
        cases side with
        | false => exact (hC.2 p).choose_spec.1
        | true => exact (hC.2 p).choose_spec.2⟩ }

def lowerCompositionOp {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i d : ℕ) :
    C.Hom (Shape.globe (i + 1 + d)) (lowerPairShape i (i + 1 + d) (by omega)) :=
  (lowerOpData hC i d).operation

theorem lowerCompositionOp_zero {C : GlobularTheory.{u}} (hC : C.IsCoherator) (i : ℕ) :
    lowerCompositionOp hC i 0 = C.composition hC i := rfl

theorem lowerCompositionOp_face {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
        (lowerCompositionOp hC i (d + 1)) =
      C.comp (lowerCompositionOp hC i d)
        (lowerPairFace C i (i + 1 + d) (by omega) side) := by
  cases side with
  | false => exact (hC.2 (lowerOpNextPair i d (lowerOpData hC i d))).choose_spec.1
  | true => exact (hC.2 (lowerOpNextPair i d (lowerOpData hC i d))).choose_spec.2

#print axioms lowerCompositionOp_face

end HomotopyHypothesis.Category.CylinderCorollary
