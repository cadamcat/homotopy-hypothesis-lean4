import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

def lowerPairInclusion (i n : ℕ) (hi : i < n) (anchor : Bool) :
    Shape.globe n ⟶ lowerPairShape i n hi :=
  if anchor then lowerPairRight i n hi else lowerPairLeft i n hi

def lowerPairMap (C : GlobularTheory.{u}) (i m n : ℕ)
    (hi : i < m) (hm : m < n) (side : Bool) :
    C.Hom (lowerPairShape i m hi) (lowerPairShape i n (Nat.lt_trans hi hm)) :=
  (C.sums (Shape.globe m) i m hi hi).desc
    (C.base (Shape.face hm side ≫ lowerPairLeft i n (Nat.lt_trans hi hm)))
    (C.base (Shape.face hm side ≫ lowerPairRight i n (Nat.lt_trans hi hm))) (by
      have h : (Shape.globe m).seam hi ≫
          (Shape.face hm side ≫ lowerPairLeft i n (Nat.lt_trans hi hm)) =
          Shape.face hi false ≫
          (Shape.face hm side ≫ lowerPairRight i n (Nat.lt_trans hi hm)) := by
        rw [Shape.globe_seam_general, ← Category.assoc, ← Category.assoc,
          shape_face_comp, shape_face_comp]
        exact lowerPair_seam i n (Nat.lt_trans hi hm)
      exact (C.base_comp _ _).symm.trans ((congrArg C.base h).trans (C.base_comp _ _)))

theorem lowerPairMap_left (C : GlobularTheory.{u}) (i m n : ℕ)
    (hi : i < m) (hm : m < n) (side : Bool) :
    C.comp (C.base (lowerPairLeft i m hi)) (lowerPairMap C i m n hi hm side) =
      C.base (Shape.face hm side ≫ lowerPairLeft i n (Nat.lt_trans hi hm)) :=
  (C.sums (Shape.globe m) i m hi hi).inl_desc _ _ _

theorem lowerPairMap_right (C : GlobularTheory.{u}) (i m n : ℕ)
    (hi : i < m) (hm : m < n) (side : Bool) :
    C.comp (C.base (lowerPairRight i m hi)) (lowerPairMap C i m n hi hm side) =
      C.base (Shape.face hm side ≫ lowerPairRight i n (Nat.lt_trans hi hm)) :=
  (C.sums (Shape.globe m) i m hi hi).inr_desc _ _ _

theorem lowerPairMap_inclusion (C : GlobularTheory.{u}) (i m n : ℕ)
    (hi : i < m) (hm : m < n) (anchor side : Bool) :
    C.comp (C.base (lowerPairInclusion i m hi anchor)) (lowerPairMap C i m n hi hm side) =
      C.base (Shape.face hm side ≫ lowerPairInclusion i n (Nat.lt_trans hi hm) anchor) := by
  cases anchor
  · exact lowerPairMap_left C i m n hi hm side
  · exact lowerPairMap_right C i m n hi hm side

theorem lowerPairMap_succ (C : GlobularTheory.{u}) (i m : ℕ) (hi : i < m)
    (side : Bool) :
    lowerPairMap C i m (m + 1) hi (Nat.lt_succ_self m) side =
      lowerPairFace C i m hi side := rfl

theorem lowerPairMap_comp (C : GlobularTheory.{u}) (i l m n : ℕ)
    (hi : i < l) (hl : l < m) (hm : m < n) (side outer : Bool) :
    C.comp (lowerPairMap C i l m hi hl side)
        (lowerPairMap C i m n (Nat.lt_trans hi hl) hm outer) =
      lowerPairMap C i l n hi (Nat.lt_trans hl hm) side := by
  apply lowerPair_hom_ext C
  · simp only [← C.assoc, lowerPairMap_left]
    simp only [C.base_comp, C.assoc, lowerPairMap_left]
    simp only [← C.base_comp]
    with_unfolding_all simp only [← Category.assoc, shape_face_comp]
  · simp only [← C.assoc, lowerPairMap_right]
    simp only [C.base_comp, C.assoc, lowerPairMap_right]
    simp only [← C.base_comp]
    with_unfolding_all simp only [← Category.assoc, shape_face_comp]

#print axioms lowerPairMap_comp

end HomotopyHypothesis.Category.CylinderCorollary
