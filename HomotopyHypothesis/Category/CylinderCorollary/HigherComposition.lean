import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory CategoryTheory.Limits
open OAI.Grothendieck

theorem shape_face_comp {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (a b : Bool) :
    Shape.face hij a ≫ Shape.face hjk b = Shape.face (Nat.lt_trans hij hjk) a :=
  (GlobularTheory.shapeGlobes.map_comp (Globe.face hij a) (Globe.face hjk b)).symm

def lowerPairShape (i n : ℕ) (hi : i < n) : Shape :=
  ⟨n, Table.attach (Table.globe n) i n hi hi⟩

def lowerPairLeft (i n : ℕ) (hi : i < n) : Shape.globe n ⟶ lowerPairShape i n hi :=
  Shape.inl (⟨n, Table.globe n⟩ : Shape) i n hi hi

def lowerPairRight (i n : ℕ) (hi : i < n) : Shape.globe n ⟶ lowerPairShape i n hi :=
  Shape.inr (⟨n, Table.globe n⟩ : Shape) i n hi hi

theorem lowerPair_seam (i n : ℕ) (hi : i < n) :
    Shape.face hi true ≫ lowerPairLeft i n hi =
      Shape.face hi false ≫ lowerPairRight i n hi := by
  have h := Shape.seam_inl (Shape.globe n) i n hi hi
  simp only [Shape.globe_seam_general] at h
  simpa only [lowerPairLeft, lowerPairRight, lowerPairShape, Shape.attach,
    Shape.globe] using h

def lowerPairFace (C : GlobularTheory.{u}) (i n : ℕ) (hi : i < n) (side : Bool) :
    C.Hom (lowerPairShape i n hi)
      (lowerPairShape i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) :=
  (C.sums (Shape.globe n) i n hi hi).desc
    (C.base (Shape.face (Nat.lt_succ_self n) side ≫
      lowerPairLeft i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))))
    (C.base (Shape.face (Nat.lt_succ_self n) side ≫
      lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)))) (by
    change C.comp (C.base ((Shape.globe n).seam hi)) _ =
      C.comp (C.base (Shape.face hi false)) _
    have h : (Shape.globe n).seam hi ≫
        (Shape.face (Nat.lt_succ_self n) side ≫
          lowerPairLeft i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) =
        Shape.face hi false ≫
        (Shape.face (Nat.lt_succ_self n) side ≫
          lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) := by
      rw [Shape.globe_seam_general, ← Category.assoc, ← Category.assoc,
        shape_face_comp, shape_face_comp]
      exact lowerPair_seam i (n + 1) _
    exact (C.base_comp _ _).symm.trans ((congrArg C.base h).trans (C.base_comp _ _)))

theorem lowerPairFace_left (C : GlobularTheory.{u}) (i n : ℕ) (hi : i < n)
    (side : Bool) :
    C.comp (C.base (lowerPairLeft i n hi)) (lowerPairFace C i n hi side) =
      C.base (Shape.face (Nat.lt_succ_self n) side ≫
        lowerPairLeft i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) :=
  (C.sums (Shape.globe n) i n hi hi).inl_desc _ _ _

theorem lowerPairFace_right (C : GlobularTheory.{u}) (i n : ℕ) (hi : i < n)
    (side : Bool) :
    C.comp (C.base (lowerPairRight i n hi)) (lowerPairFace C i n hi side) =
      C.base (Shape.face (Nat.lt_succ_self n) side ≫
        lowerPairRight i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) :=
  (C.sums (Shape.globe n) i n hi hi).inr_desc _ _ _

theorem lowerPair_hom_ext (C : GlobularTheory.{u}) {i n : ℕ} {hi : i < n} {T : Shape}
    {f g : C.Hom (lowerPairShape i n hi) T}
    (hl : C.comp (C.base (lowerPairLeft i n hi)) f =
      C.comp (C.base (lowerPairLeft i n hi)) g)
    (hr : C.comp (C.base (lowerPairRight i n hi)) f =
      C.comp (C.base (lowerPairRight i n hi)) g) : f = g :=
  (C.sums (Shape.globe n) i n hi hi).hom_ext hl hr

theorem lowerPairFace_globular (C : GlobularTheory.{u}) (i n : ℕ) (hi : i < n)
    (side : Bool) :
    C.comp (lowerPairFace C i n hi side)
        (lowerPairFace C i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)) false) =
      C.comp (lowerPairFace C i n hi side)
        (lowerPairFace C i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n)) true) := by
  apply lowerPair_hom_ext C
  · simp only [← C.assoc, lowerPairFace_left]
    simp only [C.base_comp, C.assoc, lowerPairFace_left]
    simp only [← C.base_comp]
    with_unfolding_all simp only [← Category.assoc, shape_face_comp]
  · simp only [← C.assoc, lowerPairFace_right]
    simp only [C.base_comp, C.assoc, lowerPairFace_right]
    simp only [← C.base_comp]
    with_unfolding_all simp only [← Category.assoc, shape_face_comp]

#print axioms lowerPairFace_globular

end HomotopyHypothesis.Category.CylinderCorollary
