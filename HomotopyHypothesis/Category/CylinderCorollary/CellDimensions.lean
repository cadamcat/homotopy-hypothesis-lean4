import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerBoundaries
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def lowerCompositionCellAt (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) : X.underlying.Cell n := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => (hk : i < k) → (a b : X.underlying.Cell k) →
    lowerFace X i k hk true a = lowerFace X i k hk false b → X.underlying.Cell k)
    (fun _ => lowerCompositionCell X hC i (n - (i + 1))) he) hi a b hab

theorem lowerCompositionCellAt_add (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    lowerCompositionCellAt X hC i (i + 1 + d) (by omega) a b hab =
      lowerCompositionCell X hC i d a b hab := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => (hn : i < n) → (a b : X.underlying.Cell n) →
        lowerFace X i n hn true a = lowerFace X i n hn false b → X.underlying.Cell n)
        (fun _ => lowerCompositionCell X hC i k) he) (by omega) a b hab =
        lowerCompositionCell X hC i d a b hab := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold lowerCompositionCellAt
  exact hcast _ _

theorem lowerCompositionCellAt_boundary (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    lowerFace X i n hi side (lowerCompositionCellAt X hC i n hi a b hab) =
      lowerFace X i n hi side (if side then b else a) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerCompositionCellAt_add]
  exact lowerCompositionCell_boundary X hC i d side a b hab

theorem lowerCompositionCellAt_face (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a b : X.underlying.Cell (n + 1))
    (hab : lowerFace X i (n + 1) (by omega) true a =
      lowerFace X i (n + 1) (by omega) false b) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) side
        (lowerCompositionCellAt X hC i (n + 1) (by omega) a b hab) =
      lowerCompositionCellAt X hC i n hi
        (lowerFace X n (n + 1) (Nat.lt_succ_self n) side a)
        (lowerFace X n (n + 1) (Nat.lt_succ_self n) side b)
        (by rw [lowerFace_face, lowerFace_face]; exact hab) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  change lowerFace X (i + 1 + d) (i + 1 + d + 1) _ side
      (lowerCompositionCellAt X hC i (i + 1 + (d + 1)) _ a b hab) = _
  rw [lowerCompositionCellAt_add, lowerCompositionCellAt_add]
  exact lowerCompositionCell_face X hC i d side a b hab

theorem map_lowerCompositionCellAt {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    (underlyingMap f).app n (lowerCompositionCellAt X hC i n hi a b hab) =
      lowerCompositionCellAt Y hC i n hi ((underlyingMap f).app n a)
        ((underlyingMap f).app n b) (by rw [← map_lowerFace, ← map_lowerFace, hab]) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerCompositionCellAt_add, lowerCompositionCellAt_add]
  exact map_lowerCompositionCell f hC i d a b hab

theorem lowerCompositionCellAt_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) {a₀ a₁ b₀ b₁ : X.underlying.Cell n}
    (ha : X.underlying.Joined n a₀ a₁) (hb : X.underlying.Joined n b₀ b₁)
    (hab₀ : lowerFace X i n hi true a₀ = lowerFace X i n hi false b₀)
    (hab₁ : lowerFace X i n hi true a₁ = lowerFace X i n hi false b₁) :
    X.underlying.Joined n (lowerCompositionCellAt X hC i n hi a₀ b₀ hab₀)
      (lowerCompositionCellAt X hC i n hi a₁ b₁ hab₁) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerCompositionCellAt_add, lowerCompositionCellAt_add]
  exact lowerCompositionCell_joined X hC i d ha hb hab₀ hab₁

def lowerInverseCellAt (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (a : X.underlying.Cell n) : X.underlying.Cell n := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => X.underlying.Cell k → X.underlying.Cell k)
    (lowerInverseCell X hC i (n - (i + 1))) he) a

theorem lowerInverseCellAt_add (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (a : X.underlying.Cell (i + 1 + d)) :
    lowerInverseCellAt X hC i (i + 1 + d) (by omega) a = lowerInverseCell X hC i d a := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => X.underlying.Cell n → X.underlying.Cell n)
        (lowerInverseCell X hC i k) he) a = lowerInverseCell X hC i d a := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold lowerInverseCellAt
  exact hcast _ _

theorem lowerInverseCellAt_boundary (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a : X.underlying.Cell n) :
    lowerFace X i n hi side (lowerInverseCellAt X hC i n hi a) =
      lowerFace X i n hi (!side) a := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerInverseCellAt_add]
  exact lowerInverseCell_boundary X hC i d side a

theorem lowerInverseCellAt_face (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a : X.underlying.Cell (n + 1)) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) side
        (lowerInverseCellAt X hC i (n + 1) (by omega) a) =
      lowerInverseCellAt X hC i n hi (lowerFace X n (n + 1) (Nat.lt_succ_self n) side a) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  change lowerFace X (i + 1 + d) (i + 1 + d + 1) _ side
      (lowerInverseCellAt X hC i (i + 1 + (d + 1)) _ a) = _
  rw [lowerInverseCellAt_add, lowerInverseCellAt_add]
  exact lowerInverseCell_face X hC i d side a

theorem map_lowerInverseCellAt {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a : X.underlying.Cell n) :
    (underlyingMap f).app n (lowerInverseCellAt X hC i n hi a) =
      lowerInverseCellAt Y hC i n hi ((underlyingMap f).app n a) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerInverseCellAt_add, lowerInverseCellAt_add]
  exact map_lowerInverseCell f hC i d a

theorem lowerInverseCellAt_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) {a₀ a₁ : X.underlying.Cell n}
    (ha : X.underlying.Joined n a₀ a₁) :
    X.underlying.Joined n (lowerInverseCellAt X hC i n hi a₀)
      (lowerInverseCellAt X hC i n hi a₁) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerInverseCellAt_add, lowerInverseCellAt_add]
  exact lowerInverseCell_joined X hC i d ha

def lowerTupleAt (X : C.Model) (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)) :=
  X.sumTuple (Shape.globe n) i n (by exact hi) hi a b
    ((congrArg (fun q : Shape.globe i ⟶ Shape.globe n => X.eval (C.base q) a)
      (Shape.globe_seam_general n i hi)).trans hab)

theorem lowerTupleAt_add (X : C.Model) (i d : ℕ) (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    lowerTupleAt X i (i + 1 + d) (by omega) a b hab = lowerTuple X i d a b hab := rfl

theorem lowerTupleAt_left (X : C.Model) (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    X.eval (C.base (lowerPairLeft i n hi)) (lowerTupleAt X i n hi a b hab) = a :=
  X.sumTuple_left _ _ _ _ _ _ _ _

theorem lowerTupleAt_right (X : C.Model) (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    X.eval (C.base (lowerPairRight i n hi)) (lowerTupleAt X i n hi a b hab) = b :=
  X.sumTuple_right _ _ _ _ _ _ _ _

theorem lowerTupleAt_generalFace (X : C.Model) (i m n : ℕ) (hi : i < m) (hm : m < n)
    (side : Bool) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n (Nat.lt_trans hi hm) true a =
      lowerFace X i n (Nat.lt_trans hi hm) false b) :
    X.eval (lowerPairMap C i m n hi hm side)
        (lowerTupleAt X i n (Nat.lt_trans hi hm) a b hab) =
      lowerTupleAt X i m hi (lowerFace X m n hm side a) (lowerFace X m n hm side b)
        (by rw [lowerFace_face, lowerFace_face]; exact hab) := by
  apply X.sumTuple_ext (Shape.globe m) i m (by exact hi) hi
  · change X.eval (C.base (lowerPairLeft i m hi)) (X.eval _ _) =
      X.eval (C.base (lowerPairLeft i m hi)) _
    rw [← eval_comp, lowerPairMap_left, C.base_comp, eval_comp, lowerTupleAt_left X i m]
    exact congrArg (X.eval (C.base (Shape.face hm side)))
      (lowerTupleAt_left X i n (Nat.lt_trans hi hm) a b hab)
  · change X.eval (C.base (lowerPairRight i m hi)) (X.eval _ _) =
      X.eval (C.base (lowerPairRight i m hi)) _
    rw [← eval_comp, lowerPairMap_right, C.base_comp, eval_comp, lowerTupleAt_right X i m]
    exact congrArg (X.eval (C.base (Shape.face hm side)))
      (lowerTupleAt_right X i n (Nat.lt_trans hi hm) a b hab)

theorem map_lowerTupleAt {X Y : C.Model} (f : X ⟶ Y)
    (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    f.app (op (⟨lowerPairShape i n hi⟩ : C.Obj)) (lowerTupleAt X i n hi a b hab) =
      lowerTupleAt Y i n hi ((underlyingMap f).app n a) ((underlyingMap f).app n b)
        (by rw [← map_lowerFace, ← map_lowerFace, hab]) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [lowerTupleAt_add, lowerTupleAt_add]
  exact map_lowerTuple f i d a b hab

#print axioms map_lowerCompositionCellAt
#print axioms lowerCompositionCellAt_face
#print axioms lowerCompositionCellAt_joined
#print axioms map_lowerInverseCellAt
#print axioms lowerInverseCellAt_joined
#print axioms lowerTupleAt_generalFace

end HomotopyHypothesis.Category.CylinderCorollary
