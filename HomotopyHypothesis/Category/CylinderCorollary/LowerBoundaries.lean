import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem lowerFace_source (X : C.Model) (n : ℕ) (a : X.underlying.Cell (n + 1)) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) false a =
      X.underlying.source n a := rfl

theorem lowerFace_target (X : C.Model) (n : ℕ) (a : X.underlying.Cell (n + 1)) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) true a =
      X.underlying.target n a := rfl

theorem lowerCompositionCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) (a b : X.underlying.Cell (i + 1 + d))
    (hab : lowerFace X i (i + 1 + d) (by omega) true a =
      lowerFace X i (i + 1 + d) (by omega) false b) :
    lowerFace X i (i + 1 + d) (by omega) side
        (lowerCompositionCell X hC i d a b hab) =
      lowerFace X i (i + 1 + d) (by omega) side (if side then b else a) := by
  induction d with
  | zero =>
    rw [lowerCompositionCell_zero]
    cases side
    · exact X.compCell_source hC i a b hab
    · exact X.compCell_target hC i a b hab
  | succ d ih =>
    change lowerFace X i (i + 1 + d + 1) _ side
      (lowerCompositionCell X hC i (d + 1) a b hab) =
        lowerFace X i (i + 1 + d + 1) _ side (if side then b else a)
    conv_lhs =>
      rw [← lowerFace_face X i (i + 1 + d) (i + 1 + d + 1)
        (by omega) (Nat.lt_succ_self _) side false]
    rw [lowerCompositionCell_face, ih]
    cases side <;> exact lowerFace_face X i (i + 1 + d) (i + 1 + d + 1)
      (by omega) (Nat.lt_succ_self _) _ false _

theorem lowerInverseCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (i d : ℕ) (side : Bool) (a : X.underlying.Cell (i + 1 + d)) :
    lowerFace X i (i + 1 + d) (by omega) side (lowerInverseCell X hC i d a) =
      lowerFace X i (i + 1 + d) (by omega) (!side) a := by
  induction d with
  | zero =>
    rw [lowerInverseCell_zero]
    cases side
    · exact X.inverseCell_source hC i a
    · exact X.inverseCell_target hC i a
  | succ d ih =>
    change lowerFace X i (i + 1 + d + 1) _ side (lowerInverseCell X hC i (d + 1) a) =
      lowerFace X i (i + 1 + d + 1) _ (!side) a
    conv_lhs =>
      rw [← lowerFace_face X i (i + 1 + d) (i + 1 + d + 1)
        (by omega) (Nat.lt_succ_self _) side false]
    rw [lowerInverseCell_face, ih, lowerFace_face]

theorem lowerFace_unitCell (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a : X.underlying.Cell n) :
    lowerFace X i (n + 1) (by omega) side (X.unitCell hC n a) =
      lowerFace X i n hi side a := by
  rw [← lowerFace_face X i n (n + 1) hi (Nat.lt_succ_self _) side false,
    lowerFace_source, X.unitCell_source]

theorem lowerFace_eq_of_joined (X : C.Model) (i n : ℕ) (hi : i < n)
    (side : Bool) {a b : X.underlying.Cell n} (h : X.underlying.Joined n a b) :
    lowerFace X i n hi side a = lowerFace X i n hi side b := by
  obtain ⟨c, hs, ht⟩ := h
  calc
    lowerFace X i n hi side a =
        lowerFace X i n hi side (lowerFace X n (n + 1) (Nat.lt_succ_self _) false c) := by
      rw [lowerFace_source, hs]
    _ = lowerFace X i (n + 1) (by omega) side c := lowerFace_face _ _ _ _ _ _ _ _ _
    _ = lowerFace X i n hi side
        (lowerFace X n (n + 1) (Nat.lt_succ_self _) true c) :=
      (lowerFace_face _ _ _ _ _ _ _ _ _).symm
    _ = lowerFace X i n hi side b := by rw [lowerFace_target, ht]

theorem lowerCompositionCell_joined (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    {a₀ a₁ b₀ b₁ : X.underlying.Cell (i + 1 + d)}
    (ha : X.underlying.Joined (i + 1 + d) a₀ a₁)
    (hb : X.underlying.Joined (i + 1 + d) b₀ b₁)
    (hab₀ : lowerFace X i (i + 1 + d) (by omega) true a₀ =
      lowerFace X i (i + 1 + d) (by omega) false b₀)
    (hab₁ : lowerFace X i (i + 1 + d) (by omega) true a₁ =
      lowerFace X i (i + 1 + d) (by omega) false b₁) :
    X.underlying.Joined (i + 1 + d)
      (lowerCompositionCell X hC i d a₀ b₀ hab₀)
      (lowerCompositionCell X hC i d a₁ b₁ hab₁) := by
  obtain ⟨a, has, hat⟩ := ha
  obtain ⟨b, hbs, hbt⟩ := hb
  have hab : lowerFace X i (i + 1 + (d + 1)) (by omega) true a =
      lowerFace X i (i + 1 + (d + 1)) (by omega) false b := by
    change lowerFace X i (i + 1 + d + 1) _ true a =
      lowerFace X i (i + 1 + d + 1) _ false b
    rw [← lowerFace_face X i (i + 1 + d) (i + 1 + d + 1)
      (by omega) (Nat.lt_succ_self _) true false,
      ← lowerFace_face X i (i + 1 + d) (i + 1 + d + 1)
        (by omega) (Nat.lt_succ_self _) false false,
      lowerFace_source, lowerFace_source, has, hbs]
    exact hab₀
  refine ⟨lowerCompositionCell X hC i (d + 1) a b hab, ?_, ?_⟩
  · change lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) false _ = _
    rw [lowerCompositionCell_face]
    simp only [lowerFace_source, has, hbs]
  · change lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) true _ = _
    rw [lowerCompositionCell_face]
    simp only [lowerFace_target, hat, hbt]

theorem lowerInverseCell_joined (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    {a₀ a₁ : X.underlying.Cell (i + 1 + d)}
    (h : X.underlying.Joined (i + 1 + d) a₀ a₁) :
    X.underlying.Joined (i + 1 + d)
      (lowerInverseCell X hC i d a₀) (lowerInverseCell X hC i d a₁) := by
  obtain ⟨a, hs, ht⟩ := h
  refine ⟨lowerInverseCell X hC i (d + 1) a, ?_, ?_⟩
  · change lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) false _ = _
    rw [lowerInverseCell_face, lowerFace_source, hs]
  · change lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) true _ = _
    rw [lowerInverseCell_face, lowerFace_target, ht]

#print axioms lowerCompositionCell_boundary
#print axioms lowerInverseCell_boundary
#print axioms lowerCompositionCell_joined
#print axioms lowerInverseCell_joined

end HomotopyHypothesis.Category.CylinderCorollary
