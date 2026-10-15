import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalization
import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.OperationEvaluation
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def PairCellBoundary (X : C.Model) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (z : X.underlying.Cell (n + 1)) : Prop :=
  ∀ side : Bool, lowerFace X n (n + 1) (Nat.lt_succ_self n) side z =
    X.eval q (B.value n hi le_rfl side)

theorem pairCellBoundary_parallel (X : C.Model) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    {z₀ z₁ : X.underlying.Cell (n + 1)} (hz₀ : PairCellBoundary X i n hi B q z₀)
    (hz₁ : PairCellBoundary X i n hi B q z₁) : X.underlying.Parallel (n + 1) z₀ z₁ :=
  ⟨(hz₀ false).trans (hz₁ false).symm, (hz₀ true).trans (hz₁ true).symm⟩

theorem pairCellBoundary_lowerFace (X : C.Model) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (z : X.underlying.Cell (n + 1)) (hz : PairCellBoundary X i n hi B q z)
    (m : ℕ) (hm : m < n) (side : Bool) :
    lowerFace X m (n + 1) (by omega) side z =
      lowerFace X m n hm side (X.eval q (B.value n hi le_rfl false)) := by
  rw [← lowerFace_face X m n (n + 1) hm (Nat.lt_succ_self n) side false z, hz false]

theorem pairTuple_seam (X : C.Model) (i n : ℕ) (hi : i < n)
    (t : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj))) :
    lowerFace X i n hi true (X.eval (C.base (lowerPairLeft i n hi)) t) =
      lowerFace X i n hi false (X.eval (C.base (lowerPairRight i n hi)) t) := by
  dsimp only [lowerFace]
  rw [← eval_comp, ← eval_comp, ← C.base_comp, ← C.base_comp]
  exact congrArg (fun q => X.eval (C.base q) t) (lowerPair_seam i n hi)

theorem prescribedPairBoundary_cell_seam (X : C.Model) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (a b : X.underlying.Cell (n + 1))
    (ha : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) a)
    (hb : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) b) :
    lowerFace X i (n + 1) (by omega) true a = lowerFace X i (n + 1) (by omega) false b := by
  rw [pairCellBoundary_lowerFace X i n hi B _ a ha i hi true,
    pairCellBoundary_lowerFace X i n hi B _ b hb i hi false]
  exact pairTuple_seam X i n hi (B.value n hi le_rfl false)

theorem prescribedPairBoundary_cell_tuple (X : C.Model) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (a b : X.underlying.Cell (n + 1))
    (ha : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) a)
    (hb : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) b)
    (hab : lowerFace X i (n + 1) (by omega) true a = lowerFace X i (n + 1) (by omega) false b) :
    B.Realizes (lowerTupleAt X i (n + 1) (by omega) a b hab) := by
  apply B.realizes_of_top
  intro side
  rw [lowerTupleAt_generalFace]
  apply X.sumTuple_ext (Shape.globe n) i n hi hi
  · change X.eval (C.base (lowerPairLeft i n hi)) _ = _
    rw [lowerTupleAt_left]
    exact ha side
  · change X.eval (C.base (lowerPairRight i n hi)) _ = _
    rw [lowerTupleAt_right]
    exact hb side

theorem compositionCellBoundary_lowerFace (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (z : X.underlying.Cell (n + 1)) (hz : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) z)
    (side : Bool) :
    lowerFace X i (n + 1) (by omega) side z =
      lowerFace X i n hi side
        (X.eval (C.base (lowerPairInclusion i n hi side)) (B.value n hi le_rfl false)) := by
  rw [pairCellBoundary_lowerFace X i n hi B _ z hz i hi side]
  dsimp only [lowerFace]
  rw [← eval_comp, pairCompositionAt_boundary, eval_comp]

theorem prescribedPairBoundary_composition (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (a b : X.underlying.Cell (n + 1))
    (ha : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) a)
    (hb : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) b)
    (hab : lowerFace X i (n + 1) (by omega) true a = lowerFace X i (n + 1) (by omega) false b) :
    PairCellBoundary X i n hi B (pairCompositionAt hC i n hi)
      (lowerCompositionCellAt X hC i (n + 1) (by omega) a b hab) := by
  intro side
  simp only [lowerCompositionCellAt_face X hC i n hi side, ha side, hb side,
    pairCompositionAt, eval_operationCompositionAt]

#print axioms pairTuple_seam
#print axioms prescribedPairBoundary_cell_seam
#print axioms prescribedPairBoundary_cell_tuple
#print axioms compositionCellBoundary_lowerFace
#print axioms prescribedPairBoundary_composition

end HomotopyHypothesis.Category.CylinderCorollary
