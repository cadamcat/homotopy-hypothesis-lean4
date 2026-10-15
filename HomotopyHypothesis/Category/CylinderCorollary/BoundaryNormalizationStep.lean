import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CellUnitExtensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.IteratedUnits
import HomotopyHypothesis.Category.CylinderCorollary.LowerBoundaries
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.OperationEvaluation
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}} {i h : ℕ} {hi : i < h} {anchor : Bool}

def NormalizationCellBoundary (X : C.Model) (A : NormalizationFamilyAt C i h hi anchor)
    (n : ℕ) (hn : h ≤ n) (B : PrescribedPairBoundary X i n (by omega))
    (z : X.underlying.Cell (n + 1)) : Prop :=
  ∀ side : Bool, lowerFace X n (n + 1) (Nat.lt_succ_self n) side z =
    X.eval (A.operation n hn) (B.value n (by omega) le_rfl side)

theorem normalizationCellBoundary_face (X : C.Model)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) (z : X.underlying.Cell (n + 1))
    (hz : NormalizationCellBoundary X A n hn B z) (side : Bool) :
    lowerFace X h (n + 1) (by omega) side z =
      X.eval (A.operation h le_rfl) (B.value h hi hn side) := by
  by_cases he : h = n
  · subst n
    exact hz side
  · have hhn : h < n := by omega
    rw [← lowerFace_face X h n (n + 1) hhn (Nat.lt_succ_self n) side false z, hz false]
    dsimp only [lowerFace]
    rw [← eval_comp, A.generalFace h n le_rfl hhn side, eval_comp,
      B.face h n hi hhn le_rfl side false]

theorem normalizationCellBoundary_parallel (X : C.Model)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega))
    {z₀ z₁ : X.underlying.Cell (n + 1)}
    (hz₀ : NormalizationCellBoundary X A n hn B z₀)
    (hz₁ : NormalizationCellBoundary X A n hn B z₁) :
    X.underlying.Parallel (n + 1) z₀ z₁ :=
  ⟨(hz₀ false).trans (hz₁ false).symm, (hz₀ true).trans (hz₁ true).symm⟩

def boundarySourceCorrectionCell (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) : X.underlying.Cell (n + 1) :=
  unitCellExtension X hC (h + 1) (n + 1) (by omega)
    (X.eval (normalizationCorrection hC A) (B.value h hi hn false))

def boundaryTargetCorrectionCell (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) : X.underlying.Cell (n + 1) :=
  unitCellExtension X hC (h + 1) (n + 1) (by omega)
    (X.eval (normalizationReverseCorrection hC A) (B.value h hi hn true))

theorem boundarySourceCorrectionCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) (side : Bool) :
    lowerFace X h (n + 1) (by omega) side (boundarySourceCorrectionCell X hC A n hn B) =
      X.eval (if side then A.operation h le_rfl else C.base (lowerPairInclusion i h hi anchor))
        (B.value h hi hn false) := by
  dsimp only [boundarySourceCorrectionCell]
  rw [unitCellExtension_lowerFace X hC h (h + 1) (n + 1) (Nat.lt_succ_self h) (by omega)]
  dsimp only [lowerFace]
  rw [← eval_comp]
  cases side
  · exact congrArg (fun q => X.eval q (B.value h hi hn false))
      (normalizationCorrection_source hC A)
  · exact congrArg (fun q => X.eval q (B.value h hi hn false))
      (normalizationCorrection_target hC A)

theorem boundaryTargetCorrectionCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) (side : Bool) :
    lowerFace X h (n + 1) (by omega) side (boundaryTargetCorrectionCell X hC A n hn B) =
      X.eval (if side then C.base (lowerPairInclusion i h hi anchor) else A.operation h le_rfl)
        (B.value h hi hn true) := by
  dsimp only [boundaryTargetCorrectionCell]
  rw [unitCellExtension_lowerFace X hC h (h + 1) (n + 1) (Nat.lt_succ_self h) (by omega)]
  dsimp only [lowerFace]
  rw [← eval_comp]
  cases side
  · exact congrArg (fun q => X.eval q (B.value h hi hn true))
      (normalizationReverseCorrection_source hC A)
  · exact congrArg (fun q => X.eval q (B.value h hi hn true))
      (normalizationReverseCorrection_target hC A)

def boundaryNormalizationStepCell (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) (z : X.underlying.Cell (n + 1))
    (hz : NormalizationCellBoundary X A n hn B z) : X.underlying.Cell (n + 1) :=
  lowerCompositionCellAt X hC h (n + 1) (by omega) (boundarySourceCorrectionCell X hC A n hn B)
    (lowerCompositionCellAt X hC h (n + 1) (by omega) z (boundaryTargetCorrectionCell X hC A n hn B)
      ((normalizationCellBoundary_face X A n hn B z hz true).trans
        (boundaryTargetCorrectionCell_boundary X hC A n hn B false).symm))
    (by
      rw [lowerCompositionCellAt_boundary X hC h (n + 1) (by omega) false]
      exact (boundarySourceCorrectionCell_boundary X hC A n hn B true).trans
        (normalizationCellBoundary_face X A n hn B z hz false).symm)

theorem boundaryNormalizationStepCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) (z : X.underlying.Cell (n + 1))
    (hz : NormalizationCellBoundary X A n hn B z) (side : Bool) :
    lowerFace X h (n + 1) (by omega) side (boundaryNormalizationStepCell X hC A n hn B z hz) =
      X.eval (C.base (lowerPairInclusion i h hi anchor)) (B.value h hi hn side) := by
  dsimp only [boundaryNormalizationStepCell]
  rw [lowerCompositionCellAt_boundary X hC h (n + 1) (by omega) side]
  cases side
  · exact boundarySourceCorrectionCell_boundary X hC A n hn B false
  · simp only [↓reduceIte]
    rw [lowerCompositionCellAt_boundary X hC h (n + 1) (by omega) true]
    exact boundaryTargetCorrectionCell_boundary X hC A n hn B true

theorem boundarySourceCorrectionCell_face (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h < n)
    (B : PrescribedPairBoundary X i n (by omega)) (side : Bool) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) side
        (boundarySourceCorrectionCell X hC A n (Nat.le_of_lt hn) B) =
      X.eval (liftedSourceCorrection hC A n (by omega)) (B.value n (by omega) le_rfl side) := by
  dsimp only [boundarySourceCorrectionCell]
  rw [unitCellExtension_face X hC (h + 1) n (by omega) side]
  dsimp only [liftedSourceCorrection]
  rw [eval_comp, eval_unitExtension, B.face h n hi hn le_rfl false side]

theorem boundaryTargetCorrectionCell_face (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h < n)
    (B : PrescribedPairBoundary X i n (by omega)) (side : Bool) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) side
        (boundaryTargetCorrectionCell X hC A n (Nat.le_of_lt hn) B) =
      X.eval (liftedTargetCorrection hC A n (by omega)) (B.value n (by omega) le_rfl side) := by
  dsimp only [boundaryTargetCorrectionCell]
  rw [unitCellExtension_face X hC (h + 1) n (by omega) side]
  dsimp only [liftedTargetCorrection]
  rw [eval_comp, eval_unitExtension, B.face h n hi hn le_rfl true side]

theorem boundaryNormalizationStepCell_next (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h < n)
    (B : PrescribedPairBoundary X i n (by omega)) (z : X.underlying.Cell (n + 1))
    (hz : NormalizationCellBoundary X A n (Nat.le_of_lt hn) B z) :
    NormalizationCellBoundary X (nextNormalizationFamily hC A) n (by omega) B
      (boundaryNormalizationStepCell X hC A n (Nat.le_of_lt hn) B z hz) := by
  intro side
  simp only [boundaryNormalizationStepCell, lowerCompositionCellAt_face X hC h n hn side,
    boundarySourceCorrectionCell_face X hC A n hn B side,
    boundaryTargetCorrectionCell_face X hC A n hn B side, hz side,
    nextNormalizationFamily, normalizationStepOperation, eval_operationCompositionAt]

theorem boundaryNormalizationStepCell_eval (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega))
    (t : X.presheaf.obj (op (⟨lowerPairShape i (n + 1) (by omega)⟩ : C.Obj)))
    (ht : B.Realizes t) (z : X.underlying.Cell (n + 1))
    (hz : NormalizationCellBoundary X A n hn B z)
    (he : z = X.eval (A.operation (n + 1) (by omega)) t) :
    boundaryNormalizationStepCell X hC A n hn B z hz =
      X.eval ((nextNormalizationFamily hC A).operation (n + 1) (by omega)) t := by
  simp only [boundaryNormalizationStepCell, nextNormalizationFamily, normalizationStepOperation,
    eval_operationCompositionAt, liftedSourceCorrection, liftedTargetCorrection, eval_comp,
    eval_unitExtension, ht h hi hn false, ht h hi hn true,
    boundarySourceCorrectionCell, boundaryTargetCorrectionCell, he]

theorem boundaryNormalizationStepCell_joined (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega))
    {z₀ z₁ : X.underlying.Cell (n + 1)}
    (hz₀ : NormalizationCellBoundary X A n hn B z₀)
    (hz₁ : NormalizationCellBoundary X A n hn B z₁)
    (hz : X.underlying.Joined (n + 1) z₀ z₁) :
    X.underlying.Joined (n + 1) (boundaryNormalizationStepCell X hC A n hn B z₀ hz₀)
      (boundaryNormalizationStepCell X hC A n hn B z₁ hz₁) := by
  dsimp only [boundaryNormalizationStepCell]
  apply lowerCompositionCellAt_joined X hC h (n + 1) (by omega) (X.joined_refl hC _ _)
  apply lowerCompositionCellAt_joined X hC h (n + 1) (by omega) hz (X.joined_refl hC _ _)

theorem lowerCompositionCellAt_parallel (X : C.Model) (hC : C.IsCoherator)
    (j r : ℕ) (hj : j < r) {a₀ a₁ b₀ b₁ : X.underlying.Cell r}
    (ha : X.underlying.Parallel r a₀ a₁) (hb : X.underlying.Parallel r b₀ b₁)
    (hab₀ : lowerFace X j r hj true a₀ = lowerFace X j r hj false b₀)
    (hab₁ : lowerFace X j r hj true a₁ = lowerFace X j r hj false b₁) :
    X.underlying.Parallel r (lowerCompositionCellAt X hC j r hj a₀ b₀ hab₀)
      (lowerCompositionCellAt X hC j r hj a₁ b₁ hab₁) := by
  cases r with
  | zero => omega
  | succ r =>
    by_cases he : j = r
    · subst j
      constructor
      · change lowerFace X r (r + 1) hj false _ = lowerFace X r (r + 1) hj false _
        simpa only [lowerCompositionCellAt_boundary, Bool.false_eq_true, ↓reduceIte,
          lowerFace_source] using ha.1
      · change lowerFace X r (r + 1) hj true _ = lowerFace X r (r + 1) hj true _
        simpa only [lowerCompositionCellAt_boundary, ↓reduceIte, lowerFace_target] using hb.2
    · have hjr : j < r := by omega
      constructor
      · change lowerFace X r (r + 1) (Nat.lt_succ_self r) false _ =
          lowerFace X r (r + 1) (Nat.lt_succ_self r) false _
        simp only [lowerCompositionCellAt_face X hC j r hjr false, lowerFace_source, ha.1, hb.1]
      · change lowerFace X r (r + 1) (Nat.lt_succ_self r) true _ =
          lowerFace X r (r + 1) (Nat.lt_succ_self r) true _
        simp only [lowerCompositionCellAt_face X hC j r hjr true, lowerFace_target, ha.2, hb.2]

theorem boundaryNormalizationStepCell_reflects_joined (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega))
    {z₀ z₁ : X.underlying.Cell (n + 1)}
    (hz₀ : NormalizationCellBoundary X A n hn B z₀)
    (hz₁ : NormalizationCellBoundary X A n hn B z₁)
    (hz : X.underlying.Joined (n + 1) (boundaryNormalizationStepCell X hC A n hn B z₀ hz₀)
      (boundaryNormalizationStepCell X hC A n hn B z₁ hz₁)) :
    X.underlying.Joined (n + 1) z₀ z₁ := by
  have hp := normalizationCellBoundary_parallel X A n hn B hz₀ hz₁
  have hc₀ : lowerFace X h (n + 1) (by omega) true z₀ =
      lowerFace X h (n + 1) (by omega) false (boundaryTargetCorrectionCell X hC A n hn B) :=
    (normalizationCellBoundary_face X A n hn B z₀ hz₀ true).trans
      (boundaryTargetCorrectionCell_boundary X hC A n hn B false).symm
  have hc₁ : lowerFace X h (n + 1) (by omega) true z₁ =
      lowerFace X h (n + 1) (by omega) false (boundaryTargetCorrectionCell X hC A n hn B) :=
    (normalizationCellBoundary_face X A n hn B z₁ hz₁ true).trans
      (boundaryTargetCorrectionCell_boundary X hC A n hn B false).symm
  have hp' := lowerCompositionCellAt_parallel X hC h (n + 1) (by omega) hp
    (X.joined_refl hC _ (boundaryTargetCorrectionCell X hC A n hn B)).parallel hc₀ hc₁
  have hs₀ : lowerFace X h (n + 1) (by omega) true (boundarySourceCorrectionCell X hC A n hn B) =
      lowerFace X h (n + 1) (by omega) false
        (lowerCompositionCellAt X hC h (n + 1) (by omega) z₀ (boundaryTargetCorrectionCell X hC A n hn B) hc₀) := by
    rw [lowerCompositionCellAt_boundary X hC h (n + 1) (by omega) false]
    exact (boundarySourceCorrectionCell_boundary X hC A n hn B true).trans
      (normalizationCellBoundary_face X A n hn B z₀ hz₀ false).symm
  have hs₁ : lowerFace X h (n + 1) (by omega) true (boundarySourceCorrectionCell X hC A n hn B) =
      lowerFace X h (n + 1) (by omega) false
        (lowerCompositionCellAt X hC h (n + 1) (by omega) z₁ (boundaryTargetCorrectionCell X hC A n hn B) hc₁) := by
    rw [lowerCompositionCellAt_boundary X hC h (n + 1) (by omega) false]
    exact (boundarySourceCorrectionCell_boundary X hC A n hn B true).trans
      (normalizationCellBoundary_face X A n hn B z₁ hz₁ false).symm
  have ht := lowerCompositionCellAt_left_reflects_joined X hC h (n + 1) (by omega)
    (boundarySourceCorrectionCell X hC A n hn B) _ _ hp' hs₀ hs₁ hz
  exact lowerCompositionCellAt_right_reflects_joined X hC h (n + 1) (by omega)
    z₀ z₁ (boundaryTargetCorrectionCell X hC A n hn B) hp hc₀ hc₁ ht

#print axioms normalizationCellBoundary_face
#print axioms boundaryNormalizationStepCell_boundary
#print axioms boundaryNormalizationStepCell_next
#print axioms boundaryNormalizationStepCell_eval
#print axioms boundaryNormalizationStepCell_joined
#print axioms lowerCompositionCellAt_parallel
#print axioms boundaryNormalizationStepCell_reflects_joined

end HomotopyHypothesis.Category.CylinderCorollary
