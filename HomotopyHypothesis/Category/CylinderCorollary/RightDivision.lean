import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalization
import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.DivisionBoundary
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
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

theorem rightDivisionStart_seam (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    lowerFace X i (n + 1) (by omega) true b =
      lowerFace X i (n + 1) (by omega) false (lowerInverseCellAt X hC i (n + 1) (by omega) g) :=
  (compositionCellBoundary_lowerFace X hC i n hi B b hb true).trans
    ((pairCellBoundary_lowerFace X i n hi B _ g hg i hi true).symm.trans
      (lowerInverseCellAt_boundary X hC i (n + 1) (by omega) false g).symm)

def rightDivisionStartCell (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) : X.underlying.Cell (n + 1) :=
  lowerCompositionCellAt X hC i (n + 1) (by omega) b
    (lowerInverseCellAt X hC i (n + 1) (by omega) g) (rightDivisionStart_seam X hC i n hi B g hg b hb)

theorem rightDivisionStartCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    NormalizationCellBoundary X (initialRightNormalizationFamily hC i) n (by omega) B
      (rightDivisionStartCell X hC i n hi B g hg b hb) := by
  intro side
  simp only [rightDivisionStartCell, lowerCompositionCellAt_face X hC i n hi side,
    lowerInverseCellAt_face X hC i n hi side, hg side, hb side,
    initialRightNormalizationFamily, initialRightNormalizationAt,
    eval_operationCompositionAt, eval_operationInverseAt]

def rightDivisionStart (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    NormalizationCells X (initialRightNormalizationFamily hC i) n (by omega) B :=
  ⟨rightDivisionStartCell X hC i n hi B g hg b hb, rightDivisionStartCell_boundary X hC i n hi B g hg b hb⟩

theorem rightDivisionStartCell_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairRight i n hi)) g)
    (b₀ b₁ : X.underlying.Cell (n + 1))
    (hb₀ : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b₀)
    (hb₁ : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b₁) :
    X.underlying.Joined (n + 1) (rightDivisionStartCell X hC i n hi B g hg b₀ hb₀)
      (rightDivisionStartCell X hC i n hi B g hg b₁ hb₁) ↔ X.underlying.Joined (n + 1) b₀ b₁ := by
  dsimp only [rightDivisionStartCell]
  constructor
  · intro hb
    exact lowerCompositionCellAt_right_reflects_joined X hC i (n + 1) (by omega) b₀ b₁
      (lowerInverseCellAt X hC i (n + 1) (by omega) g)
      (pairCellBoundary_parallel X i n hi B _ hb₀ hb₁)
      (rightDivisionStart_seam X hC i n hi B g hg b₀ hb₀)
      (rightDivisionStart_seam X hC i n hi B g hg b₁ hb₁) hb
  · intro hb
    exact lowerCompositionCellAt_joined X hC i (n + 1) (by omega) hb (X.joined_refl hC _ _)
      (rightDivisionStart_seam X hC i n hi B g hg b₀ hb₀)
      (rightDivisionStart_seam X hC i n hi B g hg b₁ hb₁)

def rightDivisionNormalizer (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    X.underlying.Cell (i + 1 + d + 1) :=
  boundaryNormalizer X hC (initialRightNormalizationFamily hC i) d B
    (rightDivisionStart X hC i (i + 1 + d) (by omega) B g hg b hb)

theorem rightDivisionNormalizer_boundary (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) (rightDivisionNormalizer X hC i d B g hg b hb) := by
  intro side
  exact boundaryNormalizer_boundary X hC (initialRightNormalizationFamily hC i) d B
    (rightDivisionStart X hC i (i + 1 + d) (by omega) B g hg b hb) side

theorem rightDivisionNormalizer_joined_iff (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) g)
    (b₀ b₁ : X.underlying.Cell (i + 1 + d + 1))
    (hb₀ : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b₀)
    (hb₁ : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b₁) :
    X.underlying.Joined (i + 1 + d + 1) (rightDivisionNormalizer X hC i d B g hg b₀ hb₀)
      (rightDivisionNormalizer X hC i d B g hg b₁ hb₁) ↔ X.underlying.Joined (i + 1 + d + 1) b₀ b₁ :=
  (boundaryNormalizer_joined_iff X hC (initialRightNormalizationFamily hC i) d B
    (rightDivisionStart X hC i (i + 1 + d) (by omega) B g hg b₀ hb₀)
    (rightDivisionStart X hC i (i + 1 + d) (by omega) B g hg b₁ hb₁)).trans
    (rightDivisionStartCell_joined_iff X hC i (i + 1 + d) (by omega) B g hg b₀ b₁ hb₀ hb₁)

theorem rightDivisionNormalizer_composition (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g a : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) g)
    (ha : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) a)
    (hag : lowerFace X i (i + 1 + d + 1) (by omega) true a =
      lowerFace X i (i + 1 + d + 1) (by omega) false g)
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega))
      (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) a g hag)) :
    X.underlying.Joined (i + 1 + d + 1)
      (rightDivisionNormalizer X hC i d B g hg
        (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) a g hag) hb) a := by
  let t := lowerTupleAt X i (i + 1 + d + 1) (by omega) a g hag
  have ht : B.Realizes t := prescribedPairBoundary_cell_tuple X i (i + 1 + d) (by omega) B a g ha hg hag
  let z := rightDivisionStart X hC i (i + 1 + d) (by omega) B g hg
    (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) a g hag) hb
  have he : z.1 = X.eval ((initialRightNormalizationFamily hC i).operation (i + 1 + d + 1) (by omega)) t := by
    simp only [z, t, rightDivisionStart, rightDivisionStartCell, initialRightNormalizationFamily,
      initialRightNormalizationAt, eval_operationCompositionAt, eval_operationInverseAt,
      lowerTupleAt_right, eval_pairCompositionAt]
  have hj := boundaryNormalizer_joined_anchor X hC (initialRightNormalizationFamily hC i) d B t ht z he
  simpa only [t, z, rightDivisionNormalizer, lowerPairInclusion, Bool.false_eq_true,
    ↓reduceIte, lowerTupleAt_left] using hj

theorem rightDivision_exists (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    ∃ a : X.underlying.Cell (i + 1 + d + 1),
      PairCellBoundary X i (i + 1 + d) (by omega) B (C.base (lowerPairLeft i (i + 1 + d) (by omega))) a ∧
      ∃ hag : lowerFace X i (i + 1 + d + 1) (by omega) true a =
        lowerFace X i (i + 1 + d + 1) (by omega) false g,
        X.underlying.Joined (i + 1 + d + 1)
          (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) a g hag) b := by
  let a := rightDivisionNormalizer X hC i d B g hg b hb
  have ha := rightDivisionNormalizer_boundary X hC i d B g hg b hb
  have hag := prescribedPairBoundary_cell_seam X i (i + 1 + d) (by omega) B a g ha hg
  let b' := lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) a g hag
  have hb' := prescribedPairBoundary_composition X hC i (i + 1 + d) (by omega) B a g ha hg hag
  have hj := rightDivisionNormalizer_composition X hC i d B g a hg ha hag hb'
  exact ⟨a, ha, hag, (rightDivisionNormalizer_joined_iff X hC i d B g hg b' b hb' hb).1 hj⟩

#print axioms rightDivisionStart_seam
#print axioms rightDivisionStartCell_boundary
#print axioms rightDivisionStartCell_joined_iff
#print axioms rightDivisionNormalizer_boundary
#print axioms rightDivisionNormalizer_joined_iff
#print axioms rightDivisionNormalizer_composition
#print axioms rightDivision_exists

end HomotopyHypothesis.Category.CylinderCorollary
