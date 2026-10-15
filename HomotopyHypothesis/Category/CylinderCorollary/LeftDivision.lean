import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalization
import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.DivisionBoundary
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFaces
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

theorem leftDivisionStart_seam (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    lowerFace X i (n + 1) (by omega) true (lowerInverseCellAt X hC i (n + 1) (by omega) g) =
      lowerFace X i (n + 1) (by omega) false b :=
  (lowerInverseCellAt_boundary X hC i (n + 1) (by omega) true g).trans
    ((pairCellBoundary_lowerFace X i n hi B _ g hg i hi false).trans
      (compositionCellBoundary_lowerFace X hC i n hi B b hb false).symm)

def leftDivisionStartCell (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) : X.underlying.Cell (n + 1) :=
  lowerCompositionCellAt X hC i (n + 1) (by omega)
    (lowerInverseCellAt X hC i (n + 1) (by omega) g) b (leftDivisionStart_seam X hC i n hi B g hg b hb)

theorem leftDivisionStartCell_boundary (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    NormalizationCellBoundary X (initialNormalizationFamily hC i) n (by omega) B
      (leftDivisionStartCell X hC i n hi B g hg b hb) := by
  intro side
  simp only [leftDivisionStartCell, lowerCompositionCellAt_face X hC i n hi side,
    lowerInverseCellAt_face X hC i n hi side, hg side, hb side,
    initialNormalizationFamily, initialNormalizationAt_eq,
    eval_operationCompositionAt, eval_operationInverseAt]

def leftDivisionStart (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) g)
    (b : X.underlying.Cell (n + 1))
    (hb : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b) :
    NormalizationCells X (initialNormalizationFamily hC i) n (by omega) B :=
  ⟨leftDivisionStartCell X hC i n hi B g hg b hb, leftDivisionStartCell_boundary X hC i n hi B g hg b hb⟩

theorem leftDivisionStartCell_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : X.underlying.Cell (n + 1))
    (hg : PairCellBoundary X i n hi B (C.base (lowerPairLeft i n hi)) g)
    (b₀ b₁ : X.underlying.Cell (n + 1))
    (hb₀ : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b₀)
    (hb₁ : PairCellBoundary X i n hi B (pairCompositionAt hC i n hi) b₁) :
    X.underlying.Joined (n + 1) (leftDivisionStartCell X hC i n hi B g hg b₀ hb₀)
      (leftDivisionStartCell X hC i n hi B g hg b₁ hb₁) ↔ X.underlying.Joined (n + 1) b₀ b₁ := by
  dsimp only [leftDivisionStartCell]
  constructor
  · intro hb
    exact lowerCompositionCellAt_left_reflects_joined X hC i (n + 1) (by omega)
      (lowerInverseCellAt X hC i (n + 1) (by omega) g) b₀ b₁
      (pairCellBoundary_parallel X i n hi B _ hb₀ hb₁)
      (leftDivisionStart_seam X hC i n hi B g hg b₀ hb₀)
      (leftDivisionStart_seam X hC i n hi B g hg b₁ hb₁) hb
  · intro hb
    exact lowerCompositionCellAt_joined X hC i (n + 1) (by omega) (X.joined_refl hC _ _) hb
      (leftDivisionStart_seam X hC i n hi B g hg b₀ hb₀)
      (leftDivisionStart_seam X hC i n hi B g hg b₁ hb₁)

def leftDivisionNormalizer (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    X.underlying.Cell (i + 1 + d + 1) :=
  boundaryNormalizer X hC (initialNormalizationFamily hC i) d B
    (leftDivisionStart X hC i (i + 1 + d) (by omega) B g hg b hb)

theorem leftDivisionNormalizer_boundary (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) (leftDivisionNormalizer X hC i d B g hg b hb) := by
  intro side
  exact boundaryNormalizer_boundary X hC (initialNormalizationFamily hC i) d B
    (leftDivisionStart X hC i (i + 1 + d) (by omega) B g hg b hb) side

theorem leftDivisionNormalizer_joined_iff (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) g)
    (b₀ b₁ : X.underlying.Cell (i + 1 + d + 1))
    (hb₀ : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b₀)
    (hb₁ : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b₁) :
    X.underlying.Joined (i + 1 + d + 1) (leftDivisionNormalizer X hC i d B g hg b₀ hb₀)
      (leftDivisionNormalizer X hC i d B g hg b₁ hb₁) ↔ X.underlying.Joined (i + 1 + d + 1) b₀ b₁ :=
  (boundaryNormalizer_joined_iff X hC (initialNormalizationFamily hC i) d B
    (leftDivisionStart X hC i (i + 1 + d) (by omega) B g hg b₀ hb₀)
    (leftDivisionStart X hC i (i + 1 + d) (by omega) B g hg b₁ hb₁)).trans
    (leftDivisionStartCell_joined_iff X hC i (i + 1 + d) (by omega) B g hg b₀ b₁ hb₀ hb₁)

theorem leftDivisionNormalizer_composition (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g a : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) g)
    (ha : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) a)
    (hga : lowerFace X i (i + 1 + d + 1) (by omega) true g =
      lowerFace X i (i + 1 + d + 1) (by omega) false a)
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega))
      (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) g a hga)) :
    X.underlying.Joined (i + 1 + d + 1)
      (leftDivisionNormalizer X hC i d B g hg
        (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) g a hga) hb) a := by
  let t := lowerTupleAt X i (i + 1 + d + 1) (by omega) g a hga
  have ht : B.Realizes t := prescribedPairBoundary_cell_tuple X i (i + 1 + d) (by omega) B g a hg ha hga
  let z := leftDivisionStart X hC i (i + 1 + d) (by omega) B g hg
    (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) g a hga) hb
  have he : z.1 = X.eval ((initialNormalizationFamily hC i).operation (i + 1 + d + 1) (by omega)) t := by
    simp only [z, t, leftDivisionStart, leftDivisionStartCell, initialNormalizationFamily,
      initialNormalizationAt_eq, eval_operationCompositionAt, eval_operationInverseAt,
      lowerTupleAt_left, eval_pairCompositionAt]
  have hj := boundaryNormalizer_joined_anchor X hC (initialNormalizationFamily hC i) d B t ht z he
  simpa only [t, z, leftDivisionNormalizer, lowerPairInclusion, ↓reduceIte, lowerTupleAt_right] using hj

theorem leftDivision_exists (X : C.Model) (hC : C.IsCoherator) (i d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (g : X.underlying.Cell (i + 1 + d + 1))
    (hg : PairCellBoundary X i (i + 1 + d) (by omega) B
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) g)
    (b : X.underlying.Cell (i + 1 + d + 1))
    (hb : PairCellBoundary X i (i + 1 + d) (by omega) B (pairCompositionAt hC i (i + 1 + d) (by omega)) b) :
    ∃ a : X.underlying.Cell (i + 1 + d + 1),
      PairCellBoundary X i (i + 1 + d) (by omega) B (C.base (lowerPairRight i (i + 1 + d) (by omega))) a ∧
      ∃ hga : lowerFace X i (i + 1 + d + 1) (by omega) true g =
        lowerFace X i (i + 1 + d + 1) (by omega) false a,
        X.underlying.Joined (i + 1 + d + 1)
          (lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) g a hga) b := by
  let a := leftDivisionNormalizer X hC i d B g hg b hb
  have ha := leftDivisionNormalizer_boundary X hC i d B g hg b hb
  have hga := prescribedPairBoundary_cell_seam X i (i + 1 + d) (by omega) B g a hg ha
  let b' := lowerCompositionCellAt X hC i (i + 1 + d + 1) (by omega) g a hga
  have hb' := prescribedPairBoundary_composition X hC i (i + 1 + d) (by omega) B g a hg ha hga
  have hj := leftDivisionNormalizer_composition X hC i d B g a hg ha hga hb'
  exact ⟨a, ha, hga, (leftDivisionNormalizer_joined_iff X hC i d B g hg b' b hb' hb).1 hj⟩

#print axioms leftDivisionStart_seam
#print axioms leftDivisionStartCell_boundary
#print axioms leftDivisionStartCell_joined_iff
#print axioms leftDivisionNormalizer_boundary
#print axioms leftDivisionNormalizer_joined_iff
#print axioms leftDivisionNormalizer_composition
#print axioms leftDivision_exists

end HomotopyHypothesis.Category.CylinderCorollary
