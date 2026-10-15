import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.GenericNormalization
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.InitialNormalization
import HomotopyHypothesis.Category.CylinderCorollary.IteratedUnits
import HomotopyHypothesis.Category.CylinderCorollary.LowerBoundaries
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFaces
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.OperationEvaluation
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem lowerFace_eq_of_parallel (X : C.Model) (i n : ℕ) (hi : i < n)
    (side : Bool) {a b : X.underlying.Cell n} (hab : X.underlying.Parallel n a b) :
    lowerFace X i n hi side a = lowerFace X i n hi side b := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases he : i = n
    · subst i
      cases side
      · exact hab.1
      · exact hab.2
    · have hin : i < n := by omega
      rw [← lowerFace_face X i n (n + 1) hin (Nat.lt_succ_self n) side false a,
        ← lowerFace_face X i n (n + 1) hin (Nat.lt_succ_self n) side false b,
        lowerFace_source, lowerFace_source, hab.1]

theorem lowerTupleAt_generalFace_congr (X : C.Model) (i m n : ℕ)
    (hi : i < m) (hm : m < n) (side : Bool)
    {a₀ a₁ b₀ b₁ : X.underlying.Cell n}
    (ha : X.underlying.Parallel n a₀ a₁) (hb : X.underlying.Parallel n b₀ b₁)
    (hab₀ : lowerFace X i n (Nat.lt_trans hi hm) true a₀ =
      lowerFace X i n (Nat.lt_trans hi hm) false b₀)
    (hab₁ : lowerFace X i n (Nat.lt_trans hi hm) true a₁ =
      lowerFace X i n (Nat.lt_trans hi hm) false b₁) :
    X.eval (lowerPairMap C i m n hi hm side)
        (lowerTupleAt X i n (Nat.lt_trans hi hm) a₀ b₀ hab₀) =
      X.eval (lowerPairMap C i m n hi hm side)
        (lowerTupleAt X i n (Nat.lt_trans hi hm) a₁ b₁ hab₁) := by
  simp only [lowerTupleAt_generalFace,
    lowerFace_eq_of_parallel X m n hm side ha, lowerFace_eq_of_parallel X m n hm side hb]

theorem nextNormalizationFamily_joined (X : C.Model) (hC : C.IsCoherator)
    {i h : ℕ} {hi : i < h} {anchor : Bool}
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h + 1 ≤ n)
    (t₀ t₁ : X.presheaf.obj (op (⟨lowerPairShape i n (by omega)⟩ : C.Obj)))
    (hu : X.underlying.Joined n (X.eval (A.operation n (by omega)) t₀)
      (X.eval (A.operation n (by omega)) t₁))
    (hfaces : ∀ side : Bool,
      X.eval (lowerPairMap C i h n hi (by omega) side) t₀ =
        X.eval (lowerPairMap C i h n hi (by omega) side) t₁) :
    X.underlying.Joined n (X.eval ((nextNormalizationFamily hC A).operation n hn) t₀)
      (X.eval ((nextNormalizationFamily hC A).operation n hn) t₁) := by
  dsimp only [nextNormalizationFamily, normalizationStepOperation]
  simp only [eval_operationCompositionAt]
  apply lowerCompositionCellAt_joined X hC h n (by omega)
  · simp only [liftedSourceCorrection, eval_comp, hfaces false]
    exact X.joined_refl hC n _
  · apply lowerCompositionCellAt_joined X hC h n (by omega) hu
    simp only [liftedTargetCorrection, eval_comp, hfaces true]
    exact X.joined_refl hC n _

theorem normalizedFamily_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t₀ t₁ : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (hfaces : ∀ m (him : i < m) (hmn : m < n) (side : Bool),
      X.eval (lowerPairMap C i m n him hmn side) t₀ =
        X.eval (lowerPairMap C i m n him hmn side) t₁)
    (hinitial : X.underlying.Joined n (X.eval (initialNormalizationAt hC i n hi) t₀)
      (X.eval (initialNormalizationAt hC i n hi) t₁))
    (p : ℕ) (hp : i + 1 + p ≤ n) :
    X.underlying.Joined n (X.eval ((normalizedFamily hC i p).operation n hp) t₀)
      (X.eval ((normalizedFamily hC i p).operation n hp) t₁) := by
  induction p with
  | zero => exact hinitial
  | succ p ih =>
    apply nextNormalizationFamily_joined X hC (normalizedFamily hC i p) n hp t₀ t₁
    · exact ih (by omega)
    · exact fun side => hfaces (i + 1 + p) (by omega) (by omega) side

theorem rightNormalizedFamily_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t₀ t₁ : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (hfaces : ∀ m (him : i < m) (hmn : m < n) (side : Bool),
      X.eval (lowerPairMap C i m n him hmn side) t₀ =
        X.eval (lowerPairMap C i m n him hmn side) t₁)
    (hinitial : X.underlying.Joined n (X.eval (initialRightNormalizationAt hC i n hi) t₀)
      (X.eval (initialRightNormalizationAt hC i n hi) t₁))
    (p : ℕ) (hp : i + 1 + p ≤ n) :
    X.underlying.Joined n (X.eval ((rightNormalizedFamily hC i p).operation n hp) t₀)
      (X.eval ((rightNormalizedFamily hC i p).operation n hp) t₁) := by
  induction p with
  | zero => exact hinitial
  | succ p ih =>
    apply nextNormalizationFamily_joined X hC (rightNormalizedFamily hC i p) n hp t₀ t₁
    · exact ih (by omega)
    · exact fun side => hfaces (i + 1 + p) (by omega) (by omega) side

theorem initialNormalizationAt_eq (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    initialNormalizationAt hC i n hi =
      operationCompositionAt hC i n hi
        (operationInverseAt hC i n hi (C.base (lowerPairLeft i n hi)))
        (pairCompositionAt hC i n hi) (by
          rw [operationInverseAt_boundary hC i n hi true,
            pairCompositionAt_boundary hC i n hi false]
          rfl) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  simp only [initialNormalizationAt_add, operationCompositionAt_add,
    operationInverseAt_add, pairCompositionAt_add, initialNormalization]

theorem initialNormalizationAt_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t₀ t₁ : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (hleft : X.eval (C.base (lowerPairLeft i n hi)) t₀ =
      X.eval (C.base (lowerPairLeft i n hi)) t₁)
    (hcomp : X.underlying.Joined n (X.eval (pairCompositionAt hC i n hi) t₀)
      (X.eval (pairCompositionAt hC i n hi) t₁)) :
    X.underlying.Joined n (X.eval (initialNormalizationAt hC i n hi) t₀)
      (X.eval (initialNormalizationAt hC i n hi) t₁) := by
  simp only [initialNormalizationAt_eq, eval_operationCompositionAt, eval_operationInverseAt]
  apply lowerCompositionCellAt_joined X hC i n hi
  · apply lowerInverseCellAt_joined X hC i n hi
    rw [hleft]
    exact X.joined_refl hC n _
  · exact hcomp

theorem initialRightNormalizationAt_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t₀ t₁ : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (hright : X.eval (C.base (lowerPairRight i n hi)) t₀ =
      X.eval (C.base (lowerPairRight i n hi)) t₁)
    (hcomp : X.underlying.Joined n (X.eval (pairCompositionAt hC i n hi) t₀)
      (X.eval (pairCompositionAt hC i n hi) t₁)) :
    X.underlying.Joined n (X.eval (initialRightNormalizationAt hC i n hi) t₀)
      (X.eval (initialRightNormalizationAt hC i n hi) t₁) := by
  simp only [initialRightNormalizationAt, eval_operationCompositionAt, eval_operationInverseAt]
  apply lowerCompositionCellAt_joined X hC i n hi hcomp
  apply lowerInverseCellAt_joined X hC i n hi
  rw [hright]
  exact X.joined_refl hC n _

theorem eval_pairCompositionAt (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    X.eval (pairCompositionAt hC i n hi) (lowerTupleAt X i n hi a b hab) =
      lowerCompositionCellAt X hC i n hi a b hab := by
  simp only [pairCompositionAt, eval_operationCompositionAt, lowerTupleAt_left, lowerTupleAt_right]

theorem lowerCompositionCellAt_left_reflects_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a b₀ b₁ : X.underlying.Cell n)
    (hb : X.underlying.Parallel n b₀ b₁)
    (hab₀ : lowerFace X i n hi true a = lowerFace X i n hi false b₀)
    (hab₁ : lowerFace X i n hi true a = lowerFace X i n hi false b₁)
    (hcomp : X.underlying.Joined n (lowerCompositionCellAt X hC i n hi a b₀ hab₀)
      (lowerCompositionCellAt X hC i n hi a b₁ hab₁)) : X.underlying.Joined n b₀ b₁ := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  let t₀ := lowerTupleAt X i (i + 1 + d) hi a b₀ hab₀
  let t₁ := lowerTupleAt X i (i + 1 + d) hi a b₁ hab₁
  have hinitial := initialNormalizationAt_joined X hC i (i + 1 + d) hi t₀ t₁
    (by simp only [t₀, t₁, lowerTupleAt_left])
    (by simpa only [t₀, t₁, eval_pairCompositionAt] using hcomp)
  have hnormalized := normalizedFamily_joined X hC i (i + 1 + d) hi t₀ t₁
    (fun m him hmn side => lowerTupleAt_generalFace_congr X i m (i + 1 + d) him hmn side
      (X.joined_refl hC (i + 1 + d) a).parallel hb hab₀ hab₁) hinitial d le_rfl
  have hend : X.underlying.Joined (i + 1 + d)
      (X.eval (normalizedEndpoint hC i (i + 1 + d) hi) t₀)
      (X.eval (normalizedEndpoint hC i (i + 1 + d) hi) t₁) := by
    simpa only [normalizedEndpoint_add] using hnormalized
  have h₀ : X.underlying.Joined (i + 1 + d)
      (X.eval (normalizedEndpoint hC i (i + 1 + d) hi) t₀) b₀ := by
    simpa only [t₀, lowerTupleAt_right] using normalizedEndpoint_joined X hC i _ hi t₀
  have h₁ : X.underlying.Joined (i + 1 + d)
      (X.eval (normalizedEndpoint hC i (i + 1 + d) hi) t₁) b₁ := by
    simpa only [t₁, lowerTupleAt_right] using normalizedEndpoint_joined X hC i _ hi t₁
  exact X.joined_trans hC (X.joined_symm hC h₀) (X.joined_trans hC hend h₁)

theorem lowerCompositionCellAt_right_reflects_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a₀ a₁ b : X.underlying.Cell n)
    (ha : X.underlying.Parallel n a₀ a₁)
    (hab₀ : lowerFace X i n hi true a₀ = lowerFace X i n hi false b)
    (hab₁ : lowerFace X i n hi true a₁ = lowerFace X i n hi false b)
    (hcomp : X.underlying.Joined n (lowerCompositionCellAt X hC i n hi a₀ b hab₀)
      (lowerCompositionCellAt X hC i n hi a₁ b hab₁)) : X.underlying.Joined n a₀ a₁ := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  let t₀ := lowerTupleAt X i (i + 1 + d) hi a₀ b hab₀
  let t₁ := lowerTupleAt X i (i + 1 + d) hi a₁ b hab₁
  have hinitial := initialRightNormalizationAt_joined X hC i (i + 1 + d) hi t₀ t₁
    (by simp only [t₀, t₁, lowerTupleAt_right])
    (by simpa only [t₀, t₁, eval_pairCompositionAt] using hcomp)
  have hnormalized := rightNormalizedFamily_joined X hC i (i + 1 + d) hi t₀ t₁
    (fun m him hmn side => lowerTupleAt_generalFace_congr X i m (i + 1 + d) him hmn side
      ha (X.joined_refl hC (i + 1 + d) b).parallel hab₀ hab₁) hinitial d le_rfl
  have hend : X.underlying.Joined (i + 1 + d)
      (X.eval (rightNormalizedEndpoint hC i (i + 1 + d) hi) t₀)
      (X.eval (rightNormalizedEndpoint hC i (i + 1 + d) hi) t₁) := by
    simpa only [rightNormalizedEndpoint_add] using hnormalized
  have h₀ : X.underlying.Joined (i + 1 + d)
      (X.eval (rightNormalizedEndpoint hC i (i + 1 + d) hi) t₀) a₀ := by
    simpa only [t₀, lowerTupleAt_left] using rightNormalizedEndpoint_joined X hC i _ hi t₀
  have h₁ : X.underlying.Joined (i + 1 + d)
      (X.eval (rightNormalizedEndpoint hC i (i + 1 + d) hi) t₁) a₁ := by
    simpa only [t₁, lowerTupleAt_left] using rightNormalizedEndpoint_joined X hC i _ hi t₁
  exact X.joined_trans hC (X.joined_symm hC h₀) (X.joined_trans hC hend h₁)

#print axioms lowerFace_eq_of_parallel
#print axioms lowerTupleAt_generalFace_congr
#print axioms nextNormalizationFamily_joined
#print axioms normalizedFamily_joined
#print axioms rightNormalizedFamily_joined
#print axioms initialNormalizationAt_eq
#print axioms lowerCompositionCellAt_left_reflects_joined
#print axioms lowerCompositionCellAt_right_reflects_joined

end HomotopyHypothesis.Category.CylinderCorollary
