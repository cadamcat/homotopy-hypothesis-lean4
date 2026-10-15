import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

structure PrescribedPairBoundary (X : C.Model) (i n : ℕ) (hi : i < n) where
  value : ∀ m (him : i < m) (_hmn : m ≤ n) (_side : Bool),
    X.presheaf.obj (op (⟨lowerPairShape i m him⟩ : C.Obj))
  face : ∀ m k (him : i < m) (hmk : m < k) (hkn : k ≤ n) (side outer : Bool),
    X.eval (lowerPairMap C i m k him hmk side)
        (value k (Nat.lt_trans him hmk) hkn outer) =
      value m him (Nat.le_trans (Nat.le_of_lt hmk) hkn) side

def prescribedPairValue (X : C.Model) (i n : ℕ) (hi : i < n)
    (t : Bool → X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (m : ℕ) (him : i < m) (_hmn : m ≤ n) (side : Bool) :
    X.presheaf.obj (op (⟨lowerPairShape i m him⟩ : C.Obj)) := by
  by_cases he : m = n
  · subst m
    exact t side
  · exact X.eval (lowerPairMap C i m n him (by omega) side) (t false)

theorem prescribedPairValue_top (X : C.Model) (i n : ℕ) (hi : i < n)
    (t : Bool → X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj))) (side : Bool) :
    prescribedPairValue X i n hi t n hi le_rfl side = t side := by
  simp only [prescribedPairValue, dite_true]

theorem prescribedPairValue_lower (X : C.Model) (i n : ℕ) (hi : i < n)
    (t : Bool → X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (m : ℕ) (him : i < m) (hmn : m < n) (side : Bool) :
    prescribedPairValue X i n hi t m him (Nat.le_of_lt hmn) side =
      X.eval (lowerPairMap C i m n him hmn side) (t false) := by
  simp only [prescribedPairValue, dite_eq_right (Nat.ne_of_lt hmn)]

def prescribedPairBoundaryOfTop (X : C.Model) (i n : ℕ) (hi : i < n)
    (t : Bool → X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj)))
    (ht : ∀ m (him : i < m) (hmn : m < n) (side : Bool),
      X.eval (lowerPairMap C i m n him hmn side) (t false) =
        X.eval (lowerPairMap C i m n him hmn side) (t true)) :
    PrescribedPairBoundary X i n hi where
  value := prescribedPairValue X i n hi t
  face := by
    intro m k him hmk hkn side outer
    by_cases he : k = n
    · subst k
      rw [prescribedPairValue_top, prescribedPairValue_lower X i n hi t m him hmk side]
      cases outer
      · rfl
      · exact (ht m him hmk side).symm
    · have hkn' : k < n := by omega
      rw [prescribedPairValue_lower X i n hi t k (by omega) hkn' outer,
        prescribedPairValue_lower X i n hi t m him (by omega) side,
        ← eval_comp, lowerPairMap_comp]

def prescribedPairBoundaryOfParallel (X : C.Model) (i n : ℕ) (hi : i < n)
    (a₀ a₁ b₀ b₁ : X.underlying.Cell n)
    (ha : X.underlying.Parallel n a₀ a₁) (hb : X.underlying.Parallel n b₀ b₁)
    (hab₀ : lowerFace X i n hi true a₀ = lowerFace X i n hi false b₀)
    (hab₁ : lowerFace X i n hi true a₁ = lowerFace X i n hi false b₁) :
    PrescribedPairBoundary X i n hi :=
  prescribedPairBoundaryOfTop X i n hi
    (fun side => if side then lowerTupleAt X i n hi a₁ b₁ hab₁
      else lowerTupleAt X i n hi a₀ b₀ hab₀)
    (fun m him hmn side => lowerTupleAt_generalFace_congr X i m n him hmn side ha hb hab₀ hab₁)

theorem prescribedPairBoundaryOfParallel_top (X : C.Model) (i n : ℕ) (hi : i < n)
    (a₀ a₁ b₀ b₁ : X.underlying.Cell n)
    (ha : X.underlying.Parallel n a₀ a₁) (hb : X.underlying.Parallel n b₀ b₁)
    (hab₀ : lowerFace X i n hi true a₀ = lowerFace X i n hi false b₀)
    (hab₁ : lowerFace X i n hi true a₁ = lowerFace X i n hi false b₁) (side : Bool) :
    (prescribedPairBoundaryOfParallel X i n hi a₀ a₁ b₀ b₁ ha hb hab₀ hab₁).value n hi le_rfl side =
      if side then lowerTupleAt X i n hi a₁ b₁ hab₁ else lowerTupleAt X i n hi a₀ b₀ hab₀ := by
  dsimp only [prescribedPairBoundaryOfParallel, prescribedPairBoundaryOfTop]
  exact prescribedPairValue_top X i n hi _ side

def PrescribedPairBoundary.Realizes {X : C.Model} {i n : ℕ} {hi : i < n}
    (B : PrescribedPairBoundary X i n hi)
    (t : X.presheaf.obj (op (⟨lowerPairShape i (n + 1) (by omega)⟩ : C.Obj))) : Prop :=
  ∀ m (him : i < m) (hmn : m ≤ n) (side : Bool),
    X.eval (lowerPairMap C i m (n + 1) him (by omega) side) t = B.value m him hmn side

theorem PrescribedPairBoundary.realizes_of_top {X : C.Model} {i n : ℕ} {hi : i < n}
    (B : PrescribedPairBoundary X i n hi)
    (t : X.presheaf.obj (op (⟨lowerPairShape i (n + 1) (by omega)⟩ : C.Obj)))
    (ht : ∀ side : Bool,
      X.eval (lowerPairMap C i n (n + 1) hi (Nat.lt_succ_self n) side) t =
        B.value n hi le_rfl side) : B.Realizes t := by
  intro m him hmn side
  by_cases he : m = n
  · subst m
    exact ht side
  · have hmn' : m < n := by omega
    calc
      X.eval (lowerPairMap C i m (n + 1) him (by omega) side) t =
          X.eval (lowerPairMap C i m n him hmn' side)
            (X.eval (lowerPairMap C i n (n + 1) hi (Nat.lt_succ_self n) false) t) := by
        rw [← eval_comp, lowerPairMap_comp]
      _ = X.eval (lowerPairMap C i m n him hmn' side) (B.value n hi le_rfl false) := by
        rw [ht false]
      _ = B.value m him hmn side := B.face m n him hmn' le_rfl side false

#print axioms prescribedPairBoundaryOfTop
#print axioms prescribedPairBoundaryOfParallel
#print axioms PrescribedPairBoundary.realizes_of_top

end HomotopyHypothesis.Category.CylinderCorollary
