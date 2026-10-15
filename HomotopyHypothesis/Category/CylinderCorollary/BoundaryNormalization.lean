import HomotopyHypothesis.Category.CylinderCorollary.BoundaryNormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.GenericNormalization
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationStep
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}} {i : ℕ} {anchor : Bool}

def iteratedNormalizationFamily (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) :
    (p : ℕ) → NormalizationFamilyAt C i (i + 1 + p) (by omega) anchor
  | 0 => A
  | p + 1 => nextNormalizationFamily hC (iteratedNormalizationFamily hC A p)

theorem iteratedNormalizationFamily_left (hC : C.IsCoherator) (i p : ℕ) :
    iteratedNormalizationFamily hC (initialNormalizationFamily hC i) p =
      normalizedFamily hC i p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [iteratedNormalizationFamily, normalizedFamily, ih]

theorem iteratedNormalizationFamily_right (hC : C.IsCoherator) (i p : ℕ) :
    iteratedNormalizationFamily hC (initialRightNormalizationFamily hC i) p =
      rightNormalizedFamily hC i p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [iteratedNormalizationFamily, rightNormalizedFamily, ih]

def NormalizationCells (X : C.Model) {h : ℕ} {hi : i < h}
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega)) :=
  {z : X.underlying.Cell (n + 1) // NormalizationCellBoundary X A n hn B z}

theorem normalizationCellBoundary_eval (X : C.Model) {h : ℕ} {hi : i < h}
    (A : NormalizationFamilyAt C i h hi anchor) (n : ℕ) (hn : h ≤ n)
    (B : PrescribedPairBoundary X i n (by omega))
    (t : X.presheaf.obj (op (⟨lowerPairShape i (n + 1) (by omega)⟩ : C.Obj)))
    (ht : B.Realizes t) :
    NormalizationCellBoundary X A n hn B (X.eval (A.operation (n + 1) (by omega)) t) := by
  intro side
  dsimp only [lowerFace]
  rw [← eval_comp, A.generalFace n (n + 1) hn (Nat.lt_succ_self n) side, eval_comp,
    ht n (by omega) le_rfl side]

def iterateBoundaryNormalization (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor)
    (n : ℕ) (hn : i + 1 ≤ n) (B : PrescribedPairBoundary X i n (by omega)) :
    (p : ℕ) → (hp : i + 1 + p ≤ n) → NormalizationCells X A n hn B →
      NormalizationCells X (iteratedNormalizationFamily hC A p) n hp B
  | 0, _, z => z
  | p + 1, hp, z =>
    let zp := iterateBoundaryNormalization X hC A n hn B p (by omega) z
    ⟨boundaryNormalizationStepCell X hC (iteratedNormalizationFamily hC A p) n (by omega) B zp.1 zp.2,
      boundaryNormalizationStepCell_next X hC (iteratedNormalizationFamily hC A p) n (by omega)
        B zp.1 zp.2⟩

theorem iterateBoundaryNormalization_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor)
    (n : ℕ) (hn : i + 1 ≤ n) (B : PrescribedPairBoundary X i n (by omega))
    (p : ℕ) (hp : i + 1 + p ≤ n) (z₀ z₁ : NormalizationCells X A n hn B) :
    X.underlying.Joined (n + 1) (iterateBoundaryNormalization X hC A n hn B p hp z₀).1
      (iterateBoundaryNormalization X hC A n hn B p hp z₁).1 ↔
      X.underlying.Joined (n + 1) z₀.1 z₁.1 := by
  induction p with
  | zero => rfl
  | succ p ih =>
    dsimp only [iterateBoundaryNormalization]
    constructor
    · intro hz
      apply (ih (by omega)).1
      exact boundaryNormalizationStepCell_reflects_joined X hC
        (iteratedNormalizationFamily hC A p) n (by omega) B _ _ hz
    · intro hz
      apply boundaryNormalizationStepCell_joined X hC
        (iteratedNormalizationFamily hC A p) n (by omega) B
      exact (ih (by omega)).2 hz

theorem iterateBoundaryNormalization_eval (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor)
    (n : ℕ) (hn : i + 1 ≤ n) (B : PrescribedPairBoundary X i n (by omega))
    (t : X.presheaf.obj (op (⟨lowerPairShape i (n + 1) (by omega)⟩ : C.Obj)))
    (ht : B.Realizes t) (z : NormalizationCells X A n hn B)
    (he : z.1 = X.eval (A.operation (n + 1) (by omega)) t)
    (p : ℕ) (hp : i + 1 + p ≤ n) :
    (iterateBoundaryNormalization X hC A n hn B p hp z).1 =
      X.eval ((iteratedNormalizationFamily hC A p).operation (n + 1) (by omega)) t := by
  induction p with
  | zero => exact he
  | succ p ih =>
    let zp := iterateBoundaryNormalization X hC A n hn B p (by omega) z
    exact boundaryNormalizationStepCell_eval X hC (iteratedNormalizationFamily hC A p) n (by omega)
      B t ht zp.1 zp.2 (ih (by omega))

def boundaryNormalizer (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) (d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (z : NormalizationCells X A (i + 1 + d) (by omega) B) : X.underlying.Cell (i + 1 + d + 1) :=
  let zp := iterateBoundaryNormalization X hC A (i + 1 + d) (by omega) B d le_rfl z
  boundaryNormalizationStepCell X hC (iteratedNormalizationFamily hC A d) (i + 1 + d) le_rfl B zp.1 zp.2

theorem boundaryNormalizer_boundary (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) (d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (z : NormalizationCells X A (i + 1 + d) (by omega) B) (side : Bool) :
    lowerFace X (i + 1 + d) (i + 1 + d + 1) (Nat.lt_succ_self _) side
        (boundaryNormalizer X hC A d B z) =
      X.eval (C.base (lowerPairInclusion i (i + 1 + d) (by omega) anchor))
        (B.value (i + 1 + d) (by omega) le_rfl side) := by
  let zp := iterateBoundaryNormalization X hC A (i + 1 + d) (by omega) B d le_rfl z
  exact boundaryNormalizationStepCell_boundary X hC (iteratedNormalizationFamily hC A d)
    (i + 1 + d) le_rfl B zp.1 zp.2 side

theorem boundaryNormalizer_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) (d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (z₀ z₁ : NormalizationCells X A (i + 1 + d) (by omega) B) :
    X.underlying.Joined (i + 1 + d + 1) (boundaryNormalizer X hC A d B z₀)
      (boundaryNormalizer X hC A d B z₁) ↔
      X.underlying.Joined (i + 1 + d + 1) z₀.1 z₁.1 := by
  dsimp only [boundaryNormalizer]
  constructor
  · intro hz
    apply (iterateBoundaryNormalization_joined_iff X hC A (i + 1 + d) (by omega) B d le_rfl z₀ z₁).1
    exact boundaryNormalizationStepCell_reflects_joined X hC
      (iteratedNormalizationFamily hC A d) (i + 1 + d) le_rfl B _ _ hz
  · intro hz
    apply boundaryNormalizationStepCell_joined X hC
      (iteratedNormalizationFamily hC A d) (i + 1 + d) le_rfl B
    exact (iterateBoundaryNormalization_joined_iff X hC A (i + 1 + d) (by omega) B d le_rfl z₀ z₁).2 hz

theorem boundaryNormalizer_eval (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) (d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (t : X.presheaf.obj (op (⟨lowerPairShape i (i + 1 + d + 1) (by omega)⟩ : C.Obj)))
    (ht : B.Realizes t) (z : NormalizationCells X A (i + 1 + d) (by omega) B)
    (he : z.1 = X.eval (A.operation (i + 1 + d + 1) (by omega)) t) :
    boundaryNormalizer X hC A d B z =
      X.eval ((iteratedNormalizationFamily hC A (d + 1)).operation (i + 1 + d + 1) le_rfl) t := by
  let zp := iterateBoundaryNormalization X hC A (i + 1 + d) (by omega) B d le_rfl z
  exact boundaryNormalizationStepCell_eval X hC (iteratedNormalizationFamily hC A d) (i + 1 + d) le_rfl B t ht zp.1 zp.2
    (iterateBoundaryNormalization_eval X hC A (i + 1 + d) (by omega) B t ht z he d le_rfl)

theorem normalizationFamily_joined_anchor (X : C.Model) (hC : C.IsCoherator)
    {r : ℕ} {hir : i < r} (A : NormalizationFamilyAt C i r hir anchor)
    (t : X.presheaf.obj (op (⟨lowerPairShape i r hir⟩ : C.Obj))) :
    X.underlying.Joined r (X.eval (A.operation r le_rfl) t)
      (X.eval (C.base (lowerPairInclusion i r hir anchor)) t) := by
  let P : C.AdmissiblePair := {
    n := r
    arity := lowerPairShape i r hir
    height := by change max r r ≤ r + 1; omega
    source := A.operation r le_rfl
    target := C.base (lowerPairInclusion i r hir anchor)
    parallel := A.parallel }
  obtain ⟨w, hs, ht⟩ := hC.2 P
  change C.Hom (Shape.globe (r + 1)) (lowerPairShape i r hir) at w
  change C.comp (C.base (Shape.source r)) w = A.operation r le_rfl at hs
  change C.comp (C.base (Shape.target r)) w = C.base (lowerPairInclusion i r hir anchor) at ht
  refine ⟨X.eval w t, ?_, ?_⟩
  · change X.eval (C.base (Shape.source r)) (X.eval w t) = _
    rw [← eval_comp, hs]
  · change X.eval (C.base (Shape.target r)) (X.eval w t) = _
    rw [← eval_comp, ht]

theorem boundaryNormalizer_joined_anchor (X : C.Model) (hC : C.IsCoherator)
    (A : NormalizationFamilyAt C i (i + 1) (Nat.lt_succ_self i) anchor) (d : ℕ)
    (B : PrescribedPairBoundary X i (i + 1 + d) (by omega))
    (t : X.presheaf.obj (op (⟨lowerPairShape i (i + 1 + d + 1) (by omega)⟩ : C.Obj)))
    (ht : B.Realizes t) (z : NormalizationCells X A (i + 1 + d) (by omega) B)
    (he : z.1 = X.eval (A.operation (i + 1 + d + 1) (by omega)) t) :
    X.underlying.Joined (i + 1 + d + 1) (boundaryNormalizer X hC A d B z)
      (X.eval (C.base (lowerPairInclusion i (i + 1 + d + 1) (by omega) anchor)) t) := by
  rw [boundaryNormalizer_eval X hC A d B t ht z he]
  exact normalizationFamily_joined_anchor X hC (iteratedNormalizationFamily hC A (d + 1)) t

#print axioms normalizationCellBoundary_eval
#print axioms iterateBoundaryNormalization_joined_iff
#print axioms iterateBoundaryNormalization_eval
#print axioms boundaryNormalizer_boundary
#print axioms boundaryNormalizer_joined_iff
#print axioms boundaryNormalizer_eval
#print axioms normalizationFamily_joined_anchor
#print axioms boundaryNormalizer_joined_anchor

end HomotopyHypothesis.Category.CylinderCorollary
