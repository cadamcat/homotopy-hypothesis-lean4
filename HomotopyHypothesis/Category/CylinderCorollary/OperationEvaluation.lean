import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CellUnitExtensions
import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GenericNormalization
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.LowerInverses
import HomotopyHypothesis.Category.CylinderCorollary.LowerOperations
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem eval_operationTuple {S : Shape} (X : C.Model) (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.eval (operationTuple i d a b hab) t =
      lowerTupleAt X i (i + 1 + d) (by omega) (X.eval a t) (X.eval b t)
        (by dsimp only [lowerFace]; rw [← eval_comp, ← eval_comp, hab]) := by
  apply X.sumTuple_ext (Shape.globe (i + 1 + d)) i (i + 1 + d)
    (by change i < i + 1 + d; omega) (by omega)
  · change X.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) (X.eval _ _) =
      X.eval (C.base (lowerPairLeft i (i + 1 + d) (by omega))) _
    rw [← eval_comp, operationTuple_left, lowerTupleAt_left]
  · change X.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) (X.eval _ _) =
      X.eval (C.base (lowerPairRight i (i + 1 + d) (by omega))) _
    rw [← eval_comp, operationTuple_right, lowerTupleAt_right]

theorem eval_operationCompositionAt {S : Shape} (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a b : C.Hom (Shape.globe n) S)
    (hab : C.comp (C.base (Shape.face hi true)) a = C.comp (C.base (Shape.face hi false)) b)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.eval (operationCompositionAt hC i n hi a b hab) t =
      lowerCompositionCellAt X hC i n hi (X.eval a t) (X.eval b t)
        (by dsimp only [lowerFace]; rw [← eval_comp, ← eval_comp, hab]) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationCompositionAt_add, lowerCompositionCellAt_add]
  dsimp only [operationComposition, lowerCompositionCell]
  rw [eval_comp, eval_operationTuple, lowerTupleAt_add]

theorem eval_operationInverseAt {S : Shape} (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a : C.Hom (Shape.globe n) S)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.eval (operationInverseAt hC i n hi a) t =
      lowerInverseCellAt X hC i n hi (X.eval a t) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationInverseAt_add, lowerInverseCellAt_add]
  exact eval_comp X (lowerInverseOp hC i d) a t

theorem pairCompositionAt_add (hC : C.IsCoherator) (i d : ℕ) :
    pairCompositionAt hC i (i + 1 + d) (by omega) = lowerCompositionOp hC i d := by
  let hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true))
      (C.base (lowerPairLeft i (i + 1 + d) (by omega))) =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false))
        (C.base (lowerPairRight i (i + 1 + d) (by omega))) :=
    (C.base_comp _ _).symm.trans
      ((congrArg C.base (lowerPair_seam i (i + 1 + d) (by omega))).trans (C.base_comp _ _))
  have ht : operationTuple i d (C.base (lowerPairLeft i (i + 1 + d) (by omega)))
      (C.base (lowerPairRight i (i + 1 + d) (by omega))) hab =
      C.id (lowerPairShape i (i + 1 + d) (by omega)) := by
    apply lowerPair_hom_ext C
    · rw [operationTuple_left, C.comp_id]
    · rw [operationTuple_right, C.comp_id]
  dsimp only [pairCompositionAt]
  rw [operationCompositionAt_add]
  dsimp only [operationComposition]
  rw [ht, C.comp_id]

theorem normalizedEndpoint_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj))) :
    X.underlying.Joined n (X.eval (normalizedEndpoint hC i n hi) t)
      (X.eval (C.base (lowerPairRight i n hi)) t) := by
  refine ⟨X.eval (normalizedEndpointHomotopy hC i n hi) t, ?_, ?_⟩
  · change X.eval (C.base (Shape.source n)) (X.eval _ t) = _
    rw [← eval_comp, normalizedEndpointHomotopy_source]
  · change X.eval (C.base (Shape.target n)) (X.eval _ t) = _
    rw [← eval_comp, normalizedEndpointHomotopy_target]

theorem rightNormalizedEndpoint_joined (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n)
    (t : X.presheaf.obj (op (⟨lowerPairShape i n hi⟩ : C.Obj))) :
    X.underlying.Joined n (X.eval (rightNormalizedEndpoint hC i n hi) t)
      (X.eval (C.base (lowerPairLeft i n hi)) t) := by
  refine ⟨X.eval (rightNormalizedEndpointHomotopy hC i n hi) t, ?_, ?_⟩
  · change X.eval (C.base (Shape.source n)) (X.eval _ t) = _
    rw [← eval_comp, rightNormalizedEndpointHomotopy_source]
  · change X.eval (C.base (Shape.target n)) (X.eval _ t) = _
    rw [← eval_comp, rightNormalizedEndpointHomotopy_target]

#print axioms lowerCompositionCellAt_joined
#print axioms lowerInverseCellAt_joined
#print axioms lowerTupleAt_generalFace
#print axioms eval_unitExtension
#print axioms eval_operationCompositionAt
#print axioms eval_operationInverseAt
#print axioms pairCompositionAt_add
#print axioms normalizedEndpoint_joined
#print axioms rightNormalizedEndpoint_joined

end HomotopyHypothesis.Category.CylinderCorollary
