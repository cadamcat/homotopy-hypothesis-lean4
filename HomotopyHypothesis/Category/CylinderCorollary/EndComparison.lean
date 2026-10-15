import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.HomSetDivision
import HomotopyHypothesis.Category.CylinderCorollary.HomSetNaturality
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
import HomotopyHypothesis.Category.CylinderCorollary.WeakEquivalenceTest
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem endMap_bijective_iff_of_composable {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) (a b : X.underlying.Cell n)
    (hab : lowerFace X i n hi true a = lowerFace X i n hi false b) :
    Function.Bijective (fun z : (⟨a⟩ : CellGroupoid X hC n) ⟶ ⟨a⟩ => (CellGroupoid.map f).map z) ↔
      Function.Bijective (fun z : (⟨b⟩ : CellGroupoid X hC n) ⟶ ⟨b⟩ => (CellGroupoid.map f).map z) := by
  let B := prescribedPairBoundaryOfTop X i n hi (fun _ => lowerTupleAt X i n hi a b hab)
    (fun _ _ _ _ => rfl)
  have hleft (side : Bool) :
      pairBoundaryObject X hC i n hi B (C.base (lowerPairLeft i n hi)) side = ⟨a⟩ := by
    apply congrArg CellGroupoid.mk
    change X.eval (C.base (lowerPairLeft i n hi))
      (prescribedPairValue X i n hi (fun _ => lowerTupleAt X i n hi a b hab) n hi le_rfl side) = a
    rw [prescribedPairValue_top, lowerTupleAt_left]
  have hright (side : Bool) :
      pairBoundaryObject X hC i n hi B (C.base (lowerPairRight i n hi)) side = ⟨b⟩ := by
    apply congrArg CellGroupoid.mk
    change X.eval (C.base (lowerPairRight i n hi))
      (prescribedPairValue X i n hi (fun _ => lowerTupleAt X i n hi a b hab) n hi le_rfl side) = b
    rw [prescribedPairValue_top, lowerTupleAt_right]
  let ga : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)) :=
    ⟨X.unitCell hC n a,
      by rw [hleft false]; exact X.unitCell_source hC n a,
      by rw [hleft true]; exact X.unitCell_target hC n a⟩
  let gb : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)) :=
    ⟨X.unitCell hC n b,
      by rw [hright false]; exact X.unitCell_source hC n b,
      by rw [hright true]; exact X.unitCell_target hC n b⟩
  have hleftMap :
      Function.Bijective (pairBoundaryHomMap f hC i n hi B (C.base (lowerPairLeft i n hi))) ↔
        Function.Bijective (fun z : (⟨a⟩ : CellGroupoid X hC n) ⟶ ⟨a⟩ => (CellGroupoid.map f).map z) := by
    rw [pairBoundaryHomMap_bijective_iff]
    dsimp only [PairBoundaryHom]
    rw [hleft false, hleft true]
  have hrightMap :
      Function.Bijective (pairBoundaryHomMap f hC i n hi B (C.base (lowerPairRight i n hi))) ↔
        Function.Bijective (fun z : (⟨b⟩ : CellGroupoid X hC n) ⟶ ⟨b⟩ => (CellGroupoid.map f).map z) := by
    rw [pairBoundaryHomMap_bijective_iff]
    dsimp only [PairBoundaryHom]
    rw [hright false, hright true]
  exact hleftMap.symm.trans ((pairBoundaryHomMap_right_bijective_iff f hC i n hi B gb).trans
    ((pairBoundaryHomMap_left_bijective_iff f hC i n hi B ga).symm.trans hrightMap))

theorem map_baseCellObject {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) :
    (CellGroupoid.map f).obj (⟨X.baseCell hC x n⟩ : CellGroupoid X hC n) =
      (⟨Y.baseCell hC ((underlyingMap f).app 0 x) n⟩ : CellGroupoid Y hC n) :=
  congrArg CellGroupoid.mk (map_baseCell f hC x n)

theorem homotopyMap_eq_endMap_transport {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) (a : X.HomotopyGroup hC x n) :
    homotopyMap f hC x n a =
      cellHomTransport (map_baseCellObject f hC x n) (map_baseCellObject f hC x n)
        ((CellGroupoid.map f).map a) := by
  induction a using Quot.inductionOn with | h a =>
  let A : CellGroupoid X hC n := ⟨X.baseCell hC x n⟩
  let a' : CellGroupoid.Edge ((CellGroupoid.map f).obj A) ((CellGroupoid.map f).obj A) :=
    ⟨(underlyingMap f).app (n + 1) a.1,
      ((underlyingMap f).source_app n a.1).symm.trans (congrArg _ a.2.1),
      ((underlyingMap f).target_app n a.1).symm.trans (congrArg _ a.2.2)⟩
  change CellGroupoid.ofEdge (loopsMap f hC x n a) =
    cellHomTransport _ _ (CellGroupoid.ofEdge a')
  rw [cellHomTransport_ofEdge]
  apply congrArg CellGroupoid.ofEdge
  apply Subtype.ext
  exact (cellEdgeTransport_val _ _ a').symm

theorem endMap_bijective_baseCell_iff {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) :
    Function.Bijective (fun a : (⟨X.baseCell hC x n⟩ : CellGroupoid X hC n) ⟶ ⟨X.baseCell hC x n⟩ =>
      (CellGroupoid.map f).map a) ↔ Function.Bijective (homotopyMap f hC x n) := by
  have he : homotopyMap f hC x n =
      (cellHomTransport (map_baseCellObject f hC x n) (map_baseCellObject f hC x n)) ∘
        (fun a : (⟨X.baseCell hC x n⟩ : CellGroupoid X hC n) ⟶ ⟨X.baseCell hC x n⟩ =>
          (CellGroupoid.map f).map a) := funext (homotopyMap_eq_endMap_transport f hC x n)
  rw [he]
  exact (Function.Bijective.of_comp_iff' (Equiv.bijective _) _).symm

theorem lowerFace_baseCell (X : C.Model) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) (hn : 0 < n) (side : Bool) :
    lowerFace X 0 n hn side (X.baseCell hC x n) = x := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      cases side
      · exact X.unitCell_source hC 0 x
      · exact X.unitCell_target hC 0 x
    | succ n =>
      rw [← lowerFace_face X 0 (n + 1) (n + 1 + 1) (by omega) (by omega) side false]
      change lowerFace X 0 (n + 1) (by omega) side
        (X.underlying.source (n + 1) (X.unitCell hC (n + 1) (X.baseCell hC x (n + 1)))) = x
      rw [X.unitCell_source]
      exact ih (by omega)

theorem endMapBijective_of_weakEquivalence (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) (hf : WeakEquivalence hC f) : EndMapBijective hC f := by
  intro n u
  cases n with
  | zero => exact endMapBijective_zero_of_weakEquivalence hC f hf u
  | succ n =>
    let x := lowerFace X 0 (n + 1) (by omega) false u
    have ha := (endMap_bijective_baseCell_iff f hC x (n + 1)).2 (hf.2 x (n + 1))
    exact (endMap_bijective_iff_of_composable f hC 0 (n + 1) (by omega)
      (X.baseCell hC x (n + 1)) u (lowerFace_baseCell X hC x (n + 1) (by omega) true)).1 ha

#print axioms endMap_bijective_iff_of_composable
#print axioms homotopyMap_eq_endMap_transport
#print axioms endMap_bijective_baseCell_iff
#print axioms lowerFace_baseCell
#print axioms endMapBijective_of_weakEquivalence

end HomotopyHypothesis.Category.CylinderCorollary

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Category.CylinderCorollary

theorem lifting_test_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp =
      W hC ⊓ (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp :=
  lifting_test_of_endMapBijective hC (fun f hf => endMapBijective_of_weakEquivalence hC f hf)

#print axioms lifting_test_proof

end HomotopyHypothesis.Blueprint.Packages
