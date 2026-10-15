import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.HomSetDivision
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def PrescribedPairBoundary.map {X Y : C.Model} (f : X ⟶ Y) {i n : ℕ} {hi : i < n}
    (B : PrescribedPairBoundary X i n hi) : PrescribedPairBoundary Y i n hi where
  value m him hmn side := f.app (op (⟨lowerPairShape i m him⟩ : C.Obj)) (B.value m him hmn side)
  face := by
    intro m k him hmk hkn side outer
    rw [← map_eval, B.face]

theorem map_pairBoundaryObject {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi)) (side : Bool) :
    (CellGroupoid.map f).obj (pairBoundaryObject X hC i n hi B q side) =
      pairBoundaryObject Y hC i n hi (B.map f) q side := by
  exact congrArg CellGroupoid.mk (map_eval f q (B.value n hi le_rfl side))

def pairBoundaryEdgeMap {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (a : PairBoundaryEdge X hC i n hi B q) : PairBoundaryEdge Y hC i n hi (B.map f) q :=
  ⟨(underlyingMap f).app (n + 1) a.1,
    ((underlyingMap f).source_app n a.1).symm.trans
      ((congrArg ((underlyingMap f).app n) a.2.1).trans (map_eval f q _)),
    ((underlyingMap f).target_app n a.1).symm.trans
      ((congrArg ((underlyingMap f).app n) a.2.2).trans (map_eval f q _))⟩

def pairBoundaryHomMap {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi)) :
    PairBoundaryHom X hC i n hi B q → PairBoundaryHom Y hC i n hi (B.map f) q :=
  Quotient.map (pairBoundaryEdgeMap f hC i n hi B q)
    (fun _ _ h => (underlyingMap f).map_joined h)

theorem pairBoundaryHomMap_ofEdge {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (a : PairBoundaryEdge X hC i n hi B q) :
    pairBoundaryHomMap f hC i n hi B q (CellGroupoid.ofEdge a) =
      CellGroupoid.ofEdge (pairBoundaryEdgeMap f hC i n hi B q a) := rfl

theorem map_leftMultiplicationEdge {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    pairBoundaryEdgeMap f hC i n hi B (pairCompositionAt hC i n hi)
        (leftMultiplicationEdge X hC i n hi B g a) =
      leftMultiplicationEdge Y hC i n hi (B.map f)
        (pairBoundaryEdgeMap f hC i n hi B _ g) (pairBoundaryEdgeMap f hC i n hi B _ a) := by
  apply Subtype.ext
  exact map_lowerCompositionCellAt f hC i (n + 1) (by omega) g.1 a.1 _

theorem map_rightMultiplicationEdge {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    pairBoundaryEdgeMap f hC i n hi B (pairCompositionAt hC i n hi)
        (rightMultiplicationEdge X hC i n hi B g a) =
      rightMultiplicationEdge Y hC i n hi (B.map f)
        (pairBoundaryEdgeMap f hC i n hi B _ g) (pairBoundaryEdgeMap f hC i n hi B _ a) := by
  apply Subtype.ext
  exact map_lowerCompositionCellAt f hC i (n + 1) (by omega) a.1 g.1 _

theorem map_leftMultiplicationHom {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)))
    (a : PairBoundaryHom X hC i n hi B (C.base (lowerPairRight i n hi))) :
    pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi)
        (leftMultiplicationHom X hC i n hi B g a) =
      leftMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g)
        (pairBoundaryHomMap f hC i n hi B _ a) := by
  induction a using Quotient.inductionOn with | h a =>
  change CellGroupoid.ofEdge (pairBoundaryEdgeMap f hC i n hi B _
    (leftMultiplicationEdge X hC i n hi B g a)) =
      CellGroupoid.ofEdge (leftMultiplicationEdge Y hC i n hi (B.map f)
        (pairBoundaryEdgeMap f hC i n hi B _ g) (pairBoundaryEdgeMap f hC i n hi B _ a))
  exact congrArg CellGroupoid.ofEdge (map_leftMultiplicationEdge f hC i n hi B g a)

theorem map_rightMultiplicationHom {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)))
    (a : PairBoundaryHom X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi)
        (rightMultiplicationHom X hC i n hi B g a) =
      rightMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g)
        (pairBoundaryHomMap f hC i n hi B _ a) := by
  induction a using Quotient.inductionOn with | h a =>
  change CellGroupoid.ofEdge (pairBoundaryEdgeMap f hC i n hi B _
    (rightMultiplicationEdge X hC i n hi B g a)) =
      CellGroupoid.ofEdge (rightMultiplicationEdge Y hC i n hi (B.map f)
        (pairBoundaryEdgeMap f hC i n hi B _ g) (pairBoundaryEdgeMap f hC i n hi B _ a))
  exact congrArg CellGroupoid.ofEdge (map_rightMultiplicationEdge f hC i n hi B g a)

def cellEdgeTransport {X : C.Model} {hC : C.IsCoherator} {n : ℕ}
    {x y x' y' : CellGroupoid X hC n} (hx : x = x') (hy : y = y') :
    CellGroupoid.Edge x y ≃ CellGroupoid.Edge x' y' := by
  cases hx
  cases hy
  exact Equiv.refl _

theorem cellEdgeTransport_val {X : C.Model} {hC : C.IsCoherator} {n : ℕ}
    {x y x' y' : CellGroupoid X hC n} (hx : x = x') (hy : y = y')
    (a : CellGroupoid.Edge x y) : (cellEdgeTransport hx hy a).1 = a.1 := by
  cases hx
  cases hy
  rfl

def cellHomTransport {X : C.Model} {hC : C.IsCoherator} {n : ℕ}
    {x y x' y' : CellGroupoid X hC n} (hx : x = x') (hy : y = y') :
    (x ⟶ y) ≃ (x' ⟶ y') := by
  cases hx
  cases hy
  exact Equiv.refl _

theorem cellHomTransport_ofEdge {X : C.Model} {hC : C.IsCoherator} {n : ℕ}
    {x y x' y' : CellGroupoid X hC n} (hx : x = x') (hy : y = y')
    (a : CellGroupoid.Edge x y) :
    cellHomTransport hx hy (CellGroupoid.ofEdge a) =
      CellGroupoid.ofEdge (cellEdgeTransport hx hy a) := by
  cases hx
  cases hy
  rfl

theorem pairBoundaryHomMap_eq_transport {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (a : PairBoundaryHom X hC i n hi B q) :
    pairBoundaryHomMap f hC i n hi B q a =
      cellHomTransport (map_pairBoundaryObject f hC i n hi B q false)
        (map_pairBoundaryObject f hC i n hi B q true) ((CellGroupoid.map f).map a) := by
  induction a using Quotient.inductionOn with | h a =>
  let a' : CellGroupoid.Edge
      ((CellGroupoid.map f).obj (pairBoundaryObject X hC i n hi B q false))
      ((CellGroupoid.map f).obj (pairBoundaryObject X hC i n hi B q true)) :=
    ⟨(underlyingMap f).app (n + 1) a.1,
      ((underlyingMap f).source_app n a.1).symm.trans (congrArg _ a.2.1),
      ((underlyingMap f).target_app n a.1).symm.trans (congrArg _ a.2.2)⟩
  change CellGroupoid.ofEdge (pairBoundaryEdgeMap f hC i n hi B q a) =
    cellHomTransport _ _ (CellGroupoid.ofEdge a')
  rw [cellHomTransport_ofEdge]
  apply congrArg CellGroupoid.ofEdge
  apply Subtype.ext
  exact (cellEdgeTransport_val _ _ a').symm

theorem pairBoundaryHomMap_bijective_iff {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (q : C.Hom (Shape.globe n) (lowerPairShape i n hi)) :
    Function.Bijective (pairBoundaryHomMap f hC i n hi B q) ↔
      Function.Bijective (fun a : PairBoundaryHom X hC i n hi B q => (CellGroupoid.map f).map a) := by
  have he : pairBoundaryHomMap f hC i n hi B q =
      (cellHomTransport (map_pairBoundaryObject f hC i n hi B q false)
        (map_pairBoundaryObject f hC i n hi B q true)) ∘
          (fun a : PairBoundaryHom X hC i n hi B q => (CellGroupoid.map f).map a) :=
    funext (pairBoundaryHomMap_eq_transport f hC i n hi B q)
  rw [he]
  exact Function.Bijective.of_comp_iff' (Equiv.bijective _) _

theorem pairBoundaryHomMap_left_bijective_iff {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    Function.Bijective (pairBoundaryHomMap f hC i n hi B (C.base (lowerPairRight i n hi))) ↔
      Function.Bijective (pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi)) := by
  have he : pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi) ∘
      leftMultiplicationHom X hC i n hi B g =
        leftMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g) ∘
          pairBoundaryHomMap f hC i n hi B (C.base (lowerPairRight i n hi)) :=
    funext (map_leftMultiplicationHom f hC i n hi B g)
  calc
    _ ↔ Function.Bijective
        (leftMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g) ∘
          pairBoundaryHomMap f hC i n hi B (C.base (lowerPairRight i n hi))) :=
      (Function.Bijective.of_comp_iff'
        (leftMultiplicationHom_bijective Y hC i n hi (B.map f) _) _).symm
    _ ↔ Function.Bijective
        (pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi) ∘
          leftMultiplicationHom X hC i n hi B g) := by rw [he]
    _ ↔ _ := Function.Bijective.of_comp_iff _ (leftMultiplicationHom_bijective X hC i n hi B g)

theorem pairBoundaryHomMap_right_bijective_iff {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    Function.Bijective (pairBoundaryHomMap f hC i n hi B (C.base (lowerPairLeft i n hi))) ↔
      Function.Bijective (pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi)) := by
  have he : pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi) ∘
      rightMultiplicationHom X hC i n hi B g =
        rightMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g) ∘
          pairBoundaryHomMap f hC i n hi B (C.base (lowerPairLeft i n hi)) :=
    funext (map_rightMultiplicationHom f hC i n hi B g)
  calc
    _ ↔ Function.Bijective
        (rightMultiplicationHom Y hC i n hi (B.map f) (pairBoundaryEdgeMap f hC i n hi B _ g) ∘
          pairBoundaryHomMap f hC i n hi B (C.base (lowerPairLeft i n hi))) :=
      (Function.Bijective.of_comp_iff'
        (rightMultiplicationHom_bijective Y hC i n hi (B.map f) _) _).symm
    _ ↔ Function.Bijective
        (pairBoundaryHomMap f hC i n hi B (pairCompositionAt hC i n hi) ∘
          rightMultiplicationHom X hC i n hi B g) := by rw [he]
    _ ↔ _ := Function.Bijective.of_comp_iff _ (rightMultiplicationHom_bijective X hC i n hi B g)

#print axioms PrescribedPairBoundary.map
#print axioms map_pairBoundaryObject
#print axioms map_leftMultiplicationHom
#print axioms map_rightMultiplicationHom
#print axioms pairBoundaryHomMap_eq_transport
#print axioms pairBoundaryHomMap_bijective_iff
#print axioms pairBoundaryHomMap_left_bijective_iff
#print axioms pairBoundaryHomMap_right_bijective_iff

end HomotopyHypothesis.Category.CylinderCorollary
