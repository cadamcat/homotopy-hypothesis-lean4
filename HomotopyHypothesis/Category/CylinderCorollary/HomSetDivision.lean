import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.CompositionReflection
import HomotopyHypothesis.Category.CylinderCorollary.DivisionBoundary
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.LeftDivision
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
import HomotopyHypothesis.Category.CylinderCorollary.PrescribedPairBoundary
import HomotopyHypothesis.Category.CylinderCorollary.RightDivision
import HomotopyHypothesis.Category.CylinderCorollary.RightNormalization
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def pairBoundaryObject (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (side : Bool) : CellGroupoid X hC n := ⟨X.eval q (B.value n hi le_rfl side)⟩

abbrev PairBoundaryEdge (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi)) :=
  CellGroupoid.Edge (pairBoundaryObject X hC i n hi B q false) (pairBoundaryObject X hC i n hi B q true)

abbrev PairBoundaryHom (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi)) :=
  pairBoundaryObject X hC i n hi B q false ⟶ pairBoundaryObject X hC i n hi B q true

theorem pairBoundaryEdge_boundary (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (a : PairBoundaryEdge X hC i n hi B q) : PairCellBoundary X i n hi B q a.1 := by
  intro side
  cases side
  · exact a.2.1
  · exact a.2.2

def pairBoundaryEdgeOfCell (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi) (q : C.Hom (Shape.globe n) (lowerPairShape i n hi))
    (a : X.underlying.Cell (n + 1)) (ha : PairCellBoundary X i n hi B q a) :
    PairBoundaryEdge X hC i n hi B q := ⟨a, ha false, ha true⟩

def leftMultiplicationEdge (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    PairBoundaryEdge X hC i n hi B (pairCompositionAt hC i n hi) := by
  let hg := pairBoundaryEdge_boundary X hC i n hi B _ g
  let ha := pairBoundaryEdge_boundary X hC i n hi B _ a
  let hga := prescribedPairBoundary_cell_seam X i n hi B g.1 a.1 hg ha
  exact pairBoundaryEdgeOfCell X hC i n hi B _
    (lowerCompositionCellAt X hC i (n + 1) (by omega) g.1 a.1 hga)
    (prescribedPairBoundary_composition X hC i n hi B g.1 a.1 hg ha hga)

def rightMultiplicationEdge (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    PairBoundaryEdge X hC i n hi B (pairCompositionAt hC i n hi) := by
  let hg := pairBoundaryEdge_boundary X hC i n hi B _ g
  let ha := pairBoundaryEdge_boundary X hC i n hi B _ a
  let hag := prescribedPairBoundary_cell_seam X i n hi B a.1 g.1 ha hg
  exact pairBoundaryEdgeOfCell X hC i n hi B _
    (lowerCompositionCellAt X hC i (n + 1) (by omega) a.1 g.1 hag)
    (prescribedPairBoundary_composition X hC i n hi B a.1 g.1 ha hg hag)

theorem leftMultiplicationEdge_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)))
    (a₀ a₁ : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    X.underlying.Joined (n + 1) (leftMultiplicationEdge X hC i n hi B g a₀).1
      (leftMultiplicationEdge X hC i n hi B g a₁).1 ↔ X.underlying.Joined (n + 1) a₀.1 a₁.1 := by
  let hg := pairBoundaryEdge_boundary X hC i n hi B _ g
  let ha₀ := pairBoundaryEdge_boundary X hC i n hi B _ a₀
  let ha₁ := pairBoundaryEdge_boundary X hC i n hi B _ a₁
  let hga₀ := prescribedPairBoundary_cell_seam X i n hi B g.1 a₀.1 hg ha₀
  let hga₁ := prescribedPairBoundary_cell_seam X i n hi B g.1 a₁.1 hg ha₁
  dsimp only [leftMultiplicationEdge, pairBoundaryEdgeOfCell]
  constructor
  · intro h
    exact lowerCompositionCellAt_left_reflects_joined X hC i (n + 1) (by omega) g.1 a₀.1 a₁.1
      (pairCellBoundary_parallel X i n hi B _ ha₀ ha₁) hga₀ hga₁ h
  · intro h
    exact lowerCompositionCellAt_joined X hC i (n + 1) (by omega)
      (X.joined_refl hC _ g.1) h hga₀ hga₁

theorem rightMultiplicationEdge_joined_iff (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)))
    (a₀ a₁ : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    X.underlying.Joined (n + 1) (rightMultiplicationEdge X hC i n hi B g a₀).1
      (rightMultiplicationEdge X hC i n hi B g a₁).1 ↔ X.underlying.Joined (n + 1) a₀.1 a₁.1 := by
  let hg := pairBoundaryEdge_boundary X hC i n hi B _ g
  let ha₀ := pairBoundaryEdge_boundary X hC i n hi B _ a₀
  let ha₁ := pairBoundaryEdge_boundary X hC i n hi B _ a₁
  let hag₀ := prescribedPairBoundary_cell_seam X i n hi B a₀.1 g.1 ha₀ hg
  let hag₁ := prescribedPairBoundary_cell_seam X i n hi B a₁.1 g.1 ha₁ hg
  dsimp only [rightMultiplicationEdge, pairBoundaryEdgeOfCell]
  constructor
  · intro h
    exact lowerCompositionCellAt_right_reflects_joined X hC i (n + 1) (by omega) a₀.1 a₁.1 g.1
      (pairCellBoundary_parallel X i n hi B _ ha₀ ha₁) hag₀ hag₁ h
  · intro h
    exact lowerCompositionCellAt_joined X hC i (n + 1) (by omega)
      h (X.joined_refl hC _ g.1) hag₀ hag₁

def leftMultiplicationHom (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    PairBoundaryHom X hC i n hi B (C.base (lowerPairRight i n hi)) →
      PairBoundaryHom X hC i n hi B (pairCompositionAt hC i n hi) :=
  Quotient.map (leftMultiplicationEdge X hC i n hi B g)
    (fun a b h => (leftMultiplicationEdge_joined_iff X hC i n hi B g a b).2 h)

def rightMultiplicationHom (X : C.Model) (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    PairBoundaryHom X hC i n hi B (C.base (lowerPairLeft i n hi)) →
      PairBoundaryHom X hC i n hi B (pairCompositionAt hC i n hi) :=
  Quotient.map (rightMultiplicationEdge X hC i n hi B g)
    (fun a b h => (rightMultiplicationEdge_joined_iff X hC i n hi B g a b).2 h)

theorem leftMultiplicationHom_ofEdge (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    leftMultiplicationHom X hC i n hi B g (CellGroupoid.ofEdge a) =
      CellGroupoid.ofEdge (leftMultiplicationEdge X hC i n hi B g a) := rfl

theorem rightMultiplicationHom_ofEdge (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi)))
    (a : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    rightMultiplicationHom X hC i n hi B g (CellGroupoid.ofEdge a) =
      CellGroupoid.ofEdge (rightMultiplicationEdge X hC i n hi B g a) := rfl

theorem leftMultiplicationHom_bijective (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairLeft i n hi))) :
    Function.Bijective (leftMultiplicationHom X hC i n hi B g) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  constructor
  · intro a₀ a₁ h
    induction a₀ using Quotient.inductionOn with | h a₀ =>
    induction a₁ using Quotient.inductionOn with | h a₁ =>
    apply Quotient.sound
    change CellGroupoid.ofEdge (leftMultiplicationEdge X hC i (i + 1 + d) hi B g a₀) =
      CellGroupoid.ofEdge (leftMultiplicationEdge X hC i (i + 1 + d) hi B g a₁) at h
    exact (leftMultiplicationEdge_joined_iff X hC i (i + 1 + d) hi B g a₀ a₁).1
      ((CellGroupoid.ofEdge_eq_iff _ _).1 h)
  · intro b
    induction b using Quotient.inductionOn with | h b =>
    obtain ⟨a, ha, hga, hj⟩ := leftDivision_exists X hC i d B g.1
      (pairBoundaryEdge_boundary X hC i (i + 1 + d) hi B _ g) b.1
      (pairBoundaryEdge_boundary X hC i (i + 1 + d) hi B _ b)
    let a' := pairBoundaryEdgeOfCell X hC i (i + 1 + d) hi B
      (C.base (lowerPairRight i (i + 1 + d) hi)) a ha
    refine ⟨CellGroupoid.ofEdge a', ?_⟩
    rw [leftMultiplicationHom_ofEdge]
    apply (CellGroupoid.ofEdge_eq_iff _ b).2
    simpa only [leftMultiplicationEdge, pairBoundaryEdgeOfCell, a'] using hj

theorem rightMultiplicationHom_bijective (X : C.Model) (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (B : PrescribedPairBoundary X i n hi)
    (g : PairBoundaryEdge X hC i n hi B (C.base (lowerPairRight i n hi))) :
    Function.Bijective (rightMultiplicationHom X hC i n hi B g) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  constructor
  · intro a₀ a₁ h
    induction a₀ using Quotient.inductionOn with | h a₀ =>
    induction a₁ using Quotient.inductionOn with | h a₁ =>
    apply Quotient.sound
    change CellGroupoid.ofEdge (rightMultiplicationEdge X hC i (i + 1 + d) hi B g a₀) =
      CellGroupoid.ofEdge (rightMultiplicationEdge X hC i (i + 1 + d) hi B g a₁) at h
    exact (rightMultiplicationEdge_joined_iff X hC i (i + 1 + d) hi B g a₀ a₁).1
      ((CellGroupoid.ofEdge_eq_iff _ _).1 h)
  · intro b
    induction b using Quotient.inductionOn with | h b =>
    obtain ⟨a, ha, hag, hj⟩ := rightDivision_exists X hC i d B g.1
      (pairBoundaryEdge_boundary X hC i (i + 1 + d) hi B _ g) b.1
      (pairBoundaryEdge_boundary X hC i (i + 1 + d) hi B _ b)
    let a' := pairBoundaryEdgeOfCell X hC i (i + 1 + d) hi B
      (C.base (lowerPairLeft i (i + 1 + d) hi)) a ha
    refine ⟨CellGroupoid.ofEdge a', ?_⟩
    rw [rightMultiplicationHom_ofEdge]
    apply (CellGroupoid.ofEdge_eq_iff _ b).2
    simpa only [rightMultiplicationEdge, pairBoundaryEdgeOfCell, a'] using hj

#print axioms leftMultiplicationEdge_joined_iff
#print axioms rightMultiplicationEdge_joined_iff
#print axioms leftMultiplicationHom_bijective
#print axioms rightMultiplicationHom_bijective

end HomotopyHypothesis.Category.CylinderCorollary
