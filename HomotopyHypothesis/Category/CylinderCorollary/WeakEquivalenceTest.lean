import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.LiftingTest
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u v w

open CategoryTheory
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

theorem bijective_homMap_of_endMap {G : Type u} {H : Type v}
    [Category G] [Category H] (F : G ⥤ H) {x y : G} (a : x ⟶ y) [IsIso a]
    (h : Function.Bijective (fun b : x ⟶ x => F.map b)) :
    Function.Bijective (fun b : x ⟶ y => F.map b) := by
  constructor
  · intro b c hbc
    have e : b ≫ inv a = c ≫ inv a := h.1 (by simp only [F.map_comp, hbc])
    exact (cancel_mono (inv a)).1 e
  · intro q
    obtain ⟨b, hb⟩ := h.2 (q ≫ inv (F.map a))
    refine ⟨b ≫ a, ?_⟩
    change F.map b = q ≫ inv (F.map a) at hb
    change F.map (b ≫ a) = q
    rw [F.map_comp, hb, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable {C : GlobularTheory.{w}}

def EndMapBijective (hC : C.IsCoherator) {X Y : C.Model} (f : X ⟶ Y) : Prop :=
  ∀ (n : ℕ) (x : X.underlying.Cell n),
    Function.Bijective (fun a : (⟨x⟩ : CellGroupoid X hC n) ⟶ ⟨x⟩ =>
      (CellGroupoid.map f).map a)

theorem reflects_joined_of_endMapBijective (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) (h₀ : Function.Injective (componentsMap f))
    (hend : EndMapBijective hC f) {n : ℕ} {a b : X.underlying.Cell n}
    (hp : X.underlying.Parallel n a b)
    (h : Y.underlying.Joined n ((underlyingMap f).app n a)
      ((underlyingMap f).app n b)) : X.underlying.Joined n a b := by
  cases n with
  | zero =>
    apply (X.components_eq_iff hC a b).1
    apply h₀
    exact Quot.sound h
  | succ n =>
    let A : CellGroupoid X hC n := ⟨X.underlying.source n a⟩
    let B : CellGroupoid X hC n := ⟨X.underlying.target n a⟩
    let a' : CellGroupoid.Edge A B := ⟨a, rfl, rfl⟩
    let b' : CellGroupoid.Edge A B := ⟨b, hp.1.symm, hp.2.symm⟩
    apply (CellGroupoid.ofEdge_eq_iff a' b').1
    apply (bijective_homMap_of_endMap (CellGroupoid.map f)
      (CellGroupoid.ofEdge a') (hend n A.cell)).1
    exact Quotient.sound h

theorem exactBoundaryTest_of_endMapBijective (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) (h₀ : Function.Bijective (componentsMap f))
    (hend : EndMapBijective hC f) :
    GlobularSet.ExactBoundaryTest (underlyingMap f) := by
  intro n b y hy
  cases n with
  | zero =>
    obtain ⟨a, ha⟩ := h₀.2 (Quot.mk _ y)
    induction a using Quot.inductionOn with
    | h a =>
      refine ⟨a, rfl, ?_⟩
      exact (Y.components_eq_iff hC _ _).1 ha
  | succ n =>
    have hy' := congrArg Subtype.val hy
    have hys := congrArg Prod.fst hy'
    have hyt := congrArg Prod.snd hy'
    obtain ⟨a, has, hat⟩ := reflects_joined_of_endMapBijective hC f h₀.1 hend
      b.2 (show Y.underlying.Joined n
        ((underlyingMap f).app n b.1.1) ((underlyingMap f).app n b.1.2) from
          ⟨y, hys, hyt⟩)
    let A : CellGroupoid X hC n := ⟨b.1.1⟩
    let B : CellGroupoid X hC n := ⟨b.1.2⟩
    let a' : CellGroupoid.Edge A B := ⟨a, has, hat⟩
    let F := CellGroupoid.map (hC := hC) (n := n) f
    let y' : CellGroupoid.Edge (F.obj A) (F.obj B) := ⟨y, hys, hyt⟩
    obtain ⟨q, hq⟩ := (bijective_homMap_of_endMap F (CellGroupoid.ofEdge a')
      (hend n A.cell)).2 (CellGroupoid.ofEdge y')
    induction q using Quotient.inductionOn with
    | h q =>
      refine ⟨q.1, Subtype.ext (Prod.ext q.2.1 q.2.2), ?_⟩
      exact (CellGroupoid.ofEdge_eq_iff _ y').1 hq

theorem endMapBijective_zero_of_weakEquivalence (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) (hf : WeakEquivalence hC f) (x : X.underlying.Cell 0) :
    Function.Bijective (fun a : (⟨x⟩ : CellGroupoid X hC 0) ⟶ ⟨x⟩ =>
      (CellGroupoid.map f).map a) := hf.2 x 0

theorem lifting_test_of_endMapBijective (hC : C.IsCoherator)
    (hend : ∀ {X Y : C.Model} (f : X ⟶ Y),
      WeakEquivalence hC f → EndMapBijective hC f) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp =
      HomotopyHypothesis.Blueprint.W hC ⊓
        (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp :=
  lifting_test_of_weakEquivalence_test hC fun f hf =>
    exactBoundaryTest_of_endMapBijective hC f hf.1 (hend f hf)

#print axioms exactBoundaryTest_of_endMapBijective
#print axioms lifting_test_of_endMapBijective

end HomotopyHypothesis.Category.CylinderCorollary
