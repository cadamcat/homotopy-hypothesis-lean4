import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.CylinderCorollary.CellUnitExtensions
import HomotopyHypothesis.Category.CylinderCorollary.Closure
import HomotopyHypothesis.Category.CylinderCorollary.EndComparison
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u v w

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

def endConjugation {G : Type u} [Category G] {x y : G} (a : x ≅ y) :
    (x ⟶ x) ≃ (y ⟶ y) where
  toFun b := a.inv ≫ b ≫ a.hom
  invFun b := a.hom ≫ b ≫ a.inv
  left_inv b := by simp [Category.assoc]
  right_inv b := by simp [Category.assoc]

theorem endMap_bijective_iff_of_iso {G : Type u} {H : Type v}
    [Category G] [Category H] (F : G ⥤ H) {x y : G} (a : x ≅ y) :
    Function.Bijective (fun b : x ⟶ x => F.map b) ↔
      Function.Bijective (fun b : y ⟶ y => F.map b) := by
  have he : (fun b : y ⟶ y => F.map b) ∘ endConjugation a =
      endConjugation (F.mapIso a) ∘ (fun b : x ⟶ x => F.map b) := by
    funext b
    change F.map (a.inv ≫ b ≫ a.hom) = F.map a.inv ≫ F.map b ≫ F.map a.hom
    simp only [F.map_comp]
  calc
    _ ↔ Function.Bijective (endConjugation (F.mapIso a) ∘ (fun b : x ⟶ x => F.map b)) :=
      (Function.Bijective.of_comp_iff' (endConjugation (F.mapIso a)).bijective _).symm
    _ ↔ Function.Bijective ((fun b : y ⟶ y => F.map b) ∘ endConjugation a) := by rw [he]
    _ ↔ _ := Function.Bijective.of_comp_iff _ (endConjugation a).bijective

variable {C : GlobularTheory.{w}}

theorem homotopyMap_bijective_iff_of_joined (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) {x y : X.underlying.Cell 0} (hxy : X.underlying.Joined 0 x y) (n : ℕ) :
    Function.Bijective (homotopyMap f hC x n) ↔ Function.Bijective (homotopyMap f hC y n) := by
  obtain ⟨p, hs, ht⟩ := hxy
  cases n with
  | zero =>
    let p' : CellGroupoid.Edge (⟨x⟩ : CellGroupoid X hC 0) ⟨y⟩ := ⟨p, hs, ht⟩
    exact endMap_bijective_iff_of_iso (CellGroupoid.map f) (asIso (CellGroupoid.ofEdge p'))
  | succ n =>
    let q := unitCellExtension X hC 1 (n + 1) (by omega) p
    have hqs : lowerFace X 0 (n + 1) (by omega) false q = x :=
      (unitCellExtension_lowerFace X hC 0 1 (n + 1) (by omega) (by omega) false p).trans hs
    have hqt : lowerFace X 0 (n + 1) (by omega) true q = y :=
      (unitCellExtension_lowerFace X hC 0 1 (n + 1) (by omega) (by omega) true p).trans ht
    have hleft := endMap_bijective_iff_of_composable f hC 0 (n + 1) (by omega)
      (X.baseCell hC x (n + 1)) q
      ((lowerFace_baseCell X hC x (n + 1) (by omega) true).trans hqs.symm)
    have hright := endMap_bijective_iff_of_composable f hC 0 (n + 1) (by omega)
      q (X.baseCell hC y (n + 1))
      (hqt.trans (lowerFace_baseCell X hC y (n + 1) (by omega) false).symm)
    exact (endMap_bijective_baseCell_iff f hC x (n + 1)).symm.trans
      (hleft.trans (hright.trans (endMap_bijective_baseCell_iff f hC y (n + 1))))

theorem weakEquivalence_of_comp_and_right (hC : C.IsCoherator) {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : WeakEquivalence hC (f ≫ g))
    (hg : WeakEquivalence hC g) : WeakEquivalence hC f := by
  constructor
  · apply (Function.Bijective.of_comp_iff' hg.1 (componentsMap f)).1
    rw [← componentsMap_comp]
    exact hfg.1
  · intro x n
    apply (Function.Bijective.of_comp_iff' (hg.2 ((underlyingMap f).app 0 x) n)
      (homotopyMap f hC x n)).1
    rw [← homotopyMap_comp]
    exact hfg.2 x n

theorem weakEquivalence_of_left_and_comp (hC : C.IsCoherator) {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : WeakEquivalence hC f)
    (hfg : WeakEquivalence hC (f ≫ g)) : WeakEquivalence hC g := by
  constructor
  · apply (Function.Bijective.of_comp_iff (componentsMap g) hf.1).1
    rw [← componentsMap_comp]
    exact hfg.1
  · intro y n
    obtain ⟨x, hx⟩ := hf.1.2 (Quot.mk _ y)
    induction x using Quot.inductionOn with | h x =>
    have hxy : Y.underlying.Joined 0 ((underlyingMap f).app 0 x) y :=
      (Y.components_eq_iff hC _ y).1 hx
    apply (homotopyMap_bijective_iff_of_joined hC g hxy n).1
    apply (Function.Bijective.of_comp_iff (homotopyMap g hC ((underlyingMap f).app 0 x) n)
      (hf.2 x n)).1
    rw [← homotopyMap_comp]
    exact hfg.2 x n

theorem weakEquivalence_middle (hC : C.IsCoherator) {A B D E : C.Model}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (hfg : WeakEquivalence hC (f ≫ g)) (hgh : WeakEquivalence hC (g ≫ h)) :
    WeakEquivalence hC g := by
  have hfg₀ := hfg.1
  have hgh₀ := hgh.1
  rw [componentsMap_comp] at hfg₀ hgh₀
  have hg₀ : Function.Bijective (componentsMap g) := ⟨hgh₀.1.of_comp, hfg₀.2.of_comp⟩
  have hf₀ : Function.Bijective (componentsMap f) :=
    (Function.Bijective.of_comp_iff' hg₀ (componentsMap f)).1 hfg₀
  refine ⟨hg₀, ?_⟩
  intro y n
  have hinj (y : B.underlying.Cell 0) : Function.Injective (homotopyMap g hC y n) := by
    have hh := hgh.2 y n
    rw [homotopyMap_comp] at hh
    exact hh.1.of_comp
  obtain ⟨x, hx⟩ := hf₀.2 (Quot.mk _ y)
  induction x using Quot.inductionOn with | h x =>
  have hxy : B.underlying.Joined 0 ((underlyingMap f).app 0 x) y :=
    (B.components_eq_iff hC _ y).1 hx
  apply (homotopyMap_bijective_iff_of_joined hC g hxy n).1
  refine ⟨hinj _, ?_⟩
  have hh := hfg.2 x n
  rw [homotopyMap_comp] at hh
  exact hh.2.of_comp

theorem weakEquivalence_twoOutOfSix_data (hC : C.IsCoherator) {A B D E : C.Model}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (hfg : WeakEquivalence hC (f ≫ g)) (hgh : WeakEquivalence hC (g ≫ h)) :
    WeakEquivalence hC f ∧ WeakEquivalence hC g ∧ WeakEquivalence hC h ∧
      WeakEquivalence hC (f ≫ g ≫ h) := by
  have hg := weakEquivalence_middle hC f g h hfg hgh
  have hf := weakEquivalence_of_comp_and_right hC f g hfg hg
  have hh := weakEquivalence_of_left_and_comp hC g h hg hgh
  exact ⟨hf, hg, hh, weakEquivalence_comp hC f (g ≫ h) hf hgh⟩

#print axioms homotopyMap_bijective_iff_of_joined
#print axioms weakEquivalence_of_comp_and_right
#print axioms weakEquivalence_of_left_and_comp
#print axioms weakEquivalence_middle
#print axioms weakEquivalence_twoOutOfSix_data

end HomotopyHypothesis.Category.CylinderCorollary

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory
open OAI.Grothendieck
open HomotopyHypothesis.Henry

theorem weakEquivalence_twoOutOfSix_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    TwoOutOfSix C.Model (W hC) := by
  intro A B D E f g h hfg hgh
  exact Category.CylinderCorollary.weakEquivalence_twoOutOfSix_data hC f g h hfg hgh

#print axioms weakEquivalence_twoOutOfSix_proof

end HomotopyHypothesis.Blueprint.Packages
