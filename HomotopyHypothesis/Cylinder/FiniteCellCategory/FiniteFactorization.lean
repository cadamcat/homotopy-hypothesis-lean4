import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CylinderCellPushout
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

 def ExtendsFiniteFactorization {A B : C.Model} (i : A ⟶ B) : Prop :=
  ∀ {Z X : C.Model} (c : A ⟶ Z), finiteCellMaps C c → IsFinitelyCellular C Z →
    ∀ (p : Z ⟶ X), W hC p → ∀ (f : B ⟶ X), c ≫ p = i ≫ f →
      ∃ (T : C.Model) (c' : B ⟶ T) (t : Z ⟶ T) (p' : T ⟶ X),
        finiteCellMaps C c' ∧ finiteCellMaps C t ∧ W hC p' ∧
          i ≫ c' = c ≫ t ∧ c' ≫ p' = f ∧ t ≫ p' = p

 theorem extendsFiniteFactorization_id (A : C.Model) :
    ExtendsFiniteFactorization hC (𝟙 A) := by
  intro Z X c hc hZ p hp f h
  exact ⟨Z, c, 𝟙 Z, p, hc, (finiteCellMaps C).id_mem Z, hp,
    by simp, by simpa using h, by simp⟩

 theorem extendsFiniteFactorization_iso {A B : C.Model} (i : A ⟶ B) [IsIso i] :
    ExtendsFiniteFactorization hC i := by
  intro Z X c hc hZ p hp f h
  refine ⟨Z, inv i ≫ c, 𝟙 Z, p,
    (finiteCellMaps C).comp_mem _ _ (finiteCellMaps_isomorphisms C _ inferInstance) hc,
    (finiteCellMaps C).id_mem Z, hp, ?_, ?_, by simp⟩
  · simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

 theorem extendsFiniteFactorization_cell {A B : C.Model} (n : ℕ)
    (a : boundaryDisk C n ⟶ A) (i : A ⟶ B) (x : disk C n ⟶ B)
    (sq : IsPushout a (I C n) i x) : ExtendsFiniteFactorization hC i := by
  intro Z X c hc hZ p hp f h
  have w : (a ≫ c) ≫ p = I C n ≫ (x ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨b, H, hb, hH₀, hH₁⟩ := boundary_test_lift hC p hp
    (finiteCellMaps_le_cofibrations C _ hZ) n (a ≫ c) (x ≫ f) w
  let T := pushout b (J C n)
  let t : Z ⟶ T := pushout.inl b (J C n)
  let d : disk C (n+1) ⟶ T := pushout.inr b (J C n)
  have st : IsPushout b (J C n) t d := .of_hasPushout _ _
  have w' : a ≫ (c ≫ t) = I C n ≫ (targetDisk C n ≫ d) := by
    rw [← Category.assoc, ← hb, Category.assoc, st.w, ← Category.assoc,
      (boundaryRepresentation C n).face_condition, Category.assoc]
  let c' : B ⟶ T := sq.desc (c ≫ t) (targetDisk C n ≫ d) w'
  let p' : T ⟶ X := st.desc p H hH₀.symm
  have hi : i ≫ c' = c ≫ t := sq.inl_desc _ _ _
  have hx : x ≫ c' = targetDisk C n ≫ d := sq.inr_desc _ _ _
  have ht : t ≫ p' = p := st.inl_desc _ _ _
  have hd : d ≫ p' = H := st.inr_desc _ _ _
  have htJ : (sourceMaps C).rlp.llp t :=
    (sourceMaps C).rlp.llp.of_isPushout st
      ((sourceMaps C).le_llp_rlp _ (MorphismProperty.ofHoms.mk n))
  have htW : W hC t := source_llp_weakEquivalence hC t htJ
    (finiteCellMaps_le_cofibrations C _ hZ)
  have hp' : W hC p' := (W hC).of_precomp t p' htW (by rwa [ht])
  refine ⟨T, c', t, p', cell_cylinder_cofibration n a i x sq c hc b hb t d st c' hi hx,
    (finiteCellMaps C).of_isPushout st (finiteCellMaps_J n), hp', hi, ?_, ht⟩
  apply sq.hom_ext
  · calc
      i ≫ (c' ≫ p') = c ≫ (t ≫ p') := by rw [← Category.assoc, hi, Category.assoc]
      _ = c ≫ p := by rw [ht]
      _ = i ≫ f := h
  · calc
      x ≫ (c' ≫ p') = targetDisk C n ≫ (d ≫ p') :=
        by rw [← Category.assoc, hx, Category.assoc]
      _ = targetDisk C n ≫ H := by rw [hd]
      _ = x ≫ f := hH₁

 theorem extendsFiniteFactorization_comp {A B D : C.Model} (i : A ⟶ B) (j : B ⟶ D)
    (hi : ExtendsFiniteFactorization hC i) (hj : ExtendsFiniteFactorization hC j) :
    ExtendsFiniteFactorization hC (i ≫ j) := by
  intro Z X c hc hZ p hp f h
  obtain ⟨T, c₁, t₁, p₁, hc₁, ht₁, hp₁, hi₁, hc₁p, ht₁p⟩ :=
    hi c hc hZ p hp (j ≫ f) (by simpa only [Category.assoc] using h)
  obtain ⟨U, c₂, t₂, p₂, hc₂, ht₂, hp₂, hi₂, hc₂p, ht₂p⟩ :=
    hj c₁ hc₁ (isFinitelyCellular_of_finiteCellMap hZ t₁ ht₁) p₁ hp₁ f hc₁p
  refine ⟨U, c₂, t₁ ≫ t₂, p₂, hc₂, (finiteCellMaps C).comp_mem _ _ ht₁ ht₂,
    hp₂, ?_, hc₂p, ?_⟩
  · rw [Category.assoc, hi₂, ← Category.assoc, hi₁, Category.assoc]
  · rw [Category.assoc, ht₂p, ht₁p]

 theorem finiteCellMaps_extendsFactorization {A B : C.Model} (i : A ⟶ B)
    (hi : finiteCellMaps C i) : ExtendsFiniteFactorization hC i := by
  have base : ∀ {A B : C.Model} (i : A ⟶ B),
      ((boundaryMaps C).pushouts ⊔ MorphismProperty.isomorphisms C.Model) i →
        ExtendsFiniteFactorization hC i := by
    intro A B i hi
    rcases hi with hi | hi
    · rcases hi with ⟨S, D, g, a, x, ⟨n⟩, sq⟩
      exact extendsFiniteFactorization_cell hC n a i x sq
    · let := hi
      exact @extendsFiniteFactorization_iso C hC A B i hi
  induction hi with
  | of i hi => exact base i hi
  | id A => exact extendsFiniteFactorization_id hC A
  | comp_of i j hi hj ih => exact extendsFiniteFactorization_comp hC i j ih (base j hj)

end HomotopyHypothesis.Cylinder.FiniteCellCategory
