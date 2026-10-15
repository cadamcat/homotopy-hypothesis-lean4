import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

variable {C : GlobularTheory.{u}}

 theorem cell_cylinder_cofibration {A B Z T : C.Model} (n : ℕ)
    (a : boundaryDisk C n ⟶ A) (i : A ⟶ B) (x : disk C n ⟶ B)
    (sq : IsPushout a (I C n) i x)
    (c : A ⟶ Z) (hc : finiteCellMaps C c) (b : disk C n ⟶ Z)
    (hb : I C n ≫ b = a ≫ c)
    (t : Z ⟶ T) (d : disk C (n+1) ⟶ T) (st : IsPushout b (J C n) t d)
    (c' : B ⟶ T) (hi : i ≫ c' = c ≫ t) (hx : x ≫ c' = targetDisk C n ≫ d) :
    finiteCellMaps C c' := by
  let P := pushout c i
  let k : Z ⟶ P := pushout.inl c i
  let l : B ⟶ P := pushout.inr c i
  have sp : IsPushout c i k l := .of_hasPushout c i
  have w : I C n ≫ (b ≫ k) = I C n ≫ (x ≫ l) := by
    rw [← Category.assoc, hb, Category.assoc, sp.w, ← Category.assoc,
      sq.w, Category.assoc]
  let bd : boundaryDisk C (n+1) ⟶ P := pushout.desc (b ≫ k) (x ≫ l) w
  let q : P ⟶ T := sp.desc t c' hi.symm
  have hkq : k ≫ q = t := sp.inl_desc _ _ _
  have hlq : l ≫ q = c' := sp.inr_desc _ _ _
  have hbd₀ : pushout.inl (I C n) (I C n) ≫ bd = b ≫ k := pushout.inl_desc _ _ _
  have hbd₁ : pushout.inr (I C n) (I C n) ≫ bd = x ≫ l := pushout.inr_desc _ _ _
  have wq : bd ≫ q = I C (n+1) ≫ d := by
    apply pushout.hom_ext
    · change pushout.inl (I C n) (I C n) ≫ (bd ≫ q) =
        pushout.inl (I C n) (I C n) ≫ (I C (n+1) ≫ d)
      rw [← Category.assoc, hbd₀, Category.assoc, hkq, st.w,
        ← Category.assoc, boundary_inl_I]
    · change pushout.inr (I C n) (I C n) ≫ (bd ≫ q) =
        pushout.inr (I C n) (I C n) ≫ (I C (n+1) ≫ d)
      rw [← Category.assoc, hbd₁, Category.assoc, hlq, hx,
        ← Category.assoc, boundary_inr_I]
  have sb : IsPushout bd (I C (n+1)) q d := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk q d wq)
    apply PushoutCocone.isColimitAux'
    intro s
    have ws : b ≫ (k ≫ s.inl) = J C n ≫ s.inr := by
      have e := congrArg (pushout.inl (I C n) (I C n) ≫ ·) s.condition
      rw [← Category.assoc, hbd₀] at e
      rw [← Category.assoc, boundary_inl_I] at e
      simpa only [Category.assoc] using e
    have ws' : x ≫ (l ≫ s.inl) = targetDisk C n ≫ s.inr := by
      have e := congrArg (pushout.inr (I C n) (I C n) ≫ ·) s.condition
      rw [← Category.assoc, hbd₁] at e
      rw [← Category.assoc, boundary_inr_I] at e
      simpa only [Category.assoc] using e
    let r : T ⟶ s.pt := st.desc (k ≫ s.inl) s.inr ws
    have htr : t ≫ r = k ≫ s.inl := st.inl_desc _ _ _
    have hdr : d ≫ r = s.inr := st.inr_desc _ _ _
    have hcr : c' ≫ r = l ≫ s.inl := by
      apply sq.hom_ext
      · calc
          i ≫ (c' ≫ r) = c ≫ (t ≫ r) := by rw [← Category.assoc, hi, Category.assoc]
          _ = c ≫ (k ≫ s.inl) := by rw [htr]
          _ = i ≫ (l ≫ s.inl) := by rw [← Category.assoc, sp.w, Category.assoc]
      · calc
          x ≫ (c' ≫ r) = targetDisk C n ≫ (d ≫ r) :=
            by rw [← Category.assoc, hx, Category.assoc]
          _ = targetDisk C n ≫ s.inr := by rw [hdr]
          _ = x ≫ (l ≫ s.inl) := ws'.symm
    refine ⟨r, ?_, ?_, ?_⟩
    · change q ≫ r = s.inl
      apply sp.hom_ext
      · rw [← Category.assoc, hkq, htr]
      · rw [← Category.assoc, hlq, hcr]
    · exact hdr
    · change ∀ {m : T ⟶ s.pt}, q ≫ m = s.inl → d ≫ m = s.inr → m = r
      intro m hm₀ hm₁
      apply st.hom_ext
      · calc
          t ≫ m = k ≫ s.inl := by rw [← hkq, Category.assoc, hm₀]
          _ = t ≫ r := htr.symm
      · exact hm₁.trans hdr.symm
  have hq : finiteCellMaps C q :=
    (finiteCellMaps C).of_isPushout sb (finiteCellMaps_I (n+1))
  have hl : finiteCellMaps C l := (finiteCellMaps C).of_isPushout sp.flip hc
  rw [← hlq]
  exact (finiteCellMaps C).comp_mem _ _ hl hq

end HomotopyHypothesis.Cylinder.FiniteCellCategory
