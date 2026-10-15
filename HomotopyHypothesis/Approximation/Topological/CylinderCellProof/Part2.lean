import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSubMap
import HomotopyHypothesis.Approximation.Topological.CylinderCells.DcylDBoundaryHomExt
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ExistsDcylDBoundaryDesc
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.AnodyneDcylDBoundaryIota
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryIota
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `HomotopyHypothesis.Approximation.Topological.CylinderCellProof`, part 2

Lines 236–373 of `HomotopyHypothesis.Approximation.Topological.CylinderCellProof`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

section Cell

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

section Pushout

variable {A A' : Subfunctor W} (h : A ≤ A') {n : ℕ}
  (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
  (hyA : y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n)))
  (hyA' : y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)))
  (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
    k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))
  (hA' : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
    z ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) →
      z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨ ∃ hk : k = n, hk ▸ z = y)

include hyA in
include hyA in
include hyA hfaces hA' in

theorem isPushout_cell :
    ∃ κ, IsPushout κ (dcylDBoundaryι (elNF φ (elOf y)).v) (cylSubMap φ h)
      (colimit.ι (cylSub φ A').DC (op (yEl y hyA')) ≫ (cylSub φ A').incl) := by
  obtain ⟨κ, hκf, hκb⟩ := exists_dcylDBoundary_desc φ A y hfaces
  have hl : ∀ {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T) (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T),
      κ ≫ l = dcylDBoundaryι _ ≫ r →
      ∀ (e : A.toFunctor.Elements) (f : elOf y ⟶ W.elementsMk e.obj e.val.1)
        (_ : elDim (W.elementsMk e.obj e.val.1) ≠ n),
        (dcylDElMap φ f).toSemiSSet ≫ r =
          colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl ≫ l := by
    intro T l r hlr e f hk
    rw [← faceBdryGen_ι φ y f hk, Category.assoc, ← hlr, ← Category.assoc, hκf e f hk]
    exact Category.assoc _ _ _
  have hw : ∀ {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T) (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T)
      (hlr : κ ≫ l = dcylDBoundaryι _ ≫ r),
      colimit.desc (cylSub φ A').B (Cocone.mk X (cylSub φ A').xN) ≫ ((cylSub φ A).base ≫ l) =
        colimMap (cylSub φ A').botN ≫ colimit.desc (cylSub φ A').DC
          (Cocone.mk _ (cellNat φ y hyA hyA' hA' l r (hl l r hlr))) := by
    intro T l r hlr
    apply colimit.hom_ext
    intro e
    rw [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
    change (cylSub φ A').xN.app e ≫ (cylSub φ A).base ≫ l =
      (cylSub φ A').botN.app e ≫ cellApp φ y hyA' hA' l r e
    by_cases he : e.unop.val.1 ∈ A.obj e.unop.obj
    · rw [cellApp_pos φ y hyA' hA' l r e he]
      have h₀ := CylDatum.botN_ι_incl (cylSub φ A) (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩))
      have h₁ := congrArg (· ≫ l) h₀
      simp only [Category.assoc] at h₁
      exact h₁.symm
    · have he' : e = op (yEl y hyA') := congrArg op (elem_eq_of_not_mem y hyA' hA' e.unop he)
      subst he'
      rw [cellApp_y φ y hyA hyA' hA' l r]
      have h₀ : botBdry (elNF φ (elOf y)).v ≫ κ ≫ l =
          botBdry (elNF φ (elOf y)).v ≫ dcylDBoundaryι _ ≫ r := by rw [hlr]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ l) hκb.symm)).trans
        ((Category.assoc _ _ _).trans (h₀.trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ r) (botBdry_ι _)))))
  refine ⟨κ, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s => pushout.desc ((cylSub φ A).base ≫ s.inl)
      (colimit.desc (cylSub φ A').DC (Cocone.mk _ (cellNat φ y hyA hyA' hA' s.inl s.inr
        (hl s.inl s.inr s.condition)))) (hw s.inl s.inr s.condition)) ?_ ?_ ?_)⟩
  · -- the square commutes
    apply dcylDBoundary_hom_ext φ y
    · intro k θ hk
      have hz : W.map θ.op y ∈ A.obj _ := hfaces k θ hk
      have h₁ := hκf (A.toFunctor.elementsMk _ ⟨W.map θ.op y, hz⟩) (elFaceHom y θ) hk
      have h₂ := colimit.w (cylSub φ A').DC (faceElHom y hyA' θ (h _ hz)).op
      have e₁ : (faceBdry φ y θ hk).toSemiSSet ≫ κ ≫ cylSubMap φ h =
          colimit.ι (cylSub φ A').DC ((elMap (Subfunctor.homOfLe h)).obj
            (op (A.toFunctor.elementsMk _ ⟨W.map θ.op y, hz⟩))) ≫ (cylSub φ A').incl :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cylSubMap φ h) h₁).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (incl_cylSubMap φ h)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ (cylSub φ A').incl) (colimit.ι_pre (cylSub φ A').DC
                (elMap (Subfunctor.homOfLe h))
                (op (A.toFunctor.elementsMk _ ⟨W.map θ.op y, hz⟩))))))))
      have e₂ : (faceBdry φ y θ hk).toSemiSSet ≫ dcylDBoundaryι _ ≫
            colimit.ι (cylSub φ A').DC (op (yEl y hyA')) ≫ (cylSub φ A').incl =
          (dcylDElMap φ (elFaceHom y θ)).toSemiSSet ≫
            colimit.ι (cylSub φ A').DC (op (yEl y hyA')) ≫ (cylSub φ A').incl :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (faceBdryGen_ι φ y _ hk))
      have e₃ : (cylSub φ A').DC.map (faceElHom y hyA' θ (h _ hz)).op ≫
            colimit.ι (cylSub φ A').DC (op (yEl y hyA')) ≫ (cylSub φ A').incl =
          colimit.ι (cylSub φ A').DC (op (A'.toFunctor.elementsMk _ ⟨W.map θ.op y, h _ hz⟩)) ≫
            (cylSub φ A').incl :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (cylSub φ A').incl) h₂)
      exact e₁.trans (e₃.symm.trans e₂.symm)
    · rw [← Category.assoc, hκb, Category.assoc, base_cylSubMap, ← Category.assoc, botBdry_ι]
      have h₀ := CylDatum.botN_ι_incl (cylSub φ A') (op (yEl y hyA'))
      exact h₀.symm
  · -- the left triangle
    intro s
    apply pushout.hom_ext
    · change (cylSub φ A).base ≫ _ = (cylSub φ A).base ≫ _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (base_cylSubMap φ h)).trans
        (pushout.inl_desc _ _ _))
    · change (cylSub φ A).incl ≫ _ = (cylSub φ A).incl ≫ _
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (incl_cylSubMap φ h)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pushout.inr_desc _ _ _)).trans ?_)))
      apply colimit.hom_ext
      intro e
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (colimit.ι_pre (cylSub φ A').DC (elMap (Subfunctor.homOfLe h)) e)).trans
          ((colimit.ι_desc _ _).trans ?_))
      change cellApp φ y hyA' hA' s.inl s.inr _ = _
      rw [cellApp_pos φ y hyA' hA' s.inl s.inr _ e.unop.val.2]
      rfl
  · -- the right triangle
    intro s
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pushout.inr_desc _ _ _)).trans
      ((colimit.ι_desc _ _).trans (cellApp_y φ y hyA hyA' hA' s.inl s.inr)))
  · -- uniqueness
    intro s m hm₁ hm₂
    apply pushout.hom_ext
    · change (cylSub φ A').base ≫ m = (cylSub φ A').base ≫ _
      exact (congrArg (· ≫ m) (base_cylSubMap φ h).symm).trans ((Category.assoc _ _ _).trans
        ((congrArg _ hm₁).trans (pushout.inl_desc _ _ _).symm))
    · apply colimit.hom_ext
      intro e
      change colimit.ι _ e ≫ (cylSub φ A').incl ≫ m = colimit.ι _ e ≫ (cylSub φ A').incl ≫ _
      have hd := pushout.inr_desc ((cylSub φ A).base ≫ s.inl)
        (colimit.desc (cylSub φ A').DC (Cocone.mk _ (cellNat φ y hyA hyA' hA' s.inl s.inr
          (hl s.inl s.inr s.condition)))) (hw s.inl s.inr s.condition)
      refine Eq.trans ?_ ((congrArg (colimit.ι (cylSub φ A').DC e ≫ ·) hd).trans
        (colimit.ι_desc _ _)).symm
      change _ = cellApp φ y hyA' hA' s.inl s.inr e
      by_cases he : e.unop.val.1 ∈ A.obj e.unop.obj
      · rw [cellApp_pos φ y hyA' hA' s.inl s.inr e he, ← hm₁]
        have key : colimit.ι (cylSub φ A).DC (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩)) ≫
            (cylSub φ A).incl ≫ cylSubMap φ h =
            colimit.ι (cylSub φ A').DC ((elMap (Subfunctor.homOfLe h)).obj
              (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩))) ≫ (cylSub φ A').incl :=
          (congrArg (_ ≫ ·) (incl_cylSubMap φ h)).trans ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (cylSub φ A').incl) (colimit.ι_pre (cylSub φ A').DC
              (elMap (Subfunctor.homOfLe h)) (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩)))))
        exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) key.symm)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
      · have he' : e = op (yEl y hyA') := congrArg op (elem_eq_of_not_mem y hyA' hA' e.unop he)
        subst he'
        rw [cellApp_y φ y hyA hyA' hA' s.inl s.inr, ← hm₂]
        exact (Category.assoc _ _ _).symm

end Pushout

theorem anodyne_cylSubMap_cell_proof {A A' : Subfunctor W} (h : A ≤ A') (n : ℕ)
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA : y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA' : y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))
    (hA' : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
      z ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) →
        z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨ ∃ hk : k = n, hk ▸ z = y) :
    anodyne (cylSubMap φ h) := by
  obtain ⟨κ, sq⟩ := isPushout_cell φ h y hyA hyA' hfaces hA'
  exact anodyne_of_isPushout sq (anodyne_dcylDBoundaryι _)
