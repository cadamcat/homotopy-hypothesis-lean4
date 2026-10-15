import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSubMap
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
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
# `HomotopyHypothesis.Approximation.Topological.CylinderCellProof`, part 1

Lines 18–234 of `HomotopyHypothesis.Approximation.Topological.CylinderCellProof`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

private theorem elementary_anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g')
    (hf : (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f) :
    (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f' := by
  rcases hf with hf | hf
  · exact Or.inl (MorphismProperty.of_isPushout sq hf)
  · haveI : IsIso f := hf
    exact Or.inr sq.isIso_inl_of_isIso

/-- Finite composites of horn pushouts and isomorphisms are stable under pushout. -/
theorem anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g') (hf : anodyne f) : anodyne f' := by
  unfold anodyne at hf ⊢
  induction hf generalizing D E with
  | of f hf =>
    exact .of _ (elementary_anodyne_of_isPushout sq hf)
  | id A =>
    exact .of _ (Or.inr sq.isIso_inl_of_isIso)
  | @comp_of A B C f h hf hh ih =>
    have left := IsPushout.of_hasPushout g f
    have right := sq.of_top' left
    have hi := ih left
    have ht := elementary_anodyne_of_isPushout right hh
    simpa only [IsPushout.inl_desc] using
      MorphismProperty.multiplicativeClosure.comp_of _ _ hi ht

/-- The only endomorphism of `[n]` in the semi-simplicial category is the identity. -/
theorem semiSimplex_endo_eq_id {n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk n) : θ = 𝟙 _ := by
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  exact (SemiSimplexCategory.strictMono θ).eq_id

section Cell

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The simplices of `A'` not in `A` are `y` (classification of elements). -/
theorem elem_eq_of_not_mem {A A' : Subfunctor W} {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA' : y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hA' : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
      z ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) →
        z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨ ∃ hk : k = n, hk ▸ z = y)
    (e : A'.toFunctor.Elements) (he : e.val.1 ∉ A.obj e.obj) :
    e = A'.toFunctor.elementsMk _ ⟨y, hyA'⟩ := by
  obtain @⟨c, ⟨z, hz⟩⟩ := e
  obtain ⟨⟨⟨k⟩⟩⟩ := c
  rcases hA' k z hz with h | ⟨hk, hzy⟩
  · exact absurd h he
  · subst hk
    subst hzy
    rfl

/-- The faces of a simplex of a subfunctor lie in it. -/
theorem mem_of_face_mem {A : Subfunctor W} {e₁ e₂ : W.Elements} (f : e₂ ⟶ e₁)
    (h : e₂.val ∈ A.obj e₂.obj) : e₁.val ∈ A.obj e₁.obj := by
  rw [← f.map_val]
  exact A.map f.hom h

theorem CylDatum.botN_ι_incl {X : SemiSSet.{u}} {I : Type u} [Category.{0} I] (D : CylDatum X I)
    (e : I) : D.botN.app e ≫ colimit.ι D.DC e ≫ D.incl = D.xN.app e ≫ D.base := by
  have := pushout.condition (f := colimit.desc D.B (Cocone.mk X D.xN)) (g := colimMap D.botN)
  have := congrArg (fun k => colimit.ι D.B e ≫ k) this
  simp only [colimit.ι_desc_assoc, ι_colimMap_assoc] at this
  exact this.symm

theorem incl_cylSubMap {A A' : Subfunctor W} (h : A ≤ A') :
    (cylSub φ A).incl ≫ cylSubMap φ h =
      colimit.pre (cylSub φ A').DC (elMap (Subfunctor.homOfLe h)) ≫ (cylSub φ A').incl :=
  pushout.inr_desc _ _ _

theorem base_cylSubMap {A A' : Subfunctor W} (h : A ≤ A') :
    (cylSub φ A).base ≫ cylSubMap φ h = (cylSub φ A').base := by
  unfold cylSubMap CylDatum.base CylDatum.restrictMap pushout.map
  exact (pushout.inl_desc _ _ _).trans (Category.id_comp _)

/-- The morphism of elements of `A'` from `y` to its face along `θ`. -/
def faceElHom {A' : Subfunctor W} {n k : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hy : y ∈ A'.obj _) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n)
    (hz : W.map θ.op y ∈ A'.obj _) :
    A'.toFunctor.elementsMk _ ⟨y, hy⟩ ⟶ A'.toFunctor.elementsMk _ ⟨W.map θ.op y, hz⟩ where
  hom := θ.op
  map_val := rfl

theorem faceBdry_ι {n k : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n) (hk : k ≠ n) :
    (faceBdry φ y θ hk).toSemiSSet ≫ dcylDBoundaryι _ =
      (dcylDElMap φ (elFaceHom y θ)).toSemiSSet :=
  (Complex.Hom.toSemiSSet_comp _ _ _ rfl).symm

theorem botBdry_ι {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    botBdry.{u} v ≫ dcylDBoundaryι v = dcylDBot v := by
  ext k σ
  rfl

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

/-- The element `y` of `A'`. -/
abbrev yEl : A'.toFunctor.Elements := A'.toFunctor.elementsMk _ ⟨y, hyA'⟩

open Classical in
/-- The components of the map out of the glued cylinder over `A'` given maps out of the glued
cylinder over `A` and out of the cylinder of `y`. -/

noncomputable def cellApp {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T)
    (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T) (e : A'.toFunctor.Elementsᵒᵖ) :
    (cylSub φ A').DC.obj e ⟶ T :=
  if he : e.unop.val.1 ∈ A.obj e.unop.obj then
    colimit.ι (cylSub φ A).DC (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩)) ≫
      (cylSub φ A).incl ≫ l
  else
    (cylSub φ A').DC.map (eqToHom (congrArg op (elem_eq_of_not_mem y hyA' hA' e.unop he))) ≫ r

theorem cellApp_pos {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T)
    (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T) (e : A'.toFunctor.Elementsᵒᵖ)
    (he : e.unop.val.1 ∈ A.obj e.unop.obj) :
    cellApp φ y hyA' hA' l r e =
      colimit.ι (cylSub φ A).DC (op (A.toFunctor.elementsMk _ ⟨e.unop.val.1, he⟩)) ≫
        (cylSub φ A).incl ≫ l := by
  unfold cellApp
  rw [dif_pos he]
  rfl

include hyA in

theorem cellApp_y {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T)
    (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T) :
    cellApp φ y hyA' hA' l r (op (yEl y hyA')) = r := by
  unfold cellApp
  rw [dif_neg hyA, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

include hyA in

theorem cellApp_naturality {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T)
    (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T)
    (hl : ∀ (e : A.toFunctor.Elements) (f : elOf y ⟶ W.elementsMk e.obj e.val.1)
      (_ : elDim (W.elementsMk e.obj e.val.1) ≠ n),
      (dcylDElMap φ f).toSemiSSet ≫ r = colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl ≫ l)
    {e₁ e₂ : A'.toFunctor.Elementsᵒᵖ} (g : e₁ ⟶ e₂) :
    (cylSub φ A').DC.map g ≫ cellApp φ y hyA' hA' l r e₂ = cellApp φ y hyA' hA' l r e₁ := by
  by_cases h₂ : e₂.unop.val.1 ∈ A.obj e₂.unop.obj
  · have h₁ : e₁.unop.val.1 ∈ A.obj e₁.unop.obj := by
      have hv := congrArg Subtype.val g.unop.map_val
      rw [← hv]
      exact A.map g.unop.hom h₂
    rw [cellApp_pos φ y hyA' hA' l r e₂ h₂, cellApp_pos φ y hyA' hA' l r e₁ h₁]
    let gA : op (A.toFunctor.elementsMk _ ⟨e₁.unop.val.1, h₁⟩) ⟶
        op (A.toFunctor.elementsMk _ ⟨e₂.unop.val.1, h₂⟩) :=
      Quiver.Hom.op
        { hom := g.unop.hom
          map_val := by
            apply Subtype.ext
            have hv := congrArg Subtype.val g.unop.map_val
            exact hv }
    have := colimit.w (cylSub φ A).DC gA
    rw [← this, Category.assoc]
    rfl
  · have he₂ : e₂ = op (yEl y hyA') :=
      congrArg op (elem_eq_of_not_mem y hyA' hA' e₂.unop h₂)
    subst he₂
    rw [cellApp_y φ y hyA hyA' hA' l r]
    by_cases h₁ : e₁.unop.val.1 ∈ A.obj e₁.unop.obj
    · rw [cellApp_pos φ y hyA' hA' l r e₁ h₁]
      have hk : elDim (W.elementsMk e₁.unop.obj e₁.unop.val.1) ≠ n := by
        intro hkn
        apply hyA
        obtain ⟨e₁⟩ := e₁
        obtain @⟨⟨⟨⟨k⟩⟩⟩, val⟩ := e₁
        change k = n at hkn
        subst hkn
        have hv := congrArg Subtype.val g.unop.map_val
        have hθ : g.unop.hom.unop = 𝟙 _ := semiSimplex_endo_eq_id _
        have hhom : g.unop.hom = 𝟙 _ := by
          rw [← Quiver.Hom.op_unop g.unop.hom, hθ]
          rfl
        change W.map g.unop.hom y = val.1 at hv
        rw [hhom, FunctorToTypes.map_id_apply] at hv
        exact hv ▸ h₁
      exact hl (A.toFunctor.elementsMk _ ⟨e₁.unop.val.1, h₁⟩) ((elMap A'.ι).map g).unop hk
    · have he₁ : e₁ = op (yEl y hyA') :=
        congrArg op (elem_eq_of_not_mem y hyA' hA' e₁.unop h₁)
      subst he₁
      have hg : g = 𝟙 _ := by
        apply Quiver.Hom.unop_inj
        apply Functor.Elements.Hom.ext
        apply Quiver.Hom.unop_inj
        exact semiSimplex_endo_eq_id _
      rw [hg, CategoryTheory.Functor.map_id, cellApp_y φ y hyA hyA' hA' l r]
      exact Category.id_comp _

theorem faceBdryGen_ι {n : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    {b : W.Elements} (f : elOf y ⟶ b) (hk : elDim b ≠ n) :
    (faceBdryGen φ y f hk).toSemiSSet ≫ dcylDBoundaryι _ = (dcylDElMap φ f).toSemiSSet :=
  (Complex.Hom.toSemiSSet_comp _ _ _ rfl).symm

/-- The cocone of components. -/
noncomputable def cellNat {T : SemiSSet.{u}} (l : (cylSub φ A).obj ⟶ T)
    (r : dcylD.{u} (elNF φ (elOf y)).v ⟶ T)
    (hl : ∀ (e : A.toFunctor.Elements) (f : elOf y ⟶ W.elementsMk e.obj e.val.1)
      (_ : elDim (W.elementsMk e.obj e.val.1) ≠ n),
      (dcylDElMap φ f).toSemiSSet ≫ r = colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl ≫ l) :
    (cylSub φ A').DC ⟶ (Functor.const _).obj T where
  app := cellApp φ y hyA' hA' l r
  naturality e₁ e₂ g := (cellApp_naturality φ y hyA hyA' hA' l r hl g).trans (Category.comp_id _).symm
