import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.TopSimplex.TopSimplex
import HomotopyHypothesis.Realization.SemisimplicialComparison.FreeKan
/-!
# Cell attachments in algebraic semi-simplicial Kan complexes

* Free cell attachments `X ⟶ X ⊔_{∂Δ_n} Δ_n` exist along every boundary map, and every cell
  attachment is isomorphic to the constructed one; the comparison map from the semi-simplicial
  pushout `X ⊔_{∂Δ_n} Δ_n` is a sequential composite of pushouts of coproducts of horn inclusions.
* The empty algebraic Kan complex is initial.
* Pushouts along cofibrations of `C^Δ` exist and are pushouts of algebraic Kan complexes.
* Free algebraic Kan complexes on semi-simplicial subsets of a standard simplex lie in `C^Δ`.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- A commutative square is a pushout as soon as it has the universal property. -/
theorem isPushout_of_universal {C : Type*} [Category C] {A B X P : C} {i : A ⟶ B} {f : A ⟶ X}
    {k : B ⟶ P} {j : X ⟶ P} (w : i ≫ k = f ≫ j)
    (U : ∀ (Z : C) (b : B ⟶ Z) (x : X ⟶ Z), i ≫ b = f ≫ x →
      ∃! p : P ⟶ Z, k ≫ p = b ∧ j ≫ p = x) : IsPushout i f k j := by
  refine IsPushout.of_isColimit (c := PushoutCocone.mk k j w) ?_
  refine PushoutCocone.IsColimit.mk _ (fun s => (U s.pt s.inl s.inr s.condition).choose)
    (fun s => (U s.pt s.inl s.inr s.condition).choose_spec.1.1)
    (fun s => (U s.pt s.inl s.inr s.condition).choose_spec.1.2)
    (fun s m h₁ h₂ => (U s.pt s.inl s.inr s.condition).choose_spec.2 m ⟨h₁, h₂⟩)

/-- The data of a cell attachment. -/
structure CellData {X Y : AlgKan.{u}} (j : X ⟶ Y) where
  /-- the dimension of the cell -/
  n : ℕ
  /-- the attaching map -/
  a : (SemiSSet.boundary.{u} n).toFunctor ⟶ X.X
  /-- the cell -/
  y : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y.X
  w : (SemiSSet.boundary n).ι ≫ y = a ≫ j.hom
  univ : ∀ (Z : AlgKan.{u}) (g : X ⟶ Z)
    (z : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Z.X),
      (SemiSSet.boundary n).ι ≫ z = a ≫ g.hom → ∃! g' : Y ⟶ Z, j ≫ g' = g ∧ y ≫ g'.hom = z

/-- A chosen set of cell attachment data. -/
noncomputable def AlgKan.IsCellAttachment.data {X Y : AlgKan.{u}} {j : X ⟶ Y}
    (h : AlgKan.IsCellAttachment j) : CellData j :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1, h.choose_spec.choose_spec.choose_spec.2⟩

theorem CellData.isCellAttachment {X Y : AlgKan.{u}} {j : X ⟶ Y} (d : CellData j) :
    AlgKan.IsCellAttachment j :=
  ⟨d.n, d.a, d.y, d.w, d.univ⟩

theorem CellData.hom_ext {X Y : AlgKan.{u}} {j : X ⟶ Y} (d : CellData j) {Z : AlgKan.{u}}
    {f f' : Y ⟶ Z} (h₁ : j ≫ f = j ≫ f') (h₂ : d.y ≫ f.hom = d.y ≫ f'.hom) : f = f' := by
  have hz : (SemiSSet.boundary d.n).ι ≫ d.y ≫ f.hom = d.a ≫ (j ≫ f).hom := by
    rw [← Category.assoc, d.w]; rfl
  obtain ⟨g', -, hu⟩ := d.univ Z (j ≫ f) (d.y ≫ f.hom) hz
  exact (hu f ⟨rfl, rfl⟩).trans (hu f' ⟨h₁.symm, h₂.symm⟩).symm

section Attach

variable (X : AlgKan.{u}) (n : ℕ) (a : (SemiSSet.boundary.{u} n).toFunctor ⟶ X.X)

/-- The semi-simplicial pushout `X ⊔_{∂Δ_n} Δ_n`. -/
noncomputable abbrev attachK : SemiSSet.{u} := pushout a (SemiSSet.boundary.{u} n).ι

/-- The inclusion of `X` into `X ⊔_{∂Δ_n} Δ_n`. -/
noncomputable abbrev attachM : X.X ⟶ attachK X n a := pushout.inl _ _

instance mono_attachM : Mono (attachM X n a) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  have sq := (IsPushout.of_hasPushout a (SemiSSet.boundary.{u} n).ι).map ((evaluation _ _).obj d)
  have : Mono ((SemiSSet.boundary.{u} n).ι.app d) := inferInstance
  exact (monomorphisms (Type u)).of_isPushout sq this

/-- The free cell attachment of `X` along `a`. -/
noncomputable abbrev attach : AlgKan.{u} := freeKan X (attachM X n a)

/-- The inclusion `X ⟶ X ⊔_{∂Δ_n} Δ_n` of algebraic Kan complexes. -/
noncomputable abbrev attachJ : X ⟶ attach X n a := freeJ X (attachM X n a)

/-- The attached cell. -/
noncomputable abbrev attachCell :
    SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ (attach X n a).X :=
  pushout.inr _ _ ≫ freeι X (attachM X n a)

theorem attach_w : (SemiSSet.boundary n).ι ≫ attachCell X n a = a ≫ (attachJ X n a).hom := by
  change _ = a ≫ pushout.inl _ _ ≫ freeι X (attachM X n a)
  rw [← Category.assoc, ← Category.assoc, pushout.condition]

/-- The constructed attachment is a cell attachment. -/
noncomputable def attachData : CellData (attachJ X n a) where
  n := n
  a := a
  y := attachCell X n a
  w := attach_w X n a
  univ Z g z hz := by
    have hz' : a ≫ g.hom = (SemiSSet.boundary n).ι ≫ z := hz.symm
    let z' : attachK X n a ⟶ Z.X := pushout.desc g.hom z hz'
    have hm : attachM X n a ≫ z' = g.hom := pushout.inl_desc _ _ _
    refine ⟨freeDesc X (attachM X n a) hm, ⟨freeJ_freeDesc X _ hm, ?_⟩, ?_⟩
    · change pushout.inr _ _ ≫ freeι X (attachM X n a) ≫ (freeDesc X _ hm).hom = z
      rw [freeι_freeDesc]
      exact pushout.inr_desc _ _ _
    · rintro g'' ⟨h₁, h₂⟩
      apply freeKan_hom_ext
      rw [freeι_freeDesc]
      apply pushout.hom_ext
      · rw [pushout.inl_desc]
        change (freeJ X (attachM X n a) ≫ g'').hom = g.hom
        rw [h₁]
      · rw [pushout.inr_desc, ← h₂]
        rfl

theorem attach_isCellAttachment : AlgKan.IsCellAttachment (attachJ X n a) :=
  (attachData X n a).isCellAttachment

/-- The comparison map `X ⊔_{∂Δ_n} Δ_n ⟶ attach X n a` is the inclusion of the first stage. -/
theorem attach_desc_eq :
    pushout.desc (attachJ X n a).hom (attachCell X n a) (attach_w X n a).symm =
      freeι X (attachM X n a) := by
  apply pushout.hom_ext
  · rw [pushout.inl_desc]
    rfl
  · rw [pushout.inr_desc]

end Attach

section Compare

variable {X Y : AlgKan.{u}} {j : X ⟶ Y} (d : CellData j)

/-- A cell attachment is isomorphic to the constructed one. -/
noncomputable def CellData.isoAttach : attach X d.n d.a ≅ Y where
  hom := ((attachData X d.n d.a).univ Y j d.y d.w).exists.choose
  inv := (d.univ _ (attachJ X d.n d.a) (attachCell X d.n d.a) (attach_w X d.n d.a)).exists.choose
  hom_inv_id := by
    have h₁ := ((attachData X d.n d.a).univ Y j d.y d.w).exists.choose_spec
    have h₂ := (d.univ _ (attachJ X d.n d.a) (attachCell X d.n d.a)
      (attach_w X d.n d.a)).exists.choose_spec
    apply (attachData X d.n d.a).hom_ext
    · rw [← Category.assoc, h₁.1, h₂.1, Category.comp_id]
    · change attachCell X d.n d.a ≫ _ ≫ _ = attachCell X d.n d.a ≫ 𝟙 _
      erw [← Category.assoc, h₁.2, h₂.2]
      rfl
  inv_hom_id := by
    have h₁ := ((attachData X d.n d.a).univ Y j d.y d.w).exists.choose_spec
    have h₂ := (d.univ _ (attachJ X d.n d.a) (attachCell X d.n d.a)
      (attach_w X d.n d.a)).exists.choose_spec
    apply d.hom_ext
    · rw [← Category.assoc, h₂.1, h₁.1, Category.comp_id]
    · change d.y ≫ _ ≫ _ = d.y ≫ 𝟙 _
      erw [← Category.assoc, h₂.2, h₁.2]
      rfl

theorem CellData.attachJ_isoAttach : attachJ X d.n d.a ≫ d.isoAttach.hom = j :=
  ((attachData X d.n d.a).univ Y j d.y d.w).exists.choose_spec.1

theorem CellData.attachCell_isoAttach : attachCell X d.n d.a ≫ d.isoAttach.hom.hom = d.y :=
  ((attachData X d.n d.a).univ Y j d.y d.w).exists.choose_spec.2

/-- The comparison map from the semi-simplicial pushout `X ⊔_{∂Δ_n} Δ_n` to the underlying
semi-simplicial set of a cell attachment is a sequential composite of pushouts of coproducts of
horn inclusions. -/
theorem CellData.desc_mem :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (MorphismProperty.ofHoms (fun p : Σ n : ℕ, Fin (n + 2) =>
        (SemiSSet.horn.{u} (p.1 + 1) p.2).ι))).pushouts
      (pushout.desc j.hom d.y d.w.symm) := by
  have e : pushout.desc j.hom d.y d.w.symm =
      freeι X (attachM X d.n d.a) ≫ d.isoAttach.hom.hom := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      calc j.hom = (attachJ X d.n d.a ≫ d.isoAttach.hom).hom := by rw [d.attachJ_isoAttach]
        _ = _ := Category.assoc _ _ _
    · rw [pushout.inr_desc]
      calc d.y = attachCell X d.n d.a ≫ d.isoAttach.hom.hom := by rw [d.attachCell_isoAttach]
        _ = _ := Category.assoc _ _ _
  rw [e]
  have c := ((ccComp X (attachM X d.n d.a)).ofOrderIso (orderIsoShrink.{u} ℕ).symm).ofArrowIso
    (Arrow.isoMk (Iso.refl _) (AlgKan.forget.mapIso d.isoAttach)
      (by rw [Iso.refl_hom, Category.id_comp]; rfl) : CategoryTheory.Arrow.mk (cc X (attachM X d.n d.a) 0) ≅
        CategoryTheory.Arrow.mk (freeι X (attachM X d.n d.a) ≫ d.isoAttach.hom.hom))
  exact MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _ c.mem

end Compare

end HomotopyHypothesis.Realization.SemisimplicialComparison
