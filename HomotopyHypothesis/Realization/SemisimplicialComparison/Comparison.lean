import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationBoundaryRelativeFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationHornCellsDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.RelativeCells.Part1
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.Anodyne.RealizationPushout
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.Realization
import HomotopyHypothesis.Realization.SemisimplicialComparison.Standard
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
/-!
# Comparison of a standard realization with the realization of semi-simplicial sets
(H Lemma 5.2.6)

For a standard realization `R` and `X` in `C^Δ`, the comparison map `φ_X : ‖X‖ ⟶ R X` sends the
realized simplex of `σ : Δ_n ⟶ X` to `R` of the corresponding map out of the free simplex. It is
natural, an isomorphism on objects free on semi-simplicial subsets of simplices (by induction over
their top simplices), and a homotopy equivalence on every object: a cell attachment `X ⟶ Y` is the
semi-simplicial pushout `X ⊔_{∂Δ_n} Δ_n` followed by a free addition of horn fillers, which
realizes to a strong deformation retract, and the gluing lemma concludes (H:2891–2912).
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- A chosen object of `C^Δ` free on the simplex `Δ_c`. -/
noncomputable def freeSimplex (c : Henry.SemiSimplexCategory) : CDelta.{u} :=
  (exists_free_simplex.{u} c.obj.len).choose

/-- Its generating simplex. -/
noncomputable def freeSimplexη (c : Henry.SemiSimplexCategory) :
    SemiSSet.stdSimplex.obj c ⟶ (freeSimplex.{u} c).obj.X :=
  (exists_free_simplex.{u} c.obj.len).choose_spec.choose

theorem freeSimplex_isFreeOn (c : Henry.SemiSimplexCategory) :
    (freeSimplex.{u} c).obj.IsFreeOn (freeSimplexη c) :=
  (exists_free_simplex.{u} c.obj.len).choose_spec.choose_spec

/-- The map out of the free simplex classifying a simplex. -/
noncomputable def liftS {c : Henry.SemiSimplexCategory} {X : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) : freeSimplex c ⟶ X :=
  ObjectProperty.homMk ((freeSimplex_isFreeOn c) X.obj σ).exists.choose

theorem liftS_spec {c : Henry.SemiSimplexCategory} {X : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) : freeSimplexη c ≫ (liftS σ).hom.hom = σ :=
  ((freeSimplex_isFreeOn c) X.obj σ).exists.choose_spec

theorem liftS_eq {c : Henry.SemiSimplexCategory} {X : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) (g : freeSimplex c ⟶ X)
    (hg : freeSimplexη c ≫ g.hom.hom = σ) : liftS σ = g :=
  ObjectProperty.hom_ext _ (isFreeOn_hom_ext (freeSimplex_isFreeOn c) (by rw [liftS_spec, hg]))

theorem liftS_comp {c : Henry.SemiSimplexCategory} {X Y : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) (f : X ⟶ Y) :
    liftS (σ ≫ f.hom.hom) = liftS σ ≫ f :=
  liftS_eq _ _ (by
    change freeSimplexη c ≫ (liftS σ).hom.hom ≫ f.hom.hom = _
    rw [← Category.assoc, liftS_spec])

theorem liftS_precomp {c c' : Henry.SemiSimplexCategory} {X : CDelta.{u}} (θ : c' ⟶ c)
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) :
    liftS (SemiSSet.stdSimplex.map θ ≫ σ) =
      liftS (SemiSSet.stdSimplex.map θ ≫ freeSimplexη c) ≫ liftS σ :=
  liftS_eq _ _ (by
    change freeSimplexη c' ≫ (liftS _).hom.hom ≫ (liftS σ).hom.hom = _
    rw [← Category.assoc, liftS_spec, Category.assoc, liftS_spec])

/-- A singular simplex as an element of `Sing T`. -/
def sing {c : Henry.SemiSimplexCategory} {T : TopCat.{u}} (g : SemiSSet.toTop.obj c ⟶ T) :
    (Sing.obj T).obj (op c) :=
  ULift.up g

/-- The underlying map of a singular simplex. -/
def unsing {c : Henry.SemiSimplexCategory} {T : TopCat.{u}} (x : (Sing.obj T).obj (op c)) :
    SemiSSet.toTop.obj c ⟶ T :=
  (show ULift.{u} (SemiSSet.toTop.obj c ⟶ T) from x).down

theorem sing_unsing {c : Henry.SemiSimplexCategory} {T : TopCat.{u}} (x : (Sing.obj T).obj (op c)) :
    sing (unsing x) = x := rfl

theorem Sing_map_sing {c : Henry.SemiSimplexCategory} {T T' : TopCat.{u}}
    (g : SemiSSet.toTop.obj c ⟶ T) (h : T ⟶ T') :
    (Sing.map h).app (op c) (sing g) = sing (g ≫ h) := rfl

theorem yoneda_sing_eq {c : Henry.SemiSimplexCategory} {T : TopCat.{u}}
    (g : SemiSSet.toTop.obj c ⟶ T) :
    (uliftYonedaEquiv.symm (sing g) : SemiSSet.stdSimplex.obj c ⟶ Sing.obj T) =
      uliftYonedaEquiv.symm (sing (𝟙 (SemiSSet.toTop.obj c))) ≫ Sing.map g := by
  rw [uliftYonedaEquiv_symm_comp, Sing_map_sing, Category.id_comp]

/-- The comparison of the realization of a representable with the topological simplex. -/
noncomputable def kappa (c : Henry.SemiSimplexCategory) :
    SemiSSet.realization.obj (SemiSSet.stdSimplex.{u}.obj c) ⟶ SemiSSet.toTop.obj c :=
  (realAdj.homEquiv _ _).symm (uliftYonedaEquiv.symm (sing (𝟙 (SemiSSet.toTop.obj c))))

theorem homEquiv_symm_yoneda {c : Henry.SemiSimplexCategory} {T : TopCat.{u}}
    (g : SemiSSet.toTop.obj c ⟶ T) :
    (realAdj.homEquiv _ _).symm (uliftYonedaEquiv.symm (sing g)) = kappa c ≫ g := by
  rw [yoneda_sing_eq]
  exact realAdj.homEquiv_naturality_right_symm _ _

instance isIso_kappa (c : Henry.SemiSimplexCategory) : IsIso (kappa.{u} c) := by
  let κ' : SemiSSet.toTop.obj c ⟶ SemiSSet.realization.obj (SemiSSet.stdSimplex.{u}.obj c) :=
    unsing (uliftYonedaEquiv (realAdj.unit.app (SemiSSet.stdSimplex.{u}.obj c)))
  have h1 : realAdj.unit.app _ ≫ Sing.map (kappa c) =
      uliftYonedaEquiv.symm (sing (𝟙 (SemiSSet.toTop.obj c))) :=
    (Adjunction.homEquiv_unit realAdj _ _ (kappa c)).symm.trans (Equiv.apply_symm_apply _ _)
  refine ⟨κ', ?_, ?_⟩
  · apply (realAdj.homEquiv _ _).injective
    rw [realAdj.homEquiv_naturality_right, kappa, Equiv.apply_symm_apply, ← yoneda_sing_eq,
      Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact (uliftYonedaEquiv.symm_apply_apply _).trans (Category.comp_id _).symm
  · have h3 : uliftYonedaEquiv (uliftYonedaEquiv.symm (sing (𝟙 (SemiSSet.toTop.obj c)))) =
        sing (𝟙 _) := Equiv.apply_symm_apply _ _
    calc κ' ≫ kappa c
        = unsing (uliftYonedaEquiv (realAdj.unit.app _ ≫ Sing.map (kappa c))) := rfl
      _ = unsing (uliftYonedaEquiv (uliftYonedaEquiv.symm (sing (𝟙 (SemiSSet.toTop.obj c))))) :=
          congrArg (fun t => unsing (uliftYonedaEquiv t)) h1
      _ = 𝟙 _ := by rw [h3]; rfl

section

variable {R : CDelta.{u} ⥤ TopCat.{u}} (hR : IsStandardRealization R)

/-- The chosen identification of `R` on the free simplices with the topological simplices. -/
noncomputable def simpE (c : Henry.SemiSimplexCategory) :
    R.obj (freeSimplex c) ≅ SemiSSet.toTop.obj c :=
  hR.simplex.choose c.obj.len (freeSimplex c) (freeSimplexη c) (freeSimplex_isFreeOn c)

theorem simpE_comp {c c' : Henry.SemiSimplexCategory} (θ : c' ⟶ c) :
    (simpE hR c').inv ≫ R.map (liftS (SemiSSet.stdSimplex.map θ ≫ freeSimplexη c)) =
      SemiSSet.toTop.map θ ≫ (simpE hR c).inv := by
  unfold simpE
  have := hR.simplex.choose_spec c'.obj.len c.obj.len (freeSimplex c') (freeSimplex c)
    (freeSimplexη c') (freeSimplexη c) (freeSimplex_isFreeOn c') (freeSimplex_isFreeOn c) θ
    (liftS (SemiSSet.stdSimplex.map θ ≫ freeSimplexη c)) (liftS_spec _)
  rw [Iso.inv_comp_eq, ← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The singular simplex of `R X` given by a simplex of `X`. -/
noncomputable def simpVal {c : Henry.SemiSimplexCategory} {X : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) : SemiSSet.toTop.obj c ⟶ R.obj X :=
  (simpE hR c).inv ≫ R.map (liftS σ)

/-- The comparison map `X ⟶ Sing (R X)`. -/
noncomputable def psiC (X : CDelta.{u}) : X.obj.X ⟶ Sing.obj (R.obj X) where
  app d := TypeCat.ofHom fun x => sing (simpVal hR (uliftYonedaEquiv.symm x))
  naturality d d' θ := by
    ext x
    change sing (simpVal hR (uliftYonedaEquiv.symm (X.obj.X.map θ x))) =
      sing (SemiSSet.toTop.map θ.unop ≫ simpVal hR (uliftYonedaEquiv.symm x))
    rw [uliftYonedaEquiv_symm_map, simpVal, simpVal, liftS_precomp, CategoryTheory.Functor.map_comp,
      ← Category.assoc, simpE_comp, Category.assoc]

theorem psiC_app {c : Henry.SemiSimplexCategory} {X : CDelta.{u}}
    (σ : SemiSSet.stdSimplex.obj c ⟶ X.obj.X) :
    σ ≫ psiC hR X = uliftYonedaEquiv.symm (sing (simpVal hR σ)) := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  change sing (simpVal hR (uliftYonedaEquiv.symm (uliftYonedaEquiv σ))) = _
  rw [Equiv.symm_apply_apply]

theorem psiC_naturality {X Y : CDelta.{u}} (f : X ⟶ Y) :
    f.hom.hom ≫ psiC hR Y = psiC hR X ≫ Sing.map (R.map f) := by
  ext d x
  change sing (simpVal hR (uliftYonedaEquiv.symm (f.hom.hom.app d x))) =
    sing (simpVal hR (uliftYonedaEquiv.symm x) ≫ R.map f)
  rw [← uliftYonedaEquiv_symm_comp, simpVal, simpVal, liftS_comp, CategoryTheory.Functor.map_comp,
    Category.assoc]

/-- The comparison map `‖X‖ ⟶ R X`. -/
noncomputable def phiC : ObjectProperty.ι AlgKan.IsFinitelyCellular.{u} ⋙ AlgKan.forget ⋙
    SemiSSet.realization ⟶ R where
  app X := (realAdj.homEquiv _ _).symm (psiC hR X)
  naturality X Y f :=
    ((realAdj.homEquiv_naturality_left_symm _ _).symm.trans
      (congrArg _ (psiC_naturality hR f))).trans (realAdj.homEquiv_naturality_right_symm _ _)

/-- The component of the comparison map. -/
noncomputable abbrev phiA (X : CDelta.{u}) : SemiSSet.realization.obj X.obj.X ⟶ R.obj X :=
  (phiC hR).app X

theorem phiA_naturality {X Y : CDelta.{u}} (g : X ⟶ Y) :
    SemiSSet.realization.map g.hom.hom ≫ phiA hR Y = phiA hR X ≫ R.map g :=
  (phiC hR).naturality g

theorem realization_map_phiC {S : SemiSSet.{u}} {X : CDelta.{u}} (η : S ⟶ X.obj.X) :
    SemiSSet.realization.map η ≫ (phiC hR).app X = (realAdj.homEquiv _ _).symm (η ≫ psiC hR X) :=
  (realAdj.homEquiv_naturality_left_symm η (psiC hR X)).symm

theorem phi_comm {S S' : SemiSSet.{u}} {X Y : CDelta.{u}} (ηX : S ⟶ X.obj.X) (ηY : S' ⟶ Y.obj.X)
    (s : S ⟶ S') (g : X ⟶ Y) (h : ηX ≫ g.hom.hom = s ≫ ηY) :
    SemiSSet.realization.map s ≫ (SemiSSet.realization.map ηY ≫ phiA hR Y) =
      (SemiSSet.realization.map ηX ≫ phiA hR X) ≫ R.map g := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← h, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc, phiA_naturality]

/-- **Clause on free simplices**: for `Y` free on `Δ_n`, `‖Δ_n‖ ⟶ ‖Y‖ ⟶ R Y` is an iso. -/
theorem isIso_phi_simplex {c : Henry.SemiSimplexCategory} {Y : CDelta.{u}}
    {η : SemiSSet.stdSimplex.obj c ⟶ Y.obj.X} (h : Y.obj.IsFreeOn η) :
    IsIso (SemiSSet.realization.map η ≫ (phiC hR).app Y) := by
  rw [realization_map_phiC, psiC_app, homEquiv_symm_yoneda, simpVal]
  have : IsIso (liftS η) := by
    obtain ⟨g, hg, -⟩ := h (freeSimplex c).obj (freeSimplexη c)
    refine ⟨⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ ?_, ObjectProperty.hom_ext _ ?_⟩⟩
    · apply isFreeOn_hom_ext (freeSimplex_isFreeOn c)
      change freeSimplexη c ≫ (liftS η).hom.hom ≫ g.hom = freeSimplexη c ≫ 𝟙 _
      rw [← Category.assoc, liftS_spec, hg, Category.comp_id]
    · apply isFreeOn_hom_ext h
      change η ≫ g.hom ≫ (liftS η).hom.hom = η ≫ 𝟙 _
      rw [← Category.assoc, hg, liftS_spec, Category.comp_id]
  infer_instance

end

/-- A map between pushout squares that is an isomorphism on the three corners is an isomorphism on
the pushouts. -/
theorem isIso_of_isPushout_map {C : Type*} [Category C] {A B X P A' B' X' P' : C}
    {t : A ⟶ B} {l : A ⟶ X} {r : B ⟶ P} {b : X ⟶ P}
    {t' : A' ⟶ B'} {l' : A' ⟶ X'} {r' : B' ⟶ P'} {b' : X' ⟶ P'}
    (sq : IsPushout t l r b) (sq' : IsPushout t' l' r' b') (vA : A ⟶ A') (vB : B ⟶ B')
    (vX : X ⟶ X') (φ : P ⟶ P') [IsIso vA] [IsIso vB] [IsIso vX]
    (c₁ : t ≫ vB = vA ≫ t') (c₂ : l ≫ vX = vA ≫ l') (c₃ : r ≫ φ = vB ≫ r')
    (c₄ : b ≫ φ = vX ≫ b') : IsIso φ := by
  have e₁ : t' ≫ inv vB = inv vA ≫ t := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c₁, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have e₂ : l' ≫ inv vX = inv vA ≫ l := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c₂, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  let ψ := sq'.desc (inv vB ≫ r) (inv vX ≫ b) (by
    rw [← Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc, sq.w])
  refine ⟨ψ, sq.hom_ext ?_ ?_, sq'.hom_ext ?_ ?_⟩
  · rw [← Category.assoc, c₃, Category.assoc, sq'.inl_desc, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  · rw [← Category.assoc, c₄, Category.assoc, sq'.inr_desc, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  · rw [← Category.assoc, sq'.inl_desc, Category.assoc, c₃, IsIso.inv_hom_id_assoc,
      Category.comp_id]
  · rw [← Category.assoc, sq'.inr_desc, Category.assoc, c₄, IsIso.inv_hom_id_assoc,
      Category.comp_id]

end HomotopyHypothesis.Realization.SemisimplicialComparison

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

noncomputable def isInitial_realization_of_isEmpty {S : SemiSSet.{u}} (hS : ∀ d, IsEmpty (S.obj d)) :
    IsInitial (SemiSSet.realization.obj S) :=
  IsInitial.ofUniqueHom (fun T => (realAdj.homEquiv _ _).symm (toEmptyX hS ≫ fromEmptyX _))
    (fun T f => (realAdj.homEquiv _ _).injective (by
      rw [Equiv.apply_symm_apply]
      ext d s
      exact ((hS d).false s).elim))

noncomputable def isInitial_of_isFreeOn_empty {S : SemiSSet.{u}} (hS : ∀ d, IsEmpty (S.obj d))
    {Y : CDelta.{u}} {η : S ⟶ Y.obj.X} (h : Y.obj.IsFreeOn η) : IsInitial Y :=
  IsInitial.ofUniqueHom
    (fun Z => ObjectProperty.homMk (h Z.obj (toEmptyX hS ≫ fromEmptyX _)).exists.choose)
    (fun Z f => ObjectProperty.hom_ext _ (isFreeOn_hom_ext h (by
      ext d s
      exact ((hS d).false s).elim)))

theorem isIso_of_isInitial {C : Type*} [Category C] {X Y : C} (hX : IsInitial X)
    (hY : IsInitial Y) (f : X ⟶ Y) : IsIso f :=
  ⟨⟨hY.to X, hX.hom_ext _ _, hY.hom_ext _ _⟩⟩

section

variable {R : CDelta.{u} ⥤ TopCat.{u}} (hR : IsStandardRealization R)

theorem phi_comm₁ {S : SemiSSet.{u}} {X Y : CDelta.{u}} (ηX : S ⟶ X.obj.X) (s : S ⟶ Y.obj.X)
    (g : X ⟶ Y) (h : ηX ≫ g.hom.hom = s) :
    SemiSSet.realization.map s ≫ phiA hR Y =
      (SemiSSet.realization.map ηX ≫ phiA hR X) ≫ R.map g := by
  have := phi_comm hR ηX (𝟙 _) s g (by rw [Category.comp_id, h])
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at this

theorem phi_comm₂ {S' : SemiSSet.{u}} {X Y : CDelta.{u}} (ηY : S' ⟶ Y.obj.X)
    (s : X.obj.X ⟶ S') (g : X ⟶ Y) (h : g.hom.hom = s ≫ ηY) :
    SemiSSet.realization.map s ≫ (SemiSSet.realization.map ηY ≫ phiA hR Y) =
      phiA hR X ≫ R.map g := by
  have := phi_comm hR (𝟙 _) ηY s g (by rw [Category.id_comp, h])
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at this

/-- **Clause on free subsets of simplices** (in particular on `∂Δ_n`). -/
theorem isIso_phi_subfunctor : ∀ (N : ℕ)
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (Y : CDelta.{u}) (η : S.toFunctor ⟶ Y.obj.X), Y.obj.IsFreeOn η →
      IsIso (SemiSSet.realization.map η ≫ phiA hR Y) := by
  refine subfunctor_induction _ ?_ ?_
  · intro N S hS Y η h
    exact isIso_of_isInitial (isInitial_realization_of_isEmpty hS)
      (Classical.choice (hR.isCellularRealization.map_initial (isInitial_of_isFreeOn_empty hS h))) _
  · intro N S S' hle m b σ sq ih' ihB Y η h
    obtain ⟨Y', η', h'⟩ := exists_free_subfunctor.{u} N S'
    obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} m
    obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} m
    obtain ⟨β, hβ, -⟩ := hB Y'.obj (b ≫ η')
    obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary m).ι ≫ ηD)
    obtain ⟨ι', hι', -⟩ := h' Y.obj (Subfunctor.homOfLe hle ≫ η)
    obtain ⟨ybar, hy, -⟩ := hD Y.obj (σ ≫ η)
    have sqA := isPushout_of_free sq hB h' hD h hβ hι hι' hy
    let βC : B ⟶ Y' := ObjectProperty.homMk β
    let ιC : B ⟶ D := ObjectProperty.homMk ι
    let ι'C : Y' ⟶ Y := ObjectProperty.homMk ι'
    let ybarC : D ⟶ Y := ObjectProperty.homMk ybar
    have sqC : IsPushout βC ιC ι'C ybarC := isPushout_of_alg sqA
    have hcof : cofibrations CDelta.{u} ιC := cofibration_of_isFreeOn_boundary hB hD ιC hι
    have sqR := hR.isCellularRealization.map_isPushout ιC βC ybarC ι'C sqC.flip hcof
    have sqS := Approximation.Anodyne.realization_isPushout_proof sq
    have := ihB B ηB hB
    have := ih' Y' η' h'
    have := isIso_phi_simplex hR hD
    exact isIso_of_isPushout_map sqS sqR.flip _ _ _ _ (phi_comm hR ηB η' b βC hβ)
      (phi_comm hR ηB ηD _ ιC hι) (phi_comm hR η' η _ ι'C hι') (phi_comm hR ηD η σ ybarC hy)

theorem hoeq_of_deformationRetract {A B : TopCat.{u}} (i : A ⟶ B) (r : B ⟶ A)
    (h₁ : i ≫ r = 𝟙 A) (h₂ : (r ≫ i).hom.HomotopicRel (ContinuousMap.id B) (Set.range i.hom)) :
    Top.homotopyEquivalences i :=
  ⟨r, by rw [h₁], h₂.homotopic⟩

/-- **The comparison maps are homotopy equivalences** (H Lemma 5.2.6). -/
theorem hoeq_phi (X : CDelta.{u}) : Top.homotopyEquivalences (phiA hR X) := by
  obtain ⟨X, hX⟩ := X
  induction hX with
  | initial X hX =>
    obtain ⟨hX⟩ := hX
    have hI : IsInitial (⟨X, .initial X ⟨hX⟩⟩ : CDelta.{u}) :=
      IsInitial.ofUniqueHom (fun Z => ObjectProperty.homMk (hX.to Z.obj))
        (fun Z f => ObjectProperty.hom_ext _ (hX.hom_ext _ _))
    have := isIso_of_isInitial (isInitial_realization_of_isEmpty (isEmpty_of_isInitial hX))
      (Classical.choice (hR.isCellularRealization.map_initial hI)) (phiA hR ⟨X, .initial X ⟨hX⟩⟩)
    exact hoeq_of_isIso _
  | @attach X Y j hX hj ih =>
    let d := AlgKan.IsCellAttachment.data hj
    let XC : CDelta.{u} := ⟨X, hX⟩
    let YC : CDelta.{u} := ⟨Y, .attach j hX hj⟩
    obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} d.n
    obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} d.n
    obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary d.n).ι ≫ ηD)
    obtain ⟨abar, habar, -⟩ := hB X d.a
    obtain ⟨ybar, hybar, -⟩ := hD Y d.y
    have sq := d.isPushout hB hD hι habar hybar
    let ιC : B ⟶ D := ObjectProperty.homMk ι
    let abarC : B ⟶ XC := ObjectProperty.homMk abar
    let ybarC : D ⟶ YC := ObjectProperty.homMk ybar
    let jC : XC ⟶ YC := ObjectProperty.homMk j
    have sqC : IsPushout ιC abarC ybarC jC := isPushout_of_alg sq
    have hcof : cofibrations CDelta.{u} ιC := cofibration_of_isFreeOn_boundary hB hD ιC hι
    have sqR := hR.isCellularRealization.map_isPushout ιC abarC ybarC jC sqC hcof
    have sqK := IsPushout.of_hasPushout d.a (SemiSSet.boundary.{u} d.n).ι
    have sqKR := Approximation.Anodyne.realization_isPushout_proof sqK
    let κ : pushout d.a (SemiSSet.boundary.{u} d.n).ι ⟶ Y.X := pushout.desc j.hom d.y d.w.symm
    have hB' := isIso_phi_subfunctor hR d.n (SemiSSet.boundary d.n) B ηB hB
    have hD' := isIso_phi_simplex hR hD
    have hglue : Top.homotopyEquivalences
        (SemiSSet.realization.map κ ≫ phiA hR YC) :=
      Packages.homotopyEquivalence_of_isPushout _ _ _ _ _ _ _ _
        (SemiSSet.realization.map ηB ≫ phiA hR B) (SemiSSet.realization.map ηD ≫ phiA hR D)
        (phiA hR XC) _ sqKR.flip sqR
        (Packages.realization_boundary_relativeFiniteCellComplex d.n).1
        (hR.isCellularRealization.map_cofibration ιC hcof)
        (hoeq_of_isIso _) (hoeq_of_isIso _) ih
        (phi_comm hR ηB ηD _ ιC hι) (phi_comm₁ hR ηB d.a abarC (by exact habar))
        (phi_comm hR ηD κ _ ybarC (by change ηD ≫ ybar.hom = _; rw [hybar, pushout.inr_desc]))
        (phi_comm₂ hR κ _ jC (pushout.inl_desc _ _ _).symm)
    obtain ⟨r, hr₁, hr₂⟩ := Packages.realization_hornCells_deformationRetract κ d.desc_mem
    exact hoeq_of_comp_left (hoeq_of_deformationRetract _ r hr₁ hr₂) hglue

end

/-- **H Lemma 5.2.6**. -/
theorem standardRealization_comparison_proof {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) :
    ∃ φ : ObjectProperty.ι AlgKan.IsFinitelyCellular.{u} ⋙ AlgKan.forget ⋙ SemiSSet.realization ⟶
      R,
      (∀ X : CDelta.{u}, Top.homotopyEquivalences (φ.app X)) ∧
      (∀ (n : ℕ) (Y : CDelta.{u}) (η : (SemiSSet.boundary.{u} n).toFunctor ⟶ Y.obj.X),
        Y.obj.IsFreeOn η → IsIso (SemiSSet.realization.map η ≫ φ.app Y)) ∧
      ∀ (n : ℕ) (Y : CDelta.{u})
        (η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y.obj.X),
        Y.obj.IsFreeOn η → IsIso (SemiSSet.realization.map η ≫ φ.app Y) :=
  ⟨phiC hR, hoeq_phi hR, fun n Y η h => isIso_phi_subfunctor hR n _ Y η h,
    fun _ _ _ h => isIso_phi_simplex hR h⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
