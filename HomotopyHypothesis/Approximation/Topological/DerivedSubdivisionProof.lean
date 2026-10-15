import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationIsPushout
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.A7Statements.VertexMapComp
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.AnodynePrismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsFiniteDprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsFiniteOfIso
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsSimplicialComplexOfIso
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.MonoDprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismBot
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismTopology.ExistsDprismProjections
import HomotopyHypothesis.Approximation.Topological.DerivedSubdivisionCompare.NonemptySdLanIso
import HomotopyHypothesis.Approximation.Topological.GlueStatements.ExistsHomotopyOfIsPushout
import HomotopyHypothesis.Approximation.Topological.GlueStatements.IsFiniteOfIsPushout
import HomotopyHypothesis.Approximation.Topological.GlueStatements.MonoOfIsPushout
import HomotopyHypothesis.Approximation.Topological.GlueStatements.PushoutSimplexCases
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
/-!
# The second derived subdivision with its prism

Assembly of `exists_derivedSubdivision`: `F = (−)''` (the derived subdivision applied twice, which
is the nerve of strict chains of faces, an ordered simplicial complex), `e` and `lv` the composites
of the barycentric and last vertex maps of the two derived cylinders, and the prism
`P W = D W ⊔_{W'} D W'` with the projections glued from those of the two derived cylinders.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

section Assembly

variable (pr πe : dprismLan.{u} ⋙ realization ⟶ realization)

/-- The barycentric map `‖V'‖ ⟶ ‖V‖`. -/
noncomputable def baryMap : sdLan.{u} ⋙ realization ⟶ realization where
  app V := realization.map (sdLanToDprism.app V) ≫ πe.app V
  naturality V V' φ := by
    change realization.map (sdLan.map φ) ≫ _ ≫ _ = (_ ≫ _) ≫ realization.map φ
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, sdLanToDprism.naturality,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact πe.naturality φ

theorem rsqP (W : SemiSSet.{u}) :
    IsPushout (realization.map (sdLanToDprism.app W))
      (realization.map (dprismLanTop.app (sdLan.obj W)))
      (realization.map (pushout.inl _ _ : _ ⟶ prismP.obj W))
      (realization.map (pushout.inr _ _ : _ ⟶ prismP.obj W)) :=
  Packages.realization_isPushout (IsPushout.of_hasPushout _ _)

variable {pr πe}

/-- The inclusions of the two derived cylinders into the prism. -/
noncomputable abbrev pInl (W : SemiSSet.{u}) : dprismLan.obj W ⟶ prismP.obj W :=
  pushout.inl (sdLanToDprism.app W) (dprismLanTop.app (sdLan.obj W))

noncomputable abbrev pInr (W : SemiSSet.{u}) : dprismLan.obj (sdLan.obj W) ⟶ prismP.obj W :=
  pushout.inr (sdLanToDprism.app W) (dprismLanTop.app (sdLan.obj W))

@[reassoc]
theorem pInl_map {W V : SemiSSet.{u}} (φ : W ⟶ V) :
    realization.map (pInl W) ≫ realization.map (prismP.map φ) =
      realization.map (dprismLan.map φ) ≫ realization.map (pInl V) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg realization.map (pushout.inl_desc _ _ _)

@[reassoc]
theorem pInr_map {W V : SemiSSet.{u}} (φ : W ⟶ V) :
    realization.map (pInr W) ≫ realization.map (prismP.map φ) =
      realization.map (dprismLan.map (sdLan.map φ)) ≫ realization.map (pInr V) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg realization.map (pushout.inr_desc _ _ _)

/-- A projection of the prism glued from projections of the two derived cylinders. -/
noncomputable def prismProjApp (q : dprismLan.{u} ⋙ realization ⟶ realization)
    (hq : ∀ V, realization.map (dprismLanTop.app V) ≫ q.app V = 𝟙 _) (W : SemiSSet.{u}) :
    realization.obj (prismP.obj W) ⟶ realization.obj W :=
  (rsqP W).desc (q.app W) (q.app (sdLan.obj W) ≫ (baryMap q).app W) (by
    rw [← Category.assoc, hq]
    exact (Category.id_comp _).symm)

@[reassoc]
theorem inl_prismProjApp (q : dprismLan.{u} ⋙ realization ⟶ realization)
    (hq : ∀ V, realization.map (dprismLanTop.app V) ≫ q.app V = 𝟙 _) (W : SemiSSet.{u}) :
    realization.map (pInl W) ≫ prismProjApp q hq W = q.app W :=
  (rsqP W).inl_desc _ _ _

@[reassoc]
theorem inr_prismProjApp (q : dprismLan.{u} ⋙ realization ⟶ realization)
    (hq : ∀ V, realization.map (dprismLanTop.app V) ≫ q.app V = 𝟙 _) (W : SemiSSet.{u}) :
    realization.map (pInr W) ≫ prismProjApp q hq W = q.app (sdLan.obj W) ≫ (baryMap q).app W :=
  (rsqP W).inr_desc _ _ _

/-- A projection of the prism, as a natural transformation. -/
noncomputable def prismProj (q : dprismLan.{u} ⋙ realization ⟶ realization)
    (hq : ∀ V, realization.map (dprismLanTop.app V) ≫ q.app V = 𝟙 _) :
    prismP.{u} ⋙ realization ⟶ realization where
  app := prismProjApp q hq
  naturality W V φ := by
    change realization.map (prismP.map φ) ≫ _ = _ ≫ realization.map φ
    apply (rsqP W).hom_ext
    · erw [pInl_map_assoc, inl_prismProjApp, inl_prismProjApp_assoc]
      exact q.naturality φ
    · erw [pInr_map_assoc, inr_prismProjApp, inr_prismProjApp_assoc]
      have h₂ : realization.map (dprismLan.map (sdLan.map φ)) ≫ q.app (sdLan.obj V) =
          q.app (sdLan.obj W) ≫ realization.map (sdLan.map φ) := q.naturality (sdLan.map φ)
      rw [reassoc_of% h₂]
      congr 1
      exact (baryMap q).naturality φ

end Assembly

section Homotopy

variable {pr πe : dprismLan.{u} ⋙ realization ⟶ realization}
  (htop_pr : ∀ V, realization.map (dprismLanTop.app V) ≫ pr.app V = 𝟙 _)
  (htop_πe : ∀ V, realization.map (dprismLanTop.app V) ≫ πe.app V = 𝟙 _)
  (K : ∀ V : SemiSSet.{u}, ContinuousMap.HomotopyRel (pr.app V).hom (πe.app V).hom
    (Set.range (realization.map (dprismLanTop.app V)).hom))

/-- The straight-line homotopy on `‖V'‖` from the last vertex map to the barycentric map. -/
noncomputable def lineH (V : SemiSSet.{u}) :
    ContinuousMap.Homotopy ((baryMap pr).app V).hom ((baryMap πe).app V).hom :=
  (K V).toHomotopy.compContinuousMap (realization.map (sdLanToDprism.app V)).hom

include htop_pr htop_πe in
/-- The homotopy on the prism from the simplicial to the affine projection: on `D W` it waits, then
runs the straight line; on `D W'` it runs the straight line of `D W'` followed by the last vertex
map of `W`, then the barycentric map of `W'` followed by the straight line on `‖W'‖`. -/
theorem exists_prismHomotopy (W : SemiSSet.{u}) :
    ∃ H : ContinuousMap.HomotopyRel ((prismProj pr htop_pr).app W).hom
        ((prismProj πe htop_πe).app W).hom
        (Set.range (realization.map (prismBot.app W)).hom),
      ∀ (t : unitInterval) (y : realization.obj (dprismLan.obj (sdLan.obj W))),
        H (t, (realization.map (pInr W)).hom y) =
          (((ContinuousMap.Homotopy.refl ((baryMap pr).app W).hom).comp
            (K (sdLan.obj W)).toHomotopy).trans
            ((lineH K W).compContinuousMap (πe.app (sdLan.obj W)).hom)) (t, y) := by
  let HB : ContinuousMap.Homotopy (realization.map (pInl W) ≫ (prismProj pr htop_pr).app W).hom
      (realization.map (pInl W) ≫ (prismProj πe htop_πe).app W).hom :=
    ((ContinuousMap.Homotopy.refl (pr.app W).hom).trans (K W).toHomotopy).cast
      (by erw [inl_prismProjApp pr htop_pr W]) (by erw [inl_prismProjApp πe htop_πe W])
  let HC : ContinuousMap.Homotopy (realization.map (pInr W) ≫ (prismProj pr htop_pr).app W).hom
      (realization.map (pInr W) ≫ (prismProj πe htop_πe).app W).hom :=
    (((ContinuousMap.Homotopy.refl ((baryMap pr).app W).hom).comp
      (K (sdLan.obj W)).toHomotopy).trans
      ((lineH K W).compContinuousMap (πe.app (sdLan.obj W)).hom)).cast
      (by erw [inr_prismProjApp pr htop_pr W]; rfl) (by erw [inr_prismProjApp πe htop_πe W]; rfl)
  have hBC : ∀ (t : unitInterval) (s : realization.obj (sdLan.obj W)),
      HB (t, (realization.map (sdLanToDprism.app W)).hom s) =
        HC (t, (realization.map (dprismLanTop.app (sdLan.obj W))).hom s) := by
    intro t s
    have hs : (realization.map (dprismLanTop.app (sdLan.obj W))).hom s ∈
        Set.range (realization.map (dprismLanTop.app (sdLan.obj W))).hom := ⟨s, rfl⟩
    have h₁ : ∀ u, K (sdLan.obj W) (u, (realization.map (dprismLanTop.app (sdLan.obj W))).hom s) =
        s := by
      intro u
      rw [(K (sdLan.obj W)).eq_fst u hs]
      exact congrArg (fun k => k.hom s) (htop_pr (sdLan.obj W))
    have h₂ : (πe.app (sdLan.obj W)).hom
        ((realization.map (dprismLanTop.app (sdLan.obj W))).hom s) = s :=
      congrArg (fun k => k.hom s) (htop_πe (sdLan.obj W))
    simp only [HB, HC, ContinuousMap.Homotopy.cast_apply, ContinuousMap.Homotopy.trans_apply,
      ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply,
      ContinuousMap.Homotopy.compContinuousMap_apply, ContinuousMap.HomotopyWith.coe_toHomotopy]
    split_ifs
    · erw [h₁]
      rfl
    · erw [h₂]
      rfl
  obtain ⟨H, hHB, hHC⟩ := exists_homotopy_of_isPushout (rsqP W) _ _ HB HC hBC
  refine ⟨⟨H, ?_⟩, fun t y => hHC t y⟩
  rintro t _ ⟨w, rfl⟩
  have hw : (realization.map (dprismLanTop.app W)).hom w ∈
      Set.range (realization.map (dprismLanTop.app W)).hom := ⟨w, rfl⟩
  have e₁ : (realization.map (prismBot.app W)).hom w =
      (realization.map (pInl W)).hom ((realization.map (dprismLanTop.app W)).hom w) := by
    change (realization.map (dprismLanTop.app W ≫ pInl W)).hom w = _
    rw [CategoryTheory.Functor.map_comp]
    rfl
  rw [e₁]
  refine (hHB t _).trans ?_
  have e₂ := congrArg (fun k => k.hom ((realization.map (dprismLanTop.app W)).hom w))
    (inl_prismProjApp pr htop_pr W)
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at e₂
  change _ = ((prismProjApp pr htop_pr W)).hom _
  rw [e₂]
  change ((ContinuousMap.Homotopy.refl (pr.app W).hom).trans (K W).toHomotopy) (t, _) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · rfl
  · exact (K W).eq_fst _ hw

end Homotopy

theorem isLinearEmbedding_comp {n m k : ℕ}
    {le : toTop.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ toTop.obj (Henry.SemiSimplexCategory.mk m)}
    {le' : toTop.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ toTop.obj (Henry.SemiSimplexCategory.mk k)}
    (h : IsLinearEmbedding le) (h' : IsLinearEmbedding le') : IsLinearEmbedding (le ≫ le') :=
  ⟨h'.1.comp h.1, h'.2.comp h.2⟩

/-- The homotopy of the derived cylinder of `W'` followed by the last vertex map, then the
barycentric map followed by the straight line on `‖W'‖`, is natural. -/
theorem prismHC_natural {pr πe : dprismLan.{u} ⋙ realization ⟶ realization}
    (K : ∀ V : SemiSSet.{u}, ContinuousMap.HomotopyRel (pr.app V).hom (πe.app V).hom
      (Set.range (realization.map (dprismLanTop.app V)).hom))
    (hK : ∀ {V V' : SemiSSet.{u}} (φ : V ⟶ V') (t : unitInterval)
      (x : realization.obj (dprismLan.obj V)),
      K V' (t, (realization.map (dprismLan.map φ)).hom x) = (realization.map φ).hom (K V (t, x)))
    {W W' : SemiSSet.{u}} (φ : W ⟶ W') (t : unitInterval)
    (y : realization.obj (dprismLan.obj (sdLan.obj W))) :
    (((ContinuousMap.Homotopy.refl ((baryMap pr).app W').hom).comp
        (K (sdLan.obj W')).toHomotopy).trans
        ((lineH K W').compContinuousMap (πe.app (sdLan.obj W')).hom))
      (t, (realization.map (dprismLan.map (sdLan.map φ))).hom y) =
    (realization.map φ).hom ((((ContinuousMap.Homotopy.refl ((baryMap pr).app W).hom).comp
        (K (sdLan.obj W)).toHomotopy).trans
        ((lineH K W).compContinuousMap (πe.app (sdLan.obj W)).hom)) (t, y)) := by
  have nL : ∀ z, ((baryMap pr).app W').hom ((realization.map (sdLan.map φ)).hom z) =
      (realization.map φ).hom (((baryMap pr).app W).hom z) := fun z => by
    have := congrArg (fun k => k.hom z) ((baryMap pr).naturality φ)
    simpa using this
  have nπ : ∀ z, (πe.app (sdLan.obj W')).hom
      ((realization.map (dprismLan.map (sdLan.map φ))).hom z) =
      (realization.map (sdLan.map φ)).hom ((πe.app (sdLan.obj W)).hom z) := fun z => by
    have := congrArg (fun k => k.hom z) (πe.naturality (sdLan.map φ))
    simpa using this
  have nα : ∀ z, (realization.map (sdLanToDprism.app W')).hom
      ((realization.map (sdLan.map φ)).hom z) =
      (realization.map (dprismLan.map φ)).hom ((realization.map (sdLanToDprism.app W)).hom z) :=
    fun z => by
      have := congrArg (fun k => (realization.map k).hom z) (sdLanToDprism.naturality φ)
      simp only [CategoryTheory.Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply]
        at this
      exact this
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · simp only [ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply,
      ContinuousMap.HomotopyWith.coe_toHomotopy]
    rw [hK, nL]
  · show (K W') (_, (realization.map (sdLanToDprism.app W')).hom ((πe.app (sdLan.obj W')).hom
        ((realization.map (dprismLan.map (sdLan.map φ))).hom y))) =
      (realization.map φ).hom ((K W) (_, (realization.map (sdLanToDprism.app W)).hom
        ((πe.app (sdLan.obj W)).hom y)))
    rw [nπ, nα, hK]

theorem exists_derivedSubdivision_proof : Nonempty DerivedSubdivision.{u} := by
  obtain ⟨Φ⟩ := nonempty_sdLanIso.{u}
  obtain ⟨pr, πe, K, htop_pr, htop_πe, hpr_s, hsd_s, hiso, hK⟩ := exists_dprismProjections.{u}
  haveI : IsIso (baryMap πe) := by
    haveI : ∀ V, IsIso ((baryMap πe).app V) := hiso
    exact NatIso.isIso_of_isIso_app _
  let e₁ : sdLan.{u} ⋙ realization ≅ realization := asIso (baryMap πe)
  let L₁ := baryMap pr
  let KP := fun W => (exists_prismHomotopy htop_pr htop_πe K W).choose
  have hKP := fun W => (exists_prismHomotopy htop_pr htop_πe K W).choose_spec
  have tpr : ∀ W : SemiSSet.{u}, realization.map (prismTop.app W) ≫ (prismProj pr htop_pr).app W =
      (Functor.whiskerLeft sdLan L₁ ≫ L₁).app W := by
    intro W
    change realization.map (sdLanToDprism.app (sdLan.obj W) ≫ pInr W) ≫ prismProjApp pr htop_pr W = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc, inr_prismProjApp]
    rfl
  have tπe : ∀ W : SemiSSet.{u}, realization.map (prismTop.app W) ≫ (prismProj πe htop_πe).app W =
      (Functor.isoWhiskerLeft sdLan e₁ ≪≫ e₁).hom.app W := by
    intro W
    change realization.map (sdLanToDprism.app (sdLan.obj W) ≫ pInr W) ≫ prismProjApp πe htop_πe W = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc, inr_prismProjApp]
    rfl
  have bpr : ∀ (q : dprismLan.{u} ⋙ realization ⟶ realization)
      (hq : ∀ V, realization.map (dprismLanTop.app V) ≫ q.app V = 𝟙 _) (W : SemiSSet.{u}),
      realization.map (prismBot.app W) ≫ (prismProj q hq).app W = 𝟙 _ := by
    intro q hq W
    change realization.map (dprismLanTop.app W ≫ pInl W) ≫ prismProjApp q hq W = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc, inl_prismProjApp, hq]
  have hsd : ∀ W : SemiSSet.{u}, W.IsFinite → (sdLan.obj W).IsFinite := fun W hW =>
    isFinite_of_iso (Φ.app W) (Simplicial.BarycentricSubdivision.firstSubdivision_isFinite hW)
  let ψ : ∀ W : SemiSSet.{u}, (sdLan ⋙ sdLan).obj W ≅ Simplicial.BarycentricSubdivision.secondSubdivision.obj W :=
    fun W => Φ.app (sdLan.obj W) ≪≫ Simplicial.BarycentricSubdivision.firstSubdivision.mapIso (Φ.app W)
  have hψ : ∀ {A B : SemiSSet.{u}} (φ : A ⟶ B),
      (sdLan ⋙ sdLan).map φ ≫ (ψ B).hom = (ψ A).hom ≫ Simplicial.BarycentricSubdivision.secondSubdivision.map φ := by
    intro A B φ
    show sdLan.map (sdLan.map φ) ≫ Φ.hom.app (sdLan.obj B) ≫
        Simplicial.BarycentricSubdivision.firstSubdivision.map (Φ.hom.app B) =
      (Φ.hom.app (sdLan.obj A) ≫ Simplicial.BarycentricSubdivision.firstSubdivision.map (Φ.hom.app A)) ≫
        Simplicial.BarycentricSubdivision.firstSubdivision.map (Simplicial.BarycentricSubdivision.firstSubdivision.map φ)
    rw [← Category.assoc, Φ.hom.naturality (sdLan.map φ), Category.assoc,
      ← Simplicial.BarycentricSubdivision.firstSubdivision.map_comp, Φ.hom.naturality φ, Simplicial.BarycentricSubdivision.firstSubdivision.map_comp,
      Category.assoc]
  refine ⟨{
    F := sdLan ⋙ sdLan
    e := Functor.isoWhiskerLeft sdLan e₁ ≪≫ e₁
    lv := Functor.whiskerLeft sdLan L₁ ≫ L₁
    finite_complex := fun W hW =>
      ⟨isFinite_of_iso (ψ W) (Simplicial.BarycentricSubdivision.secondSubdivision_isFinite hW),
        isSimplicialComplex_of_iso (ψ W) (Simplicial.BarycentricSubdivision.secondSubdivision_obj_isSimplicialComplex W)⟩
    mono_map := fun {A B} φ hφ => by
      haveI := hφ
      haveI := Simplicial.BarycentricSubdivision.secondSubdivision_map_mono φ
      have : Mono ((sdLan ⋙ sdLan).map φ ≫ (ψ B).hom) := by
        rw [hψ]
        infer_instance
      exact mono_of_mono _ (ψ B).hom
    simplex := fun W n y => by
      obtain ⟨m₁, c, le₁, v₁, hle₁, he₁, hl₁⟩ := hsd_s (sdLan.obj W) n y
      obtain ⟨m, w, le₂, v₂, hle₂, he₂, hl₂⟩ := hsd_s W m₁ c
      refine ⟨m, w, le₁ ≫ le₂, v₂ ∘ v₁, isLinearEmbedding_comp hle₁ hle₂, ?_, ?_⟩
      · change simplexChar y ≫ (baryMap πe).app (sdLan.obj W) ≫ (baryMap πe).app W = _
        rw [← Category.assoc]
        erw [he₁]
        rw [Category.assoc]
        erw [he₂]
        rw [Category.assoc]
      · change simplexChar y ≫ (baryMap pr).app (sdLan.obj W) ≫ (baryMap pr).app W = _
        rw [← Category.assoc]
        erw [hl₁]
        rw [Category.assoc]
        erw [hl₂]
        rw [← Category.assoc, vertexMap_comp]
    H := fun W => ((KP W).toHomotopy.compContinuousMap
      (realization.map (prismTop.app W)).hom).cast
        (by rw [← TopCat.hom_comp, tpr]) (by rw [← TopCat.hom_comp, tπe])
    H_natural := fun {W W'} φ t x => by
      change KP W' (t, (realization.map (prismTop.app W')).hom
        ((realization.map ((sdLan ⋙ sdLan).map φ)).hom x)) =
        (realization.map φ).hom (KP W (t, (realization.map (prismTop.app W)).hom x))
      have hx : ∀ (V : SemiSSet.{u}) (z : realization.obj ((sdLan ⋙ sdLan).obj V)),
          (realization.map (prismTop.app V)).hom z = (realization.map (pInr V)).hom
            ((realization.map (sdLanToDprism.app (sdLan.obj V))).hom z) := by
        intro V z
        change (realization.map (sdLanToDprism.app (sdLan.obj V) ≫ pInr V)).hom z = _
        rw [CategoryTheory.Functor.map_comp]
        rfl
      have nα : (realization.map (sdLanToDprism.app (sdLan.obj W'))).hom
          ((realization.map ((sdLan ⋙ sdLan).map φ)).hom x) =
          (realization.map (dprismLan.map (sdLan.map φ))).hom
            ((realization.map (sdLanToDprism.app (sdLan.obj W))).hom x) := by
        have := congrArg (fun k => (realization.map k).hom x)
          (sdLanToDprism.naturality (sdLan.map φ))
        simp only [CategoryTheory.Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply]
          at this
        exact this
      rw [hx, hx, hKP W', hKP W, nα]
      exact prismHC_natural K hK φ t _
    P := prismP
    top := prismTop
    bot := prismBot
    mono_bot := fun W => by
      haveI := mono_dprismLanTop W
      haveI := mono_dprismLanTop (sdLan.obj W)
      haveI : Mono (pInl W) :=
        mono_of_isPushout (IsPushout.of_hasPushout (sdLanToDprism.app W)
          (dprismLanTop.app (sdLan.obj W))).flip
      exact mono_comp _ _
    finite_P := fun W hW => isFinite_of_isPushout (IsPushout.of_hasPushout (sdLanToDprism.app W)
      (dprismLanTop.app (sdLan.obj W))) (isFinite_dprismLan hW) (isFinite_dprismLan (hsd W hW))
    anodyne_top := fun W J hW => anodyne_prismTop W J hW
    pr := prismProj pr htop_pr
    pr_simplex := fun W n z => by
      rcases pushout_simplex_cases (IsPushout.of_hasPushout (sdLanToDprism.app W)
        (dprismLanTop.app (sdLan.obj W))) n z with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · obtain ⟨m, w, v, h⟩ := hpr_s W n b
        refine ⟨m, w, v, ?_⟩
        erw [simplexChar_comp, Category.assoc, inl_prismProjApp pr htop_pr W]
        exact h
      · obtain ⟨m₁, c', v₁, h₁⟩ := hpr_s (sdLan.obj W) n c
        obtain ⟨m, w, -, v₂, -, -, h₂⟩ := hsd_s W m₁ c'
        refine ⟨m, w, v₂ ∘ v₁, ?_⟩
        erw [simplexChar_comp, Category.assoc, inr_prismProjApp pr htop_pr W]
        rw [← Category.assoc, h₁, Category.assoc]
        erw [h₂]
        rw [← Category.assoc, vertexMap_comp]
    top_pr := tpr
    bot_pr := bpr pr htop_pr
    πe := prismProj πe htop_πe
    top_πe := tπe
    bot_πe := bpr πe htop_πe
    K := fun W => KP W
    K_top := fun W t x => rfl }⟩

end HomotopyHypothesis.Approximation.Topological
