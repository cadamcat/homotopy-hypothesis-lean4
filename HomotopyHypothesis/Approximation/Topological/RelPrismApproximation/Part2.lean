import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.KanSimplices.Part1
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsDerivedSubdivision
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationAnodyneDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationIsPushout
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ZeemanRelativeApproximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationExistsFiniteSubcomplex
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.Topological.A7Statements.CompactSpaceRealizationOfIsFinite
import HomotopyHypothesis.Approximation.Topological.A7Statements.IsFiniteOfFiniteObj
import HomotopyHypothesis.Approximation.Topological.A7Statements.IsFiniteOfMono
import HomotopyHypothesis.Approximation.Topological.A7Statements.IsFiniteRange
import HomotopyHypothesis.Approximation.Topological.A7Statements.IsFiniteSup
import HomotopyHypothesis.Approximation.Topological.A7Statements.IsSimplicialRealizationMap
import HomotopyHypothesis.Approximation.Topological.A7Statements.VertexMapComp
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.GlueStatements.IsFiniteOfIsPushout
import HomotopyHypothesis.Approximation.Topological.GlueStatements.IsSimplicialOfForall
import HomotopyHypothesis.Approximation.Topological.GlueStatements.MonoOfIsPushout
import HomotopyHypothesis.Approximation.Topological.GlueStatements.PushoutSimplexCases
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part1

/-!
# `HomotopyHypothesis.Approximation.Topological.RelPrismApproximation`, part 2

Lines 55–385 of `HomotopyHypothesis.Approximation.Topological.RelPrismApproximation`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem exists_relPrism_simplicialApproximation_proof {Y X : SemiSSet.{u}} (hY : Y.IsFinite)
    (J : Subfunctor Y) (g : J.toFunctor ⟶ X) (f : realization.obj Y ⟶ realization.obj X)
    (hf : realization.map J.ι ≫ f = realization.map g) :
    ∃ (S : RelPrism Y J) (f' : realization.obj S.Y' ⟶ realization.obj X),
      IsSimplicial f' ∧ realization.map S.j ≫ f' = realization.map g ∧
        (realization.map S.c₁ ≫ S.ρ ≫ f').hom.HomotopicRel f.hom
          (Set.range (realization.map J.ι).hom) := by
  obtain ⟨D⟩ := Packages.exists_derivedSubdivision.{u}
  -- a finite part `X₀` of `X` containing the image of `f` and of `g`
  haveI := compactSpace_realization_of_isFinite' hY
  obtain ⟨hinj, hfin⟩ := Packages.realization_exists_finite_subcomplex X
  obtain ⟨Y₁, hY₁f, hY₁e, f₁, hf₁⟩ := hfin (realization.obj Y) f
  let X₀ : Subfunctor X := Y₁ ⊔ Subfunctor.range g
  have hJ : SemiSSet.IsFinite J.toFunctor := isFinite_of_mono J.ι hY
  have hX₀ : SemiSSet.IsFinite X₀.toFunctor :=
    isFinite_sup _ _ (isFinite_of_finite_obj Y₁ hY₁f hY₁e) (isFinite_range g hJ)
  let i₁ : Y₁.toFunctor ⟶ X₀.toFunctor := Subfunctor.homOfLe le_sup_left
  let g₀ : J.toFunctor ⟶ X₀.toFunctor := Subfunctor.lift g le_sup_right
  have hg₀ : g₀ ≫ X₀.ι = g := Subfunctor.lift_ι _ _
  let f₀' : realization.obj Y ⟶ realization.obj X₀.toFunctor := f₁ ≫ realization.map i₁
  have hf₀' : f₀' ≫ realization.map X₀.ι = f := by
    simp only [f₀', Category.assoc, ← CategoryTheory.Functor.map_comp, i₁,
      Subfunctor.homOfLe_ι, hf₁]
  have hJf₀' : realization.map J.ι ≫ f₀' = realization.map g₀ := by
    ext p
    apply hinj X₀
    have h₁ := congrArg (fun k => k.hom p) (hf₀'.symm ▸ hf :
      realization.map J.ι ≫ f₀' ≫ realization.map X₀.ι = realization.map g)
    have h₂ := congrArg (fun k => (realization.map k).hom p) hg₀
    simp only [CategoryTheory.Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply]
      at h₁ h₂
    exact h₁.trans h₂.symm
  -- Zeeman's theorem on the second derived subdivisions
  let FJι := D.F.map J.ι
  haveI : Mono FJι := D.mono_map _ inferInstance
  let L : Subfunctor (D.F.obj Y) := Subfunctor.range FJι
  let ψ : D.F.obj J.toFunctor ⟶ L.toFunctor := Subfunctor.toRange FJι
  haveI : IsIso ψ := (Cylinder.AnodyneCells.rangeIso FJι).isIso_hom
  have hψ : ψ ≫ L.ι = FJι := Subfunctor.toRange_ι _
  let f₀ : realization.obj (D.F.obj Y) ⟶ realization.obj (D.F.obj X₀.toFunctor) :=
    D.e.hom.app Y ≫ f₀' ≫ D.e.inv.app X₀.toFunctor
  have heJ : realization.map FJι ≫ D.e.hom.app Y = D.e.hom.app J.toFunctor ≫ realization.map J.ι :=
    D.e.hom.naturality J.ι
  have heg : realization.map (D.F.map g₀) ≫ D.e.hom.app X₀.toFunctor =
      D.e.hom.app J.toFunctor ≫ realization.map g₀ := D.e.hom.naturality g₀
  have E₁ : realization.map FJι ≫ f₀ = realization.map (D.F.map g₀) := by
    have : realization.map FJι ≫ f₀ =
        (D.e.hom.app J.toFunctor ≫ realization.map g₀) ≫ D.e.inv.app X₀.toFunctor := by
      simp only [f₀, ← Category.assoc, heJ]
      simp only [Category.assoc, ← hJf₀']
    rw [this, ← heg, Category.assoc]
    erw [Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hL : IsSimplicial (realization.map L.ι ≫ f₀) := by
    have hi : realization.map (inv ψ) ≫ realization.map ψ = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    have hF : realization.map FJι = realization.map ψ ≫ realization.map L.ι := by
      rw [← CategoryTheory.Functor.map_comp, hψ]
    have h₁ : realization.map L.ι ≫ f₀ = realization.map (inv ψ) ≫ realization.map FJι ≫ f₀ := by
      rw [hF, Category.assoc, ← Category.assoc (realization.map (inv ψ)), hi, Category.id_comp]
    rw [h₁, E₁, ← CategoryTheory.Functor.map_comp]
    exact isSimplicial_realization_map _
  obtain ⟨S₁, g₁, hg₁s, hg₁j, hg₁h⟩ := Packages.zeeman_relativeApproximation
    (D.finite_complex Y hY).1 (D.finite_complex Y hY).2
    (D.finite_complex _ hX₀).1 (D.finite_complex _ hX₀).2 L f₀ hL
  -- the collar: attach the prism `P J` to the subdivision along `F J`
  let jJ : D.F.obj J.toFunctor ⟶ S₁.Y' := ψ ≫ S₁.j
  haveI := S₁.mono_j
  haveI : Mono jJ := mono_comp _ _
  have E₂ : realization.map jJ ≫ g₁ = realization.map (D.F.map g₀) := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hg₁j, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, hψ, E₁]
  let Y' := pushout jJ (D.top.app J.toFunctor)
  have sqY : IsPushout jJ (D.top.app J.toFunctor) (pushout.inl _ _ : S₁.Y' ⟶ Y')
      (pushout.inr _ _) := IsPushout.of_hasPushout _ _
  have rsqY := Packages.realization_isPushout sqY
  have hcond : realization.map jJ ≫ g₁ ≫ D.lv.app X₀.toFunctor ≫ realization.map X₀.ι =
      realization.map (D.top.app J.toFunctor) ≫ D.pr.app J.toFunctor ≫ realization.map g := by
    rw [← Category.assoc, E₂, ← Category.assoc, ← Category.assoc, D.top_pr]
    have hlv : realization.map (D.F.map g₀) ≫ D.lv.app X₀.toFunctor =
        D.lv.app J.toFunctor ≫ realization.map g₀ := D.lv.naturality g₀
    rw [hlv, Category.assoc, ← CategoryTheory.Functor.map_comp, hg₀]
  let f' : realization.obj Y' ⟶ realization.obj X :=
    rsqY.desc (g₁ ≫ D.lv.app X₀.toFunctor ≫ realization.map X₀.ι)
      (D.pr.app J.toFunctor ≫ realization.map g) hcond
  have hf'l : realization.map (pushout.inl _ _) ≫ f' =
      g₁ ≫ D.lv.app X₀.toFunctor ≫ realization.map X₀.ι := rsqY.inl_desc _ _ _
  have hf'r : realization.map (pushout.inr _ _) ≫ f' =
      D.pr.app J.toFunctor ≫ realization.map g := rsqY.inr_desc _ _ _
  -- `f'` is simplicial and equal to `‖g‖` on `J`
  have hf's : IsSimplicial f' := by
    apply isSimplicial_of_forall
    intro n d
    obtain ⟨φ₁, hφ₁⟩ := hg₁s
    rcases pushout_simplex_cases sqY n d with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨m, x, v, -, hx⟩ := hφ₁ n b
      obtain ⟨m', w, -, v', -, -, hw⟩ := D.simplex X₀.toFunctor m x
      refine ⟨m', w ≫ X₀.ι, v' ∘ v, ?_⟩
      rw [simplexChar_comp, Category.assoc, hf'l, ← Category.assoc, hx, Category.assoc,
        ← Category.assoc (simplexChar x), hw, simplexChar_comp, ← vertexMap_comp]
      simp only [Category.assoc]
    · obtain ⟨m, w, v, hw⟩ := D.pr_simplex J.toFunctor n c
      refine ⟨m, w ≫ g, v, ?_⟩
      rw [simplexChar_comp, Category.assoc, hf'r, ← Category.assoc, hw, Category.assoc,
        ← simplexChar_comp]
  let j : J.toFunctor ⟶ Y' := D.bot.app J.toFunctor ≫ pushout.inr _ _
  have hjf' : realization.map j ≫ f' = realization.map g := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hf'r, ← Category.assoc]
    erw [D.bot_pr]
    exact Category.id_comp _
  have hY' : Y'.IsFinite := isFinite_of_isPushout sqY S₁.finite (D.finite_P _ hJ)
  have hjmono : Mono j := by
    haveI := D.mono_bot J.toFunctor
    haveI : Mono (pushout.inr jJ (D.top.app J.toFunctor)) := mono_of_isPushout sqY
    exact mono_comp _ _
  -- the prism: Zeeman's prism, then the prism `P Y`
  let Z := pushout (pushout.inl jJ (D.top.app J.toFunctor)) S₁.c₀
  have sqZ : IsPushout (pushout.inl jJ (D.top.app J.toFunctor)) S₁.c₀
      (pushout.inl _ _ : Y' ⟶ Z) (pushout.inr _ _) := IsPushout.of_hasPushout _ _
  have hZ : anodyne (pushout.inl _ _ : Y' ⟶ Z) := anodyne_of_isPushout sqZ S₁.anodyne_c₀
  let Q := pushout FJι (D.top.app J.toFunctor)
  let q : Q ⟶ D.P.obj Y := pushout.desc (D.top.app Y) (D.P.map J.ι) (D.top.naturality J.ι)
  have hq : anodyne q := D.anodyne_top Y J hY
  have hr : FJι ≫ S₁.c₁ ≫ (pushout.inr _ _ : S₁.C ⟶ Z) =
      D.top.app J.toFunctor ≫ pushout.inr jJ (D.top.app J.toFunctor) ≫ pushout.inl _ _ := by
    rw [← Category.assoc (D.top.app J.toFunctor), ← pushout.condition, Category.assoc, sqZ.w,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Category.assoc, S₁.hc, ← Category.assoc, hψ]
  let r : Q ⟶ Z := pushout.desc (S₁.c₁ ≫ pushout.inr _ _)
    (pushout.inr jJ (D.top.app J.toFunctor) ≫ pushout.inl _ _) hr
  let C := pushout r q
  have sqC : IsPushout r q (pushout.inl _ _ : Z ⟶ C) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  have hC : anodyne (pushout.inl _ _ : Z ⟶ C) := anodyne_of_isPushout sqC hq
  let c₀ : Y' ⟶ C := pushout.inl _ _ ≫ pushout.inl _ _
  have hc₀ : anodyne c₀ := anodyne_comp' hZ hC
  let c₁ : Y ⟶ C := D.bot.app Y ≫ pushout.inr _ _
  have hc : j ≫ c₀ = J.ι ≫ c₁ := by
    have h₁ : J.ι ≫ D.bot.app Y = D.bot.app J.toFunctor ≫ D.P.map J.ι := D.bot.naturality J.ι
    have h₂ : D.P.map J.ι = pushout.inr _ _ ≫ q := (pushout.inr_desc _ _ _).symm
    have h₃ : (pushout.inr _ _ : D.P.obj J.toFunctor ⟶ Q) ≫ r =
        pushout.inr jJ (D.top.app J.toFunctor) ≫ pushout.inl _ _ := pushout.inr_desc _ _ _
    simp only [j, c₀, c₁, ← Category.assoc, h₁, h₂]
    simp only [Category.assoc]
    rw [← sqC.w, ← Category.assoc (pushout.inr _ _ : D.P.obj J.toFunctor ⟶ Q), h₃]
    simp only [Category.assoc]
  obtain ⟨ρ, hρ, -⟩ := Packages.realization_anodyne_deformationRetract c₀ hc₀
  refine ⟨⟨Y', hY', j, hjmono, C, c₀, c₁, hc, hc₀, ρ, hρ⟩, f', hf's, hjf', ?_⟩
  dsimp only
  -- the comparison map `p : ‖Y'‖ ⟶ ‖Y‖`
  have hjJh : realization.map jJ ≫ S₁.h.hom = realization.map FJι := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, S₁.hj, ← CategoryTheory.Functor.map_comp,
      hψ]
  have hpc : realization.map jJ ≫ S₁.h.hom ≫ D.e.hom.app Y =
      realization.map (D.top.app J.toFunctor) ≫ D.πe.app J.toFunctor ≫ realization.map J.ι := by
    rw [← Category.assoc, hjJh, heJ, ← Category.assoc, D.top_πe]
  let p : realization.obj Y' ⟶ realization.obj Y :=
    rsqY.desc (S₁.h.hom ≫ D.e.hom.app Y) (D.πe.app J.toFunctor ≫ realization.map J.ι) hpc
  have hpl : realization.map (pushout.inl _ _) ≫ p = S₁.h.hom ≫ D.e.hom.app Y :=
    rsqY.inl_desc _ _ _
  have hpr : realization.map (pushout.inr _ _) ≫ p =
      D.πe.app J.toFunctor ≫ realization.map J.ι := rsqY.inr_desc _ _ _
  -- the intermediate map `f''`
  have hcond' : realization.map jJ ≫ S₁.h.hom ≫ f₀ ≫ D.lv.app X₀.toFunctor ≫
      realization.map X₀.ι =
      realization.map (D.top.app J.toFunctor) ≫ D.pr.app J.toFunctor ≫ realization.map g := by
    rw [← hcond, ← Category.assoc, hjJh, ← Category.assoc, E₁, ← E₂, Category.assoc]
  let f'' : realization.obj Y' ⟶ realization.obj X :=
    rsqY.desc (S₁.h.hom ≫ f₀ ≫ D.lv.app X₀.toFunctor ≫ realization.map X₀.ι)
      (D.pr.app J.toFunctor ≫ realization.map g) hcond'
  have hf''l : realization.map (pushout.inl _ _) ≫ f'' =
      S₁.h.hom ≫ f₀ ≫ D.lv.app X₀.toFunctor ≫ realization.map X₀.ι := rsqY.inl_desc _ _ _
  have hf''r : realization.map (pushout.inr _ _) ≫ f'' =
      D.pr.app J.toFunctor ≫ realization.map g := rsqY.inr_desc _ _ _
  have hrange : Set.range (realization.map j).hom ⊆
      (realization.map (pushout.inr jJ (D.top.app J.toFunctor))).hom ''
        Set.range (realization.map (D.bot.app J.toFunctor)).hom := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, by simp [j]⟩
  -- stage 1: Zeeman's homotopy, followed by the last vertex map of `X₀`
  have stage₁ : f'.hom.HomotopicRel f''.hom (Set.range (realization.map j).hom) := by
    obtain ⟨G⟩ := hg₁h
    let q₀ := D.lv.app X₀.toFunctor ≫ realization.map X₀.ι
    let HB : ContinuousMap.Homotopy (realization.map (pushout.inl _ _) ≫ f').hom
        (realization.map (pushout.inl _ _) ≫ f'').hom :=
      (G.compContinuousMap q₀.hom).toHomotopy.cast (by rw [hf'l]; rfl) (by rw [hf''l]; rfl)
    let HC : ContinuousMap.HomotopyRel (realization.map (pushout.inr _ _) ≫ f').hom
        (realization.map (pushout.inr _ _) ≫ f'').hom
        (Set.range (realization.map (D.bot.app J.toFunctor)).hom) := ContinuousMap.HomotopyRel.cast
      (ContinuousMap.HomotopyRel.refl (realization.map (pushout.inr _ _) ≫ f').hom
        (Set.range (realization.map (D.bot.app J.toFunctor)).hom))
      rfl (by rw [hf'r, hf''r])
    refine homotopicRel_mono (homotopicRel_of_isPushout rsqY f' f'' HB _ HC ?_) hrange
    intro t a
    have hx : (realization.map jJ).hom a ∈ Set.range (realization.map S₁.j).hom :=
      ⟨(realization.map ψ).hom a, by simp [jJ]⟩
    have h₁ := G.eq_fst t hx
    have h₂ := congrArg (fun k => k.hom a) rsqY.w
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h₂
    calc HB (t, (realization.map jJ).hom a)
        = q₀.hom (G (t, (realization.map jJ).hom a)) := rfl
      _ = q₀.hom (g₁.hom ((realization.map jJ).hom a)) := by rw [h₁]
      _ = (realization.map (pushout.inl _ _) ≫ f').hom ((realization.map jJ).hom a) := by
          rw [hf'l]; rfl
      _ = (realization.map (pushout.inr _ _) ≫ f').hom
            ((realization.map (D.top.app J.toFunctor)).hom a) := by
          simp only [TopCat.hom_comp, ContinuousMap.comp_apply]; rw [h₂]
      _ = HC (t, (realization.map (D.top.app J.toFunctor)).hom a) := rfl
  -- stage 2: the straight-line homotopies from `lv` to `e` and from `pr` to `πe`
  have stage₂ : f''.hom.HomotopicRel (p ≫ f).hom (Set.range (realization.map j).hom) := by
    let a₀ := S₁.h.hom ≫ f₀
    have hB₁ : (realization.map (pushout.inl _ _) ≫ p ≫ f) =
        a₀ ≫ D.e.hom.app X₀.toFunctor ≫ realization.map X₀.ι := by
      rw [← Category.assoc, hpl]
      simp only [a₀, f₀, Category.assoc]
      erw [Iso.inv_hom_id_app_assoc]
      rw [hf₀']
    let HB : ContinuousMap.Homotopy (realization.map (pushout.inl _ _) ≫ f'').hom
        (realization.map (pushout.inl _ _) ≫ p ≫ f).hom :=
      (((ContinuousMap.Homotopy.refl (realization.map X₀.ι).hom).comp
        (D.H X₀.toFunctor)).compContinuousMap a₀.hom).cast
        (by rw [hf''l]; rfl) (by rw [hB₁]; rfl)
    have hC₁ : (realization.map (pushout.inr _ _) ≫ p ≫ f) =
        D.πe.app J.toFunctor ≫ realization.map g := by
      rw [← Category.assoc, hpr, Category.assoc, hf]
    let HC : ContinuousMap.HomotopyRel (realization.map (pushout.inr _ _) ≫ f'').hom
        (realization.map (pushout.inr _ _) ≫ p ≫ f).hom
        (Set.range (realization.map (D.bot.app J.toFunctor)).hom) :=
      ((D.K J.toFunctor).compContinuousMap (realization.map g).hom).cast
        (by rw [hf''r]; rfl) (by rw [hC₁]; rfl)
    refine homotopicRel_mono (homotopicRel_of_isPushout rsqY f'' (p ≫ f) HB _ HC ?_) hrange
    intro t a
    have h₁ : a₀.hom ((realization.map jJ).hom a) =
        (realization.map (D.F.map g₀)).hom a := by
      have := congrArg (fun k => k.hom a) (show realization.map jJ ≫ a₀ =
        realization.map (D.F.map g₀) by simp only [a₀, ← Category.assoc, hjJh, E₁])
      simpa using this
    have h₂ := D.H_natural g₀ t a
    have h₃ := D.K_top J.toFunctor t a
    calc HB (t, (realization.map jJ).hom a)
        = (realization.map X₀.ι).hom (D.H X₀.toFunctor (t, a₀.hom ((realization.map jJ).hom a))) :=
          rfl
      _ = (realization.map X₀.ι).hom ((realization.map g₀).hom (D.H J.toFunctor (t, a))) := by
          rw [h₁, h₂]
      _ = (realization.map g).hom (D.K J.toFunctor (t, (realization.map
            (D.top.app J.toFunctor)).hom a)) := by
          rw [h₃, ← hg₀, CategoryTheory.Functor.map_comp]; rfl
      _ = HC (t, (realization.map (D.top.app J.toFunctor)).hom a) := rfl
  have hb : f'.hom.HomotopicRel (p ≫ f).hom (Set.range (realization.map j).hom) :=
    stage₁.trans stage₂
  -- the projection `Π` of the prism onto `‖Y‖`
  have sqQ : IsPushout FJι (D.top.app J.toFunctor) (pushout.inl _ _ : D.F.obj Y ⟶ Q)
      (pushout.inr _ _) := IsPushout.of_hasPushout _ _
  have rsqZ := Packages.realization_isPushout sqZ
  have rsqQ := Packages.realization_isPushout sqQ
  have rsqC := Packages.realization_isPushout sqC
  have hPZ : realization.map (pushout.inl jJ (D.top.app J.toFunctor)) ≫ p =
      realization.map S₁.c₀ ≫ S₁.ρ ≫ S₁.h.hom ≫ D.e.hom.app Y := by
    rw [hpl, ← Category.assoc, S₁.hρ₀, Category.id_comp]
  let PZ : realization.obj Z ⟶ realization.obj Y :=
    rsqZ.desc p (S₁.ρ ≫ S₁.h.hom ≫ D.e.hom.app Y) hPZ
  have hPZl : realization.map (pushout.inl _ _ : Y' ⟶ Z) ≫ PZ = p := rsqZ.inl_desc _ _ _
  have hPZr : realization.map (pushout.inr _ _ : S₁.C ⟶ Z) ≫ PZ =
      S₁.ρ ≫ S₁.h.hom ≫ D.e.hom.app Y := rsqZ.inr_desc _ _ _
  have hPi : realization.map r ≫ PZ = realization.map q ≫ D.πe.app Y := by
    apply rsqQ.hom_ext
    · have e1 : realization.map (pushout.inl _ _ : D.F.obj Y ⟶ Q) ≫ realization.map r =
          realization.map S₁.c₁ ≫ realization.map (pushout.inr _ _ : S₁.C ⟶ Z) := by
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
          pushout.inl_desc]
      have e2 : realization.map (pushout.inl _ _ : D.F.obj Y ⟶ Q) ≫ realization.map q =
          realization.map (D.top.app Y) := by
        rw [← CategoryTheory.Functor.map_comp, pushout.inl_desc]
      rw [← Category.assoc, e1, Category.assoc, hPZr, ← Category.assoc (realization.map S₁.c₁),
        S₁.hρ₁, Iso.inv_hom_id_assoc, ← Category.assoc, e2, D.top_πe]
    · have e1 : realization.map (pushout.inr _ _ : D.P.obj J.toFunctor ⟶ Q) ≫ realization.map r =
          realization.map (pushout.inr jJ (D.top.app J.toFunctor)) ≫
            realization.map (pushout.inl _ _ : Y' ⟶ Z) := by
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
          pushout.inr_desc]
      have e2 : realization.map (pushout.inr _ _ : D.P.obj J.toFunctor ⟶ Q) ≫
          realization.map q = realization.map (D.P.map J.ι) := by
        rw [← CategoryTheory.Functor.map_comp, pushout.inr_desc]
      have e3 : realization.map (D.P.map J.ι) ≫ D.πe.app Y =
          D.πe.app J.toFunctor ≫ realization.map J.ι := D.πe.naturality J.ι
      rw [← Category.assoc, e1, Category.assoc, hPZl, hpr, ← Category.assoc, e2, e3]
  let Pi : realization.obj C ⟶ realization.obj Y := rsqC.desc PZ (D.πe.app Y) hPi
  have hc₀Pi : realization.map c₀ ≫ Pi = p := by
    simp only [c₀, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [rsqC.inl_desc, hPZl]
  have hc₁Pi : realization.map c₁ ≫ Pi = 𝟙 _ := by
    simp only [c₁, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [rsqC.inr_desc]
    exact D.bot_πe Y
  -- conclusion
  have hS₂ : ∀ x ∈ Set.range (realization.map J.ι).hom,
      (realization.map c₁ ≫ ρ).hom x ∈ Set.range (realization.map j).hom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    have h₁ := congrArg (fun k => (realization.map k ≫ ρ).hom x) hc
    have h₂ := congrArg (fun k => (realization.map j ≫ k).hom x) hρ
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, TopCat.hom_comp,
      ContinuousMap.comp_apply] at h₁ h₂
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
    rw [← h₁, h₂]
    rfl
  have hS₁ : ∀ x ∈ Set.range (realization.map J.ι).hom,
      (realization.map c₁).hom x ∈ Set.range (realization.map c₀).hom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(realization.map j).hom x, ?_⟩
    have := congrArg (fun k => (realization.map k).hom x) hc
    simpa using this
  have h₁ := homotopicRel_comp_right hb (realization.map c₁ ≫ ρ).hom hS₂
  have h₁' : (realization.map c₁ ≫ ρ ≫ f').hom.HomotopicRel
      (realization.map c₁ ≫ ρ ≫ p ≫ f).hom (Set.range (realization.map J.ι).hom) := by
    simpa using h₁
  have h₃ := homotopicRel_of_anodyne c₀ hc₀ (Pi ≫ f) ρ hρ
  have h₄ := homotopicRel_comp_right h₃ (realization.map c₁).hom hS₁
  have e₁ : realization.map c₁ ≫ Pi ≫ f = f := by
    rw [← Category.assoc, hc₁Pi, Category.id_comp]
  have e₂ : realization.map c₁ ≫ ρ ≫ realization.map c₀ ≫ Pi ≫ f =
      realization.map c₁ ≫ ρ ≫ p ≫ f := by
    rw [← Category.assoc (realization.map c₀), hc₀Pi]
  have h₄' : f.hom.HomotopicRel (realization.map c₁ ≫ ρ ≫ p ≫ f).hom
      (Set.range (realization.map J.ι).hom) := by
    have h₄'' := h₄
    rw [← TopCat.hom_comp, ← TopCat.hom_comp, e₁, e₂] at h₄''
    exact h₄''
  exact h₁'.trans h₄'.symm
