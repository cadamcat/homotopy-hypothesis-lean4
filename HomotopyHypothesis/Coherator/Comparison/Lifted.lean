import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexLift
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Coherator.Comparison.Nerve
import HomotopyHypothesis.Coherator.Comparison.Target
/-!
# Corepresentations along the nerve of a lifted cosimplicial object

Let `p : X ⥤ Y` be a pre-fibration and isofibration of cylinder categories and `h : C^Δ ⥤ Y` a
morphism of cylinder categories. The free simplices and the canonical horn retractions of `C^Δ`,
mapped by `h`, lift along `p` to cosimplicial data in `X` (built dimension by dimension). We show
that every object `A` of `C^Δ` is corepresented along the nerve `X ⥤ AlgKan` of the lifted data by
an object `P` lying strictly over `h A`, compatibly with the corepresentation of `A` by `h A`.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Coherator.Comparison

open HomotopyHypothesis.Henry HomotopyHypothesis.Cylinder.SimplicialCategory

section General

variable {C : Type (u + 1)} [Category.{u} C]

/-- The semi-simplicial map into a nerve given by the legs of a realization. -/
def realizationNat (D : Henry.SemiSimplexCategory ⥤ C) {M : ℕ} {F : SemiSSet.{u}}
    (hF : HasDimLe M F) (Q : SimplicialRealization (toUpTo D M) F) :
    F ⟶ nerveSemiSSet D Q.pt where
  app Δ := ↾fun x => Q.cocone.ι (unop Δ).obj.len (hF x) x
  naturality {Δ₁ Δ₂} g := by
    ext x
    have hm : (unop Δ₁).obj.len ≤ M := hF x
    have hk : (unop Δ₂).obj.len ≤ (unop Δ₁).obj.len := len_le_of_hom g.unop
    exact (Q.cocone.w hk hm g.unop x).symm

/-- A free object on a realized semi-simplicial set is corepresented by the realization. -/
lemma exists_isCorep_free (CD : CosimplicialData C) {M : ℕ} {F : SemiSSet.{u}}
    (hF : HasDimLe M F) (Q : SimplicialRealization (toUpTo CD.D M) F) {A : AlgKan.{u}}
    {η : F ⟶ A.X} (hA : A.IsFreeOn η) :
    ∃ u : A ⟶ CD.nerve.obj Q.pt, IsCorep CD.nerve A Q.pt u ∧
      ∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
        (η ≫ u.hom).app (op (Henry.SemiSimplexCategory.mk k)) x = Q.cocone.ι k hk x := by
  obtain ⟨u, hu, -⟩ := hA (CD.nerve.obj Q.pt) (realizationNat CD.D hF Q)
  have hu' : ∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      (η ≫ u.hom).app (op (Henry.SemiSimplexCategory.mk k)) x = Q.cocone.ι k hk x := by
    intro k hk x
    rw [hu]
    rfl
  exact ⟨u, IsCorep.of_isFreeOn CD hF Q hA u hu', hu'⟩

namespace CosimplicialMorphism

variable {C₁ C₂ : Type (u + 1)} [Category.{u} C₁] [Category.{u} C₂]
  {G : C₁ ⥤ C₂} {CD₁ : CosimplicialData C₁} {CD₂ : CosimplicialData C₂}
  (Φ : CosimplicialMorphism G CD₁ CD₂)

/-- The truncations of the cosimplicial objects are identified by `Φ`. -/
def diagramIso (M : ℕ) :
    DiagramIsoOn M (le_refl M) (le_refl M) ((toUpTo CD₁.D M).mapFunctor G) (toUpTo CD₂.D M) where
  iso k _ := eqToIso (Φ.obj_eq (Henry.SemiSimplexCategory.mk k))
  naturality _ _ g := by
    change G.map (CD₁.D.map g) ≫ eqToHom (Φ.obj_eq _) = eqToHom (Φ.obj_eq _) ≫ CD₂.D.map g
    rw [Φ.map_eq g]
    simp

/-- If `G` preserves a realization corepresenting a free object, then its image corepresents the
free object along the target nerve. -/
lemma isCorep_map {M : ℕ} {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q : SimplicialRealization (toUpTo CD₁.D M) F) (hGQ : IsUniversalCocone (Q.cocone.mapFunctor G))
    {A : AlgKan.{u}} {η : F ⟶ A.X} (hA : A.IsFreeOn η) (u : A ⟶ CD₁.nerve.obj Q.pt)
    (hu : ∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      (η ≫ u.hom).app (op (Henry.SemiSimplexCategory.mk k)) x = Q.cocone.ι k hk x) :
    IsCorep CD₂.nerve A (G.obj Q.pt) (u ≫ Φ.mapNerve.app Q.pt) := by
  refine IsCorep.of_isFreeOn CD₂ hF ((hGQ.toRealization).changeDiagram (Φ.diagramIso M) hF) hA _ ?_
  intro k hk x
  change eqToHom (Φ.obj_eq _).symm ≫ G.map ((η ≫ u.hom).app _ x) =
    eqToHom (Φ.obj_eq _).symm ≫ G.map (Q.cocone.ι k _ x)
  rw [hu k ((hF x).trans (le_refl M)) x]

lemma mapNerve_naturality {z₁ z₂ : C₁} (f : z₁ ⟶ z₂) :
    CD₁.nerve.map f ≫ Φ.mapNerve.app z₂ = Φ.mapNerve.app z₁ ≫ CD₂.nerve.map (G.map f) :=
  Φ.mapNerve.naturality f

end CosimplicialMorphism

end General

section Lifted

variable {X Y : Type (u + 1)} [Category.{u} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y]
  (p : X ⥤ Y) (hp : IsLiftingTarget false X Y p)
  (h : CDelta.{u} ⥤ Y) (hh : IsCylinderMorphism h)
  (x₀ : X) (hx₀ : p.obj x₀ = h.obj (stdSimplexCDelta.{u} 0))

set_option hygiene false in
local notation "𝓛" => liftedCosimplicialUpTo p hp h hh x₀ hx₀

/-- The lifted free `k`-simplex. -/
noncomputable abbrev objX (k : ℕ) : X := (𝓛 k).D.obj k (le_refl k)

include hp hh in
lemma objEq {k M : ℕ} (hk : k ≤ M) : (𝓛 M).D.obj k hk = objX p hp h hh x₀ hx₀ k := by
  induction hk with
  | refl => rfl
  | @step m hm ih => exact (liftedCosimplicialUpTo_obj_agrees p hp h hh x₀ hx₀ k hm).trans ih

/-- The lifted face maps. -/
noncomputable def mapX {k m : ℕ}
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    objX p hp h hh x₀ hx₀ k ⟶ objX p hp h hh x₀ hx₀ m :=
  eqToHom (objEq p hp h hh x₀ hx₀ (len_le_of_hom g)).symm ≫
    (𝓛 m).D.map (len_le_of_hom g) (le_refl m) g

include hp hh in
lemma mapEq {k m M : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    (𝓛 M).D.map hk hm g = eqToHom (objEq p hp h hh x₀ hx₀ (hk.trans hm)) ≫
      mapX p hp h hh x₀ hx₀ g ≫ eqToHom (objEq p hp h hh x₀ hx₀ hm).symm := by
  induction hm with
  | refl => simp [mapX]
  | @step M' hm' ih =>
    rw [liftedCosimplicialUpTo_map_agrees p hp h hh x₀ hx₀ hk hm' g, ih]
    simp

/-- The lifted cosimplicial object. -/
noncomputable def DX : Henry.SemiSimplexCategory ⥤ X where
  obj Δ := objX p hp h hh x₀ hx₀ Δ.obj.len
  map {Δ₁ Δ₂} g := mapX p hp h hh x₀ hx₀ (k := Δ₁.obj.len) (m := Δ₂.obj.len) g
  map_id Δ := by
    simp only [mapX]
    rw [(𝓛 _).D.map_id]
    simp
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    have hf : Δ₁.obj.len ≤ Δ₂.obj.len := len_le_of_hom f
    have hg : Δ₂.obj.len ≤ Δ₃.obj.len := len_le_of_hom g
    simp only [mapX]
    rw [(𝓛 _).D.map_comp hf hg (le_refl _) f g, mapEq p hp h hh x₀ hx₀ hf (hg.trans (le_refl _)) f]
    simp [mapX]

lemma DX_obj (k : ℕ) : (DX p hp h hh x₀ hx₀).obj (Henry.SemiSimplexCategory.mk k) =
    objX p hp h hh x₀ hx₀ k := rfl

/-- The truncations of the lifted cosimplicial object. -/
noncomputable def isoOn (M : ℕ) :
    DiagramIsoOn M (le_refl M) (le_refl M) (𝓛 M).D (toUpTo (DX p hp h hh x₀ hx₀) M) where
  iso k hk := eqToIso (objEq p hp h hh x₀ hx₀ hk)
  naturality {k m} hk hm g := by
    change (𝓛 M).D.map hk (hm.trans (le_refl M)) g ≫ eqToHom (objEq p hp h hh x₀ hx₀ hm) =
      eqToHom (objEq p hp h hh x₀ hx₀ (hk.trans hm)) ≫ mapX p hp h hh x₀ hx₀ g
    rw [mapEq p hp h hh x₀ hx₀ hk (hm.trans (le_refl M)) g]
    simp

/-- The chosen lifted horn retraction. -/
noncomputable def rX (n : ℕ) (k : Fin (n + 2)) :
    objX p hp h hh x₀ hx₀ (n + 1) ⟶ (liftedHornRealization p hp h hh x₀ hx₀ n k).pt :=
  (exists_liftedHornRetraction p hp h hh x₀ hx₀ n k).choose

include hp hh in
lemma rX_retraction (n : ℕ) (k : Fin (n + 2)) :
    SimplicialRealization.realizationMap (liftedHornRealization p hp h hh x₀ hx₀ n k)
      (stdSimplexRealization (𝓛 (n + 1)).D (n + 1) (le_refl (n + 1)))
      (SemiSSet.horn.{u} (n + 1) k).ι ≫ rX p hp h hh x₀ hx₀ n k = 𝟙 _ :=
  (exists_liftedHornRetraction p hp h hh x₀ hx₀ n k).choose_spec.1

include hp hh in
lemma map_rX (n : ℕ) (k : Fin (n + 2)) :
    p.map (rX p hp h hh x₀ hx₀ n k) =
      eqToHom ((𝓛 (n + 1)).p_obj (n + 1) (le_refl (n + 1))) ≫
        h.map (canonicalHornRetraction.{u} n k) ≫ (liftedHornIso p hp h hh x₀ hx₀ n k).inv :=
  (exists_liftedHornRetraction p hp h hh x₀ hx₀ n k).choose_spec.2

/-- The lifted cosimplicial data in `X`. -/
noncomputable def dataX : CosimplicialData X where
  D := DX p hp h hh x₀ hx₀
  Q_horn n k := (liftedHornRealization p hp h hh x₀ hx₀ n k).changeDiagram
    (isoOn p hp h hh x₀ hx₀ (n + 1))
    (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
  r_horn n k := rX p hp h hh x₀ hx₀ n k
  r_horn_spec n k m hm x := by
    let Q := liftedHornRealization p hp h hh x₀ hx₀ n k
    have h1 := SimplicialRealization.ι_realizationMap Q
      (stdSimplexRealization (𝓛 (n + 1)).D (n + 1) (le_refl (n + 1)))
      (SemiSSet.horn.{u} (n + 1) k).ι m hm x
    have h4 := rX_retraction p hp h hh x₀ hx₀ n k
    have h3 : (stdSimplexRealization (𝓛 (n + 1)).D (n + 1) (le_refl (n + 1))).cocone.ι m hm
        ((SemiSSet.horn.{u} (n + 1) k).ι.app _ x) ≫ rX p hp h hh x₀ hx₀ n k =
          Q.cocone.ι m hm x := by
      rw [← h1]
      erw [Category.assoc, h4, Category.comp_id]
    change (eqToHom (objEq p hp h hh x₀ hx₀ (len_le_of_hom (ULift.down x.1))).symm ≫
        (𝓛 (n + 1)).D.map (len_le_of_hom (ULift.down x.1)) (le_refl (n + 1)) (ULift.down x.1)) ≫
        rX p hp h hh x₀ hx₀ n k =
      eqToHom (objEq p hp h hh x₀ hx₀ hm).symm ≫ Q.cocone.ι m _ x
    rw [Category.assoc]
    exact congrArg _ h3

set_option hygiene false in
local notation "𝓧" => dataX p hp h hh x₀ hx₀

set_option hygiene false in
local notation "𝓨" => targetData h hh.toIsCofibrationMorphism

/-- The lifted cosimplicial data lie over the cosimplicial data of `h`. -/
theorem morphXY : CosimplicialMorphism p 𝓧 𝓨 where
  obj_eq Δ := (𝓛 Δ.obj.len).p_obj Δ.obj.len (le_refl _)
  map_eq {Δ₁ Δ₂} g := by
    change p.map (eqToHom (objEq p hp h hh x₀ hx₀ (len_le_of_hom g)).symm ≫
        (𝓛 Δ₂.obj.len).D.map (len_le_of_hom g) (le_refl _) g) =
      eqToHom ((𝓛 Δ₁.obj.len).p_obj Δ₁.obj.len (le_refl _)) ≫ h.map (stdSimplexCDeltaMap g) ≫
        eqToHom ((𝓛 Δ₂.obj.len).p_obj Δ₂.obj.len (le_refl _)).symm
    rw [p.map_comp, eqToHom_map, (𝓛 Δ₂.obj.len).p_map]
    simp
  fill_eq n k {z} α β hβ := by
    let Q := liftedHornRealization p hp h hh x₀ hx₀ n k
    have hF := hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k)
    have hpQ := isUniversalCocone_mapFunctor_liftedHornRealization p hp h hh x₀ hx₀ n k
    have key : p.map ((𝓧).hornDesc α) =
        (liftedHornIso p hp h hh x₀ hx₀ n k).hom ≫ (𝓨).hornDesc β := by
      apply (hpQ.toRealization).hom_ext
      intro m hm x
      have hX : Q.cocone.ι m hm x ≫ (𝓧).hornDesc α =
          eqToHom (objEq p hp h hh x₀ hx₀ hm) ≫ α.app _ x :=
        Q.fac _ m hm x
      have hY := (𝓨).ι_hornDesc β m hm x
      have hiso := ι_liftedRealizationIso_hom p (𝓛 (n + 1)).diagramIsoOn hF Q hpQ
        ((𝓨).Q_horn n k) hm x
      change p.map (Q.cocone.ι m hm x) ≫ p.map ((𝓧).hornDesc α) =
        p.map (Q.cocone.ι m hm x) ≫ (liftedHornIso p hp h hh x₀ hx₀ n k).hom ≫ (𝓨).hornDesc β
      erw [← p.map_comp, hX, p.map_comp, eqToHom_map, ← Category.assoc, hiso]
      change _ = (eqToHom ((𝓛 (n + 1)).p_obj m hm) ≫ ((𝓨).Q_horn n k).cocone.ι m hm x) ≫ _
      erw [Category.assoc, hY, hβ, eqToHom_trans_assoc]
      rfl
    change eqToHom ((𝓛 (n + 1)).p_obj (n + 1) (le_refl _)).symm ≫
        p.map (rX p hp h hh x₀ hx₀ n k ≫ (𝓧).hornDesc α) =
      h.map (canonicalHornRetraction.{u} n k) ≫ (𝓨).hornDesc β
    have key' : (liftedHornIso p hp h hh x₀ hx₀ n k).inv ≫ p.map ((𝓧).hornDesc α) =
        (𝓨).hornDesc β := (Iso.inv_comp_eq _).mpr key
    erw [p.map_comp, map_rX]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg _ key'

set_option hygiene false in
local notation "Θ" => (morphXY p hp h hh x₀ hx₀).mapNerve

lemma free_hom_ext {F : SemiSSet.{u}} {Z : AlgKan.{u}} {g₁ g₂ : freeAlgKan F ⟶ Z}
    (e : ∀ (k : ℕ) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      g₁.hom.app _ ((freeAlgKanUnit F).app _ x) = g₂.hom.app _ ((freeAlgKanUnit F).app _ x)) :
    g₁ = g₂ := by
  apply freeAlgKan_hom_ext
  ext Δ x
  exact e (unop Δ).obj.len x

include hp hh in
/-- Attaching a cell to a corepresented object gives a corepresented object; the corepresenting
objects differ by a cofibration, and `p` preserves the corepresentation. -/
theorem cellStep {A A' : AlgKan.{u}} (j : A ⟶ A') (hj : AlgKan.IsCellAttachment j) {P : X}
    {u₀ : A ⟶ (𝓧).nerve.obj P} (hP : IsCorep (𝓧).nerve A P u₀) :
    ∃ (P' : X) (u' : A' ⟶ (𝓧).nerve.obj P') (g : P ⟶ P'),
      IsCorep (𝓧).nerve A' P' u' ∧ cofibrations X g ∧ j ≫ u' = u₀ ≫ (𝓧).nerve.map g ∧
      (IsCorep (𝓨).nerve A (p.obj P) (u₀ ≫ (Θ).app P) →
        IsCorep (𝓨).nerve A' (p.obj P') (u' ≫ (Θ).app P')) := by
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  let d := Realization.SemisimplicialComparison.AlgKan.IsCellAttachment.data hj
  obtain ⟨abar, habar, -⟩ := freeAlgKan_isFreeOn _ A d.a
  obtain ⟨ybar, hybar, -⟩ := freeAlgKan_isFreeOn _ A' d.y
  have sq : IsPushout (boundaryCDeltaInclusion.{u} d.n).hom abar ybar j :=
    d.isPushout (freeAlgKan_isFreeOn _) (freeAlgKan_isFreeOn _)
      (freeAlgKanUnit_comp_freeAlgKanMap _) habar hybar
  have hFbd := hasDimLe_subfunctor_stdSimplex (le_refl d.n) (SemiSSet.boundary.{u} d.n)
  have hFD := hasDimLe_stdSimplex.{u} (le_refl d.n)
  let Qbd₀ := (𝓛 d.n).BData.bdRealization d.n (le_refl _)
  let Qbd : SimplicialRealization (toUpTo (𝓧).D d.n) (SemiSSet.boundary.{u} d.n).toFunctor :=
    Qbd₀.changeDiagram (isoOn p hp h hh x₀ hx₀ d.n) hFbd
  let QD : SimplicialRealization (toUpTo (𝓧).D d.n)
      (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk d.n)) :=
    stdSimplexRealization (toUpTo (𝓧).D d.n) d.n (le_refl _)
  obtain ⟨uB, hB, huB⟩ := exists_isCorep_free 𝓧 hFbd Qbd (freeAlgKan_isFreeOn _)
  obtain ⟨uD, hD, huD⟩ := exists_isCorep_free 𝓧 hFD QD (freeAlgKan_isFreeOn _)
  let f₁ := SimplicialRealization.realizationMap Qbd QD (SemiSSet.boundary.{u} d.n).ι
  have hf₁ : cofibrations X f₁ := by
    have e : f₁ = SimplicialRealization.realizationMap Qbd₀
        (stdSimplexRealization (𝓛 d.n).D d.n (le_refl _)) (SemiSSet.boundary.{u} d.n).ι ≫
          ((isoOn p hp h hh x₀ hx₀ d.n).iso d.n (le_refl d.n)).hom :=
      SimplicialRealization.realizationMap_changeDiagram_stdSimplex
        (isoOn p hp h hh x₀ hx₀ d.n) hFbd Qbd₀ (le_refl d.n) (SemiSSet.boundary.{u} d.n).ι
    rw [e]
    exact cofibrations_comp _ _ ((𝓛 d.n).BData.bdInclusion_cofibration d.n _)
      (cofibrations_of_isIso ((isoOn p hp h hh x₀ hx₀ d.n).iso d.n (le_refl d.n)).hom)
  have c₁ : (boundaryCDeltaInclusion.{u} d.n).hom ≫ uD = uB ≫ (𝓧).nerve.map f₁ := by
    apply free_hom_ext
    intro k x
    have hk : k ≤ d.n := hFbd x
    have e1 := ConcreteCategory.congr_hom (congr_app
      (freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.boundary.{u} d.n).ι)
      (op (Henry.SemiSimplexCategory.mk k))) x
    have e2 := huD k hk ((SemiSSet.boundary.{u} d.n).ι.app _ x)
    have e3 := huB k hk x
    have e4 := SimplicialRealization.ι_realizationMap Qbd QD (SemiSSet.boundary.{u} d.n).ι k hk x
    change uD.hom.app _ ((boundaryCDeltaInclusion.{u} d.n).hom.hom.app _
        ((freeAlgKanUnit _).app _ x)) =
      uB.hom.app _ ((freeAlgKanUnit _).app _ x) ≫ f₁
    refine (congrArg (uD.hom.app _) e1).trans ?_
    refine e2.trans ?_
    refine e4.symm.trans ?_
    exact congrArg (· ≫ f₁) e3.symm
  let f₂ := hB.desc (abar ≫ u₀)
  have c₂ : abar ≫ u₀ = uB ≫ (𝓧).nerve.map f₂ := (hB.fac _).symm
  have : HasPushout f₁ f₂ := IsCofibrationCategory.hasPushout f₁ f₂ hf₁
  have hPO : IsPushout f₁ f₂ (pushout.inl f₁ f₂) (pushout.inr f₁ f₂) := IsPushout.of_hasPushout f₁ f₂
  have hw : (boundaryCDeltaInclusion.{u} d.n).hom ≫ uD ≫ (𝓧).nerve.map (pushout.inl f₁ f₂) =
      abar ≫ u₀ ≫ (𝓧).nerve.map (pushout.inr f₁ f₂) := by
    erw [← Category.assoc (boundaryCDeltaInclusion.{u} d.n).hom, c₁, Category.assoc,
      ← Functor.map_comp, hPO.w, Functor.map_comp, ← Category.assoc, ← c₂, Category.assoc]
  let u' := sq.desc _ _ hw
  have d₁ : ybar ≫ u' = uD ≫ (𝓧).nerve.map (pushout.inl f₁ f₂) := sq.inl_desc _ _ hw
  have d₂ : j ≫ u' = u₀ ≫ (𝓧).nerve.map (pushout.inr f₁ f₂) := sq.inr_desc _ _ hw
  refine ⟨pushout f₁ f₂, u', pushout.inr f₁ f₂,
    IsCorep.of_isPushout sq hPO hB hD hP c₁ c₂ d₁ d₂, cofibrations_of_isPushout hPO hf₁, d₂, ?_⟩
  intro hPY
  have hBY := (morphXY p hp h hh x₀ hx₀).isCorep_map hFbd Qbd
    (isUniversalCocone_mapFunctor_changeDiagram p (isoOn p hp h hh x₀ hx₀ d.n) hFbd Qbd₀
      ((𝓛 d.n).p_preserves_bd d.n (le_refl _))) (freeAlgKan_isFreeOn _) uB huB
  have hDY := (morphXY p hp h hh x₀ hx₀).isCorep_map hFD QD
    (isUniversalCocone_mapFunctor_stdSimplexCocone p _ d.n (le_refl _))
    (freeAlgKan_isFreeOn _) uD huD
  have hPOY := hp.2.2.1.map_isPushout _ _ _ _ hPO hf₁
  have nat : ∀ {z₁ z₂ : X} (f : z₁ ⟶ z₂), (𝓧).nerve.map f ≫ (Θ).app z₂ =
      (Θ).app z₁ ≫ (𝓨).nerve.map (p.map f) :=
    fun f => (morphXY p hp h hh x₀ hx₀).mapNerve_naturality f
  refine IsCorep.of_isPushout sq hPOY hBY hDY hPY ?_ ?_ ?_ ?_
  · erw [← Category.assoc, c₁, Category.assoc, nat, Category.assoc]
  · erw [← Category.assoc, c₂, Category.assoc, nat, Category.assoc]
  · erw [← Category.assoc, d₁, Category.assoc, nat, Category.assoc]
  · erw [← Category.assoc, d₂, Category.assoc, nat, Category.assoc]

include hp hh in
/-- Every finitely cellular algebraic Kan complex is corepresented along the lifted nerve, and `p`
preserves the corepresentation. -/
theorem exists_isCorep (A : AlgKan.{u}) (hA : A.IsFinitelyCellular) :
    ∃ (P : X) (u₀ : A ⟶ (𝓧).nerve.obj P), IsCorep (𝓧).nerve A P u₀ ∧
      IsCorep (𝓨).nerve A (p.obj P) (u₀ ≫ (Θ).app P) := by
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  induction hA with
  | initial A hA =>
    obtain ⟨hA⟩ := hA
    obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := X)
    exact ⟨I, hA.to _, IsCorep.of_isInitial hA hI _,
      IsCorep.of_isInitial hA (hp.2.2.1.map_initial hI).some _⟩
  | attach j _ hj ih =>
    obtain ⟨P, u₀, hPX, hPY⟩ := ih
    obtain ⟨P', u', g, h1, -, -, h4⟩ := cellStep p hp h hh x₀ hx₀ j hj hPX
    exact ⟨P', u', h1, h4 hPY⟩

include hp hh in
/-- **Strict corepresentations.** Every object `A` of `C^Δ` is corepresented along the lifted nerve
by an object lying strictly over `h A`, compatibly with the corepresentation by `h A`. -/
theorem exists_strict (A : CDelta.{u}) :
    ∃ (P : X) (u₀ : A.obj ⟶ (𝓧).nerve.obj P), IsCorep (𝓧).nerve A.obj P u₀ ∧
      ∃ e : p.obj P = h.obj A,
        u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map (eqToHom e) = unitY h hh.toIsCofibrationMorphism A := by
  obtain ⟨P, u₀, hX, hY⟩ := exists_isCorep p hp h hh x₀ hx₀ A.obj A.property
  obtain ⟨ψ, hψ⟩ := hY.exists_iso (isCorep_unitY h hh.toIsCofibrationMorphism A)
  obtain ⟨P', e', hP', he'⟩ := hp.2.2.2.2.1 P (h.obj A) ψ
  refine ⟨P', u₀ ≫ (𝓧).nerve.map e'.hom, hX.of_iso e', hP', ?_⟩
  have nat := (morphXY p hp h hh x₀ hx₀).mapNerve_naturality e'.hom
  calc (u₀ ≫ (𝓧).nerve.map e'.hom) ≫ (Θ).app P' ≫ (𝓨).nerve.map (eqToHom hP')
      = u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map (p.map e'.hom ≫ eqToHom hP') := by
        rw [Category.assoc, ← Category.assoc ((𝓧).nerve.map e'.hom), nat, Functor.map_comp]
        simp only [Category.assoc]
    _ = u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map ψ.hom := by
        rw [he', Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = unitY h hh.toIsCofibrationMorphism A := by rw [← Category.assoc, hψ]

end Lifted

end HomotopyHypothesis.Coherator.Comparison
