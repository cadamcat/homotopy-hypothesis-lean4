import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Acyclic
import HomotopyHypothesis.Homotopy.TwoOutOfSix.Homotopy
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
/-!
# Acyclic morphisms of cylinder categories satisfy 2-out-of-6

H Prop 2.3.6 (H:970). Following H Prop 2.3.4 (H:879), a morphism `F` of cylinder categories is
acyclic iff it induces an equivalence `hF : hC ⥤ hD` of homotopy categories. We phrase the latter
condition directly on representatives (`IsHEquiv`): `F` is homotopy surjective, and full and
faithful up to homotopy. Since equivalences of categories satisfy 2-out-of-6, so do acyclic
morphisms.

For the direction "`hF` an equivalence ⇒ `F` homotopy fully faithful" we follow the proof of
H Prop 2.3.4 (3 ⇒ 2 ⇒ 1): `F` detects weak equivalences, the coslice morphisms `F_A` are
homotopy surjective (strictly under `F A`), and an extension problem along a cofibration `i`
reduces to a retraction problem for the cobase change of `i` (H Lemma 2.3.2), which is solved
using that two retractions of a trivial cofibration are homotopic relative to its source.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Homotopy.TwoOutOfSix

section Equivalence

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

/-- `F` is full up to homotopy: every map `F X ⟶ F Y` is homotopic to the image of a map. -/
def HFull (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (v : F.obj X ⟶ F.obj Y), ∃ u : X ⟶ Y, Homotopic (F.map u) v

/-- `F` is faithful up to homotopy: maps with homotopic images are homotopic. -/
def HFaithful (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (u u' : X ⟶ Y), Homotopic (F.map u) (F.map u') → Homotopic u u'

/-- `F` induces an equivalence of homotopy categories, phrased on representatives. -/
def IsHEquiv (F : C ⥤ D) : Prop :=
  IsHomotopySurjective F ∧ HFull F ∧ HFaithful F

/-- An acyclic morphism is full up to homotopy (H Cor 2.3.3, case `A` initial). -/
theorem hFull_of_isHomotopyFullyFaithful [IsCylinderCategory C] (F : C ⥤ D)
    (hF : IsCylinderMorphism F) (hff : IsHomotopyFullyFaithful F) : HFull F := by
  intro X Y v
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hFO⟩ := hF.map_initial hO
  obtain ⟨u, -, hu⟩ := hff (hO.to X) (initial_cofibration hO X) (hO.to Y) v (hFO.hom_ext _ _)
  rw [map_initial_to F hO hFO X] at hu
  exact ⟨u, F.obj O, hFO, hu⟩

/-- An acyclic morphism is faithful up to homotopy (H Cor 2.3.3, proof of 4.). -/
theorem hFaithful_of_isHomotopyFullyFaithful [IsCylinderCategory C] [IsCylinderCategory D]
    (F : C ⥤ D) (hF : IsCylinderMorphism F) (hff : IsHomotopyFullyFaithful F) :
    HFaithful F := by
  intro X Y u u' huu
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hFO⟩ := hF.map_initial hO
  have hcofX := initial_cofibration hO X
  let cyl : RelativeCylinder (hO.to X) :=
    Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO X)
  have hrel : RelHomotopic (F.map (hO.to X)) (F.map u) (F.map u') := by
    rw [map_initial_to F hO hFO X]
    exact homotopic_normalize huu hFO
  have hH : ∃ H : F.obj cyl.I ⟶ F.obj Y,
      F.map cyl.j₀ ≫ F.map cyl.c ≫ H = F.map u ∧ F.map cyl.j₁ ≫ F.map cyl.c ≫ H = F.map u' :=
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof _ (hF.map_cofibration _ hcofX)).2
      (Cylinder.PreCylinderCategory.RelativeCylinder.map F hF hcofX cyl) _ _ hrel
  obtain ⟨H, h₀, h₁⟩ := hH
  have hw : hO.to X ≫ u = hO.to X ≫ u' := hO.hom_ext _ _
  let x : cyl.P ⟶ Y := cyl.isPushout.desc u u' hw
  have hsq : F.map cyl.c ≫ H = F.map x := by
    apply (hF.map_isPushout _ _ _ _ cyl.isPushout hcofX).hom_ext
    · rw [h₀, ← F.map_comp, cyl.isPushout.inl_desc]
    · rw [h₁, ← F.map_comp, cyl.isPushout.inr_desc]
  obtain ⟨v', hv', -⟩ := hff cyl.c cyl.c_mem x H hsq
  refine ⟨O, hO, cyl, v', ?_, ?_⟩
  · rw [hv', cyl.isPushout.inl_desc]
  · rw [hv', cyl.isPushout.inr_desc]

/-- An acyclic morphism induces an equivalence of homotopy categories (H Prop 2.3.4, 1 ⇒ 3). -/
theorem isHEquiv_of_isAcyclic [IsCylinderCategory C] [IsCylinderCategory D] (F : C ⥤ D)
    (hF : IsCylinderMorphism F) (hac : IsAcyclic F) : IsHEquiv F :=
  ⟨hac.1, hFull_of_isHomotopyFullyFaithful F hF hac.2,
    hFaithful_of_isHomotopyFullyFaithful F hF hac.2⟩

/-- A morphism inducing an equivalence of homotopy categories detects weak equivalences
(H Prop 2.3.4, 3 ⇒ 2). -/
theorem we_of_we_map [IsCylinderCategory C] [IsCylinderCategory D] (F : C ⥤ D)
    (hfull : HFull F) (hfaith : HFaithful F) {X Y : C} (φ : X ⟶ Y)
    (hφ : weakEquivalences D (F.map φ)) : weakEquivalences C φ := by
  obtain ⟨ψ', h₁, h₂⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof _).mp hφ
  obtain ⟨ψ, hψ⟩ := hfull ψ'
  refine (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof φ).mpr ⟨ψ, hfaith _ _ ?_, hfaith _ _ ?_⟩
  · rw [F.map_comp, F.map_id]
    exact homotopic_trans (homotopic_precomp hψ _) h₁
  · rw [F.map_comp, F.map_id]
    exact homotopic_trans (homotopic_postcomp hψ _) h₂

/-- Strict homotopy surjectivity of the coslice morphisms `F_A` (H Prop 2.3.4, 3 ⇒ 2): every map
`m : F A ⟶ M` factors as `F j ≫ λ` with `j : A ↪ B` a cofibration and `λ` a weak equivalence. -/
theorem exists_cofibration_under [IsCylinderCategory C] [IsCylinderCategory D] (F : C ⥤ D)
    (hF : IsCylinderMorphism F) (hS : IsHomotopySurjective F) (hfull : HFull F) (A : C) {M : D}
    (m : F.obj A ⟶ M) :
    ∃ (B : C) (j : A ⟶ B) (l : F.obj B ⟶ M),
      cofibrations C j ∧ weakEquivalences D l ∧ F.map j ≫ l = m := by
  classical
  obtain ⟨B', w, hw⟩ := hS M
  obtain ⟨ψ, hψ, hwψ, -⟩ := exists_homotopyInverse w hw
  obtain ⟨u, hu⟩ := hfull (m ≫ w)
  obtain ⟨B, a, p, ha, hp, hap⟩ := Category.SemiModelStructure.brown_factorization u
  have hψ₂ : weakEquivalences D (F.map p ≫ ψ) := we_comp (hF.map_weakEquivalence p hp) hψ
  have hhtpy : Homotopic (F.map a ≫ F.map p ≫ ψ) m := by
    have e : F.map a ≫ F.map p ≫ ψ = F.map u ≫ ψ := by
      rw [← Category.assoc, ← F.map_comp, hap]
    rw [e]
    refine homotopic_trans (homotopic_postcomp hu ψ) ?_
    simpa [Category.assoc] using homotopic_precomp hwψ m
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hFO⟩ := hF.map_initial hO
  have hcofA := initial_cofibration hO A
  let cyl : RelativeCylinder (hO.to A) :=
    Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO A)
  have hrel : RelHomotopic (F.map (hO.to A)) (F.map a ≫ F.map p ≫ ψ) m := by
    rw [map_initial_to F hO hFO A]
    exact homotopic_normalize hhtpy hFO
  have hH : ∃ H : F.obj cyl.I ⟶ M,
      F.map cyl.j₀ ≫ F.map cyl.c ≫ H = F.map a ≫ F.map p ≫ ψ ∧
        F.map cyl.j₁ ≫ F.map cyl.c ≫ H = m :=
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof _ (hF.map_cofibration _ hcofA)).2
      (Cylinder.PreCylinderCategory.RelativeCylinder.map F hF hcofA cyl) _ _ hrel
  obtain ⟨H, h₀, h₁⟩ := hH
  have hend := Category.SemiModelStructure.relativeCylinder_endpoint_properties hcofA cyl
  have : HasPushout (cyl.j₀ ≫ cyl.c) a :=
    IsCofibrationCategory.hasPushout (C := C) _ a hend.1.1
  have hP : IsPushout (cyl.j₀ ≫ cyl.c) a (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  have hPF := hF.map_isPushout _ _ _ _ hP hend.1.1
  have hcomm : F.map (cyl.j₀ ≫ cyl.c) ≫ H = F.map a ≫ F.map p ≫ ψ := by
    rw [F.map_comp, Category.assoc, h₀]
  refine ⟨pushout (cyl.j₀ ≫ cyl.c) a, (cyl.j₁ ≫ cyl.c) ≫ pushout.inl _ _,
    hPF.desc H (F.map p ≫ ψ) hcomm, ?_, ?_, ?_⟩
  · exact (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem _ _ hend.2.1
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP ha)
  · have hqB : weakEquivalences C (pushout.inr (cyl.j₀ ≫ cyl.c) a) :=
      IsCylinderCategory.trivialCofibration_cobaseChange (C := C) _ _ _ _ hP hend.1.1 hend.1.2
    refine we_of_comp_left (F.map (pushout.inr (cyl.j₀ ≫ cyl.c) a)) _
      (hF.map_weakEquivalence _ hqB) ?_
    rw [hPF.inr_desc]
    exact hψ₂
  · rw [F.map_comp, Category.assoc, hPF.inl_desc, F.map_comp, Category.assoc]
    exact h₁

/-- A morphism inducing an equivalence of homotopy categories is homotopy fully faithful
(H Prop 2.3.4, 2 ⇒ 1, with H Lemma 2.3.2). -/
theorem isHomotopyFullyFaithful_of_isHEquiv [IsCylinderCategory C] [IsCylinderCategory D]
    (F : C ⥤ D) (hF : IsCylinderMorphism F) (hE : IsHEquiv F) : IsHomotopyFullyFaithful F := by
  classical
  obtain ⟨hS, hfull, hfaith⟩ := hE
  intro A B X i hi x v hv
  have : HasPushout i x := IsCofibrationCategory.hasPushout (C := C) i x hi
  have hQ : IsPushout i x (pushout.inl i x) (pushout.inr i x) := IsPushout.of_hasPushout i x
  have hk : cofibrations C (pushout.inr i x) :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hQ.flip hi
  have hQF := hF.map_isPushout _ _ _ _ hQ hi
  let R : F.obj (pushout i x) ⟶ F.obj X := hQF.desc v (𝟙 _) (by rw [hv, Category.comp_id])
  have hkR : F.map (pushout.inr i x) ≫ R = 𝟙 _ := hQF.inr_desc _ _ _
  have hlR : F.map (pushout.inl i x) ≫ R = v := hQF.inl_desc _ _ _
  obtain ⟨C', j, l, hj, hl, hjl⟩ := exists_cofibration_under F hF hS hfull (pushout i x) R
  have h₁ : F.map (pushout.inr i x ≫ j) ≫ l = 𝟙 _ := by
    rw [F.map_comp, Category.assoc, hjl, hkR]
  have hkjF : weakEquivalences D (F.map (pushout.inr i x ≫ j)) :=
    we_of_comp_right _ l hl (by rw [h₁]; exact we_id _)
  have hkj_cof : cofibrations C (pushout.inr i x ≫ j) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem _ _ hk hj
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) _ hkj_cof
    (we_of_we_map F hfull hfaith _ hkjF)
  refine ⟨pushout.inl i x ≫ j ≫ r, ?_, ?_⟩
  · rw [← Category.assoc, hQ.w, Category.assoc, ← Category.assoc _ j r, hr, Category.comp_id]
  · have h₂ : RelHomotopic (F.map (pushout.inr i x ≫ j)) (F.map r) l :=
      Category.SemiModelStructure.trivialCofibration_relHomotopic _ (hF.map_cofibration _ hkj_cof) hkjF _ _
        (by rw [← F.map_comp, hr, F.map_id, h₁])
    have hsq : F.map i ≫ F.map (pushout.inl i x ≫ j) =
        F.map x ≫ F.map (pushout.inr i x ≫ j) := by
      rw [← F.map_comp, ← F.map_comp, ← Category.assoc, hQ.w, Category.assoc]
    have h₃ := Category.SemiModelStructure.relHomotopic_precomp _ (F.map i) (F.map x) _ hsq
      (hF.map_cofibration i hi) h₂
    have e₁ : F.map (pushout.inl i x ≫ j) ≫ F.map r = F.map (pushout.inl i x ≫ j ≫ r) := by
      rw [← F.map_comp, Category.assoc]
    have e₂ : F.map (pushout.inl i x ≫ j) ≫ l = v := by
      rw [F.map_comp, Category.assoc, hjl, hlR]
    rwa [e₁, e₂] at h₃

/-- A morphism inducing an equivalence of homotopy categories is acyclic
(H Prop 2.3.4, 3 ⇒ 1). -/
theorem isAcyclic_of_isHEquiv [IsCylinderCategory C] [IsCylinderCategory D] (F : C ⥤ D)
    (hF : IsCylinderMorphism F) (hE : IsHEquiv F) : IsAcyclic F :=
  ⟨hE.1, isHomotopyFullyFaithful_of_isHEquiv F hF hE⟩

end Equivalence

section TwoOutOfSix

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type u₃} [Category.{v₃} E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
  {T : Type u₄} [Category.{v₄} T] [CategoryWithCofibrations T] [CategoryWithWeakEquivalences T]

theorem isCylinderMorphism_comp {F : C ⥤ D} {G : D ⥤ E} (hF : IsCylinderMorphism F)
    (hG : IsCylinderMorphism G) : IsCylinderMorphism (F ⋙ G) where
  map_cofibration _ _ f hf := hG.map_cofibration _ (hF.map_cofibration f hf)
  map_initial _ hI := by
    obtain ⟨h⟩ := hF.map_initial hI
    exact hG.map_initial h
  map_isPushout _ _ _ _ i f k j h hi :=
    hG.map_isPushout _ _ _ _ (hF.map_isPushout i f k j h hi) (hF.map_cofibration i hi)
  map_weakEquivalence _ _ f hf := hG.map_weakEquivalence _ (hF.map_weakEquivalence f hf)

/-- Equivalences of homotopy categories satisfy 2-out-of-6. -/
theorem isHEquiv_twoOutOfSix [IsCylinderCategory C] [IsCylinderCategory D]
    [IsCylinderCategory E] [IsCylinderCategory T] (f : C ⥤ D) (g : D ⥤ E) (h : E ⥤ T)
    (hg : IsCylinderMorphism g) (hh : IsCylinderMorphism h) (hfg : IsHEquiv (f ⋙ g)) (hgh : IsHEquiv (g ⋙ h)) :
    IsHEquiv f ∧ IsHEquiv g ∧ IsHEquiv h := by
  have gFaith : HFaithful g := fun X Y u u' huu => hgh.2.2 u u' (homotopic_map h hh huu)
  have fFaith : HFaithful f := fun X Y u u' huu => hfg.2.2 u u' (homotopic_map g hg huu)
  have gS : IsHomotopySurjective g := Cylinder.PreCylinderCategory.isHomotopySurjective_of_comp_right f g hfg.1
  have hS : IsHomotopySurjective h := Cylinder.PreCylinderCategory.isHomotopySurjective_of_comp_right g h hgh.1
  -- `h` is faithful: transport along homotopy equivalences to the image of `f ⋙ g`.
  have hFaith : HFaithful h := by
    intro Z W p q hpq
    obtain ⟨Z₀, wZ, hwZ⟩ := hfg.1 Z
    obtain ⟨W₀, wW, hwW⟩ := hfg.1 W
    obtain ⟨eZ, -, hZ₁, -⟩ := exists_homotopyInverse wZ hwZ
    obtain ⟨eW, -, hW₁, -⟩ := exists_homotopyInverse wW hwW
    obtain ⟨a, ha⟩ := hfg.2.1 (eZ ≫ p ≫ wW)
    obtain ⟨b, hb⟩ := hfg.2.1 (eZ ≫ q ≫ wW)
    have hab : Homotopic ((f ⋙ g).map a) ((f ⋙ g).map b) := by
      refine homotopic_map g hg (hgh.2.2 _ _ ?_)
      change Homotopic (h.map ((f ⋙ g).map a)) (h.map ((f ⋙ g).map b))
      refine homotopic_trans (homotopic_map h hh ha)
        (homotopic_trans ?_ (homotopic_symm (homotopic_map h hh hb)))
      simp only [CategoryTheory.Functor.map_comp]
      exact homotopic_comp (homotopic_refl _) (homotopic_comp hpq (homotopic_refl _))
    have hpq' : Homotopic (eZ ≫ p ≫ wW) (eZ ≫ q ≫ wW) :=
      homotopic_trans (homotopic_symm ha) (homotopic_trans hab hb)
    have key : ∀ p : Z ⟶ W, Homotopic (wZ ≫ (eZ ≫ p ≫ wW) ≫ eW) p := by
      intro p
      have := homotopic_comp hZ₁ (homotopic_comp (homotopic_refl p) hW₁)
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this
    exact homotopic_trans (homotopic_symm (key p))
      (homotopic_trans (homotopic_comp (homotopic_refl wZ) (homotopic_postcomp hpq' eW))
        (key q))
  have gFull : HFull g := by
    intro X Y v
    obtain ⟨u, hu⟩ := hgh.2.1 (h.map v)
    exact ⟨u, hFaith _ _ hu⟩
  have fFull : HFull f := by
    intro X Y v
    obtain ⟨u, hu⟩ := hfg.2.1 (g.map v)
    exact ⟨u, gFaith _ _ hu⟩
  have hFull : HFull h := by
    intro Z W v
    obtain ⟨Z₀, wZ, hwZ⟩ := gS Z
    obtain ⟨W₀, wW, hwW⟩ := gS W
    obtain ⟨eZ, -, hZ₁, -⟩ := exists_homotopyInverse wZ hwZ
    obtain ⟨eW, -, hW₁, -⟩ := exists_homotopyInverse wW hwW
    obtain ⟨u, hu⟩ := hgh.2.1 (h.map eZ ≫ v ≫ h.map wW)
    refine ⟨wZ ≫ g.map u ≫ eW, ?_⟩
    have hZ₁' := homotopic_map h hh hZ₁
    have hW₁' := homotopic_map h hh hW₁
    rw [h.map_comp, h.map_id] at hZ₁'
    rw [h.map_comp, h.map_id] at hW₁'
    have := homotopic_comp hZ₁' (homotopic_comp (homotopic_refl v) hW₁')
    simp only [Category.assoc, Category.id_comp, Category.comp_id] at this
    refine homotopic_trans ?_ this
    simp only [CategoryTheory.Functor.map_comp]
    refine homotopic_comp (homotopic_refl _) ?_
    have hu' := homotopic_postcomp hu (h.map eW)
    simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using hu'
  have fS : IsHomotopySurjective f := by
    intro Y
    obtain ⟨X, w, hw⟩ := hfg.1 (g.obj Y)
    obtain ⟨φ, hφ⟩ := gFull w
    exact ⟨X, φ, we_of_we_map g gFull gFaith φ (we_of_homotopic hφ hw)⟩
  exact ⟨⟨fS, fFull, fFaith⟩, ⟨gS, gFull, gFaith⟩, ⟨hS, hFull, hFaith⟩⟩

/-- H Prop 2.3.6 (H:970): acyclic morphisms of cylinder categories satisfy 2-out-of-6. -/
theorem isAcyclic_twoOutOfSix_proof [IsCylinderCategory C] [IsCylinderCategory D]
    [IsCylinderCategory E] [IsCylinderCategory T] (f : C ⥤ D) (g : D ⥤ E) (h : E ⥤ T)
    (hf : IsCylinderMorphism f) (hg : IsCylinderMorphism g) (hh : IsCylinderMorphism h)
    (hfg : IsAcyclic (f ⋙ g)) (hgh : IsAcyclic (g ⋙ h)) :
    IsAcyclic f ∧ IsAcyclic g ∧ IsAcyclic h ∧ IsAcyclic (f ⋙ g ⋙ h) := by
  have hgh' := isCylinderMorphism_comp hg hh
  obtain ⟨ef, eg, eh⟩ := isHEquiv_twoOutOfSix f g h hg hh
    (isHEquiv_of_isAcyclic _ (isCylinderMorphism_comp hf hg) hfg)
    (isHEquiv_of_isAcyclic _ hgh' hgh)
  have af := isAcyclic_of_isHEquiv f hf ef
  have ag := isAcyclic_of_isHEquiv g hg eg
  have ah := isAcyclic_of_isHEquiv h hh eh
  exact ⟨af, ag, ah, Cylinder.PreCylinderCategory.isAcyclic_comp f (g ⋙ h) hf hgh' af
    (Cylinder.PreCylinderCategory.isAcyclic_comp g h hg hh ag ah)⟩

end TwoOutOfSix

end HomotopyHypothesis.Homotopy.TwoOutOfSix

#print axioms HomotopyHypothesis.Homotopy.TwoOutOfSix.isAcyclic_twoOutOfSix_proof
