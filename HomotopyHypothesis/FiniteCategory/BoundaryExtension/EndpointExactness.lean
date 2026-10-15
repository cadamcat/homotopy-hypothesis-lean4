import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Subcategory.DiskFinitelyCellular
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CylinderCategory
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CylinderCellPushout
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
import HomotopyHypothesis.FiniteCategory.Lifting.HelperStatements
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.BoundaryExtension

def finiteEndpointMaps (C : GlobularTheory.{v}) (hC : C.IsCoherator) :
    MorphismProperty (Afin C hC) :=
  ((MorphismProperty.ofHoms (fun n : ℕ => FiniteCategory.Lifting.finiteEndpoint hC n)).pushouts ⊔
    MorphismProperty.isomorphisms (Afin C hC)).multiplicativeClosure

theorem finiteEndpointMaps_comp (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    {A B D : Afin C hC} (f : A ⟶ B) (g : B ⟶ D)
    (hf : finiteEndpointMaps C hC f) (hg : finiteEndpointMaps C hC g) :
    finiteEndpointMaps C hC (f ≫ g) := by
  unfold finiteEndpointMaps at hf hg ⊢
  induction hg with
  | of g hg => exact .comp_of f g hf hg
  | id B => simpa using hf
  | comp_of g₁ g₂ hg₁ hg₂ ih =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ g₁) g₂ (ih f hf) hg₂

def ExtendsFiniteEndpointFactorization (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    {A B : C.Model} (i : A ⟶ B) : Prop :=
  ∀ {Z X : C.Model} (c : A ⟶ Z), finiteCellMaps C c →
    (hZ : IsFinitelyCellular C Z) →
    ∀ (p : Z ⟶ X), W hC p → ∀ (f : B ⟶ X), c ≫ p = i ≫ f →
      ∃ (T : C.Model) (hT : IsFinitelyCellular C T) (c' : B ⟶ T) (t : Z ⟶ T)
        (p' : T ⟶ X),
        finiteCellMaps C c' ∧ finiteCellMaps C t ∧
          finiteEndpointMaps C hC (ObjectProperty.homMk t :
            (⟨Z, hZ⟩ : Afin C hC) ⟶ ⟨T, hT⟩) ∧
          W hC p' ∧ i ≫ c' = c ≫ t ∧ c' ≫ p' = f ∧ t ≫ p' = p

theorem extendsFiniteEndpointFactorization_id (C : GlobularTheory.{v})
    (hC : C.IsCoherator) (A : C.Model) :
    ExtendsFiniteEndpointFactorization C hC (𝟙 A) := by
  intro Z X c hc hZ p hp f h
  let Z' : Afin C hC := ⟨Z, hZ⟩
  exact ⟨Z, hZ, c, 𝟙 Z, p, hc, (finiteCellMaps C).id_mem Z,
    (show finiteEndpointMaps C hC (𝟙 Z') from .id Z'), hp,
    by simp, by simpa using h, by simp⟩

theorem extendsFiniteEndpointFactorization_iso (C : GlobularTheory.{v})
    (hC : C.IsCoherator) {A B : C.Model} (i : A ⟶ B) [IsIso i] :
    ExtendsFiniteEndpointFactorization C hC i := by
  intro Z X c hc hZ p hp f h
  let Z' : Afin C hC := ⟨Z, hZ⟩
  refine ⟨Z, hZ, inv i ≫ c, 𝟙 Z, p,
    (finiteCellMaps C).comp_mem _ _ (Cylinder.FiniteCellCategory.finiteCellMaps_isomorphisms C _ inferInstance) hc,
    (finiteCellMaps C).id_mem Z, (show finiteEndpointMaps C hC (𝟙 Z') from .id Z'), hp,
    ?_, ?_, by simp⟩
  · simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem extendsFiniteEndpointFactorization_cell (C : GlobularTheory.{v})
    (hC : C.IsCoherator) {A B : C.Model} (n : ℕ)
    (a : boundaryDisk C n ⟶ A) (i : A ⟶ B) (x : disk C n ⟶ B)
    (sq : IsPushout a (I C n) i x) : ExtendsFiniteEndpointFactorization C hC i := by
  intro Z X c hc hZ p hp f h
  have w : (a ≫ c) ≫ p = I C n ≫ (x ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨b, H, hb, hH₀, hH₁⟩ := Cylinder.FiniteCellCategory.boundary_test_lift hC p hp
    (Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C _ hZ) n (a ≫ c) (x ≫ f) w
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
  have htJ : (Cylinder.FiniteCellCategory.sourceMaps C).rlp.llp t :=
    (Cylinder.FiniteCellCategory.sourceMaps C).rlp.llp.of_isPushout st
      ((Cylinder.FiniteCellCategory.sourceMaps C).le_llp_rlp _ (MorphismProperty.ofHoms.mk n))
  have htW : W hC t := Cylinder.FiniteCellCategory.source_llp_weakEquivalence hC t htJ
    (Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C _ hZ)
  have hc' : finiteCellMaps C c' :=
    Cylinder.FiniteCellCategory.cell_cylinder_cofibration n a i x sq c hc b hb t d st c' hi hx
  have htFinite : finiteCellMaps C t :=
    (finiteCellMaps C).of_isPushout st (Cylinder.FiniteCellCategory.finiteCellMaps_J n)
  let hT : IsFinitelyCellular C T :=
    Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hZ t htFinite
  let Z' : Afin C hC := ⟨Z, hZ⟩
  let T' : Afin C hC := ⟨T, hT⟩
  let D₀ : Afin C hC := ⟨disk C n, FiniteCategory.Subcategory.disk_finitelyCellular_proof C n⟩
  let D₁ : Afin C hC := ⟨disk C (n+1), FiniteCategory.Subcategory.disk_finitelyCellular_proof C (n+1)⟩
  let b' : D₀ ⟶ Z' := ObjectProperty.homMk b
  let j' : D₀ ⟶ D₁ := FiniteCategory.Lifting.finiteEndpoint hC n
  let t' : Z' ⟶ T' := ObjectProperty.homMk t
  let d' : D₁ ⟶ T' := ObjectProperty.homMk d
  have st' : IsPushout b' j' t' d' := IsPushout.of_map_of_faithful (Afin.ι hC) st
  have htEndpoints : finiteEndpointMaps C hC t' :=
    .of t'
      (Or.inl ((MorphismProperty.ofHoms
        (fun n : ℕ => FiniteCategory.Lifting.finiteEndpoint hC n)).pushouts_mk st'
          (MorphismProperty.ofHoms.mk n)))
  have hp' : W hC p' := (W hC).of_precomp t p' htW (by rwa [ht])
  refine ⟨T, hT, c', t, p', hc', htFinite, htEndpoints, hp', hi, ?_, ht⟩
  apply sq.hom_ext
  · calc
      i ≫ (c' ≫ p') = c ≫ (t ≫ p') := by rw [← Category.assoc, hi, Category.assoc]
      _ = c ≫ p := by rw [ht]
      _ = i ≫ f := h
  · calc
      x ≫ (c' ≫ p') = targetDisk C n ≫ (d ≫ p') := by rw [← Category.assoc, hx, Category.assoc]
      _ = targetDisk C n ≫ H := by rw [hd]
      _ = x ≫ f := hH₁

theorem extendsFiniteEndpointFactorization_comp (C : GlobularTheory.{v})
    (hC : C.IsCoherator) {A B D : C.Model} (i : A ⟶ B) (j : B ⟶ D)
    (hi : ExtendsFiniteEndpointFactorization C hC i)
    (hj : ExtendsFiniteEndpointFactorization C hC j) :
    ExtendsFiniteEndpointFactorization C hC (i ≫ j) := by
  intro Z X c hc hZ p hp f h
  obtain ⟨T, hT, c₁, t₁, p₁, hc₁, ht₁, ht₁J, hp₁, hi₁, hc₁p, ht₁p⟩ :=
    hi c hc hZ p hp (j ≫ f) (by simpa only [Category.assoc] using h)
  obtain ⟨U, hU, c₂, t₂, p₂, hc₂, ht₂, ht₂J, hp₂, hi₂, hc₂p, ht₂p⟩ :=
    hj c₁ hc₁ hT p₁ hp₁ f hc₁p
  let t₂' : (⟨T, hT⟩ : Afin C hC).obj ⟶ (⟨U, hU⟩ : Afin C hC).obj := t₂
  have ht1J : finiteEndpointMaps C hC (ObjectProperty.homMk t₁ :
      (⟨Z, hZ⟩ : Afin C hC) ⟶ ⟨T, hT⟩) := ht₁J
  have ht2J : finiteEndpointMaps C hC (ObjectProperty.homMk t₂' :
      (⟨T, hT⟩ : Afin C hC) ⟶ ⟨U, hU⟩) := ht₂J
  have hcomp : ObjectProperty.homMk (t₁ ≫ t₂ : Z ⟶ U) =
      (ObjectProperty.homMk t₁ : (⟨Z, hZ⟩ : Afin C hC) ⟶ ⟨T, hT⟩) ≫
        ObjectProperty.homMk t₂' := by
    apply ObjectProperty.hom_ext
    rfl
  refine ⟨U, hU, c₂, t₁ ≫ t₂, p₂, hc₂,
    (finiteCellMaps C).comp_mem _ _ ht₁ ht₂, ?_, hp₂, ?_, hc₂p, ?_⟩
  · rw [hcomp]
    exact finiteEndpointMaps_comp C hC _ _ ht1J ht2J
  · rw [Category.assoc, hi₂, ← Category.assoc, hi₁, Category.assoc]
  · rw [Category.assoc, ht₂p, ht₁p]

theorem finiteCellMaps_extendsEndpointFactorization (C : GlobularTheory.{v})
    (hC : C.IsCoherator) {A B : C.Model} (i : A ⟶ B)
    (hi : finiteCellMaps C i) : ExtendsFiniteEndpointFactorization C hC i := by
  have base : ∀ {A B : C.Model} (i : A ⟶ B),
      ((Cylinder.FiniteCellCategory.boundaryMaps C).pushouts ⊔ MorphismProperty.isomorphisms C.Model) i →
        ExtendsFiniteEndpointFactorization C hC i := by
    intro A B i hi
    rcases hi with hi | hi
    · rcases hi with ⟨S, D, g, a, x, ⟨n⟩, sq⟩
      exact extendsFiniteEndpointFactorization_cell C hC n a i x sq
    · let := hi
      exact @extendsFiniteEndpointFactorization_iso C hC A B i hi
  induction hi with
  | of i hi => exact base i hi
  | id A => exact extendsFiniteEndpointFactorization_id C hC A
  | comp_of i j hi hj ih =>
      exact extendsFiniteEndpointFactorization_comp C hC i j ih (base j hj)

theorem finiteEndpointMaps_preserved {Target : Type u} [Category.{v} Target]
    [CategoryWithCofibrations Target] [CategoryWithWeakEquivalences Target]
    [IsCylinderCategory Target]
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (F : Afin C hC ⥤ Target) (hF : IsCofibrationMorphism F)
    (hEnd : ∀ n, weakEquivalences Target (F.map (FiniteCategory.Lifting.finiteEndpoint hC n)))
    {A B : Afin C hC} (f : A ⟶ B) (hf : finiteEndpointMaps C hC f) :
      weakEquivalences Target (F.map f) := by
  have base : ∀ {A B : Afin C hC} (f : A ⟶ B),
      ((MorphismProperty.ofHoms (fun n : ℕ => FiniteCategory.Lifting.finiteEndpoint hC n)).pushouts ⊔
        MorphismProperty.isomorphisms (Afin C hC)) f → weakEquivalences Target (F.map f) := by
    intro A B f hf
    rcases hf with hf | hf
    · rcases hf with ⟨S, D, g, a, x, ⟨n⟩, sq⟩
      have hj : cofibrations (Afin C hC) (FiniteCategory.Lifting.finiteEndpoint hC n) := by
        change finiteCellMaps C (J C n)
        exact Cylinder.FiniteCellCategory.finiteCellMaps_J n
      exact IsCylinderCategory.trivialCofibration_cobaseChange (C := Target)
        (F.map (FiniteCategory.Lifting.finiteEndpoint hC n)) (F.map a) (F.map x) (F.map f)
        (hF.map_isPushout _ _ _ _ sq.flip hj) (hF.map_cofibration _ hj) (hEnd n)
    · letI : IsIso f := hf
      exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := Target)
        (F.map f) (MorphismProperty.isomorphisms.infer_property _)
  unfold finiteEndpointMaps at hf
  induction hf with
  | of f hf => exact base f hf
  | id A =>
      have hId :=
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := Target)).toContainsIdentities.id_mem
          (F.obj A)
      simpa only [F.map_id A] using hId
  | comp_of f g hf hg ih =>
      rw [Functor.map_comp]
      exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := Target)).comp_mem _ _
        ih (base g hg)

theorem trivialFiniteCofibration_preserved {Target : Type u} [Category.{v} Target]
    [CategoryWithCofibrations Target] [CategoryWithWeakEquivalences Target]
    [IsCylinderCategory Target]
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (F : Afin C hC ⥤ Target) (hF : IsCofibrationMorphism F)
    (hEnd : ∀ n, weakEquivalences Target (F.map (FiniteCategory.Lifting.finiteEndpoint hC n)))
    {A B : Afin C hC} (i : A ⟶ B) (hi : cofibrations (Afin C hC) i)
    (hwi : weakEquivalences (Afin C hC) i) : weakEquivalences Target (F.map i) := by
  change finiteCellMaps C i.hom at hi
  obtain ⟨T, hT, c, t, p, hc, ht, htJ, hp, hic, hcp, htp⟩ :=
    finiteCellMaps_extendsEndpointFactorization C hC i.hom hi
      (𝟙 A.obj) ((finiteCellMaps C).id_mem A.obj) A.property i.hom hwi
      (𝟙 B.obj) (by simp)
  let Y : Afin C hC := ⟨T, hT⟩
  let c' : B ⟶ Y := ObjectProperty.homMk c
  let t' : A ⟶ Y := ObjectProperty.homMk t
  let p' : Y ⟶ B := ObjectProperty.homMk p
  have hic' : i ≫ c' = t' := by
    apply ObjectProperty.hom_ext
    exact hic
  have hcp' : c' ≫ p' = 𝟙 B := by
    apply ObjectProperty.hom_ext
    exact hcp
  have htp' : t' ≫ p' = i := by
    apply ObjectProperty.hom_ext
    exact htp
  have htF : weakEquivalences Target (F.map t') :=
    finiteEndpointMaps_preserved C hC F hF hEnd t' htJ
  have h₁ : weakEquivalences Target (F.map i ≫ F.map c') := by
    simpa only [← Functor.map_comp, hic'] using htF
  have h₂ : weakEquivalences Target (F.map c' ≫ F.map p') := by
    have hId : weakEquivalences Target (F.map (𝟙 B)) := by
      rw [F.map_id B]
      exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := Target)).toContainsIdentities.id_mem
        (F.obj B)
    simpa only [← Functor.map_comp, hcp'] using hId
  exact (IsCylinderCategory.twoOutOfSix (C := Target) (F.map i) (F.map c') (F.map p') h₁ h₂).1

section BrownFactorization

variable {K : Type w} [Category.{v} K] [CategoryWithCofibrations K]
  [CategoryWithWeakEquivalences K] [IsCylinderCategory K]

private theorem relativeCylinder_endpoint_properties {A B : K} {i : A ⟶ B}
    (hi : cofibrations K i) (cyl : RelativeCylinder i) :
    (cofibrations K (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences K (cyl.j₀ ≫ cyl.c)) ∧
      (cofibrations K (cyl.j₁ ≫ cyl.c) ∧ weakEquivalences K (cyl.j₁ ≫ cyl.c)) := by
  have hcof₀ := (IsCofibrationCategory.isStableUnderCobaseChange (C := K)).of_isPushout
    cyl.isPushout hi
  have hcof₁ := (IsCofibrationCategory.isStableUnderCobaseChange (C := K)).of_isPushout
    cyl.isPushout.flip hi
  have hcomp₀ := (IsCofibrationCategory.isMultiplicative (C := K)).comp_mem
    cyl.j₀ cyl.c hcof₀ cyl.c_mem
  have hcomp₁ := (IsCofibrationCategory.isMultiplicative (C := K)).comp_mem
    cyl.j₁ cyl.c hcof₁ cyl.c_mem
  have hid : weakEquivalences K (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := K) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hw₀ := IsCylinderCategory.twoOutOfSix (C := K) (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₀_c_p] using hid) (by simpa using cyl.p_mem)
  have hw₁ := IsCylinderCategory.twoOutOfSix (C := K) (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₁_c_p] using hid) (by simpa using cyl.p_mem)
  exact ⟨⟨hcomp₀, hw₀.1⟩, ⟨hcomp₁, hw₁.1⟩⟩

theorem brownFactorizationWithSection {A B : K} (f : A ⟶ B) :
    ∃ (M : K) (i : A ⟶ M) (p : M ⟶ B) (s : B ⟶ M),
      cofibrations K i ∧ weakEquivalences K p ∧ cofibrations K s ∧
        weakEquivalences K s ∧ i ≫ p = f ∧ s ≫ p = 𝟙 B := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := K)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hA0 : cofibrations K (hO.to A) :=
    IsCofibrationCategory.initial_cofibration hO A
  have hB0 : cofibrations K (hO.to B) :=
    IsCofibrationCategory.initial_cofibration hO B
  let cyl := Classical.choice (IsCylinderCategory.exists_cylinder (C := K) hO A)
  have hPAB : HasPushout (hO.to A) (hO.to B) :=
    IsCofibrationCategory.hasPushout (C := K) (hO.to A) (hO.to B) hA0
  letI := hPAB
  let PAB := pushout (hO.to A) (hO.to B)
  let a : A ⟶ PAB := pushout.inl (hO.to A) (hO.to B)
  let b : B ⟶ PAB := pushout.inr (hO.to A) (hO.to B)
  let hAB : IsPushout (hO.to A) (hO.to B) a b :=
    IsPushout.of_hasPushout (hO.to A) (hO.to B)
  have hP0 : HasPushout (hO.to A) (hO.to A) := cyl.isPushout.hasPushout
  letI := hP0
  have hdcond : (hO.to A) ≫ a = (hO.to A) ≫ (f ≫ b) := hO.hom_ext _ _
  let d : cyl.P ⟶ PAB := cyl.isPushout.desc a (f ≫ b) hdcond
  have hM : HasPushout cyl.c d :=
    IsCofibrationCategory.hasPushout (C := K) cyl.c d cyl.c_mem
  letI := hM
  let M := pushout cyl.c d
  let mI : cyl.I ⟶ M := pushout.inl cyl.c d
  let mAB : PAB ⟶ M := pushout.inr cyl.c d
  have hMpo : IsPushout cyl.c d mI mAB := IsPushout.of_hasPushout cyl.c d
  let qAB : PAB ⟶ B := hAB.desc f (𝟙 B) (by apply hO.hom_ext)
  have hqABa : a ≫ qAB = f := hAB.inl_desc _ _ _
  have hqABb : b ≫ qAB = 𝟙 B := hAB.inr_desc _ _ _
  have hcomm : cyl.c ≫ (cyl.p ≫ f) = d ≫ qAB := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₀_c_p]; simp
        _ = cyl.j₀ ≫ d ≫ qAB := by simp [d, qAB]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₁_c_p]; simp
        _ = cyl.j₁ ≫ d ≫ qAB := by simp [d, qAB]
  let qM : M ⟶ B := hMpo.desc (cyl.p ≫ f) qAB hcomm
  have hqMI : mI ≫ qM = cyl.p ≫ f := hMpo.inl_desc _ _ _
  have hqMAB : mAB ≫ qM = qAB := hMpo.inr_desc _ _ _
  have hinc : IsPushout (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) := by
    let e₀ : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
    let e₁ : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
    have hsq : e₁ ≫ mI = f ≫ (b ≫ mAB) := by
      calc
        e₁ ≫ mI = cyl.j₁ ≫ (cyl.c ≫ mI) := by simp [e₁, Category.assoc]
        _ = cyl.j₁ ≫ (d ≫ mAB) := by rw [hMpo.w]
        _ = (cyl.j₁ ≫ d) ≫ mAB := by simp [Category.assoc]
        _ = f ≫ (b ≫ mAB) := by simp [d, Category.assoc]
    let t : PushoutCocone e₁ f := PushoutCocone.mk mI (b ≫ mAB) hsq
    have ht : IsColimit t := by
      apply PushoutCocone.isColimitAux' t
      intro s
      have hinit : (hO.to A) ≫ (e₀ ≫ s.inl) = (hO.to B) ≫ s.inr := hO.hom_ext _ _
      let q : PAB ⟶ s.pt := hAB.desc (e₀ ≫ s.inl) s.inr hinit
      have hcompat : d ≫ q = cyl.c ≫ s.inl := by
        apply cyl.isPushout.hom_ext
        · simp [q, d, hAB, e₀]
        · calc
            cyl.j₁ ≫ d ≫ q = f ≫ b ≫ q := by simp [d, Category.assoc]
            _ = f ≫ s.inr := by simp [q]
            _ = e₁ ≫ s.inl := s.condition.symm
            _ = cyl.j₁ ≫ cyl.c ≫ s.inl := by simpa [e₁]
      let m := hMpo.desc s.inl q hcompat.symm
      have hmI : mI ≫ m = s.inl := by
        dsimp [m]
        exact hMpo.inl_desc s.inl q hcompat.symm
      have hmAB : mAB ≫ m = q := by
        dsimp [m]
        exact hMpo.inr_desc s.inl q hcompat.symm
      refine ⟨m, ?_, ?_, ?_⟩
      · exact hmI
      · calc
          (b ≫ mAB) ≫ m = b ≫ (mAB ≫ m) := by simp [Category.assoc]
          _ = b ≫ q := by rw [hmAB]
          _ = s.inr := by simp [q]
      · intro m' hm'I hm'B
        change M ⟶ s.pt at m'
        change mI ≫ m' = s.inl at hm'I
        have hmAB' : mAB ≫ m' = q := by
          apply hAB.hom_ext
          · calc
              a ≫ mAB ≫ m' = cyl.j₀ ≫ d ≫ mAB ≫ m' := by simp [d, Category.assoc]
              _ = cyl.j₀ ≫ (d ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = cyl.j₀ ≫ (cyl.c ≫ mI) ≫ m' := by rw [← hMpo.w]
              _ = cyl.j₀ ≫ cyl.c ≫ s.inl := by simp [Category.assoc, hm'I]
              _ = a ≫ q := by simp [q, e₀]
          · calc
              b ≫ mAB ≫ m' = (b ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = s.inr := hm'B
              _ = b ≫ q := by simp [q]
        apply hMpo.hom_ext
        · calc
            mI ≫ m' = s.inl := hm'I
            _ = mI ≫ m := hmI.symm
        · exact hmAB'.trans hmAB.symm
    exact IsPushout.of_isColimit ht
  let sMap : B ⟶ M := b ≫ mAB
  have hend := relativeCylinder_endpoint_properties hA0 cyl
  have hsCof : cofibrations K sMap :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := K)).of_isPushout hinc.flip hend.2.1
  have hsW : weakEquivalences K sMap :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := K)
      (cyl.j₁ ≫ cyl.c) f mI sMap hinc hend.2.1 hend.2.2
  have hid : weakEquivalences K (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := K) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hsqW : weakEquivalences K (sMap ≫ qM) := by
    rw [Category.assoc, hqMAB, hqABb]
    exact hid
  have hqW := IsCylinderCategory.twoOutOfSix (C := K) (𝟙 B) sMap qM
    (by simpa using hsW) hsqW
  have hpW : weakEquivalences K qM := hqW.2.2.1
  have hia : cofibrations K (a ≫ mAB) :=
    (IsCofibrationCategory.isMultiplicative (C := K)).comp_mem a mAB
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := K)).of_isPushout hAB hB0)
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := K)).of_isPushout hMpo.flip cyl.c_mem)
  refine ⟨M, a ≫ mAB, qM, sMap, hia, hpW, hsCof, hsW, ?_, ?_⟩
  · calc
      (a ≫ mAB) ≫ qM = a ≫ (mAB ≫ qM) := by simp [Category.assoc]
      _ = a ≫ qAB := by rw [hqMAB]
      _ = f := hqABa
  · calc
      sMap ≫ qM = (b ≫ mAB) ≫ qM := rfl
      _ = b ≫ qAB := by simp [Category.assoc, hqMAB]
      _ = 𝟙 B := hqABb

end BrownFactorization

end HomotopyHypothesis.FiniteCategory.BoundaryExtension

namespace HomotopyHypothesis.FiniteCategory.BoundaryExtension

theorem endpointExactnessStatement_proof {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] :
    FiniteCategory.Lifting.EndpointExactnessStatement (C := C) hC (X := X) := by
  letI : IsCylinderCategory (Afin C hC) :=
    HomotopyHypothesis.Blueprint.Packages.afin_isCylinderCategory_proof hC
  intro F hF hEnd
  refine { toIsCofibrationMorphism := hF, map_weakEquivalence := ?_ }
  intro A B f hf
  obtain ⟨M, i, p, s, hi, hp, hs, hsW, hip, hsp⟩ :=
    brownFactorizationWithSection (K := Afin C hC) f
  have h₁ : weakEquivalences (Afin C hC) (i ≫ p) := by
    rw [hip]
    exact hf
  have h₂ : weakEquivalences (Afin C hC) (p ≫ 𝟙 B) := by
    simpa using hp
  have hiW : weakEquivalences (Afin C hC) i :=
    (IsCylinderCategory.twoOutOfSix (C := Afin C hC) i p (𝟙 B) h₁ h₂).1
  have hFi : weakEquivalences X (F.map i) :=
    trivialFiniteCofibration_preserved C hC F hF hEnd i hi hiW
  have hFs : weakEquivalences X (F.map s) :=
    trivialFiniteCofibration_preserved C hC F hF hEnd s hs hsW
  have h₃ : weakEquivalences X (𝟙 (F.obj B) ≫ F.map s) := by
    simpa only [Category.id_comp] using hFs
  have h₄ : weakEquivalences X (F.map s ≫ F.map p) := by
    have hsp' : F.map s ≫ F.map p = 𝟙 (F.obj B) := by
      rw [← F.map_comp, hsp, F.map_id B]
    rw [hsp']
    exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).toContainsIdentities.id_mem
      (F.obj B)
  have hFp : weakEquivalences X (F.map p) :=
    (IsCylinderCategory.twoOutOfSix (C := X) (𝟙 (F.obj B)) (F.map s) (F.map p) h₃ h₄).2.2.1
  have hcomp : F.map i ≫ F.map p = F.map f := by
    simpa only [Functor.map_comp] using congrArg F.map hip
  rw [← hcomp]
  exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).comp_mem _ _ hFi hFp

example {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] :
    FiniteCategory.Lifting.EndpointExactnessStatement (C := C) hC (X := X) :=
      endpointExactnessStatement_proof hC

#print axioms endpointExactnessStatement_proof

end HomotopyHypothesis.FiniteCategory.BoundaryExtension
