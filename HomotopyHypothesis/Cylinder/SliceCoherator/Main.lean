import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part1
import HomotopyHypothesis.Blueprint.Henry.Packages.General.PathObjIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjForgetIsAcyclicIff
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjIsLiftingTarget
import HomotopyHypothesis.Cylinder.HomotopyTerminalSlice.Main
/-!
# Endpoint projections of path categories

The two legs of a path category are acyclic pre-fibrations. The projection to the product of the
ends is an acyclic lifting target only after composing with a product projection, and a product
projection is itself a pre-fibration and an isofibration.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.SliceCoherator

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- A componentwise pushout square is a pushout square in the product. -/
theorem isPushout_prod {A₁ B₁ X₁ P₁ A₂ B₂ X₂ P₂ : C}
    {f₁ : A₁ ⟶ B₁} {g₁ : A₁ ⟶ X₁} {k₁ : B₁ ⟶ P₁} {j₁ : X₁ ⟶ P₁}
    {f₂ : A₂ ⟶ B₂} {g₂ : A₂ ⟶ X₂} {k₂ : B₂ ⟶ P₂} {j₂ : X₂ ⟶ P₂}
    (h₁ : IsPushout f₁ g₁ k₁ j₁) (h₂ : IsPushout f₂ g₂ k₂ j₂) :
    IsPushout (Prod.mkHom f₁ f₂) (Prod.mkHom g₁ g₂) (Prod.mkHom k₁ k₂)
      (Prod.mkHom j₁ j₂) := by
  have hw : Prod.mkHom f₁ f₂ ≫ Prod.mkHom k₁ k₂ =
      Prod.mkHom g₁ g₂ ≫ Prod.mkHom j₁ j₂ := by
    apply Prod.hom_ext
    · simpa using h₁.w
    · simpa using h₂.w
  refine IsPushout.of_isColimit <|
    PushoutCocone.IsColimit.mk hw
      (fun s =>
        Prod.mkHom
          (h₁.desc s.inl.1 s.inr.1 (congrArg Prod.fst s.condition))
          (h₂.desc s.inl.2 s.inr.2 (congrArg Prod.snd s.condition)))
      (fun s => by
        apply Prod.hom_ext
        · simpa using h₁.inl_desc _ _ _
        · simpa using h₂.inl_desc _ _ _)
      (fun s => by
        apply Prod.hom_ext
        · simpa using h₁.inr_desc _ _ _
        · simpa using h₂.inr_desc _ _ _)
      (fun s m hmL hmR => by
        apply Prod.hom_ext
        · apply h₁.hom_ext
          · have hml : k₁ ≫ m.1 = s.inl.1 := by simpa using congrArg Prod.fst hmL
            have hdl : k₁ ≫ h₁.desc s.inl.1 s.inr.1 (congrArg Prod.fst s.condition) =
                s.inl.1 := by
              simpa using h₁.inl_desc s.inl.1 s.inr.1 (congrArg Prod.fst s.condition)
            exact hml.trans hdl.symm
          · have hmr : j₁ ≫ m.1 = s.inr.1 := by simpa using congrArg Prod.fst hmR
            have hdr : j₁ ≫ h₁.desc s.inl.1 s.inr.1 (congrArg Prod.fst s.condition) =
                s.inr.1 := by
              simpa using h₁.inr_desc s.inl.1 s.inr.1 (congrArg Prod.fst s.condition)
            exact hmr.trans hdr.symm
        · apply h₂.hom_ext
          · have hml : k₂ ≫ m.2 = s.inl.2 := by simpa using congrArg Prod.snd hmL
            have hdl : k₂ ≫ h₂.desc s.inl.2 s.inr.2 (congrArg Prod.snd s.condition) =
                s.inl.2 := by
              simpa using h₂.inl_desc s.inl.2 s.inr.2 (congrArg Prod.snd s.condition)
            exact hml.trans hdl.symm
          · have hmr : j₂ ≫ m.2 = s.inr.2 := by simpa using congrArg Prod.snd hmR
            have hdr : j₂ ≫ h₂.desc s.inl.2 s.inr.2 (congrArg Prod.snd s.condition) =
                s.inr.2 := by
              simpa using h₂.inr_desc s.inl.2 s.inr.2 (congrArg Prod.snd s.condition)
            exact hmr.trans hdr.symm)

/-- The first component of a pushout square in a product is a pushout square. -/
theorem isPushout_prod_fst {A₁ B₁ X₁ P₁ A₂ B₂ X₂ P₂ : C}
    {f₁ : A₁ ⟶ B₁} {g₁ : A₁ ⟶ X₁} {k₁ : B₁ ⟶ P₁} {j₁ : X₁ ⟶ P₁}
    {f₂ : A₂ ⟶ B₂} {g₂ : A₂ ⟶ X₂} {k₂ : B₂ ⟶ P₂} {j₂ : X₂ ⟶ P₂}
    (h : IsPushout (Prod.mkHom f₁ f₂) (Prod.mkHom g₁ g₂) (Prod.mkHom k₁ k₂)
      (Prod.mkHom j₁ j₂))
    [HasPushout f₂ g₂] : IsPushout f₁ g₁ k₁ j₁ := by
  have hw₁ : f₁ ≫ k₁ = g₁ ≫ j₁ := congrArg Prod.fst h.w
  -- One commuting proof, reused by every `desc`, so the induced maps agree definitionally.
  have hwS (s : PushoutCocone f₁ g₁) :
      Prod.mkHom f₁ f₂ ≫ Prod.mkHom s.inl (pushout.inl f₂ g₂) =
        Prod.mkHom g₁ g₂ ≫ Prod.mkHom s.inr (pushout.inr f₂ g₂) := by
    apply Prod.hom_ext
    · simpa using s.condition
    · simpa using pushout.condition (f := f₂) (g := g₂)
  refine IsPushout.of_isColimit <|
    PushoutCocone.IsColimit.mk hw₁
      (fun s =>
        (h.desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
          (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s)).1)
      (fun s =>
        congrArg Prod.fst
          (h.inl_desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
            (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s)))
      (fun s =>
        congrArg Prod.fst
          (h.inr_desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
            (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s)))
      (fun s m hmL hmR => by
        let δ : (P₁, P₂) ⟶ (s.pt, pushout f₂ g₂) :=
          h.desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
            (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s)
        let packed : (P₁, P₂) ⟶ (s.pt, pushout f₂ g₂) := Prod.mkHom m δ.2
        have hpack : packed = δ := by
          apply h.hom_ext
          · apply Prod.hom_ext
            · have hδ : k₁ ≫ δ.1 = s.inl :=
                congrArg Prod.fst
                  (h.inl_desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
                    (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s))
              exact hmL.trans hδ.symm
            · rfl
          · apply Prod.hom_ext
            · have hδ : j₁ ≫ δ.1 = s.inr :=
                congrArg Prod.fst
                  (h.inr_desc (Prod.mkHom s.inl (pushout.inl f₂ g₂))
                    (Prod.mkHom s.inr (pushout.inr f₂ g₂)) (hwS s))
              exact hmR.trans hδ.symm
            · rfl
        exact congrArg Prod.fst hpack)

noncomputable def prod_fst_initial {I₁ I₂ : C} (h : IsInitial (I₁, I₂)) : IsInitial I₁ := by
  refine IsInitial.ofUniqueHom (fun X => (h.to (X, I₂)).1) ?_
  intro X f
  exact congrArg Prod.fst (h.hom_ext ((f, 𝟙 I₂) : (I₁, I₂) ⟶ (X, I₂)) (h.to (X, I₂)))

theorem prod_fst_isCylinderMorphism [IsCofibrationCategory C] :
    IsCylinderMorphism (CategoryTheory.Prod.fst C C) where
  map_cofibration _ _ f hf := hf.1
  map_initial _ hI := ⟨prod_fst_initial hI⟩
  map_isPushout _ _ _ _ i f k j h hi := by
    have hi₂ : cofibrations C i.2 := hi.2
    haveI : HasPushout i.2 f.2 :=
      (inferInstance : IsCofibrationCategory C).hasPushout i.2 f.2 hi₂
    simpa using isPushout_prod_fst (f₂ := i.2) (g₂ := f.2) h
  map_weakEquivalence _ _ f hf := hf.1

theorem prod_fst_isIsofibration :
    IsIsofibration (CategoryTheory.Prod.fst C C) := by
  intro x y e
  refine ⟨(y, x.2), Iso.prod e (Iso.refl x.2), rfl, ?_⟩
  simp

theorem prod_fst_isPreFibration [IsCylinderCategory C] :
    IsPreFibration (CategoryTheory.Prod.fst C C) where
  lift_retraction := by
    intro A B s hs hw r hr
    obtain ⟨r₂, hr₂⟩ :=
      IsCylinderCategory.exists_retraction (C := C) s.2 hs.2 hw.2
    refine ⟨(r, r₂), ?_, rfl⟩
    apply Prod.hom_ext
    · exact hr
    · exact hr₂
  lift_factorization := by
    intro A B f Q i w hi hw hiw
    obtain ⟨Q₂, i₂, w₂, hi₂, hw₂, hiw₂⟩ :=
      Cylinder.HomotopyTerminalSlice.brown_factorization (C := C) f.2
    refine ⟨(Q, Q₂), (i, i₂), (w, w₂), rfl, ⟨hi, hi₂⟩, ⟨hw, hw₂⟩, ?_, ?_, ?_⟩
    · apply Prod.hom_ext
      · exact hiw
      · exact hiw₂
    · simp
    · simp

theorem isPreFibration_comp {D E : Type (u + 1)} [Category.{u} D] [Category.{u} E]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    {p : C ⥤ D} {q : D ⥤ E} (hp : IsPreFibration p) (hq : IsPreFibration q)
    (hpM : IsCylinderMorphism p) : IsPreFibration (p ⋙ q) where
  lift_retraction := by
    intro A B s hs hw r hr
    have hs' : cofibrations D (p.map s) := hpM.map_cofibration s hs
    have hw' : weakEquivalences D (p.map s) := hpM.map_weakEquivalence s hw
    obtain ⟨rD, hrD, hqr⟩ := hq.lift_retraction (p.map s) hs' hw' r hr
    obtain ⟨rC, hrC, hpr⟩ := hp.lift_retraction s hs hw rD hrD
    refine ⟨rC, hrC, ?_⟩
    simp [hpr, hqr]
  lift_factorization := by
    intro A B f Q i w hi hw hiw
    obtain ⟨P, iD, wD, e, hiD, hwD, hiwD, hmiD, hmwD⟩ :=
      hq.lift_factorization (p.map f) i w hi hw hiw
    obtain ⟨R, iC, wC, e', hiC, hwC, hiwC, hmiC, hmwC⟩ :=
      hp.lift_factorization f iD wD hiD hwD hiwD
    have eF : (p ⋙ q).obj R = Q := by
      change q.obj (p.obj R) = Q
      rw [e']
      exact e
    refine ⟨R, iC, wC, eF, hiC, hwC, hiwC, ?_, ?_⟩
    · calc
        (p ⋙ q).map iC = q.map (p.map iC) := rfl
        _ = q.map (iD ≫ eqToHom e'.symm) := by rw [hmiC]
        _ = q.map iD ≫ q.map (eqToHom e'.symm) := by simp
        _ = (i ≫ eqToHom e.symm) ≫ eqToHom (congrArg q.obj e'.symm) := by
          rw [hmiD, eqToHom_map]
        _ = i ≫ eqToHom eF.symm := by
          rw [Category.assoc, eqToHom_trans]
    · calc
        (p ⋙ q).map wC = q.map (p.map wC) := rfl
        _ = q.map (eqToHom e' ≫ wD) := by rw [hmwC]
        _ = q.map (eqToHom e') ≫ q.map wD := by simp
        _ = eqToHom (congrArg q.obj e') ≫ (eqToHom e ≫ w) := by
          rw [eqToHom_map, hmwD]
        _ = eqToHom eF ≫ w := by
          rw [← Category.assoc, eqToHom_trans]

theorem isIsofibration_comp {D E : Type (u + 1)} [Category.{u} D] [Category.{u} E]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    {p : C ⥤ D} {q : D ⥤ E} (hp : IsIsofibration p) (hq : IsIsofibration q) :
    IsIsofibration (p ⋙ q) := by
  intro x y e
  obtain ⟨d, e₁, hd, he₁⟩ := hq (p.obj x) y e
  obtain ⟨x', e₂, hx, he₂⟩ := hp x d e₁
  have hobj : (p ⋙ q).obj x' = y := by
    change q.obj (p.obj x') = y
    rw [hx, hd]
  refine ⟨x', e₂, hobj, ?_⟩
  calc
    (p ⋙ q).map e₂.hom = q.map (p.map e₂.hom) := rfl
    _ = q.map (e₁.hom ≫ eqToHom hx.symm) := by rw [he₂]
    _ = q.map e₁.hom ≫ q.map (eqToHom hx.symm) := by simp
    _ = (e.hom ≫ eqToHom hd.symm) ≫ eqToHom (congrArg q.obj hx.symm) := by
      rw [he₁, eqToHom_map]
    _ = e.hom ≫ eqToHom hobj.symm := by
      rw [Category.assoc, eqToHom_trans]

theorem pathObj_left_isLiftingTarget [IsCylinderCategory C] :
    IsLiftingTarget true (PathObj C) C (PathObj.left C) := by
  obtain ⟨hPath, _, hProj, hPre, hIso, _⟩ :=
    (Packages.pathObj_isLiftingTarget (C := C)).1
  have hAcyclic : IsAcyclic (PathObj.left C) :=
    (Packages.pathObj_isLiftingTarget (C := C)).2.1
  have hFstM : IsCylinderMorphism (CategoryTheory.Prod.fst C C) :=
    prod_fst_isCylinderMorphism (C := C)
  have hFstP : IsPreFibration (CategoryTheory.Prod.fst C C) :=
    prod_fst_isPreFibration (C := C)
  have hFstI : IsIsofibration (CategoryTheory.Prod.fst C C) :=
    prod_fst_isIsofibration (C := C)
  exact ⟨hPath, inferInstance, IsCylinderMorphism.comp hProj hFstM,
    isPreFibration_comp hPre hFstP hProj, isIsofibration_comp hIso hFstI, fun _ => hAcyclic⟩

/-- If the image of the marked object is h-terminal, the forgetful map of its homotopy slice is an
acyclic lifting target, so cofibrancy chooses the lift through any prescribed slice object. -/
theorem lift_to_sliceObj_of_base_hTerminal {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    [CategoryWithCofibrations 𝒜] [CategoryWithWeakEquivalences 𝒜] [IsCylinderCategory 𝒜]
    {o : 𝒜} (hcof : IsCofibrantAt.{u + 1, u} 𝒜 o)
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D] {f : 𝒜 ⥤ D}
    (hf : IsCylinderMorphism f) (hbase : IsHTerminal (f.obj o))
    (A : SliceObj (f.obj o)) (hA₀ : A.A₀ = f.obj o) :
    ∃ l : 𝒜 ⥤ SliceObj (f.obj o), IsCylinderMorphism l ∧
      l ⋙ SliceObj.forget (f.obj o) = f ∧ l.obj o = A := by
  have hforget := Packages.sliceObj_isLiftingTarget (f.obj o)
  have hAcyclic := (Packages.sliceObj_forget_isAcyclic_iff (f.obj o)).2 hbase
  have htarget : IsLiftingTarget true (SliceObj (f.obj o)) D (SliceObj.forget (f.obj o)) := by
    rcases hforget with ⟨hS, hD, hF, hP, hIso, _⟩
    exact ⟨hS, hD, hF, hP, hIso, fun _ => hAcyclic⟩
  exact hcof (SliceObj (f.obj o)) D (SliceObj.forget (f.obj o)) htarget A trivial f hf hA₀.symm

/-- Conjugating the two legs of a cofibrant pair by isomorphisms keeps the pair cofibrant. -/
theorem isCofibrantPair_of_iso [IsCofibrationCategory C] {B B' X T T' : C}
    {u : B ⟶ T} {w : X ⟶ T} (h : IsCofibrantPair u w) (eB : B ≅ B') (eT : T ≅ T') :
    IsCofibrantPair (eB.inv ≫ u ≫ eT.hom) (w ≫ eT.hom) := by
  rcases h with ⟨I, hI, P, k, j, hP, m, hkm, hjm, hm⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  have hk' : (eB.inv ≫ k) ≫ (m ≫ eT.hom) = eB.inv ≫ u ≫ eT.hom := by
    rw [Category.assoc, ← Category.assoc k m eT.hom, hkm]
  have hj' : j ≫ (m ≫ eT.hom) = w ≫ eT.hom := by
    rw [← Category.assoc j m eT.hom, hjm]
  have hm' : cofibrations C (m ≫ eT.hom) :=
    hcof.isMultiplicative.comp_mem m eT.hom hm
      (hcof.isomorphisms_le eT.hom (by infer_instance))
  have hto : hI.to B ≫ eB.hom = (Iso.refl I).hom ≫ hI.to B' := hI.hom_ext _ _
  have htg : hI.to X ≫ (Iso.refl X).hom = (Iso.refl I).hom ≫ hI.to X := hI.hom_ext _ _
  have hinl : k ≫ (Iso.refl P).hom = eB.hom ≫ (eB.inv ≫ k) := by
    simp [Category.assoc, eB.hom_inv_id]
  have hinr : j ≫ (Iso.refl P).hom = (Iso.refl X).hom ≫ j := by simp
  have hpush : IsPushout (hI.to B') (hI.to X) (eB.inv ≫ k) j :=
    hP.of_iso (Iso.refl I) eB (Iso.refl X) (Iso.refl P) hto htg hinl hinr
  exact ⟨I, hI, P, eB.inv ≫ k, j, hpush, m ≫ eT.hom, hk', hj', hm'⟩

lemma sliceObj_ext {X : C} {A B : SliceObj X} (h₀ : A.A₀ = B.A₀) (hf : A.Af = B.Af)
    (ha : A.a ≫ eqToHom hf = eqToHom h₀ ≫ B.a) (hx : A.x ≫ eqToHom hf = B.x) : A = B := by
  cases A
  cases B
  dsimp at h₀ hf ha hx
  cases h₀
  cases hf
  simp [eqToHom_refl] at ha hx
  cases ha
  cases hx
  congr 1

set_option backward.isDefEq.respectTransparency false in
lemma sliceObj_eqToHom_v₀ {X : C} {A B : SliceObj X} (h : A = B) :
    (eqToHom h).v₀ = eqToHom (congrArg SliceObj.A₀ h) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma sliceObj_eqToHom_vf {X : C} {A B : SliceObj X} (h : A = B) :
    (eqToHom h).vf = eqToHom (congrArg SliceObj.Af h) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma sliceObj_comp_v₀ {X : C} {A B D : SliceObj X} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).v₀ = f.v₀ ≫ g.v₀ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma sliceObj_comp_vf {X : C} {A B D : SliceObj X} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).vf = f.vf ≫ g.vf := rfl

lemma sliceObj_id_v₀ {X : C} (A : SliceObj X) :
    SliceObj.Hom.v₀ (𝟙 A) = 𝟙 A.A₀ := by
  set_option backward.isDefEq.respectTransparency false in
  rfl

lemma sliceObj_id_vf {X : C} (A : SliceObj X) :
    SliceObj.Hom.vf (𝟙 A) = 𝟙 A.Af := by
  set_option backward.isDefEq.respectTransparency false in
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma sliceMap_map_v₀ {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory C] {F : C ⥤ D}
    (hF : IsCylinderMorphism F) (X : C) {A B : SliceObj X} (f : A ⟶ B) :
    ((Cylinder.HomotopyTerminalSlice.sliceMap hF X).map f).v₀ = F.map f.v₀ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma sliceMap_map_vf {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory C] {F : C ⥤ D}
    (hF : IsCylinderMorphism F) (X : C) {A B : SliceObj X} (f : A ⟶ B) :
    ((Cylinder.HomotopyTerminalSlice.sliceMap hF X).map f).vf = F.map f.vf := rfl

/-- The concrete slice functor of an isofibration is an isofibration. -/
theorem sliceMap_isIsofibration {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
    [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y]
    {p : X ⥤ Y} (hp : IsCylinderMorphism p) (hiso : IsIsofibration p) (x : X) :
    IsIsofibration (Cylinder.HomotopyTerminalSlice.sliceMap hp x) := by
  intro A B e
  have hv₀ : e.hom.v₀ ≫ e.inv.v₀ = 𝟙 _ := congrArg SliceObj.Hom.v₀ e.hom_inv_id
  have hv₀' : e.inv.v₀ ≫ e.hom.v₀ = 𝟙 _ := congrArg SliceObj.Hom.v₀ e.inv_hom_id
  have hvf : e.hom.vf ≫ e.inv.vf = 𝟙 _ := congrArg SliceObj.Hom.vf e.hom_inv_id
  have hvf' : e.inv.vf ≫ e.hom.vf = 𝟙 _ := congrArg SliceObj.Hom.vf e.inv_hom_id
  let e₀ : p.obj A.A₀ ≅ B.A₀ := ⟨e.hom.v₀, e.inv.v₀, hv₀, hv₀'⟩
  let ef : p.obj A.Af ≅ B.Af := ⟨e.hom.vf, e.inv.vf, hvf, hvf'⟩
  obtain ⟨A₀', ε₀, hA₀, hε₀⟩ := hiso A.A₀ B.A₀ e₀
  obtain ⟨Af', εf, hAf, hεf⟩ := hiso A.Af B.Af ef
  have hcofX := (inferInstance : IsCofibrationCategory X)
  have hweX : (weakEquivalences X).IsMultiplicative :=
    IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)
  let a' : A₀' ⟶ Af' := ε₀.inv ≫ A.a ≫ εf.hom
  let x' : x ⟶ Af' := A.x ≫ εf.hom
  have hx'cof : cofibrations X x' :=
    hcofX.isMultiplicative.comp_mem A.x εf.hom A.x_cofibration
      (hcofX.isomorphisms_le εf.hom (by infer_instance))
  have hx'we : weakEquivalences X x' :=
    hweX.comp_mem A.x εf.hom A.x_weakEquivalence
      ((inferInstance : IsCylinderCategory X).isomorphisms_le_weakEquivalences
        εf.hom (by infer_instance))
  let A' : SliceObj x :=
    { A₀ := A₀'
      Af := Af'
      a := a'
      x := x'
      cofibrant := isCofibrantPair_of_iso A.cofibrant ε₀ εf
      x_cofibration := hx'cof
      x_weakEquivalence := hx'we }
  have hε₀inv : p.map ε₀.inv = eqToHom hA₀ ≫ e₀.inv := by
    have hmul : p.map ε₀.hom ≫ p.map ε₀.inv = 𝟙 (p.obj A.A₀) := by
      rw [← p.map_comp, ε₀.hom_inv_id, p.map_id]
    rw [hε₀] at hmul
    have hleft : (eqToHom hA₀ ≫ e₀.inv) ≫ (e₀.hom ≫ eqToHom hA₀.symm) = 𝟙 _ := by
      simp [Category.assoc, e₀.inv_hom_id, eqToHom_trans]
    calc
      p.map ε₀.inv = ((eqToHom hA₀ ≫ e₀.inv) ≫ (e₀.hom ≫ eqToHom hA₀.symm)) ≫
          p.map ε₀.inv := by rw [hleft, Category.id_comp]
      _ = (eqToHom hA₀ ≫ e₀.inv) ≫ ((e₀.hom ≫ eqToHom hA₀.symm) ≫ p.map ε₀.inv) := by
        simp [Category.assoc]
      _ = (eqToHom hA₀ ≫ e₀.inv) ≫ 𝟙 _ := by rw [hmul]
      _ = eqToHom hA₀ ≫ e₀.inv := Category.comp_id _
  have haImg : p.map a' ≫ eqToHom hAf = eqToHom hA₀ ≫ B.a := by
    have hnat : p.map A.a ≫ ef.hom = e₀.hom ≫ B.a := e.hom.a_vf
    calc
      p.map a' ≫ eqToHom hAf = p.map ε₀.inv ≫ p.map A.a ≫ p.map εf.hom ≫ eqToHom hAf := by
        simp [a', Functor.map_comp, Category.assoc]
      _ = p.map ε₀.inv ≫ p.map A.a ≫ ef.hom := by
        simp [hεf, Category.assoc, eqToHom_trans]
      _ = p.map ε₀.inv ≫ e₀.hom ≫ B.a := by rw [hnat]
      _ = (eqToHom hA₀ ≫ e₀.inv) ≫ e₀.hom ≫ B.a := by rw [hε₀inv]
      _ = eqToHom hA₀ ≫ B.a := by simp [Category.assoc, e₀.inv_hom_id]
  have hxImg : p.map x' ≫ eqToHom hAf = B.x := by
    calc
      p.map x' ≫ eqToHom hAf = p.map A.x ≫ p.map εf.hom ≫ eqToHom hAf := by
        simp [x', Functor.map_comp, Category.assoc]
      _ = p.map A.x ≫ ef.hom := by simp [hεf, Category.assoc, eqToHom_trans]
      _ = B.x := e.hom.x_vf
  have hobj : (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj A' = B :=
    sliceObj_ext hA₀ hAf
      (by simpa [Cylinder.HomotopyTerminalSlice.sliceMap, A', a'] using haImg)
      (by simpa [Cylinder.HomotopyTerminalSlice.sliceMap, A', x'] using hxImg)
  have hhom_a : A.a ≫ εf.hom = ε₀.hom ≫ a' := by
    show A.a ≫ εf.hom = ε₀.hom ≫ (ε₀.inv ≫ A.a ≫ εf.hom)
    rw [← Category.assoc, ε₀.hom_inv_id, Category.id_comp]
  have hhom_x : A.x ≫ εf.hom = x' := by
    show A.x ≫ εf.hom = A.x ≫ εf.hom
    rfl
  have hinv_a : a' ≫ εf.inv = ε₀.inv ≫ A.a := by
    show (ε₀.inv ≫ A.a ≫ εf.hom) ≫ εf.inv = ε₀.inv ≫ A.a
    rw [Category.assoc, Category.assoc, εf.hom_inv_id, Category.comp_id]
  have hinv_x : x' ≫ εf.inv = A.x := by
    show (A.x ≫ εf.hom) ≫ εf.inv = A.x
    rw [Category.assoc, εf.hom_inv_id, Category.comp_id]
  let ε : A ≅ A' :=
    { hom := ⟨ε₀.hom, εf.hom, hhom_a, hhom_x⟩
      inv := ⟨ε₀.inv, εf.inv, hinv_a, hinv_x⟩
      hom_inv_id := by
        apply SliceObj.Hom.ext
        · rw [sliceObj_comp_v₀, sliceObj_id_v₀]
          exact ε₀.hom_inv_id
        · rw [sliceObj_comp_vf, sliceObj_id_vf]
          exact εf.hom_inv_id
      inv_hom_id := by
        apply SliceObj.Hom.ext
        · rw [sliceObj_comp_v₀, sliceObj_id_v₀]
          exact ε₀.inv_hom_id
        · rw [sliceObj_comp_vf, sliceObj_id_vf]
          exact εf.inv_hom_id }
  refine ⟨A', ε, hobj, ?_⟩
  apply SliceObj.Hom.ext
  · rw [sliceMap_map_v₀, sliceObj_comp_v₀, sliceObj_eqToHom_v₀]
    have hA₀eq : congrArg SliceObj.A₀ hobj.symm = hA₀.symm := Subsingleton.elim _ _
    have hv : ε.hom.v₀ = ε₀.hom := rfl
    have he : e₀.hom = e.hom.v₀ := rfl
    rw [hv, hε₀, he]
    exact congrArg (fun q => e.hom.v₀ ≫ eqToHom q) hA₀eq.symm
  · rw [sliceMap_map_vf, sliceObj_comp_vf, sliceObj_eqToHom_vf]
    have hAfeq : congrArg SliceObj.Af hobj.symm = hAf.symm := Subsingleton.elim _ _
    have hv : ε.hom.vf = εf.hom := rfl
    have he : ef.hom = e.hom.vf := rfl
    rw [hv, hεf, he]
    exact congrArg (fun q => e.hom.vf ≫ eqToHom q) hAfeq.symm

/-- The structure map `A₀ ⟶ A_f` of a slice object is a cofibration. -/
theorem sliceObj_a_cofibration [IsCylinderCategory C] {X : C} (A : SliceObj X) :
    cofibrations C A.a := by
  rcases A.cofibrant with ⟨I, hI, P, k, j, hP, m, hkm, _, hm⟩
  have hcof : IsCofibrationCategory C := inferInstance
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hk : cofibrations C k :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP
      (hcof.initial_cofibration hI X)
  simpa [hkm] using hcof.isMultiplicative.comp_mem k m hk hm

/-- A retraction of a trivial cofibration in the homotopy slice lifts along `sliceMap` when `p`
lifts retractions of trivial cofibrations. -/
theorem sliceMap_lift_retraction {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
    [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y]
    {p : X ⥤ Y} (hp : IsCylinderMorphism p) (hpre : IsPreFibration p) (x : X) :
    ∀ ⦃A B : SliceObj x⦄ (s : A ⟶ B), cofibrations (SliceObj x) s →
      weakEquivalences (SliceObj x) s →
      ∀ r : (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj B ⟶ (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj A,
        (Cylinder.HomotopyTerminalSlice.sliceMap hp x).map s ≫ r = 𝟙 _ →
        ∃ r' : B ⟶ A, s ≫ r' = 𝟙 A ∧ (Cylinder.HomotopyTerminalSlice.sliceMap hp x).map r' = r := by
  intro A B s hs hw r hr
  rcases hs with ⟨hs₀, hglue⟩
  rcases hglue with ⟨P, k, j, hP, m, hkm, hjm, hm⟩
  have hcofX : IsCofibrationCategory X := inferInstance
  letI : (cofibrations X).IsStableUnderCobaseChange := hcofX.isStableUnderCobaseChange
  letI : (cofibrations X).IsMultiplicative := hcofX.isMultiplicative
  have hrv : p.map s.v₀ ≫ r.v₀ = 𝟙 (p.obj A.A₀) := by
    have h := congrArg SliceObj.Hom.v₀ hr
    rw [sliceObj_comp_v₀, sliceMap_map_v₀, sliceObj_id_v₀] at h
    exact h
  have hrfImg : p.map s.vf ≫ r.vf = 𝟙 (p.obj A.Af) := by
    have h := congrArg SliceObj.Hom.vf hr
    rw [sliceObj_comp_vf, sliceMap_map_vf, sliceObj_id_vf] at h
    exact h
  obtain ⟨r₀, hr₀, hpr₀⟩ := hpre.lift_retraction s.v₀ hs₀ hw r.v₀ hrv
  have haCof : cofibrations X A.a := sliceObj_a_cofibration A
  have hkWe : weakEquivalences X k :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := X) s.v₀ A.a j k hP.flip hs₀ hw
  have hvfWe : weakEquivalences X s.vf :=
    Cylinder.HomotopyTerminalSlice.sliceObjHom_vf_weakEquivalence s
  have hmWe : weakEquivalences X m :=
    (IsCylinderCategory.twoOutOfSix (C := X) (𝟙 A.Af) k m
      (by rw [Category.id_comp]; exact hkWe)
      (by rw [hkm]; exact hvfWe)).2.2.1
  have hcomm_t : A.a ≫ 𝟙 A.Af = s.v₀ ≫ r₀ ≫ A.a := by
    rw [Category.comp_id, ← Category.assoc, hr₀, Category.id_comp]
  let t : P ⟶ A.Af := hP.desc (𝟙 A.Af) (r₀ ≫ A.a) hcomm_t
  have hkt : k ≫ t = 𝟙 A.Af := hP.inl_desc (𝟙 A.Af) (r₀ ≫ A.a) hcomm_t
  have hjt : j ≫ t = r₀ ≫ A.a := hP.inr_desc (𝟙 A.Af) (r₀ ≫ A.a) hcomm_t
  have hPimg := hp.map_isPushout A.a s.v₀ k j hP haCof
  have hraf : p.map B.a ≫ r.vf = r.v₀ ≫ p.map A.a := by
    set_option backward.isDefEq.respectTransparency false in
    exact r.a_vf
  have hmt : p.map m ≫ r.vf = p.map t := by
    apply hPimg.hom_ext
    · set_option backward.isDefEq.respectTransparency false in
      rw [← Category.assoc, ← p.map_comp, hkm, hrfImg, ← p.map_id A.Af, ← hkt, p.map_comp]
    · set_option backward.isDefEq.respectTransparency false in
      rw [← Category.assoc, ← p.map_comp, hjm, hraf, ← hpr₀, ← p.map_comp, ← hjt, p.map_comp]
  haveI : HasPushout m t := hcofX.hasPushout m t hm
  let inlQ : B.Af ⟶ pushout m t := pushout.inl m t
  let inrQ : A.Af ⟶ pushout m t := pushout.inr m t
  have hQp : IsPushout m t inlQ inrQ := IsPushout.of_hasPushout m t
  have hinrCof : cofibrations X inrQ :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hQp.flip hm
  have hinrWe : weakEquivalences X inrQ :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := X) m t inlQ inrQ hQp hm hmWe
  have hQpImg := hp.map_isPushout m t inlQ inrQ hQp hm
  have hcommρ : p.map m ≫ r.vf = p.map t ≫ 𝟙 (p.obj A.Af) := by
    rw [hmt, Category.comp_id]
  let ρD : p.obj (pushout m t) ⟶ p.obj A.Af := hQpImg.desc r.vf (𝟙 _) hcommρ
  have hρD : p.map inrQ ≫ ρD = 𝟙 _ := hQpImg.inr_desc r.vf (𝟙 _) hcommρ
  obtain ⟨ρ, hρ, hpρ⟩ := hpre.lift_retraction inrQ hinrCof hinrWe ρD hρD
  let rf : B.Af ⟶ A.Af := inlQ ≫ ρ
  have hmrf : m ≫ rf = t := by
    calc
      m ≫ rf = (m ≫ inlQ) ≫ ρ := by simp [rf, Category.assoc]
      _ = (t ≫ inrQ) ≫ ρ := by rw [hQp.w]
      _ = t ≫ inrQ ≫ ρ := by simp [Category.assoc]
      _ = t ≫ 𝟙 A.Af := by rw [hρ]
      _ = t := Category.comp_id _
  have hsvf : s.vf ≫ rf = 𝟙 A.Af := by
    calc
      s.vf ≫ rf = (k ≫ m) ≫ rf := by rw [← hkm]
      _ = k ≫ m ≫ rf := by simp [Category.assoc]
      _ = k ≫ t := by rw [hmrf]
      _ = 𝟙 A.Af := hkt
  have ha_rf : B.a ≫ rf = r₀ ≫ A.a := by
    calc
      B.a ≫ rf = (j ≫ m) ≫ rf := by rw [← hjm]
      _ = j ≫ m ≫ rf := by simp [Category.assoc]
      _ = j ≫ t := by rw [hmrf]
      _ = r₀ ≫ A.a := hjt
  have hx_rf : B.x ≫ rf = A.x := by
    calc
      B.x ≫ rf = (A.x ≫ s.vf) ≫ rf := by rw [← s.x_vf]
      _ = A.x ≫ s.vf ≫ rf := by simp [Category.assoc]
      _ = A.x ≫ 𝟙 A.Af := by rw [hsvf]
      _ = A.x := Category.comp_id _
  have hprf : p.map rf = r.vf := by
    have hstep : p.map rf = p.map inlQ ≫ ρD := by
      calc
        p.map rf = p.map (inlQ ≫ ρ) := rfl
        _ = p.map inlQ ≫ p.map ρ := p.map_comp _ _
        _ = p.map inlQ ≫ ρD := by rw [hpρ]
    rw [hstep]
    exact hQpImg.inl_desc r.vf (𝟙 (p.obj A.Af)) hcommρ
  let r' : B ⟶ A := ⟨r₀, rf, ha_rf, hx_rf⟩
  refine ⟨r', ?_, ?_⟩
  · apply SliceObj.Hom.ext
    · rw [sliceObj_comp_v₀, sliceObj_id_v₀]
      exact hr₀
    · rw [sliceObj_comp_vf, sliceObj_id_vf]
      exact hsvf
  · apply SliceObj.Hom.ext
    · rw [sliceMap_map_v₀]
      exact hpr₀
    · rw [sliceMap_map_vf]
      exact hprf

/-- Two pushouts of the same span are uniquely isomorphic, compatibly with the inclusions. -/
theorem pushout_uniqueIso {A B X P P' : C} {i : A ⟶ B} {f : A ⟶ X}
    {k : B ⟶ P} {j : X ⟶ P} {k' : B ⟶ P'} {j' : X ⟶ P'}
    (h : IsPushout i f k j) (h' : IsPushout i f k' j') :
    ∃ e : P ≅ P', k ≫ e.hom = k' ∧ j ≫ e.hom = j' := by
  let eHom : P ⟶ P' := h.desc k' j' h'.w
  let eInv : P' ⟶ P := h'.desc k j h.w
  have hkHom : k ≫ eHom = k' := h.inl_desc k' j' h'.w
  have hjHom : j ≫ eHom = j' := h.inr_desc k' j' h'.w
  have hkInv : k' ≫ eInv = k := h'.inl_desc k j h.w
  have hjInv : j' ≫ eInv = j := h'.inr_desc k j h.w
  let e : P ≅ P' :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply h.hom_ext
        · calc
            k ≫ (eHom ≫ eInv) = (k ≫ eHom) ≫ eInv := by rw [Category.assoc]
            _ = k' ≫ eInv := by rw [hkHom]
            _ = k := hkInv
            _ = k ≫ 𝟙 P := by rw [Category.comp_id]
        · calc
            j ≫ (eHom ≫ eInv) = (j ≫ eHom) ≫ eInv := by rw [Category.assoc]
            _ = j' ≫ eInv := by rw [hjHom]
            _ = j := hjInv
            _ = j ≫ 𝟙 P := by rw [Category.comp_id]
      inv_hom_id := by
        apply h'.hom_ext
        · calc
            k' ≫ (eInv ≫ eHom) = (k' ≫ eInv) ≫ eHom := by rw [Category.assoc]
            _ = k ≫ eHom := by rw [hkInv]
            _ = k' := hkHom
            _ = k' ≫ 𝟙 P' := by rw [Category.comp_id]
        · calc
            j' ≫ (eInv ≫ eHom) = (j' ≫ eInv) ≫ eHom := by rw [Category.assoc]
            _ = j ≫ eHom := by rw [hjInv]
            _ = j' := hjHom
            _ = j' ≫ 𝟙 P' := by rw [Category.comp_id] }
  exact ⟨e, hkHom, hjHom⟩

theorem comp_assoc4_left {A B D E F : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : E ⟶ F) :
    ((f ≫ g) ≫ h) ≫ i = f ≫ ((g ≫ h) ≫ i) := by
  calc
    ((f ≫ g) ≫ h) ≫ i = (f ≫ g) ≫ (h ≫ i) := Category.assoc _ _ _
    _ = f ≫ (g ≫ (h ≫ i)) := Category.assoc _ _ _
    _ = f ≫ ((g ≫ h) ≫ i) := congrArg (fun z => f ≫ z) (Category.assoc _ _ _).symm

/-- Postcomposing both legs of a cofibrant pair by a cofibration keeps the pair cofibrant. -/
theorem cofibrantPair_postcomp [IsCylinderCategory C] {B X T T' : C} {u : B ⟶ T} {w : X ⟶ T}
    (h : IsCofibrantPair u w) (v : T ⟶ T') (hv : cofibrations C v) :
    IsCofibrantPair (u ≫ v) (w ≫ v) := by
  obtain ⟨I, hI, P, k, j, hP, m, hkm, hjm, hm⟩ := h
  have hcof : IsCofibrationCategory C := inferInstance
  refine ⟨I, hI, P, k, j, hP, m ≫ v, ?_, ?_, hcof.isMultiplicative.comp_mem m v hm hv⟩
  · rw [← Category.assoc, hkm]
  · rw [← Category.assoc, hjm]

/-- Pushing the first leg of a cofibrant pair out along a cofibration keeps the pair cofibrant. -/
theorem cofibrantPair_pushoutFirst [IsCylinderCategory C] {A Af X P L : C} {a : A ⟶ Af}
    {x : X ⟶ Af} (hpair : IsCofibrantPair a x) (i : A ⟶ P) (hi : cofibrations C i)
    {kP : P ⟶ L} {kA : Af ⟶ L} (hL : IsPushout i a kP kA) :
    IsCofibrantPair kP (x ≫ kA) := by
  classical
  obtain ⟨I, hI, T, tA, tX, hT, mA, htA, htX, hmA⟩ := hpair
  have hcof : IsCofibrationCategory C := inferInstance
  have hIP : cofibrations C (hI.to P) := hcof.initial_cofibration hI P
  letI : HasPushout (hI.to P) (hI.to X) := hcof.hasPushout (hI.to P) (hI.to X) hIP
  let S := pushout (hI.to P) (hI.to X)
  let sP : P ⟶ S := pushout.inl (hI.to P) (hI.to X)
  let sX : X ⟶ S := pushout.inr (hI.to P) (hI.to X)
  let hS : IsPushout (hI.to P) (hI.to X) sP sX := IsPushout.of_hasPushout (hI.to P) (hI.to X)
  have hScomm : hI.to A ≫ (i ≫ sP) = hI.to X ≫ sX := hI.hom_ext _ _
  let tS : T ⟶ S := hT.desc (i ≫ sP) sX hScomm
  have htS_A : tA ≫ tS = i ≫ sP := hT.inl_desc (i ≫ sP) sX hScomm
  have htS_X : tX ≫ tS = sX := hT.inr_desc (i ≫ sP) sX hScomm
  letI : HasPushout mA tS := hcof.hasPushout mA tS hmA
  let R := pushout mA tS
  let rAf : Af ⟶ R := pushout.inl mA tS
  let rS : S ⟶ R := pushout.inr mA tS
  let hR : IsPushout mA tS rAf rS := IsPushout.of_hasPushout mA tS
  have hSdesc : hI.to P ≫ kP = hI.to X ≫ (x ≫ kA) := hI.hom_ext _ _
  let sL : S ⟶ L := hS.desc kP (x ≫ kA) hSdesc
  have hsL_P : sP ≫ sL = kP := hS.inl_desc kP (x ≫ kA) hSdesc
  have hsL_X : sX ≫ sL = x ≫ kA := hS.inr_desc kP (x ≫ kA) hSdesc
  have hRcompat : mA ≫ kA = tS ≫ sL := by
    apply hT.hom_ext
    · calc
        tA ≫ (mA ≫ kA) = (tA ≫ mA) ≫ kA := by rw [Category.assoc]
        _ = a ≫ kA := by rw [htA]
        _ = i ≫ kP := by rw [hL.w]
        _ = i ≫ (sP ≫ sL) := by rw [hsL_P]
        _ = (i ≫ sP) ≫ sL := by rw [Category.assoc]
        _ = (tA ≫ tS) ≫ sL := by rw [htS_A]
        _ = tA ≫ (tS ≫ sL) := by rw [Category.assoc]
    · calc
        tX ≫ (mA ≫ kA) = (tX ≫ mA) ≫ kA := by rw [Category.assoc]
        _ = x ≫ kA := by rw [htX]
        _ = sX ≫ sL := by rw [hsL_X]
        _ = (tX ≫ tS) ≫ sL := by rw [htS_X]
        _ = tX ≫ (tS ≫ sL) := by rw [Category.assoc]
  let φ : R ⟶ L := hR.desc kA sL hRcompat
  have hφ_Af : rAf ≫ φ = kA := hR.inl_desc kA sL hRcompat
  have hφ_S : rS ≫ φ = sL := hR.inr_desc kA sL hRcompat
  have hSboundary : i ≫ sP ≫ rS = a ≫ rAf := by
    calc
      i ≫ (sP ≫ rS) = (i ≫ sP) ≫ rS := by rw [Category.assoc]
      _ = (tA ≫ tS) ≫ rS := by rw [htS_A]
      _ = tA ≫ (tS ≫ rS) := by rw [Category.assoc]
      _ = tA ≫ (mA ≫ rAf) := by rw [hR.w]
      _ = (tA ≫ mA) ≫ rAf := by rw [Category.assoc]
      _ = a ≫ rAf := by rw [htA]
  let ψ : L ⟶ R := hL.desc (sP ≫ rS) rAf hSboundary
  have hψ_P : kP ≫ ψ = sP ≫ rS := hL.inl_desc (sP ≫ rS) rAf hSboundary
  have hψ_Af : kA ≫ ψ = rAf := hL.inr_desc (sP ≫ rS) rAf hSboundary
  have hsXrS : sX ≫ rS = x ≫ rAf := by
    calc
      sX ≫ rS = (tX ≫ tS) ≫ rS := by rw [htS_X]
      _ = tX ≫ (tS ≫ rS) := by rw [Category.assoc]
      _ = tX ≫ (mA ≫ rAf) := by rw [hR.w]
      _ = (tX ≫ mA) ≫ rAf := by rw [Category.assoc]
      _ = x ≫ rAf := by rw [htX]
  have hφψ : φ ≫ ψ = 𝟙 R := by
    apply hR.hom_ext
    · calc
        rAf ≫ (φ ≫ ψ) = (rAf ≫ φ) ≫ ψ := by rw [Category.assoc]
        _ = kA ≫ ψ := by rw [hφ_Af]
        _ = rAf := hψ_Af
        _ = rAf ≫ 𝟙 R := by rw [Category.comp_id]
    · apply hS.hom_ext
      · have hstep : rS ≫ (φ ≫ ψ) = sL ≫ ψ := by
          rw [← Category.assoc, hφ_S]
        calc
          sP ≫ (rS ≫ (φ ≫ ψ)) = sP ≫ (sL ≫ ψ) := by rw [hstep]
          _ = (sP ≫ sL) ≫ ψ := by rw [Category.assoc]
          _ = kP ≫ ψ := by rw [hsL_P]
          _ = sP ≫ rS := hψ_P
          _ = sP ≫ rS ≫ 𝟙 R := by rw [Category.comp_id]
      · have hstep : rS ≫ (φ ≫ ψ) = sL ≫ ψ := by
          rw [← Category.assoc, hφ_S]
        calc
          sX ≫ (rS ≫ (φ ≫ ψ)) = sX ≫ (sL ≫ ψ) := by rw [hstep]
          _ = (sX ≫ sL) ≫ ψ := by rw [Category.assoc]
          _ = (x ≫ kA) ≫ ψ := by rw [hsL_X]
          _ = x ≫ (kA ≫ ψ) := by rw [Category.assoc]
          _ = x ≫ rAf := by rw [hψ_Af]
          _ = sX ≫ rS := hsXrS.symm
          _ = sX ≫ rS ≫ 𝟙 R := by rw [Category.comp_id]
  have hψφ : ψ ≫ φ = 𝟙 L := by
    apply hL.hom_ext
    · calc
        kP ≫ (ψ ≫ φ) = (kP ≫ ψ) ≫ φ := by rw [Category.assoc]
        _ = (sP ≫ rS) ≫ φ := by rw [hψ_P]
        _ = sP ≫ (rS ≫ φ) := by rw [Category.assoc]
        _ = sP ≫ sL := by rw [hφ_S]
        _ = kP := hsL_P
        _ = kP ≫ 𝟙 L := by rw [Category.comp_id]
    · calc
        kA ≫ (ψ ≫ φ) = (kA ≫ ψ) ≫ φ := by rw [Category.assoc]
        _ = rAf ≫ φ := by rw [hψ_Af]
        _ = kA := hφ_Af
        _ = kA ≫ 𝟙 L := by rw [Category.comp_id]
  let e : R ≅ L := ⟨φ, ψ, hφψ, hψφ⟩
  haveI : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have hrS : cofibrations C rS :=
    hcof.isStableUnderCobaseChange.of_isPushout hR.flip hmA
  have hφcof : cofibrations C φ :=
    hcof.isomorphisms_le φ (by infer_instance)
  have hsLcof : cofibrations C sL := by
    have hcomp := hcof.isMultiplicative.comp_mem rS φ hrS hφcof
    rw [hφ_S] at hcomp
    exact hcomp
  exact ⟨I, hI, S, sP, sX, hS, sL, hsL_P, hsL_X, hsLcof⟩

/-- A cofibration followed by a weak equivalence in the homotopy slice lifts along `sliceMap`
when `p` lifts such factorizations. -/
theorem sliceMap_lift_factorization {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
    [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]
    {p : X ⥤ Y} (hp : IsCylinderMorphism p) (hpre : IsPreFibration p) (x : X) :
    ∀ ⦃A B : SliceObj x⦄ (f : A ⟶ B) ⦃Q : SliceObj (p.obj x)⦄
      (i : (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj A ⟶ Q)
      (w : Q ⟶ (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj B),
      cofibrations (SliceObj (p.obj x)) i →
      weakEquivalences (SliceObj (p.obj x)) w →
      i ≫ w = (Cylinder.HomotopyTerminalSlice.sliceMap hp x).map f →
      ∃ (P : SliceObj x) (i' : A ⟶ P) (w' : P ⟶ B)
        (e : (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj P = Q),
        cofibrations (SliceObj x) i' ∧ weakEquivalences (SliceObj x) w' ∧
          i' ≫ w' = f ∧
          (Cylinder.HomotopyTerminalSlice.sliceMap hp x).map i' = i ≫ eqToHom e.symm ∧
          (Cylinder.HomotopyTerminalSlice.sliceMap hp x).map w' = eqToHom e ≫ w := by
  intro A B f Q i w hi hw hfactor
  rcases hi with ⟨hi₀, hiG⟩
  obtain ⟨Qₗ, qAf, qQ₀, hQₗ, mQ, hmQAf, hmQQ₀, hmQ⟩ := hiG
  have hfactor₀ : i.v₀ ≫ w.v₀ = p.map f.v₀ := by
    have h := congrArg SliceObj.Hom.v₀ hfactor
    rw [sliceObj_comp_v₀, sliceMap_map_v₀] at h
    exact h
  have hfactorf : i.vf ≫ w.vf = p.map f.vf := by
    have h := congrArg SliceObj.Hom.vf hfactor
    rw [sliceObj_comp_vf, sliceMap_map_vf] at h
    exact h
  obtain ⟨P₀, i₀, w₀, e₀, hi₀', hw₀, hcomp₀, hpi₀, hpw₀⟩ :=
    hpre.lift_factorization f.v₀ i.v₀ w.v₀ hi₀ hw hfactor₀
  have hcofX : IsCofibrationCategory X := inferInstance
  have hcofY : IsCofibrationCategory Y := inferInstance
  letI : HasPushout i₀ A.a := hcofX.hasPushout i₀ A.a hi₀'
  let L := pushout i₀ A.a
  let kP : P₀ ⟶ L := pushout.inl i₀ A.a
  let kA : A.Af ⟶ L := pushout.inr i₀ A.a
  let hL : IsPushout i₀ A.a kP kA := IsPushout.of_hasPushout i₀ A.a
  letI : HasPushout (p.map i₀) (p.map A.a) :=
    hcofY.hasPushout (p.map i₀) (p.map A.a) (hp.map_cofibration i₀ hi₀')
  let pL := pushout (p.map i₀) (p.map A.a)
  let pkP : p.obj P₀ ⟶ pL := pushout.inl (p.map i₀) (p.map A.a)
  let pkA : p.obj A.Af ⟶ pL := pushout.inr (p.map i₀) (p.map A.a)
  let hpL : IsPushout (p.map i₀) (p.map A.a) pkP pkA :=
    IsPushout.of_hasPushout (p.map i₀) (p.map A.a)
  have hpmL : IsPushout (p.map i₀) (p.map A.a) (p.map kP) (p.map kA) :=
    hp.map_isPushout i₀ A.a kP kA hL hi₀'
  let eB : Q.A₀ ≅ p.obj P₀ := eqToIso e₀.symm
  have hQL' : IsPushout (p.map i₀) (p.map A.a) (eqToHom e₀ ≫ qQ₀) qAf := by
    apply hQₗ.flip.of_iso (Iso.refl (p.obj A.A₀)) eB (Iso.refl (p.obj A.Af)) (Iso.refl Qₗ)
    · set_option backward.isDefEq.respectTransparency false in
      exact (hpi₀.symm.trans (Category.id_comp (p.map i₀)).symm :
        i.v₀ ≫ eqToHom e₀.symm = 𝟙 (p.obj A.A₀) ≫ p.map i₀)
    · set_option backward.isDefEq.respectTransparency false in
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · have hcancel : eB.hom ≫ eqToHom e₀ = 𝟙 Q.A₀ := by simp [eB]
      simpa [Category.assoc] using congrArg (fun z : Q.A₀ ⟶ Q.A₀ => z ≫ qQ₀) hcancel.symm
    · set_option backward.isDefEq.respectTransparency false in
      exact (Category.comp_id qAf).trans (Category.id_comp qAf).symm
  obtain ⟨eL, heLP, heLA⟩ := pushout_uniqueIso hpmL hQL'
  have heLcof : cofibrations Y eL.hom :=
    hcofY.isomorphisms_le eL.hom (by infer_instance)
  have hmQ' : cofibrations Y (eL.hom ≫ mQ) :=
    hcofY.isMultiplicative.comp_mem eL.hom mQ heLcof hmQ
  have hLd : i₀ ≫ (w₀ ≫ B.a) = A.a ≫ f.vf := by
    calc
      i₀ ≫ (w₀ ≫ B.a) = (i₀ ≫ w₀) ≫ B.a := by rw [Category.assoc]
      _ = f.v₀ ≫ B.a := by rw [hcomp₀]
      _ = A.a ≫ f.vf := f.a_vf.symm
  let d : L ⟶ B.Af := hL.desc (w₀ ≫ B.a) f.vf hLd
  have hkdP : kP ≫ d = w₀ ≫ B.a := hL.inl_desc (w₀ ≫ B.a) f.vf hLd
  have hkdA : kA ≫ d = f.vf := hL.inr_desc (w₀ ≫ B.a) f.vf hLd
  have hw_a : Q.a ≫ w.vf = w.v₀ ≫ p.map B.a := by
    set_option backward.isDefEq.respectTransparency false in
    exact w.a_vf
  have hbase : (eqToHom e₀ ≫ w.v₀) ≫ p.map B.a = eqToHom e₀ ≫ (Q.a ≫ w.vf) := by
    set_option backward.isDefEq.respectTransparency false in
    calc
      (eqToHom e₀ ≫ w.v₀) ≫ p.map B.a = eqToHom e₀ ≫ (w.v₀ ≫ p.map B.a) :=
        Category.assoc _ _ _
      _ = eqToHom e₀ ≫ (Q.a ≫ w.vf) := by rw [← hw_a]
  have hdmap : p.map d = (eL.hom ≫ mQ) ≫ w.vf := by
    apply hpmL.hom_ext
    · set_option backward.isDefEq.respectTransparency false in
      calc
        p.map kP ≫ p.map d = p.map (kP ≫ d) := by rw [p.map_comp]
        _ = p.map (w₀ ≫ B.a) := by rw [hkdP]
        _ = p.map w₀ ≫ p.map B.a := by rw [p.map_comp]
        _ = (eqToHom e₀ ≫ w.v₀) ≫ p.map B.a := congrArg (fun z => z ≫ p.map B.a) hpw₀
        _ = eqToHom e₀ ≫ (Q.a ≫ w.vf) := hbase
        _ = eqToHom e₀ ≫ ((qQ₀ ≫ mQ) ≫ w.vf) := by rw [← hmQQ₀]
        _ = eqToHom e₀ ≫ (qQ₀ ≫ (mQ ≫ w.vf)) := by rw [Category.assoc]
        _ = (eqToHom e₀ ≫ qQ₀) ≫ (mQ ≫ w.vf) := by rw [← Category.assoc]
        _ = (p.map kP ≫ eL.hom) ≫ (mQ ≫ w.vf) := by rw [heLP]
        _ = p.map kP ≫ ((eL.hom ≫ mQ) ≫ w.vf) := by
          rw [Category.assoc, Category.assoc]
    · rw [← p.map_comp, hkdA, ← hfactorf, ← hmQAf, ← heLA]
      exact comp_assoc4_left (p.map kA) eL.hom mQ w.vf
  have hwf : weakEquivalences Y w.vf :=
    Cylinder.HomotopyTerminalSlice.sliceObjHom_vf_weakEquivalence w
  obtain ⟨P_f, c, w_f, e_f, hc, hw_f, hcw, hpc, hpw_f⟩ :=
    hpre.lift_factorization d (eL.hom ≫ mQ) w.vf hmQ' hwf hdmap.symm
  have hkAcof : cofibrations X kA :=
    hcofX.isStableUnderCobaseChange.of_isPushout hL.flip hi₀'
  let aP : P₀ ⟶ P_f := kP ≫ c
  let xP : x ⟶ P_f := A.x ≫ kA ≫ c
  have hpair₀ : IsCofibrantPair kP (A.x ≫ kA) :=
    cofibrantPair_pushoutFirst A.cofibrant i₀ hi₀' hL
  have hpair : IsCofibrantPair aP xP := by
    simpa [aP, xP] using cofibrantPair_postcomp hpair₀ c hc
  have hxcof : cofibrations X xP := by
    have hkAx : cofibrations X (A.x ≫ kA) :=
      hcofX.isMultiplicative.comp_mem A.x kA A.x_cofibration hkAcof
    simpa [xP] using hcofX.isMultiplicative.comp_mem (A.x ≫ kA) c hkAx hc
  have hxw : xP ≫ w_f = B.x := by
    calc
      xP ≫ w_f = (A.x ≫ kA ≫ c) ≫ w_f := rfl
      _ = A.x ≫ (kA ≫ (c ≫ w_f)) := by
        rw [Category.assoc, Category.assoc]
      _ = A.x ≫ (kA ≫ d) := by rw [hcw]
      _ = A.x ≫ f.vf := by rw [hkdA]
      _ = B.x := f.x_vf
  have hxwe : weakEquivalences X xP := by
    have hcomp : weakEquivalences X (xP ≫ w_f) := by rw [hxw]; exact B.x_weakEquivalence
    have hwf_id : weakEquivalences X (w_f ≫ 𝟙 B.Af) := by
      simpa using hw_f
    exact (IsCylinderCategory.twoOutOfSix (C := X) xP w_f (𝟙 B.Af) hcomp hwf_id).1
  let P : SliceObj x :=
    { A₀ := P₀
      Af := P_f
      a := aP
      x := xP
      cofibrant := hpair
      x_cofibration := hxcof
      x_weakEquivalence := hxwe }
  have hi_a : A.a ≫ (kA ≫ c) = i₀ ≫ aP := by
    calc
      A.a ≫ (kA ≫ c) = (A.a ≫ kA) ≫ c := by rw [Category.assoc]
      _ = (i₀ ≫ kP) ≫ c := by rw [← hL.w]
      _ = i₀ ≫ (kP ≫ c) := by rw [Category.assoc]
      _ = i₀ ≫ aP := rfl
  have hi_x : A.x ≫ (kA ≫ c) = xP := rfl
  let i' : A ⟶ P := ⟨i₀, kA ≫ c, hi_a, hi_x⟩
  have hw_a' : aP ≫ w_f = w₀ ≫ B.a := by
    calc
      aP ≫ w_f = (kP ≫ c) ≫ w_f := rfl
      _ = kP ≫ (c ≫ w_f) := by rw [Category.assoc]
      _ = kP ≫ d := by rw [hcw]
      _ = w₀ ≫ B.a := hkdP
  have hw_x : xP ≫ w_f = B.x := hxw
  let w' : P ⟶ B := ⟨w₀, w_f, hw_a', hw_x⟩
  have hi' : cofibrations (SliceObj x) i' := by
    refine ⟨hi₀', ?_⟩
    refine ⟨L, kA, kP, hL.flip, c, ?_, ?_, hc⟩
    · rfl
    · rfl
  have hw' : weakEquivalences (SliceObj x) w' := hw₀
  have hcomp : i' ≫ w' = f := by
    apply SliceObj.Hom.ext
    · rw [sliceObj_comp_v₀]
      exact hcomp₀
    · rw [sliceObj_comp_vf]
      calc
        (kA ≫ c) ≫ w_f = kA ≫ (c ≫ w_f) := by rw [Category.assoc]
        _ = kA ≫ d := by rw [hcw]
        _ = f.vf := hkdA
  have hPaCast : eqToHom e₀.symm ≫ p.map aP ≫ eqToHom e_f = Q.a := by
    calc
      eqToHom e₀.symm ≫ p.map aP ≫ eqToHom e_f =
          eqToHom e₀.symm ≫ p.map (kP ≫ c) ≫ eqToHom e_f := rfl
      _ = eqToHom e₀.symm ≫ p.map kP ≫ p.map c ≫ eqToHom e_f := by
        rw [p.map_comp, Category.assoc]
      _ = eqToHom e₀.symm ≫ p.map kP ≫ ((eL.hom ≫ mQ) ≫ eqToHom e_f.symm) ≫ eqToHom e_f := by
        rw [hpc]
      _ = eqToHom e₀.symm ≫ p.map kP ≫ (eL.hom ≫ mQ) := by
        rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      _ = eqToHom e₀.symm ≫ (p.map kP ≫ eL.hom) ≫ mQ := by rw [Category.assoc]
      _ = eqToHom e₀.symm ≫ (eqToHom e₀ ≫ qQ₀) ≫ mQ := by rw [heLP]
      _ = qQ₀ ≫ mQ := by
        rw [← Category.assoc, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      _ = Q.a := hmQQ₀
  have haImg : p.map aP ≫ eqToHom e_f = eqToHom e₀ ≫ Q.a := by
    calc
      p.map aP ≫ eqToHom e_f =
          (eqToHom e₀ ≫ eqToHom e₀.symm) ≫ p.map aP ≫ eqToHom e_f := by
        rw [eqToHom_trans, eqToHom_refl, Category.id_comp]
      _ = eqToHom e₀ ≫ (eqToHom e₀.symm ≫ p.map aP ≫ eqToHom e_f) := by
        rw [Category.assoc]
      _ = eqToHom e₀ ≫ Q.a := by rw [hPaCast]
  have hPxCast : p.map xP ≫ eqToHom e_f = Q.x := by
    calc
      p.map xP ≫ eqToHom e_f = p.map (A.x ≫ kA ≫ c) ≫ eqToHom e_f := rfl
      _ = p.map A.x ≫ p.map kA ≫ p.map c ≫ eqToHom e_f := by
        rw [p.map_comp, p.map_comp, Category.assoc, Category.assoc]
      _ = p.map A.x ≫ p.map kA ≫ ((eL.hom ≫ mQ) ≫ eqToHom e_f.symm) ≫ eqToHom e_f := by
        rw [hpc]
      _ = p.map A.x ≫ (p.map kA ≫ eL.hom) ≫ mQ := by
        rw [Category.assoc, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
      _ = p.map A.x ≫ qAf ≫ mQ := by rw [heLA]
      _ = p.map A.x ≫ i.vf := by
        set_option backward.isDefEq.respectTransparency false in
        rw [hmQAf]
      _ = Q.x := by
        set_option backward.isDefEq.respectTransparency false in
        exact i.x_vf
  have hobj : (Cylinder.HomotopyTerminalSlice.sliceMap hp x).obj P = Q :=
    sliceObj_ext e₀ e_f
      (by simpa [Cylinder.HomotopyTerminalSlice.sliceMap, P, aP] using haImg)
      (by simpa [Cylinder.HomotopyTerminalSlice.sliceMap, P, xP] using hPxCast)
  have hpi_f : p.map (kA ≫ c) = i.vf ≫ eqToHom e_f.symm := by
    rw [p.map_comp, hpc, ← hmQAf, ← heLA]
    exact (comp_assoc4_left (p.map kA) eL.hom mQ (eqToHom e_f.symm)).symm
  refine ⟨P, i', w', hobj, hi', hw', hcomp, ?_, ?_⟩
  · apply SliceObj.Hom.ext
    · rw [sliceMap_map_v₀, sliceObj_comp_v₀, sliceObj_eqToHom_v₀]
      have hcast : congrArg SliceObj.A₀ hobj.symm = e₀.symm := Subsingleton.elim _ _
      rw [hcast]
      exact hpi₀
    · rw [sliceMap_map_vf, sliceObj_comp_vf, sliceObj_eqToHom_vf]
      have hcast : congrArg SliceObj.Af hobj.symm = e_f.symm := Subsingleton.elim _ _
      rw [hcast]
      exact hpi_f
  · apply SliceObj.Hom.ext
    · rw [sliceMap_map_v₀, sliceObj_comp_v₀, sliceObj_eqToHom_v₀]
      have hcast : congrArg SliceObj.A₀ hobj = e₀ := Subsingleton.elim _ _
      rw [hcast]
      exact hpw₀
    · rw [sliceMap_map_vf, sliceObj_comp_vf, sliceObj_eqToHom_vf]
      have hcast : congrArg SliceObj.Af hobj = e_f := Subsingleton.elim _ _
      rw [hcast]
      exact hpw_f

/-- The concrete slice functor of a pre-fibration is a pre-fibration. -/
theorem sliceMap_isPreFibration {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
    [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]
    {p : X ⥤ Y} (hp : IsCylinderMorphism p) (hpre : IsPreFibration p) (x : X) :
    IsPreFibration (Cylinder.HomotopyTerminalSlice.sliceMap hp x) where
  lift_retraction := sliceMap_lift_retraction hp hpre x
  lift_factorization := sliceMap_lift_factorization hp hpre x

/-- The concrete slice functor of a lifting target is a lifting target. -/
theorem sliceMap_concrete_isLiftingTarget {X Y : Type (u + 1)} [Category.{u} X]
    [Category.{u} Y] [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X]
    [IsCylinderCategory X] [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y]
    [IsCylinderCategory Y] {p : X ⥤ Y} (hp : IsLiftingTarget false X Y p) (x : X) :
    IsLiftingTarget false (SliceObj x) (SliceObj (p.obj x))
      (Cylinder.HomotopyTerminalSlice.sliceMap hp.2.2.1 x) := by
  exact ⟨(Packages.sliceObj_isLiftingTarget x).1,
    (Packages.sliceObj_isLiftingTarget (p.obj x)).1,
    Cylinder.HomotopyTerminalSlice.sliceMap_isCylinderMorphism hp.2.2.1 x,
    sliceMap_isPreFibration hp.2.2.1 hp.2.2.2.1 x,
    sliceMap_isIsofibration hp.2.2.1 hp.2.2.2.2.1 x, fun h => by cases h⟩

/-- Transport a slice object along an equality of base objects. -/
def sliceObjTransport {b b' : C} (e : b = b') (A : SliceObj b) : SliceObj b' :=
  Eq.ndrec (motive := fun y => SliceObj y) A e

/-- Transport a functor into a slice along an equality of base objects. -/
def sliceFunctorTransport {D : Type (u + 1)} [Category.{u} D] {b b' : C} (e : b = b')
    (F : D ⥤ SliceObj b) : D ⥤ SliceObj b' :=
  Eq.ndrec (motive := fun y => D ⥤ SliceObj y) F e

lemma sliceObj_transport_ext {b b' : C} (e : b = b') {A : SliceObj b} {B : SliceObj b'}
    (h₀ : A.A₀ = B.A₀) (hf : A.Af = B.Af)
    (ha : A.a ≫ eqToHom hf = eqToHom h₀ ≫ B.a)
    (hx : eqToHom e.symm ≫ A.x ≫ eqToHom hf = B.x) :
    sliceObjTransport e A = B := by
  subst e
  have hx' : A.x ≫ eqToHom hf = B.x := by
    simpa [eqToHom_refl, Category.id_comp] using hx
  exact sliceObj_ext h₀ hf ha hx'

lemma sliceFunctorTransport_obj {D : Type (u + 1)} [Category.{u} D] {b b' : C} (e : b = b')
    (F : D ⥤ SliceObj b) (d : D) :
    (sliceFunctorTransport e F).obj d = sliceObjTransport e (F.obj d) := by
  subst e
  rfl

lemma sliceFunctorTransport_forget {D : Type (u + 1)} [Category.{u} D] {b b' : C} (e : b = b')
    (F : D ⥤ SliceObj b) :
    sliceFunctorTransport e F ⋙ SliceObj.forget b' = F ⋙ SliceObj.forget b := by
  subst e
  rfl

lemma isCylinderMorphism_sliceFunctorTransport {D : Type (u + 1)} [Category.{u} D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] {b b' : C} (e : b = b')
    (F : D ⥤ SliceObj b) (hF : IsCylinderMorphism F) :
    IsCylinderMorphism (sliceFunctorTransport e F) := by
  subst e
  exact hF

section CoheratorProof

omit C [Category.{u} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- A cylinder category that is cofibrant at an h-terminal object, and that lifts along
pre-fibrations at h-terminal objects, is a cylinder coherator at that object. -/
theorem isCylinderCoherator_of_liftsAtHTerminal_proof
    {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
    [CategoryWithWeakEquivalences 𝒜] [IsCylinderCategory 𝒜] {o : 𝒜}
    (hcof : IsCofibrantAt.{u + 1, u} 𝒜 o) (ho : IsHTerminal o)
    (hlift : LiftsAtHTerminal.{u + 1, u} 𝒜 o) :
    IsCylinderCoherator.{u + 1, u} 𝒜 o := by
  refine ⟨inferInstance, ?_⟩
  intro X _ _ _ Y _ _ _ p hpLift x _ h hh hex
  letI : IsCylinderCategory X := hpLift.1
  letI : IsCylinderCategory Y := hpLift.2.1
  let hp : IsCylinderMorphism p := hpLift.2.2.1
  let hpre : IsPreFibration p := hpLift.2.2.2.1
  let d := Cylinder.HomotopyTerminalSlice.chooseSliceCylinder o
  let cyl := d.cyl
  let i₀ : d.I ⟶ o := d.hI.to o
  have hcofA : IsCofibrationCategory 𝒜 := inferInstance
  have hcofX : IsCofibrationCategory X := inferInstance
  have hcofY : IsCofibrationCategory Y := inferInstance
  have hi₀ : cofibrations 𝒜 i₀ := hcofA.initial_cofibration d.hI o
  have hhP : IsPushout (h.map i₀) (h.map i₀) (h.map cyl.j₀) (h.map cyl.j₁) :=
    hh.map_isPushout i₀ i₀ cyl.j₀ cyl.j₁ cyl.isPushout hi₀
  obtain ⟨J, hJne⟩ := IsCofibrationCategory.exists_initial (C := X)
  obtain ⟨hJ⟩ := hJne
  have hiJ : cofibrations X (hJ.to x) := hcofX.initial_cofibration hJ x
  letI : HasPushout (hJ.to x) (hJ.to x) := hcofX.hasPushout (hJ.to x) (hJ.to x) hiJ
  let Px := pushout (hJ.to x) (hJ.to x)
  let k₀ : x ⟶ Px := pushout.inl (hJ.to x) (hJ.to x)
  let k₁ : x ⟶ Px := pushout.inr (hJ.to x) (hJ.to x)
  let hPx : IsPushout (hJ.to x) (hJ.to x) k₀ k₁ :=
    IsPushout.of_hasPushout (hJ.to x) (hJ.to x)
  have hpm : IsPushout (p.map (hJ.to x)) (p.map (hJ.to x)) (p.map k₀) (p.map k₁) :=
    hp.map_isPushout (hJ.to x) (hJ.to x) k₀ k₁ hPx hiJ
  obtain ⟨hJp⟩ := hp.map_initial hJ
  obtain ⟨hIh⟩ := hh.map_initial d.hI
  let eW : h.obj d.I ≅ p.obj J := hIh.uniqueUpToIso hJp
  let eB : h.obj o ≅ p.obj x := eqToIso hex
  let j₀Y : p.obj x ⟶ h.obj cyl.P := eqToHom hex.symm ≫ h.map cyl.j₀
  let j₁Y : p.obj x ⟶ h.obj cyl.P := eqToHom hex.symm ≫ h.map cyl.j₁
  have hround : eqToHom hex ≫ eqToHom hex.symm = 𝟙 (h.obj o) := by simp
  have hQ' : IsPushout (p.map (hJ.to x)) (p.map (hJ.to x)) j₀Y j₁Y := by
    apply hhP.of_iso eW eB eB (Iso.refl (h.obj cyl.P))
    · exact hIh.hom_ext _ _
    · exact hIh.hom_ext _ _
    · rw [Iso.refl_hom, Category.comp_id]
      calc
        h.map cyl.j₀ = 𝟙 (h.obj o) ≫ h.map cyl.j₀ := (Category.id_comp _).symm
        _ = (eqToHom hex ≫ eqToHom hex.symm) ≫ h.map cyl.j₀ :=
          congrArg (fun z => z ≫ h.map cyl.j₀) hround.symm
        _ = eqToHom hex ≫ j₀Y := Category.assoc _ _ _
        _ = eB.hom ≫ j₀Y := rfl
    · rw [Iso.refl_hom, Category.comp_id]
      calc
        h.map cyl.j₁ = 𝟙 (h.obj o) ≫ h.map cyl.j₁ := (Category.id_comp _).symm
        _ = (eqToHom hex ≫ eqToHom hex.symm) ≫ h.map cyl.j₁ :=
          congrArg (fun z => z ≫ h.map cyl.j₁) hround.symm
        _ = eqToHom hex ≫ j₁Y := Category.assoc _ _ _
        _ = eB.hom ≫ j₁Y := rfl
  obtain ⟨eP, heP₀, heP₁⟩ := pushout_uniqueIso hpm hQ'
  have hδcond : hJ.to x ≫ 𝟙 x = hJ.to x ≫ 𝟙 x := hJ.hom_ext _ _
  let δ : Px ⟶ x := pushout.desc (𝟙 x) (𝟙 x) hδcond
  have hδ₀ : k₀ ≫ δ = 𝟙 x := pushout.inl_desc (𝟙 x) (𝟙 x) hδcond
  have hδ₁ : k₁ ≫ δ = 𝟙 x := pushout.inr_desc (𝟙 x) (𝟙 x) hδcond
  let iY : p.obj Px ⟶ h.obj cyl.I := eP.hom ≫ h.map cyl.c
  let wY : h.obj cyl.I ⟶ p.obj x := h.map cyl.p ≫ eqToHom hex
  have h1 : p.map k₀ ≫ iY = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c) := by
    calc
      p.map k₀ ≫ iY = p.map k₀ ≫ (eP.hom ≫ h.map cyl.c) := rfl
      _ = (p.map k₀ ≫ eP.hom) ≫ h.map cyl.c := (Category.assoc _ _ _).symm
      _ = j₀Y ≫ h.map cyl.c := by rw [heP₀]
      _ = (eqToHom hex.symm ≫ h.map cyl.j₀) ≫ h.map cyl.c := rfl
      _ = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c) := Category.assoc _ _ _
  have h2 : p.map k₁ ≫ iY = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c) := by
    calc
      p.map k₁ ≫ iY = p.map k₁ ≫ (eP.hom ≫ h.map cyl.c) := rfl
      _ = (p.map k₁ ≫ eP.hom) ≫ h.map cyl.c := (Category.assoc _ _ _).symm
      _ = j₁Y ≫ h.map cyl.c := by rw [heP₁]
      _ = (eqToHom hex.symm ≫ h.map cyl.j₁) ≫ h.map cyl.c := rfl
      _ = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c) := Category.assoc _ _ _
  have hpre₀ : (eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c)) ≫
      (h.map cyl.p ≫ eqToHom hex) = 𝟙 (p.obj x) := by
    calc
      (eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c)) ≫ (h.map cyl.p ≫ eqToHom hex)
          = eqToHom hex.symm ≫ ((h.map cyl.j₀ ≫ h.map cyl.c) ≫ (h.map cyl.p ≫ eqToHom hex)) :=
            Category.assoc _ _ _
      _ = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ (h.map cyl.c ≫ (h.map cyl.p ≫ eqToHom hex))) :=
            congrArg (fun z => eqToHom hex.symm ≫ z) (Category.assoc _ _ _)
      _ = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ ((h.map cyl.c ≫ h.map cyl.p) ≫ eqToHom hex)) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ z))
              ((Category.assoc (h.map cyl.c) (h.map cyl.p) (eqToHom hex)).symm)
      _ = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ (h.map (cyl.c ≫ cyl.p) ≫ eqToHom hex)) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ (z ≫ eqToHom hex)))
              (h.map_comp cyl.c cyl.p).symm
      _ = eqToHom hex.symm ≫ ((h.map cyl.j₀ ≫ h.map (cyl.c ≫ cyl.p)) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ z)
              ((Category.assoc (h.map cyl.j₀) (h.map (cyl.c ≫ cyl.p)) (eqToHom hex)).symm)
      _ = eqToHom hex.symm ≫ (h.map (cyl.j₀ ≫ (cyl.c ≫ cyl.p)) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (z ≫ eqToHom hex))
              (h.map_comp cyl.j₀ (cyl.c ≫ cyl.p)).symm
      _ = eqToHom hex.symm ≫ (h.map (𝟙 o) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map z ≫ eqToHom hex)) cyl.j₀_c_p
      _ = eqToHom hex.symm ≫ (𝟙 (h.obj o) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (z ≫ eqToHom hex)) (h.map_id o)
      _ = eqToHom hex.symm ≫ eqToHom hex :=
            congrArg (fun z => eqToHom hex.symm ≫ z) (Category.id_comp _)
      _ = 𝟙 (p.obj x) := by rw [eqToHom_trans, eqToHom_refl]
  have hpre₁ : (eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c)) ≫
      (h.map cyl.p ≫ eqToHom hex) = 𝟙 (p.obj x) := by
    calc
      (eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c)) ≫ (h.map cyl.p ≫ eqToHom hex)
          = eqToHom hex.symm ≫ ((h.map cyl.j₁ ≫ h.map cyl.c) ≫ (h.map cyl.p ≫ eqToHom hex)) :=
            Category.assoc _ _ _
      _ = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ (h.map cyl.c ≫ (h.map cyl.p ≫ eqToHom hex))) :=
            congrArg (fun z => eqToHom hex.symm ≫ z) (Category.assoc _ _ _)
      _ = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ ((h.map cyl.c ≫ h.map cyl.p) ≫ eqToHom hex)) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ z))
              ((Category.assoc (h.map cyl.c) (h.map cyl.p) (eqToHom hex)).symm)
      _ = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ (h.map (cyl.c ≫ cyl.p) ≫ eqToHom hex)) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ (z ≫ eqToHom hex)))
              (h.map_comp cyl.c cyl.p).symm
      _ = eqToHom hex.symm ≫ ((h.map cyl.j₁ ≫ h.map (cyl.c ≫ cyl.p)) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ z)
              ((Category.assoc (h.map cyl.j₁) (h.map (cyl.c ≫ cyl.p)) (eqToHom hex)).symm)
      _ = eqToHom hex.symm ≫ (h.map (cyl.j₁ ≫ (cyl.c ≫ cyl.p)) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (z ≫ eqToHom hex))
              (h.map_comp cyl.j₁ (cyl.c ≫ cyl.p)).symm
      _ = eqToHom hex.symm ≫ (h.map (𝟙 o) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (h.map z ≫ eqToHom hex)) cyl.j₁_c_p
      _ = eqToHom hex.symm ≫ (𝟙 (h.obj o) ≫ eqToHom hex) :=
            congrArg (fun z => eqToHom hex.symm ≫ (z ≫ eqToHom hex)) (h.map_id o)
      _ = eqToHom hex.symm ≫ eqToHom hex :=
            congrArg (fun z => eqToHom hex.symm ≫ z) (Category.id_comp _)
      _ = 𝟙 (p.obj x) := by rw [eqToHom_trans, eqToHom_refl]
  have hpre₀' : p.map k₀ ≫ (iY ≫ wY) = 𝟙 (p.obj x) := by
    calc
      p.map k₀ ≫ (iY ≫ wY) = (p.map k₀ ≫ iY) ≫ wY := (Category.assoc _ _ _).symm
      _ = (eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c)) ≫ wY :=
            congrArg (fun z => z ≫ wY) h1
      _ = (eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c)) ≫ (h.map cyl.p ≫ eqToHom hex) := by
            rw [show wY = h.map cyl.p ≫ eqToHom hex from rfl]
      _ = 𝟙 (p.obj x) := hpre₀
  have hpre₁' : p.map k₁ ≫ (iY ≫ wY) = 𝟙 (p.obj x) := by
    calc
      p.map k₁ ≫ (iY ≫ wY) = (p.map k₁ ≫ iY) ≫ wY := (Category.assoc _ _ _).symm
      _ = (eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c)) ≫ wY :=
            congrArg (fun z => z ≫ wY) h2
      _ = (eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c)) ≫ (h.map cyl.p ≫ eqToHom hex) := by
            rw [show wY = h.map cyl.p ≫ eqToHom hex from rfl]
      _ = 𝟙 (p.obj x) := hpre₁
  have hpost₀ : p.map k₀ ≫ p.map δ = 𝟙 (p.obj x) := by
    rw [← p.map_comp, hδ₀, p.map_id]
  have hpost₁ : p.map k₁ ≫ p.map δ = 𝟙 (p.obj x) := by
    rw [← p.map_comp, hδ₁, p.map_id]
  have hiw : iY ≫ wY = p.map δ :=
    hpm.hom_ext (hpre₀'.trans hpost₀.symm) (hpre₁'.trans hpost₁.symm)
  have hiY : cofibrations Y iY := by
    exact hcofY.isMultiplicative.comp_mem eP.hom (h.map cyl.c)
      (hcofY.isomorphisms_le eP.hom (by infer_instance))
      (hh.map_cofibration cyl.c cyl.c_mem)
  have hwY : weakEquivalences Y wY :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := Y)).comp_mem
      (h.map cyl.p) (eqToHom hex) (hh.map_weakEquivalence cyl.p cyl.p_mem)
      (weakEquivalence_of_isIso (eqToHom hex))
  obtain ⟨Ix, cx, px, eI, hcx, hpx, hcxp, hpc, _hpw⟩ :=
    hpre.lift_factorization δ iY wY hiY hwY hiw
  have hk₀ : cofibrations X k₀ :=
    hcofX.isStableUnderCobaseChange.of_isPushout hPx hiJ
  have hk₁ : cofibrations X k₁ :=
    hcofX.isStableUnderCobaseChange.of_isPushout hPx.flip hiJ
  let aKx : x ⟶ Ix := k₀ ≫ cx
  let xKx : x ⟶ Ix := k₁ ≫ cx
  have haWe : weakEquivalences X aKx := by
    have hcomp : aKx ≫ px = 𝟙 x := by
      calc
        aKx ≫ px = (k₀ ≫ cx) ≫ px := rfl
        _ = k₀ ≫ (cx ≫ px) := by rw [Category.assoc]
        _ = k₀ ≫ δ := by rw [hcxp]
        _ = 𝟙 x := hδ₀
    exact (IsCylinderCategory.twoOutOfSix (C := X) aKx px (𝟙 x)
      (by rw [hcomp]; exact
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).id_mem x)
      (by simpa using hpx)).1
  have hxcof : cofibrations X xKx :=
    hcofX.isMultiplicative.comp_mem k₁ cx hk₁ hcx
  have hxwe : weakEquivalences X xKx := by
    have hcomp : xKx ≫ px = 𝟙 x := by
      calc
        xKx ≫ px = (k₁ ≫ cx) ≫ px := rfl
        _ = k₁ ≫ (cx ≫ px) := by rw [Category.assoc]
        _ = k₁ ≫ δ := by rw [hcxp]
        _ = 𝟙 x := hδ₁
    exact (IsCylinderCategory.twoOutOfSix (C := X) xKx px (𝟙 x)
      (by rw [hcomp]; exact
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).id_mem x)
      (by simpa using hpx)).1
  let Kx : SliceObj x :=
    { A₀ := x
      Af := Ix
      a := aKx
      x := xKx
      cofibrant := ⟨J, hJ, Px, k₀, k₁, hPx, cx, rfl, rfl, hcx⟩
      x_cofibration := hxcof
      x_weakEquivalence := hxwe }
  let K₀ : SliceObj o := Cylinder.HomotopyTerminalSlice.cylinderSliceObjOfData o d
  let sP := Cylinder.HomotopyTerminalSlice.sliceMap hp x
  let sH := Cylinder.HomotopyTerminalSlice.sliceMap hh o
  have hleg₀ : p.map aKx ≫ eqToHom eI =
      eqToHom hex.symm ≫ h.map (cyl.j₀ ≫ cyl.c) := by
    calc
      p.map aKx ≫ eqToHom eI = p.map (k₀ ≫ cx) ≫ eqToHom eI := by
        rw [show aKx = k₀ ≫ cx from rfl]
      _ = (p.map k₀ ≫ p.map cx) ≫ eqToHom eI := by rw [p.map_comp]
      _ = (p.map k₀ ≫ (iY ≫ eqToHom eI.symm)) ≫ eqToHom eI := by rw [hpc]
      _ = ((p.map k₀ ≫ iY) ≫ eqToHom eI.symm) ≫ eqToHom eI := by rw [← Category.assoc]
      _ = (p.map k₀ ≫ iY) ≫ (eqToHom eI.symm ≫ eqToHom eI) := by rw [Category.assoc]
      _ = (p.map k₀ ≫ iY) ≫ 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl]
      _ = p.map k₀ ≫ iY := by rw [Category.comp_id]
      _ = eqToHom hex.symm ≫ (h.map cyl.j₀ ≫ h.map cyl.c) := h1
      _ = eqToHom hex.symm ≫ h.map (cyl.j₀ ≫ cyl.c) := by rw [← h.map_comp]
  have hleg₁ : p.map xKx ≫ eqToHom eI =
      eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c) := by
    calc
      p.map xKx ≫ eqToHom eI = p.map (k₁ ≫ cx) ≫ eqToHom eI := by
        rw [show xKx = k₁ ≫ cx from rfl]
      _ = (p.map k₁ ≫ p.map cx) ≫ eqToHom eI := by rw [p.map_comp]
      _ = (p.map k₁ ≫ (iY ≫ eqToHom eI.symm)) ≫ eqToHom eI := by rw [hpc]
      _ = ((p.map k₁ ≫ iY) ≫ eqToHom eI.symm) ≫ eqToHom eI := by rw [← Category.assoc]
      _ = (p.map k₁ ≫ iY) ≫ (eqToHom eI.symm ≫ eqToHom eI) := by rw [Category.assoc]
      _ = (p.map k₁ ≫ iY) ≫ 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl]
      _ = p.map k₁ ≫ iY := by rw [Category.comp_id]
      _ = eqToHom hex.symm ≫ (h.map cyl.j₁ ≫ h.map cyl.c) := h2
      _ = eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c) := by rw [← h.map_comp]
  have hxFields : eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c) ≫ eqToHom eI.symm =
      p.map xKx := by
    calc
      eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c) ≫ eqToHom eI.symm
          = (eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c)) ≫ eqToHom eI.symm :=
            (Category.assoc _ _ _).symm
      _ = (p.map xKx ≫ eqToHom eI) ≫ eqToHom eI.symm := by rw [← hleg₁]
      _ = p.map xKx ≫ (eqToHom eI ≫ eqToHom eI.symm) := Category.assoc _ _ _
      _ = p.map xKx ≫ 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl]
      _ = p.map xKx := Category.comp_id _
  have haFields : h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm = eqToHom hex ≫ p.map aKx := by
    calc
      h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm
          = 𝟙 (h.obj o) ≫ h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm :=
            (Category.id_comp _).symm
      _ = (eqToHom hex ≫ eqToHom hex.symm) ≫ (h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm) := by
            rw [← hround]
      _ = eqToHom hex ≫ (eqToHom hex.symm ≫ (h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm)) :=
            Category.assoc _ _ _
      _ = eqToHom hex ≫ ((eqToHom hex.symm ≫ h.map (cyl.j₀ ≫ cyl.c)) ≫ eqToHom eI.symm) :=
            congrArg (fun z => eqToHom hex ≫ z)
              ((Category.assoc (eqToHom hex.symm) (h.map (cyl.j₀ ≫ cyl.c)) (eqToHom eI.symm)).symm)
      _ = eqToHom hex ≫ ((p.map aKx ≫ eqToHom eI) ≫ eqToHom eI.symm) :=
            congrArg (fun z => eqToHom hex ≫ (z ≫ eqToHom eI.symm)) hleg₀.symm
      _ = eqToHom hex ≫ (p.map aKx ≫ (eqToHom eI ≫ eqToHom eI.symm)) :=
            congrArg (fun z => eqToHom hex ≫ z)
              (Category.assoc (p.map aKx) (eqToHom eI) (eqToHom eI.symm))
      _ = eqToHom hex ≫ p.map aKx ≫ 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl]
      _ = eqToHom hex ≫ p.map aKx := by rw [Category.comp_id]
  have htermKx : IsHTerminal Kx :=
    Cylinder.HomotopyTerminalSlice.sliceObj_isHTerminal_proof Kx haWe
  have hBaWe : weakEquivalences Y (sP.obj Kx).a := by
    set_option backward.isDefEq.respectTransparency false in
    simpa [sP, Cylinder.HomotopyTerminalSlice.sliceMap] using hp.map_weakEquivalence aKx haWe
  have htermKy : IsHTerminal (sP.obj Kx) :=
    Cylinder.HomotopyTerminalSlice.sliceObj_isHTerminal_proof (sP.obj Kx) hBaWe
  have h₀ : (sH.obj K₀).A₀ = (sP.obj Kx).A₀ := by
    set_option backward.isDefEq.respectTransparency false in exact hex
  have hf : (sH.obj K₀).Af = (sP.obj Kx).Af := by
    set_option backward.isDefEq.respectTransparency false in exact eI.symm
  have ha : (sH.obj K₀).a ≫ eqToHom hf = eqToHom h₀ ≫ (sP.obj Kx).a := by
    set_option backward.isDefEq.respectTransparency false in
    calc
      (sH.obj K₀).a ≫ eqToHom hf = h.map (cyl.j₀ ≫ cyl.c) ≫ eqToHom eI.symm := by
        rw [show (sH.obj K₀).a = h.map (cyl.j₀ ≫ cyl.c) from rfl,
          show eqToHom hf = eqToHom eI.symm from rfl]
      _ = eqToHom hex ≫ p.map aKx := haFields
      _ = eqToHom h₀ ≫ (sP.obj Kx).a := by
        rw [show eqToHom hex = eqToHom h₀ from rfl,
          show p.map aKx = (sP.obj Kx).a from rfl]
  have hx : eqToHom hex.symm ≫ (sH.obj K₀).x ≫ eqToHom hf = (sP.obj Kx).x := by
    set_option backward.isDefEq.respectTransparency false in
    calc
      eqToHom hex.symm ≫ (sH.obj K₀).x ≫ eqToHom hf
          = eqToHom hex.symm ≫ h.map (cyl.j₁ ≫ cyl.c) ≫ eqToHom eI.symm := by
            rw [show (sH.obj K₀).x = h.map (cyl.j₁ ≫ cyl.c) from rfl,
              show eqToHom hf = eqToHom eI.symm from rfl]
      _ = p.map xKx := hxFields
      _ = (sP.obj Kx).x := by rw [show p.map xKx = (sP.obj Kx).x from rfl]
  have htransport : sliceObjTransport hex (sH.obj K₀) = sP.obj Kx :=
    sliceObj_transport_ext hex h₀ hf ha hx
  obtain ⟨lY0, hlY0, hlY0comp, hlY0o⟩ :=
    Cylinder.HomotopyTerminalSlice.lift_to_sliceObj_canonical hcof ho hh
  let lY : 𝒜 ⥤ SliceObj (p.obj x) := sliceFunctorTransport hex lY0
  have hlY : IsCylinderMorphism lY :=
    isCylinderMorphism_sliceFunctorTransport hex lY0 hlY0
  have hlYcomp : lY ⋙ SliceObj.forget (p.obj x) = h :=
    (sliceFunctorTransport_forget hex lY0).trans hlY0comp
  have hsquare : lY.obj o = sP.obj Kx := by
    have hobj : lY.obj o = sliceObjTransport hex (lY0.obj o) :=
      sliceFunctorTransport_obj hex lY0 o
    rw [hlY0o] at hobj
    have hcan :
        (Cylinder.HomotopyTerminalSlice.sliceMap hh o).obj (Cylinder.HomotopyTerminalSlice.cylinderSliceObj o) = sH.obj K₀ := by
      set_option backward.isDefEq.respectTransparency false in rfl
    rw [hcan] at hobj
    exact hobj.trans htransport
  have htarget := sliceMap_concrete_isLiftingTarget hpLift x
  obtain ⟨lS, hlS, hlSp, hlSo⟩ :=
    hlift (SliceObj x) (SliceObj (p.obj x)) sP htarget Kx ⟨htermKx, htermKy⟩ lY hlY hsquare
  refine ⟨lS ⋙ SliceObj.forget x,
    IsCylinderMorphism.comp hlS (Packages.sliceObj_isLiftingTarget x).2.2.1, ?_, ?_⟩
  · have hforget : sP ⋙ SliceObj.forget (p.obj x) = SliceObj.forget x ⋙ p := by
      set_option backward.isDefEq.respectTransparency false in rfl
    calc
      (lS ⋙ SliceObj.forget x) ⋙ p = lS ⋙ (SliceObj.forget x ⋙ p) := by
        set_option backward.isDefEq.respectTransparency false in rfl
      _ = lS ⋙ (sP ⋙ SliceObj.forget (p.obj x)) := by rw [hforget]
      _ = (lS ⋙ sP) ⋙ SliceObj.forget (p.obj x) := by
        set_option backward.isDefEq.respectTransparency false in rfl
      _ = lY ⋙ SliceObj.forget (p.obj x) := by rw [hlSp]
      _ = h := hlYcomp
  · change (lS.obj o).A₀ = x
    rw [hlSo]

#print axioms HomotopyHypothesis.Cylinder.SliceCoherator.isCylinderCoherator_of_liftsAtHTerminal_proof

end CoheratorProof

end HomotopyHypothesis.Cylinder.SliceCoherator
