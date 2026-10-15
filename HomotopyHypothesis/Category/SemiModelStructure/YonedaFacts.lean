import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# The Yoneda embedding into the completion

The Yoneda embedding of a cofibration category into its completion preserves the initial object,
pushouts along cofibrations and finite coproducts, and sends weak equivalences of a cylinder
category to weak equivalences of the completion. Finite coproducts of (trivial) cofibrations of a
cylinder category exist and are (trivial) cofibrations.
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [LocallySmall.{w} C]

theorem completionSmallYoneda_isInitial {I : C} (hI : IsInitial I) :
    Nonempty (IsInitial (completionSmallYoneda.{w}.obj I)) := by
  classical
  refine ⟨IsInitial.ofUniqueHom (fun P => ?_) (fun P f => ?_)⟩
  · letI : Unique (P.obj.obj (op I)) := Classical.choice (P.property.1 hI)
    exact (completionSmallYonedaHomEquiv I P).symm default
  · letI : Unique (P.obj.obj (op I)) := Classical.choice (P.property.1 hI)
    apply (completionSmallYonedaHomEquiv I P).injective
    exact Subsingleton.elim _ _

private theorem completionSmallYonedaHomEquiv_precomp {A B : C} (i : A ⟶ B)
    (P : Completion.{w} C) (φ : completionSmallYoneda.{w}.obj B ⟶ P) :
    completionSmallYonedaHomEquiv A P (completionSmallYoneda.map i ≫ φ) =
      P.obj.map i.op (completionSmallYonedaHomEquiv B P φ) := by
  change shrinkYonedaEquiv (shrinkYoneda.map i ≫ φ.hom) =
    P.obj.map i.op (shrinkYonedaEquiv φ.hom)
  exact (shrinkYonedaEquiv_naturality φ.hom i).symm

private theorem completionObjectPreservesFiniteProducts [IsCofibrationCategory C]
    (P : Completion.{w} C) : PreservesFiniteProducts P.obj := by
  classical
  obtain ⟨I, hI⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hI
  letI : HasInitial C := hI.hasInitial
  letI : ∀ {A B : C}, HasColimit (pair A B) := by
    intro A B
    letI : HasPushout (hI.to A) (hI.to B) :=
      IsCofibrationCategory.hasPushout (hI.to A) (hI.to B)
        (IsCofibrationCategory.initial_cofibration hI A)
    have hp : IsPushout (hI.to A) (hI.to B) (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    refine ⟨⟨BinaryCofan.mk (pushout.inl (hI.to A) (hI.to B))
      (pushout.inr (hI.to A) (hI.to B)), ?_⟩⟩
    exact isCoproductOfIsInitialIsPushout _ _ _ _ hI hp.isColimit
  letI : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair C
  letI : HasFiniteCoproducts C := hasFiniteCoproducts_of_has_binary_and_initial
  letI : HasFiniteProducts Cᵒᵖ := inferInstance
  have hterminal : PreservesLimit (Functor.empty Cᵒᵖ) P.obj := by
    let hunique := Classical.choice (P.property.1 hI)
    let hs : IsLimit (asEmptyCone (op I)) :=
      (isLimitEquivIsTerminalOfIsEmpty (c := asEmptyCone (op I))).symm hI.op
    apply preservesLimit_of_preserves_limit_cone hs
    exact (isLimitMapConeEmptyConeEquiv P.obj (op I)).symm
      ((Types.isTerminalEquivUnique _).symm hunique)
  have hbinary : ∀ (A B : Cᵒᵖ), PreservesLimit (pair A B) P.obj := by
    intro A B
    cases A with
    | op A =>
      cases B with
      | op B =>
        let c : BinaryCofan A B :=
          BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ B) coprod.inr
        have hc : IsColimit c := coprodIsCoprod A B
        have hpush : IsPushout (hI.to A) (hI.to B) c.inl c.inr :=
          IsPushout.of_is_coproduct hc hI
        have hpb := P.property.2 (hI.to A) (hI.to B) c.inl c.inr hpush
          (IsCofibrationCategory.initial_cofibration hI A)
        letI : Unique (P.obj.obj (op I)) := Classical.choice (P.property.1 hI)
        let hcompat {T : Type w} (f : T ⟶ P.obj.obj (op A))
            (g : T ⟶ P.obj.obj (op B)) :
            f ≫ P.obj.map (hI.to A).op = g ≫ P.obj.map (hI.to B).op := by
          ext t
          exact Subsingleton.elim _ _
        let d {T : Type w} (f : T ⟶ P.obj.obj (op A))
            (g : T ⟶ P.obj.obj (op B)) : T ⟶ P.obj.obj (op c.pt) :=
          Classical.choose (hpb.exists_lift f g (hcompat f g))
        have hmap : IsLimit (BinaryFan.mk (P.obj.map c.inl.op) (P.obj.map c.inr.op)) := by
          refine BinaryFan.IsLimit.mk _ (fun {T} f g => ?_) ?_ ?_ ?_
          · exact d f g
          · intro T f g
            change d f g ≫ P.obj.map c.inl.op = f
            exact (Classical.choose_spec (hpb.exists_lift f g (hcompat f g))).1
          · intro T f g
            change d f g ≫ P.obj.map c.inr.op = g
            exact (Classical.choose_spec (hpb.exists_lift f g (hcompat f g))).2
          · intro T f g m hm₁ hm₂
            have hd₁ : d f g ≫ P.obj.map c.inl.op = f :=
              (Classical.choose_spec (hpb.exists_lift f g (hcompat f g))).1
            have hd₂ : d f g ≫ P.obj.map c.inr.op = g :=
              (Classical.choose_spec (hpb.exists_lift f g (hcompat f g))).2
            apply hpb.hom_ext
            · exact hm₁.trans hd₁.symm
            · exact hm₂.trans hd₂.symm
        apply preservesLimit_of_preserves_limit_cone (BinaryCofan.IsColimit.op hc)
        exact (isLimitMapConeBinaryFanEquiv P.obj c.inl.op c.inr.op).symm hmap
  letI : PreservesLimit (Functor.empty Cᵒᵖ) P.obj := hterminal
  letI : PreservesLimitsOfShape (Discrete PEmpty) P.obj :=
    preservesLimitsOfShape_pempty_of_preservesTerminal P.obj
  letI : PreservesLimitsOfShape (Discrete WalkingPair) P.obj := by
    refine ⟨fun {K} => ?_⟩
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) P.obj :=
      hbinary _ _
    exact preservesLimit_of_iso_diagram P.obj (diagramIsoPair K).symm
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal P.obj

private noncomputable def completionCofanElementEquiv [IsCofibrationCategory C]
    {T : Type w} [Finite T] {Cs : T → C} {C' : C} {ι : ∀ t, Cs t ⟶ C'}
    (h : IsColimit (Cofan.mk C' ι)) (P : Completion.{w} C) :
    P.obj.obj (op C') ≃ ∀ t, P.obj.obj (op (Cs t)) := by
  classical
  letI : PreservesFiniteProducts P.obj := completionObjectPreservesFiniteProducts P
  have hc₀ : IsLimit (Fan.mk (op C') fun t => (ι t).op) := Cofan.IsColimit.op h
  have hc : IsLimit (Fan.mk (P.obj.obj (op C')) fun t => P.obj.map (ι t).op) :=
    (isLimitMapConeFanMkEquiv P.obj (fun t => op (Cs t)) (fun t => (ι t).op))
      (isLimitOfPreserves P.obj hc₀)
  let toFun (q : P.obj.obj (op C')) (t : T) := P.obj.map (ι t).op q
  let invFun (a : ∀ t, P.obj.obj (op (Cs t))) :=
    (hc.lift (Fan.mk PUnit fun t => TypeCat.ofHom (fun _ => a t))) PUnit.unit
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro q
    have hconst : (TypeCat.ofHom (fun _ : PUnit => q)) =
        hc.lift (Fan.mk PUnit fun t => TypeCat.ofHom (fun _ => toFun q t)) := by
      apply hc.hom_ext
      intro ⟨t⟩
      ext z
      have hf := hc.fac (Fan.mk PUnit fun j => TypeCat.ofHom (fun _ => toFun q j)) ⟨t⟩
      exact (congrArg (fun f => f z) hf).symm
    exact congrArg (fun f => f PUnit.unit) hconst.symm
  · intro a
    funext t
    have hf := hc.fac (Fan.mk PUnit fun j => TypeCat.ofHom (fun _ => a j)) ⟨t⟩
    exact congrArg (fun f => f PUnit.unit) hf

set_option backward.isDefEq.respectTransparency.types false in
theorem completionSmallYoneda_isPushout {A B X Q : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q)
    (j : X ⟶ Q) (h : IsPushout i f k j) (hi : cofibrations C i) :
    IsPushout (completionSmallYoneda.{w}.map i) (completionSmallYoneda.{w}.map f)
      (completionSmallYoneda.{w}.map k) (completionSmallYoneda.{w}.map j) := by
  classical
  let t : PushoutCocone (completionSmallYoneda.{w}.map i) (completionSmallYoneda.{w}.map f) :=
    PushoutCocone.mk (completionSmallYoneda.map k) (completionSmallYoneda.map j) (by
      rw [← Functor.map_comp, ← Functor.map_comp, h.w])
  have hpt : t.pt = completionSmallYoneda.{w}.obj Q := by
    rfl
  have htinl : t.inl ≫ eqToHom hpt = completionSmallYoneda.{w}.map k := by
    dsimp [t, PushoutCocone.mk]
    simp
  have htinr : t.inr ≫ eqToHom hpt = completionSmallYoneda.{w}.map j := by
    dsimp [t, PushoutCocone.mk]
    simp
  have htinlInv : completionSmallYoneda.{w}.map k ≫ eqToHom hpt.symm = t.inl := by
    rw [← htinl]
    simp [Category.assoc]
  have htinrInv : completionSmallYoneda.{w}.map j ≫ eqToHom hpt.symm = t.inr := by
    rw [← htinr]
    simp [Category.assoc]
  have ht : IsColimit t := PushoutCocone.isColimitAux' t (by
  intro s
  let pullback := (s.pt.property.2 i f k j h hi)
  let b := completionSmallYonedaHomEquiv B s.pt s.inl
  let x := completionSmallYonedaHomEquiv X s.pt s.inr
  have hbx : s.pt.obj.map i.op b = s.pt.obj.map f.op x := by
    have hs := congrArg (completionSmallYonedaHomEquiv A s.pt) s.condition
    rw [completionSmallYonedaHomEquiv_precomp, completionSmallYonedaHomEquiv_precomp] at hs
    exact hs
  have heq := pullback.exists_lift (W := PUnit.{w + 1})
    (TypeCat.ofHom fun _ : PUnit.{w + 1} => b)
    (TypeCat.ofHom fun _ : PUnit.{w + 1} => x)
    (by ext z; exact hbx)
  let qf := Classical.choose heq
  have hqB := (Classical.choose_spec heq).1
  have hqX := (Classical.choose_spec heq).2
  let q := qf PUnit.unit
  let l : t.pt ⟶ s.pt := eqToHom hpt ≫ (completionSmallYonedaHomEquiv Q s.pt).symm q
  refine ⟨l, ?_, ?_, ?_⟩
  · dsimp [t]
    have hfac : t.inl ≫ l = completionSmallYoneda.map k ≫
        (completionSmallYonedaHomEquiv Q s.pt).symm q := by
      calc
        t.inl ≫ l = t.inl ≫ (eqToHom hpt ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q) := rfl
        _ = (t.inl ≫ eqToHom hpt) ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q := by simp [Category.assoc]
        _ = completionSmallYoneda.map k ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q := by rw [htinl]
    apply (completionSmallYonedaHomEquiv B s.pt).injective
    change completionSmallYonedaHomEquiv B s.pt (t.inl ≫ l) =
      completionSmallYonedaHomEquiv B s.pt s.inl
    rw [hfac, completionSmallYonedaHomEquiv_precomp]
    simpa [q] using congrArg (fun g => g PUnit.unit) hqB
  · dsimp [t]
    have hfac : t.inr ≫ l = completionSmallYoneda.map j ≫
        (completionSmallYonedaHomEquiv Q s.pt).symm q := by
      calc
        t.inr ≫ l = t.inr ≫ (eqToHom hpt ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q) := rfl
        _ = (t.inr ≫ eqToHom hpt) ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q := by simp [Category.assoc]
        _ = completionSmallYoneda.map j ≫
            (completionSmallYonedaHomEquiv Q s.pt).symm q := by rw [htinr]
    apply (completionSmallYonedaHomEquiv X s.pt).injective
    change completionSmallYonedaHomEquiv X s.pt (t.inr ≫ l) =
      completionSmallYonedaHomEquiv X s.pt s.inr
    rw [hfac, completionSmallYonedaHomEquiv_precomp]
    simpa [q] using congrArg (fun g => g PUnit.unit) hqX
  · intro m hmB hmX
    dsimp [t] at hmB hmX
    let m' : completionSmallYoneda.{w}.obj Q ⟶ s.pt := eqToHom hpt.symm ≫ m
    have hmB' : completionSmallYoneda.{w}.map k ≫ m' = s.inl := by
      calc
        completionSmallYoneda.map k ≫ m' =
            (completionSmallYoneda.map k ≫ eqToHom hpt.symm) ≫ m := by
              simp [m', Category.assoc]
        _ = t.inl ≫ m := by rw [htinlInv]
        _ = s.inl := hmB
    have hmX' : completionSmallYoneda.{w}.map j ≫ m' = s.inr := by
      calc
        completionSmallYoneda.map j ≫ m' =
            (completionSmallYoneda.map j ≫ eqToHom hpt.symm) ≫ m := by
              simp [m', Category.assoc]
        _ = t.inr ≫ m := by rw [htinrInv]
        _ = s.inr := hmX
    have hmb := congrArg (completionSmallYonedaHomEquiv B s.pt) hmB'
    rw [completionSmallYonedaHomEquiv_precomp] at hmb
    have hmx := congrArg (completionSmallYonedaHomEquiv X s.pt) hmX'
    rw [completionSmallYonedaHomEquiv_precomp] at hmx
    have hqBv := congrArg (fun g => g PUnit.unit) hqB
    have hqXv := congrArg (fun g => g PUnit.unit) hqX
    have h := pullback.hom_ext
      (k := TypeCat.ofHom fun _ : PUnit.{w + 1} =>
        completionSmallYonedaHomEquiv Q s.pt m')
      (l := TypeCat.ofHom fun _ : PUnit.{w + 1} => q)
      (by ext z; exact hmb.trans hqBv.symm)
      (by ext z; exact hmx.trans hqXv.symm)
    have hmq : completionSmallYonedaHomEquiv Q s.pt m' = q := by
      exact congrArg (fun g => g PUnit.unit) h
    have hcast : eqToHom hpt.symm ≫ m = eqToHom hpt.symm ≫ l := by
      apply (completionSmallYonedaHomEquiv Q s.pt).injective
      simpa [m', l] using hmq
    calc
      m = eqToHom hpt ≫ (eqToHom hpt.symm ≫ m) := by simp [Category.assoc]
      _ = eqToHom hpt ≫ (eqToHom hpt.symm ≫ l) := by rw [hcast]
      _ = l := by simp [Category.assoc])
  change IsPushout _ _ t.inl t.inr
  exact IsPushout.of_isColimit ht

theorem completionSmallYoneda_isColimit_cofan [IsCofibrationCategory C] {T : Type w} [Finite T]
    {Cs : T → C} {C' : C} {ι : ∀ t, Cs t ⟶ C'} (h : IsColimit (Cofan.mk C' ι)) :
    Nonempty (IsColimit (Cofan.mk (completionSmallYoneda.{w}.obj C')
      (fun t => completionSmallYoneda.{w}.map (ι t)))) := by
  classical
  let coc : Cofan (fun t => completionSmallYoneda.{w}.obj (Cs t)) :=
    Cofan.mk (completionSmallYoneda.{w}.obj C') (fun t => completionSmallYoneda.{w}.map (ι t))
  let desc (s : Cofan (fun t => completionSmallYoneda.{w}.obj (Cs t))) :
      completionSmallYoneda.{w}.obj C' ⟶ s.pt :=
    (completionSmallYonedaHomEquiv C' s.pt).symm
      ((completionCofanElementEquiv h s.pt).symm
        (fun t => completionSmallYonedaHomEquiv (Cs t) s.pt (s.inj t)))
  have desc_fac (s : Cofan (fun t => completionSmallYoneda.{w}.obj (Cs t))) (t : T) :
      coc.inj t ≫ desc s = s.inj t := by
    apply (completionSmallYonedaHomEquiv (Cs t) s.pt).injective
    change (completionSmallYonedaHomEquiv (Cs t) s.pt)
        (completionSmallYoneda.{w}.map (ι t) ≫ desc s) =
      (completionSmallYonedaHomEquiv (Cs t) s.pt) (s.inj t)
    rw [completionSmallYonedaHomEquiv_precomp]
    change (completionCofanElementEquiv h s.pt)
        (completionSmallYonedaHomEquiv C' s.pt (desc s)) t = _
    simp [desc]
  refine ⟨Cofan.IsColimit.mk coc desc desc_fac ?_⟩
  intro s m hm
  apply (completionSmallYonedaHomEquiv C' s.pt).injective
  apply (completionCofanElementEquiv h s.pt).injective
  funext t
  have hm' := hm t
  change completionSmallYoneda.{w}.map (ι t) ≫ m = s.inj t at hm'
  have ht := congrArg (completionSmallYonedaHomEquiv (Cs t) s.pt) hm'
  rw [completionSmallYonedaHomEquiv_precomp] at ht
  have hdt := congrArg (completionSmallYonedaHomEquiv (Cs t) s.pt) (desc_fac s t)
  change (completionSmallYonedaHomEquiv (Cs t) s.pt)
      (completionSmallYoneda.{w}.map (ι t) ≫ desc s) = _ at hdt
  rw [completionSmallYonedaHomEquiv_precomp] at hdt
  change s.pt.obj.map (ι t).op
      (completionSmallYonedaHomEquiv C' s.pt m) =
    s.pt.obj.map (ι t).op (completionSmallYonedaHomEquiv C' s.pt (desc s))
  exact ht.trans hdt.symm

private theorem cofibrationCategory_hasFiniteCoproducts [IsCofibrationCategory C] :
    HasFiniteCoproducts C := by
  classical
  obtain ⟨I, hI⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hI
  letI : HasInitial C := hI.hasInitial
  letI : ∀ {A B : C}, HasColimit (pair A B) := by
    intro A B
    letI : HasPushout (hI.to A) (hI.to B) :=
      IsCofibrationCategory.hasPushout (hI.to A) (hI.to B)
        (IsCofibrationCategory.initial_cofibration hI A)
    have hp : IsPushout (hI.to A) (hI.to B) (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    refine ⟨⟨BinaryCofan.mk (pushout.inl (hI.to A) (hI.to B))
      (pushout.inr (hI.to A) (hI.to B)), ?_⟩⟩
    exact isCoproductOfIsInitialIsPushout _ _ _ _ hI hp.isColimit
  letI : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair C
  exact hasFiniteCoproducts_of_has_binary_and_initial

private theorem isPushout_coprod_inr_with_id {A X Y : C} (f : X ⟶ Y)
    [HasBinaryCoproduct A X] [HasBinaryCoproduct A Y] :
    IsPushout (coprod.inr : X ⟶ A ⨿ X) f (coprod.map (𝟙 A) f) coprod.inr := by
  apply IsPushout.mk'
  · simp
  · intro T φ ψ h₁ h₂
    apply coprod.hom_ext
    · have h := congrArg (fun g => coprod.inl ≫ g) h₁
      simpa using h
    · exact h₂
  · intro T a b h
    refine ⟨coprod.desc (coprod.inl ≫ a) b, ?_, ?_⟩
    · apply coprod.hom_ext
      · simp
      · calc
          coprod.inr ≫ (coprod.map (𝟙 A) f ≫ coprod.desc (coprod.inl ≫ a) b) =
              (f ≫ coprod.inr) ≫ coprod.desc (coprod.inl ≫ a) b := by simp [Category.assoc]
          _ = f ≫ b := by simp
          _ = coprod.inr ≫ a := h.symm
    · simp

private theorem coprod_map_isCofibration [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] [HasFiniteCoproducts C] {A₁ A₂ B₁ B₂ : C}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂)
    (hf : cofibrations C f) (hg : cofibrations C g) :
    cofibrations C (coprod.map f g) := by
  have h₁ : IsPushout coprod.inl f (coprod.map f (𝟙 A₂)) coprod.inl :=
    IsPushout.of_coprod_inl_with_id f A₂
  have h₂ : IsPushout coprod.inr g (coprod.map (𝟙 B₁) g) coprod.inr :=
    isPushout_coprod_inr_with_id g
  have hc₁ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout h₁ hf
  have hc₂ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout h₂ hg
  have hcomp : coprod.map f (𝟙 A₂) ≫ coprod.map (𝟙 B₁) g = coprod.map f g := by
    simpa using coprod.map_map f (𝟙 A₂) (𝟙 B₁) g
  rw [← hcomp]
  exact (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem _ _ hc₁ hc₂

private theorem coprod_map_weakEquivalence [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] [HasFiniteCoproducts C] {A₁ A₂ B₁ B₂ : C}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂)
    (hf : cofibrations C f) (hg : cofibrations C g)
    (wf : weakEquivalences C f) (wg : weakEquivalences C g) :
    weakEquivalences C (coprod.map f g) := by
  have h₁ : IsPushout coprod.inl f (coprod.map f (𝟙 A₂)) coprod.inl :=
    IsPushout.of_coprod_inl_with_id f A₂
  have h₂ : IsPushout coprod.inr g (coprod.map (𝟙 B₁) g) coprod.inr :=
    isPushout_coprod_inr_with_id g
  have hw₁ := IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
    f coprod.inl coprod.inl (coprod.map f (𝟙 A₂)) h₁.flip hf wf
  have hw₂ := IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
    g coprod.inr coprod.inr (coprod.map (𝟙 B₁) g) h₂.flip hg wg
  have hcomp : coprod.map f (𝟙 A₂) ≫ coprod.map (𝟙 B₁) g = coprod.map f g := by
    simpa using coprod.map_map f (𝟙 A₂) (𝟙 B₁) g
  rw [← hcomp]
  exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _
    (by simpa using hw₁) (by simpa using hw₂)

private theorem exists_coproduct_cell_fin [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] :
    ∀ (n : ℕ) {Cs Ds : Fin n → C} (c : ∀ i, Cs i ⟶ Ds i)
      (hc : ∀ i, cofibrations C (c i)),
      ∃ (C' D' : C) (c' : C' ⟶ D') (ιC : ∀ i, Cs i ⟶ C') (ιD : ∀ i, Ds i ⟶ D'),
        Nonempty (IsColimit (Cofan.mk C' ιC)) ∧ Nonempty (IsColimit (Cofan.mk D' ιD)) ∧
        (∀ i, ιC i ≫ c' = c i ≫ ιD i) ∧ cofibrations C c' ∧
        ((∀ i, weakEquivalences C (c i)) → weakEquivalences C c') := by
  classical
  letI : HasFiniteCoproducts C := cofibrationCategory_hasFiniteCoproducts
  intro n
  induction n with
  | zero =>
    intro Cs Ds c hc
    obtain ⟨I, hIne⟩ := IsCofibrationCategory.exists_initial (C := C)
    let hI : IsInitial I := Classical.choice hIne
    let ιC : ∀ i : Fin 0, Cs i ⟶ I := fun i => Fin.elim0 i
    let ιD : ∀ i : Fin 0, Ds i ⟶ I := fun i => Fin.elim0 i
    have hC : IsColimit (Cofan.mk I ιC) := by
      refine Cofan.IsColimit.mk _ (fun s => hI.to s.pt) ?_ ?_
      · intro s i
        exact Fin.elim0 i
      · intro s m hm
        exact hI.hom_ext m (hI.to s.pt)
    have hD : IsColimit (Cofan.mk I ιD) := by
      refine Cofan.IsColimit.mk _ (fun s => hI.to s.pt) ?_ ?_
      · intro s i
        exact Fin.elim0 i
      · intro s m hm
        exact hI.hom_ext m (hI.to s.pt)
    refine ⟨I, I, 𝟙 I, ιC, ιD, ⟨hC⟩, ⟨hD⟩, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · exact IsCofibrationCategory.isomorphisms_le (C := C) (𝟙 I)
        (MorphismProperty.isomorphisms.infer_property (𝟙 I))
    · intro _
      exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 I)
        (MorphismProperty.isomorphisms.infer_property (𝟙 I))
  | succ n ih =>
    intro Cs Ds c hc
    obtain ⟨C₁, D₁, c₁, ιC₁, ιD₁, hC₁, hD₁, hcomm₁, hcof₁, hwe₁⟩ :=
      ih (Cs := fun i => Cs i.succ) (Ds := fun i => Ds i.succ)
        (fun i => c i.succ) (fun i => hc i.succ)
    let hC₁ : IsColimit (Cofan.mk C₁ ιC₁) := Classical.choice hC₁
    let hD₁ : IsColimit (Cofan.mk D₁ ιD₁) := Classical.choice hD₁
    let bC : BinaryCofan (Cs 0) C₁ :=
      BinaryCofan.mk (coprod.inl : Cs 0 ⟶ Cs 0 ⨿ C₁) coprod.inr
    let bD : BinaryCofan (Ds 0) D₁ :=
      BinaryCofan.mk (coprod.inl : Ds 0 ⟶ Ds 0 ⨿ D₁) coprod.inr
    have hbC : IsColimit bC := coprodIsCoprod (Cs 0) C₁
    have hbD : IsColimit bD := coprodIsCoprod (Ds 0) D₁
    let fullC : Cofan (fun i : Fin (n + 1) => Cs i) := extendCofan (Cofan.mk C₁ ιC₁) bC
    let fullD : Cofan (fun i : Fin (n + 1) => Ds i) := extendCofan (Cofan.mk D₁ ιD₁) bD
    let c' : fullC.pt ⟶ fullD.pt := coprod.map (c 0) c₁
    have hfullC : IsColimit fullC := extendCofanIsColimit Cs hC₁ hbC
    have hfullD : IsColimit fullD := extendCofanIsColimit Ds hD₁ hbD
    have hcomm : ∀ i, fullC.inj i ≫ c' = c i ≫ fullD.inj i := by
      intro i
      refine Fin.cases ?_ ?_ i
      · change coprod.inl ≫ coprod.map (c 0) c₁ = c 0 ≫ coprod.inl
        simp
      · intro i
        change (ιC₁ i ≫ coprod.inr) ≫ coprod.map (c 0) c₁ =
          c i.succ ≫ (ιD₁ i ≫ coprod.inr)
        calc
          (ιC₁ i ≫ coprod.inr) ≫ coprod.map (c 0) c₁ =
              (ιC₁ i ≫ c₁) ≫ coprod.inr := by simp [Category.assoc]
          _ = (c i.succ ≫ ιD₁ i) ≫ coprod.inr := by rw [hcomm₁ i]
          _ = c i.succ ≫ (ιD₁ i ≫ coprod.inr) := by simp [Category.assoc]
    have hcof : cofibrations C c' := by
      change cofibrations C (coprod.map (c 0) c₁)
      exact coprod_map_isCofibration (c 0) c₁ (hc 0) hcof₁
    refine ⟨fullC.pt, fullD.pt, c', fullC.inj, fullD.inj,
      ⟨hfullC⟩, ⟨hfullD⟩, hcomm, hcof, ?_⟩
    intro hw
    change weakEquivalences C (coprod.map (c 0) c₁)
    exact coprod_map_weakEquivalence (c 0) c₁ (hc 0) hcof₁ (hw 0)
      (hwe₁ (fun i => hw i.succ))

theorem exists_coproduct_cell [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {T : Type w} [Finite T] {Cs Ds : T → C} (c : ∀ t, Cs t ⟶ Ds t)
    (hc : ∀ t, cofibrations C (c t)) :
    ∃ (C' D' : C) (c' : C' ⟶ D') (ιC : ∀ t, Cs t ⟶ C') (ιD : ∀ t, Ds t ⟶ D'),
      Nonempty (IsColimit (Cofan.mk C' ιC)) ∧ Nonempty (IsColimit (Cofan.mk D' ιD)) ∧
      (∀ t, ιC t ≫ c' = c t ≫ ιD t) ∧ cofibrations C c' ∧
      ((∀ t, weakEquivalences C (c t)) → weakEquivalences C c') := by
  classical
  letI : HasFiniteCoproducts C := cofibrationCategory_hasFiniteCoproducts
  letI : Fintype T := Fintype.ofFinite T
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  obtain ⟨C', D', c', ιC₀, ιD₀, hC₀, hD₀, hcomm₀, hcof₀, hwe₀⟩ :=
    exists_coproduct_cell_fin (Fintype.card T)
      (Cs := fun i => Cs (e.symm i)) (Ds := fun i => Ds (e.symm i))
      (fun i => c (e.symm i)) (fun i => hc (e.symm i))
  let αC : (Discrete.equivalence e).functor ⋙
      Discrete.functor (fun i => Cs (e.symm i)) ≅ Discrete.functor Cs :=
    Discrete.natIso (fun ⟨t⟩ => eqToIso (congrArg Cs (e.symm_apply_apply t)))
  let αD : (Discrete.equivalence e).functor ⋙
      Discrete.functor (fun i => Ds (e.symm i)) ≅ Discrete.functor Ds :=
    Discrete.natIso (fun ⟨t⟩ => eqToIso (congrArg Ds (e.symm_apply_apply t)))
  let EC := Cocone.equivalenceOfReindexing (Discrete.equivalence e) αC
  let ED := Cocone.equivalenceOfReindexing (Discrete.equivalence e) αD
  let coC := EC.functor.obj (Cofan.mk C' ιC₀)
  let coD := ED.functor.obj (Cofan.mk D' ιD₀)
  let ιC : ∀ t, Cs t ⟶ C' := fun t => coC.ι.app ⟨t⟩
  let ιD : ∀ t, Ds t ⟶ D' := fun t => coD.ι.app ⟨t⟩
  have hC : IsColimit (Cofan.mk C' ιC) := by
    have h : IsColimit coC := IsColimit.ofLeftAdjoint EC.toAdjunction (Classical.choice hC₀)
    exact IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _) (fun ⟨t⟩ => by
      change coC.ι.app ⟨t⟩ ≫ 𝟙 C' = coC.ι.app ⟨t⟩
      exact Category.comp_id _))
  have hD : IsColimit (Cofan.mk D' ιD) := by
    have h : IsColimit coD := IsColimit.ofLeftAdjoint ED.toAdjunction (Classical.choice hD₀)
    exact IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _) (fun ⟨t⟩ => by
      change coD.ι.app ⟨t⟩ ≫ 𝟙 D' = coD.ι.app ⟨t⟩
      exact Category.comp_id _))
  refine ⟨C', D', c', ιC, ιD, ⟨hC⟩, ⟨hD⟩, ?_, hcof₀, ?_⟩
  · intro t
    dsimp [ιC, ιD, coC, coD, EC, ED, Cocone.equivalenceOfReindexing,
      Cocone.whiskeringEquivalence, Cocone.whiskering, Cocone.precomposeEquivalence]
    have ht : e.symm (e t) = t := e.symm_apply_apply t
    have castNat (a b : T) (h : b = a) :
        eqToHom (congrArg Cs h).symm ≫ c b =
          c a ≫ eqToHom (congrArg Ds h).symm := by
      cases h
      simp
    calc
      (αC.inv.app ⟨t⟩ ≫ ιC₀ (e t)) ≫ c' =
          αC.inv.app ⟨t⟩ ≫ (c (e.symm (e t)) ≫ ιD₀ (e t)) := by
            rw [Category.assoc, hcomm₀ (e t)]
      _ = c t ≫ (αD.inv.app ⟨t⟩ ≫ ιD₀ (e t)) := by
            rw [← Category.assoc]
            have hCast := castNat t (e.symm (e t)) ht
            change αC.inv.app ⟨t⟩ ≫ c (e.symm (e t)) =
              c t ≫ αD.inv.app ⟨t⟩ at hCast
            rw [hCast]
            simp [Category.assoc]
  · intro hw
    apply hwe₀
    intro i
    exact hw (e.symm i)

theorem completionSmallYoneda_weakEquivalence [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    Completion.weakEquivalences C (completionSmallYoneda.{w}.map f) := by
  change presheafWeakEquivalences (completionSmallYoneda.{w}.map f).hom
  intro A B i hi a b hab
  change (shrinkYoneda.map f).app (op A) a = (shrinkYoneda.obj Y).map i.op b at hab
  let a' : A ⟶ X := shrinkYonedaObjObjEquiv a
  let b' : B ⟶ Y := shrinkYonedaObjObjEquiv b
  have hab' : a' ≫ f = i ≫ b' := by
    have h := congrArg shrinkYonedaObjObjEquiv hab
    rw [shrinkYonedaObjObjEquiv_map_app, shrinkYonedaObjObjEquiv_obj_map] at h
    simpa [a', b'] using h
  obtain ⟨l, hl, hrel⟩ :=
    cofibration_semilifts_against_weak_equivalence i hi a' f b' hab'.symm hf
  obtain ⟨cyl, H, h₀, h₁⟩ := hrel
  let le : (shrinkYoneda.obj X).obj (op B) := shrinkYonedaObjObjEquiv.symm l
  let he : (shrinkYoneda.obj Y).obj (op cyl.I) := shrinkYonedaObjObjEquiv.symm H
  refine ⟨le, cyl, he, ?_, ?_, ?_⟩
  · apply shrinkYonedaObjObjEquiv.injective
    change shrinkYonedaObjObjEquiv ((shrinkYoneda.obj X).map i.op le) =
      shrinkYonedaObjObjEquiv a
    rw [shrinkYonedaObjObjEquiv_obj_map]
    simpa [le, a'] using hl
  · apply shrinkYonedaObjObjEquiv.injective
    change shrinkYonedaObjObjEquiv
        ((shrinkYoneda.obj Y).map (cyl.j₀ ≫ cyl.c).op he) =
      shrinkYonedaObjObjEquiv ((shrinkYoneda.map f).app (op B) le)
    rw [shrinkYonedaObjObjEquiv_obj_map, shrinkYonedaObjObjEquiv_map_app]
    simpa [he, le] using h₀
  · apply shrinkYonedaObjObjEquiv.injective
    change shrinkYonedaObjObjEquiv
        ((shrinkYoneda.obj Y).map (cyl.j₁ ≫ cyl.c).op he) =
      shrinkYonedaObjObjEquiv b
    rw [shrinkYonedaObjObjEquiv_obj_map]
    simpa [he, b'] using h₁

end HomotopyHypothesis.Category.SemiModelStructure
