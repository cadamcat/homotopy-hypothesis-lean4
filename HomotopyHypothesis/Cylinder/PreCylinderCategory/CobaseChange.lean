import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Brown
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Cor
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Coslice
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Pushout
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
  {A B : C} (v : A ⟶ B)

/-- `v♯` on objects: pushout along `v` (H:536). -/
noncomputable def wSharpObj (X : UnderCof (C := C) A) : UnderCof (C := C) B := by
  classical
  have hcof : cofibrations C X.hom := X.cof
  haveI : HasPushout X.hom v :=
    IsCofibrationCategory.hasPushout _ _ hcof
  exact ⟨pushout X.hom v, pushout.inr _ _,
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := (IsPushout.of_hasPushout X.hom v).flip) (hf := hcof)⟩

/-- `v♯` on morphisms via universal property in `C`. -/
noncomputable def wSharpMap {X Y : UnderCof (C := C) A} (f : X ⟶ Y) :
    wSharpObj (C := C) (A := A) (B := B) v X ⟶
    wSharpObj (C := C) (A := A) (B := B) v Y := by
  have hcofX : cofibrations C X.hom := X.cof
  have hcofY : cofibrations C Y.hom := Y.cof
  haveI : HasPushout X.hom v :=
    IsCofibrationCategory.hasPushout _ _ hcofX
  haveI : HasPushout Y.hom v :=
    IsCofibrationCategory.hasPushout _ _ hcofY
  let hPX : IsPushout X.hom v (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  let hPY : IsPushout Y.hom v (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  have hagree : X.hom ≫ (f.hom ≫ pushout.inl Y.hom v) =
      v ≫ pushout.inr Y.hom v := by
    calc X.hom ≫ (f.hom ≫ pushout.inl _ _)
        = (X.hom ≫ f.hom) ≫ pushout.inl _ _ := by rw [← Category.assoc]
      _ = Y.hom ≫ pushout.inl _ _ := by rw [f.w]
      _ = v ≫ pushout.inr _ _ := hPY.w
  let d : pushout X.hom v ⟶ pushout Y.hom v :=
    hPX.desc (f.hom ≫ pushout.inl _ _) (pushout.inr _ _) hagree
  have htri : (wSharpObj (C := C) (A := A) (B := B) v X).hom ≫ d =
      (wSharpObj (C := C) (A := A) (B := B) v Y).hom := by
    show pushout.inr X.hom v ≫ d = pushout.inr Y.hom v
    exact hPX.inr_desc _ _ _
  exact UnderCofHom.mk (X := wSharpObj (C := C) (A := A) (B := B) v X)
    (Y := wSharpObj (C := C) (A := A) (B := B) v Y) d htri

/-- `v♯` sends trivial cofibrations to trivial cofibrations (key input to Ken Brown). -/
theorem wSharp_preservesTrivialCof {X Y : UnderCof (C := C) A} (f : X ⟶ Y)
    (hcof : cofibrations C f.hom) (hwe : weakEquivalences C f.hom) :
    cofibrations C (wSharpMap (C := C) (A := A) (B := B) v f).hom ∧
    weakEquivalences C (wSharpMap (C := C) (A := A) (B := B) v f).hom := by
  have hcofX : cofibrations C X.hom := X.cof
  have hcofY : cofibrations C Y.hom := Y.cof
  haveI : HasPushout X.hom v :=
    IsCofibrationCategory.hasPushout _ _ hcofX
  haveI : HasPushout Y.hom v :=
    IsCofibrationCategory.hasPushout _ _ hcofY
  let hPX : IsPushout X.hom v (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  let hPY : IsPushout Y.hom v (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  have hag : X.hom ≫ (f.hom ≫ pushout.inl Y.hom v) =
      v ≫ pushout.inr Y.hom v := by
    calc X.hom ≫ (f.hom ≫ pushout.inl _ _)
        = (X.hom ≫ f.hom) ≫ pushout.inl _ _ := by rw [← Category.assoc]
      _ = Y.hom ≫ pushout.inl _ _ := by rw [f.w]
      _ = v ≫ pushout.inr _ _ := hPY.w
  let d : pushout X.hom v ⟶ pushout Y.hom v :=
    hPX.desc (f.hom ≫ pushout.inl Y.hom v) (pushout.inr Y.hom v) hag
  have hcommD : f.hom ≫ pushout.inl Y.hom v =
      pushout.inl X.hom v ≫ d :=
    (hPX.inl_desc _ _ _).symm
  have hsq : IsPushout f.hom (pushout.inl X.hom v)
      (pushout.inl Y.hom v) d := by
    apply IsPushout.mk' hcommD
    · intro T φ φ' hφ hφ'
      apply hPY.hom_ext
      · exact hφ
      · have eInr : pushout.inr X.hom v ≫ d = pushout.inr Y.hom v :=
          hPX.inr_desc _ _ _
        have e : pushout.inr Y.hom v ≫ φ = pushout.inr Y.hom v ≫ φ' := by
          calc pushout.inr Y.hom v ≫ φ
              = (pushout.inr X.hom v ≫ d) ≫ φ := by rw [← eInr]
            _ = pushout.inr X.hom v ≫ (d ≫ φ) := by rw [Category.assoc]
            _ = pushout.inr X.hom v ≫ (d ≫ φ') := by rw [hφ']
            _ = (pushout.inr X.hom v ≫ d) ≫ φ' := by rw [← Category.assoc]
            _ = pushout.inr Y.hom v ≫ φ' := by rw [eInr]
        exact e
    · intro T a b hab
      have habC : f.hom ≫ a = pushout.inl X.hom v ≫ b := hab
      have hagL : Y.hom ≫ a = v ≫ (pushout.inr X.hom v ≫ b) := by
        calc Y.hom ≫ a
            = (X.hom ≫ f.hom) ≫ a := by rw [← f.w]
          _ = X.hom ≫ (f.hom ≫ a) := by rw [Category.assoc]
          _ = X.hom ≫ (pushout.inl X.hom v ≫ b) := by rw [habC]
          _ = (X.hom ≫ pushout.inl X.hom v) ≫ b := by rw [← Category.assoc]
          _ = (v ≫ pushout.inr X.hom v) ≫ b := by rw [hPX.w]
          _ = v ≫ (pushout.inr X.hom v ≫ b) := by rw [Category.assoc]
      let l : pushout Y.hom v ⟶ T :=
        hPY.desc a (pushout.inr X.hom v ≫ b) hagL
      have hl1 : pushout.inl Y.hom v ≫ l = a :=
        hPY.inl_desc _ _ _
      have hl2 : pushout.inr Y.hom v ≫ l = pushout.inr X.hom v ≫ b :=
        hPY.inr_desc _ _ _
      refine ⟨l, hl1, ?_⟩
      apply hPX.hom_ext
      · have eInl : pushout.inl X.hom v ≫ d =
            f.hom ≫ pushout.inl Y.hom v :=
          hPX.inl_desc _ _ _
        calc pushout.inl X.hom v ≫ (d ≫ l)
            = (pushout.inl X.hom v ≫ d) ≫ l := by rw [← Category.assoc]
          _ = (f.hom ≫ pushout.inl Y.hom v) ≫ l := by rw [eInl]
          _ = f.hom ≫ (pushout.inl Y.hom v ≫ l) := by rw [Category.assoc]
          _ = f.hom ≫ a := by rw [hl1]
          _ = pushout.inl X.hom v ≫ b := by rw [← habC]
      · have eInrX : pushout.inr X.hom v ≫ d = pushout.inr Y.hom v :=
          hPX.inr_desc _ _ _
        calc pushout.inr X.hom v ≫ (d ≫ l)
            = (pushout.inr X.hom v ≫ d) ≫ l := by rw [← Category.assoc]
          _ = pushout.inr Y.hom v ≫ l := by rw [eInrX]
          _ = pushout.inr X.hom v ≫ b := by rw [hl2]
  have hcof_d : cofibrations C d :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hsq.flip) (hf := hcof)
  have hwe_d : weakEquivalences C d :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      f.hom (pushout.inl X.hom v) (pushout.inl Y.hom v) d hsq hcof hwe
  show cofibrations C (wSharpMap (C := C) (A := A) (B := B) v f).hom ∧
    weakEquivalences C (wSharpMap (C := C) (A := A) (B := B) v f).hom
  exact ⟨hcof_d, hwe_d⟩


/-- `v♯` as a functor (H:536, morphism of cofibration categories in the making). -/
noncomputable def wSharpFunctor : UnderCof (C := C) A ⥤ UnderCof (C := C) B where
  obj X := wSharpObj (C := C) (A := A) (B := B) v X
  map f := wSharpMap (C := C) (A := A) (B := B) v f
  map_id X := by
    apply UnderCof.hom_ext
    have hcofX : cofibrations C X.hom := X.cof
    haveI : HasPushout X.hom v :=
      IsCofibrationCategory.hasPushout _ _ hcofX
    let hPX : IsPushout X.hom v (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    show hPX.desc ((𝟙 X.obj) ≫ pushout.inl X.hom v) (pushout.inr X.hom v) _ = 𝟙 _
    apply hPX.hom_ext
    · calc pushout.inl X.hom v ≫ hPX.desc _ _ _
          = (𝟙 X.obj) ≫ pushout.inl X.hom v := hPX.inl_desc _ _ _
        _ = pushout.inl X.hom v := Category.id_comp _
        _ = pushout.inl X.hom v ≫ 𝟙 _ := by rw [Category.comp_id]
    · calc pushout.inr X.hom v ≫ hPX.desc _ _ _
          = pushout.inr X.hom v := hPX.inr_desc _ _ _
        _ = pushout.inr X.hom v ≫ 𝟙 _ := by rw [Category.comp_id]
  map_comp {X Y Z} f g := by
    apply UnderCof.hom_ext
    have hcofX : cofibrations C X.hom := X.cof
    have hcofY : cofibrations C Y.hom := Y.cof
    have hcofZ : cofibrations C Z.hom := Z.cof
    haveI : HasPushout X.hom v :=
      IsCofibrationCategory.hasPushout _ _ hcofX
    haveI : HasPushout Y.hom v :=
      IsCofibrationCategory.hasPushout _ _ hcofY
    haveI : HasPushout Z.hom v :=
      IsCofibrationCategory.hasPushout _ _ hcofZ
    let hPX : IsPushout X.hom v (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    let hPY : IsPushout Y.hom v (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    let hPZ : IsPushout Z.hom v (pushout.inl _ _) (pushout.inr _ _) :=
      IsPushout.of_hasPushout _ _
    have hagX : X.hom ≫ (f.hom ≫ pushout.inl Y.hom v) =
        v ≫ pushout.inr Y.hom v := by
      calc X.hom ≫ (f.hom ≫ pushout.inl _ _)
          = (X.hom ≫ f.hom) ≫ pushout.inl _ _ := by rw [← Category.assoc]
        _ = Y.hom ≫ pushout.inl _ _ := by rw [f.w]
        _ = v ≫ pushout.inr _ _ := hPY.w
    have hagY : Y.hom ≫ (g.hom ≫ pushout.inl Z.hom v) =
        v ≫ pushout.inr Z.hom v := by
      calc Y.hom ≫ (g.hom ≫ pushout.inl _ _)
          = (Y.hom ≫ g.hom) ≫ pushout.inl _ _ := by rw [← Category.assoc]
        _ = Z.hom ≫ pushout.inl _ _ := by rw [g.w]
        _ = v ≫ pushout.inr _ _ := hPZ.w
    have hagXZ : X.hom ≫ ((f.hom ≫ g.hom) ≫ pushout.inl Z.hom v) =
        v ≫ pushout.inr Z.hom v := by
      calc X.hom ≫ ((f.hom ≫ g.hom) ≫ pushout.inl _ _)
          = (X.hom ≫ (f.hom ≫ g.hom)) ≫ pushout.inl _ _ := by rw [← Category.assoc]
        _ = ((X.hom ≫ f.hom) ≫ g.hom) ≫ pushout.inl _ _ := by rw [← Category.assoc]
        _ = ((Y.hom ≫ g.hom)) ≫ pushout.inl _ _ := by rw [f.w]
        _ = Z.hom ≫ pushout.inl _ _ := by rw [g.w]
        _ = v ≫ pushout.inr _ _ := hPZ.w
    let dXZ : pushout X.hom v ⟶ pushout Z.hom v :=
      hPX.desc ((f.hom ≫ g.hom) ≫ pushout.inl Z.hom v) (pushout.inr Z.hom v) hagXZ
    let dX : pushout X.hom v ⟶ pushout Y.hom v :=
      hPX.desc (f.hom ≫ pushout.inl Y.hom v) (pushout.inr Y.hom v) hagX
    let dY : pushout Y.hom v ⟶ pushout Z.hom v :=
      hPY.desc (g.hom ≫ pushout.inl Z.hom v) (pushout.inr Z.hom v) hagY
    show dXZ = dX ≫ dY
    apply hPX.hom_ext
    · have eX : pushout.inl X.hom v ≫ dX = f.hom ≫ pushout.inl Y.hom v :=
        hPX.inl_desc _ _ _
      have eY : pushout.inl Y.hom v ≫ dY = g.hom ≫ pushout.inl Z.hom v :=
        hPY.inl_desc _ _ _
      calc pushout.inl X.hom v ≫ dXZ
          = (f.hom ≫ g.hom) ≫ pushout.inl Z.hom v := hPX.inl_desc _ _ _
        _ = f.hom ≫ (g.hom ≫ pushout.inl Z.hom v) := by rw [Category.assoc]
        _ = f.hom ≫ (pushout.inl Y.hom v ≫ dY) := by rw [← eY]
        _ = (f.hom ≫ pushout.inl Y.hom v) ≫ dY := by rw [Category.assoc]
        _ = (pushout.inl X.hom v ≫ dX) ≫ dY := by rw [← eX]
        _ = pushout.inl X.hom v ≫ (dX ≫ dY) := by rw [Category.assoc]
    · have eXr : pushout.inr X.hom v ≫ dX = pushout.inr Y.hom v :=
        hPX.inr_desc _ _ _
      have eYr : pushout.inr Y.hom v ≫ dY = pushout.inr Z.hom v :=
        hPY.inr_desc _ _ _
      calc pushout.inr X.hom v ≫ dXZ
          = pushout.inr Z.hom v := hPX.inr_desc _ _ _
        _ = pushout.inr Y.hom v ≫ dY := by rw [← eYr]
        _ = (pushout.inr X.hom v ≫ dX) ≫ dY := by rw [← eXr]
        _ = pushout.inr X.hom v ≫ (dX ≫ dY) := by rw [Category.assoc]

/-- `v♯` preserves weak equivalences by Ken Brown (H Cor 2.2.2(2) in `C(A)`). -/
theorem wSharp_preservesWE {X Y : UnderCof (C := C) A} (f : X ⟶ Y)
    (hf : weakEquivalences (UnderCof (C := C) A) f) :
    weakEquivalences (UnderCof (C := C) B)
      ((wSharpFunctor v).map f) := by
  have hF : ∀ ⦃X Y : UnderCof (C := C) A⦄ (f : X ⟶ Y),
      cofibrations (UnderCof (C := C) A) f →
      weakEquivalences (UnderCof (C := C) A) f →
      cofibrations (UnderCof (C := C) B)
        ((wSharpFunctor v).map f) ∧
      weakEquivalences (UnderCof (C := C) B)
        ((wSharpFunctor v).map f) := by
    intro X Y f hcof hwe
    have hcofC : cofibrations C f.hom := hcof
    have hweC : weakEquivalences C f.hom := hwe
    have h := wSharp_preservesTrivialCof (C := C) (A := A) (B := B) v f hcofC hweC
    show cofibrations C (wSharpMap (C := C) (A := A) (B := B) v f).hom ∧
      weakEquivalences C (wSharpMap (C := C) (A := A) (B := B) v f).hom
    exact h
  exact kenBrown (wSharpFunctor v) hF f hf

/-- H Cor 2.2.2(3): pushout of a weak equivalence along a cofibration is a weak equivalence. -/
theorem weakEquivalence_cobaseChange_proof :
    ∀ {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
      [IsCylinderCategory C] {A B X P : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P),
      IsPushout i f k j → cofibrations C i → weakEquivalences C f → weakEquivalences C k := by
  intro C _ _ _ _ A B X P i f k j h hi hf
  haveI := we_twoOutOfThree (C := C)
  -- 1. Initial object and cylinder for A
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hcof_OA : cofibrations C (hO.to A) := IsCofibrationCategory.initial_cofibration hO A
  have hcof_OX : cofibrations C (hO.to X) := IsCofibrationCategory.initial_cofibration hO X
  let cyl := Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO A)
  let j0 : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let j1 : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  let p : cyl.I ⟶ A := cyl.p
  obtain ⟨hcof_j0, hwe_j0, hcof_j1, hwe_j1⟩ := cyl_incl_trivial hO cyl
  have hj0_p : j0 ≫ p = 𝟙 A := by
    change (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 A
    rw [Category.assoc]
    exact cyl.j₀_c_p
  have hj1_p : j1 ≫ p = 𝟙 A := by
    change (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 A
    rw [Category.assoc]
    exact cyl.j₁_c_p

  -- 2. Pushout Pcyl = pushout j0 f
  haveI : HasPushout j0 f := IsCofibrationCategory.hasPushout _ _ hcof_j0
  let Pcyl := pushout j0 f
  let inI_P : cyl.I ⟶ Pcyl := pushout.inl _ _
  let inX_P : X ⟶ Pcyl := pushout.inr _ _
  let hPcyl : IsPushout j0 f inI_P inX_P := IsPushout.of_hasPushout _ _
  have hwe_inX : weakEquivalences C inX_P :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      j0 f inI_P inX_P hPcyl hcof_j0 hwe_j0
  have hcof_inX : cofibrations C inX_P :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hPcyl.flip) (hf := hcof_j0)

  -- Retraction rP : Pcyl ⟶ X
  have hagree_P : j0 ≫ (p ≫ f) = f ≫ 𝟙 X := by
    calc j0 ≫ (p ≫ f) = (j0 ≫ p) ≫ f := by rw [← Category.assoc]
      _ = 𝟙 A ≫ f := by rw [hj0_p]
      _ = f := by rw [Category.id_comp]
      _ = f ≫ 𝟙 X := by rw [Category.comp_id]
  let rP : Pcyl ⟶ X := hPcyl.desc (p ≫ f) (𝟙 X) hagree_P
  have hrP_inX : inX_P ≫ rP = 𝟙 X := hPcyl.inr_desc _ _ _
  have hrP_inI : inI_P ≫ rP = p ≫ f := hPcyl.inl_desc _ _ _
  have hwe_rP : weakEquivalences C rP :=
    MorphismProperty.of_precomp (weakEquivalences C) inX_P rP hwe_inX (by
      rw [hrP_inX]
      exact we_id X)
  let j1P : A ⟶ Pcyl := j1 ≫ inI_P
  have hj1P_rP : j1P ≫ rP = f := by
    calc j1P ≫ rP = (j1 ≫ inI_P) ≫ rP := rfl
      _ = j1 ≫ (inI_P ≫ rP) := by rw [Category.assoc]
      _ = j1 ≫ (p ≫ f) := by rw [hrP_inI]
      _ = (j1 ≫ p) ≫ f := by rw [← Category.assoc]
      _ = 𝟙 A ≫ f := by rw [hj1_p]
      _ = f := by rw [Category.id_comp]
  have hwe_j1P : weakEquivalences C j1P :=
    MorphismProperty.of_postcomp (weakEquivalences C) j1P rP hwe_rP (by
      rw [hj1P_rP]
      exact hf)

  -- j1P is a cofibration via P0 = pushout cyl.j0 f and P' = pushout cyl.c inlP
  have hcof_cylj0 : cofibrations C cyl.j₀ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := cyl.isPushout) (hf := hcof_OA)
  haveI : HasPushout cyl.j₀ f := IsCofibrationCategory.hasPushout _ _ hcof_cylj0
  let P0 := pushout cyl.j₀ f
  let inlP : cyl.P ⟶ P0 := pushout.inl _ _
  let inX0 : X ⟶ P0 := pushout.inr _ _
  let hP0 : IsPushout cyl.j₀ f inlP inX0 := IsPushout.of_hasPushout _ _
  have hPast := cyl.isPushout.paste_horiz hP0.flip
  have hOf : (hO.to A) ≫ f = hO.to X := hO.hom_ext _ _
  have hPast' : IsPushout (hO.to X) (hO.to A) inX0 (cyl.j₁ ≫ inlP) := by
    have h := hPast
    rw [hOf] at h
    exact h
  have hcof_j1_inlP : cofibrations C (cyl.j₁ ≫ inlP) :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hPast'.flip) (hf := hcof_OX)

  haveI : HasPushout cyl.c inlP := IsCofibrationCategory.hasPushout _ _ cyl.c_mem
  let P' := pushout cyl.c inlP
  let inlI' : cyl.I ⟶ P' := pushout.inl _ _
  let inP0 : P0 ⟶ P' := pushout.inr _ _
  let hP' : IsPushout cyl.c inlP inlI' inP0 := IsPushout.of_hasPushout _ _
  have hcof_inP0 : cofibrations C inP0 :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hP'.flip) (hf := cyl.c_mem)
  have hcof_comp : cofibrations C ((cyl.j₁ ≫ inlP) ≫ inP0) :=
    IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hcof_j1_inlP hcof_inP0

  -- P' is pushout of (j0) and f
  have hP'_paste : IsPushout (cyl.j₀ ≫ cyl.c) f inlI' (inX0 ≫ inP0) :=
    hP0.paste_horiz hP'
  let e_P : P' ≅ Pcyl := hP'_paste.isoIsPushout _ _ hPcyl
  have he_P_inl : inlI' ≫ e_P.hom = inI_P :=
    hP'_paste.inl_isoIsPushout_hom _ _ hPcyl
  have hj1P_eq : ((cyl.j₁ ≫ inlP) ≫ inP0) ≫ e_P.hom = j1P := by
    calc ((cyl.j₁ ≫ inlP) ≫ inP0) ≫ e_P.hom
        = (cyl.j₁ ≫ (inlP ≫ inP0)) ≫ e_P.hom := by rw [Category.assoc cyl.j₁ inlP inP0]
      _ = (cyl.j₁ ≫ (cyl.c ≫ inlI')) ≫ e_P.hom := by rw [← hP'.w]
      _ = ((cyl.j₁ ≫ cyl.c) ≫ inlI') ≫ e_P.hom := by rw [← Category.assoc cyl.j₁ cyl.c inlI']
      _ = (cyl.j₁ ≫ cyl.c) ≫ (inlI' ≫ e_P.hom) := by rw [Category.assoc (cyl.j₁ ≫ cyl.c) inlI' e_P.hom]
      _ = (cyl.j₁ ≫ cyl.c) ≫ inI_P := by rw [he_P_inl]
      _ = j1 ≫ inI_P := rfl
      _ = j1P := rfl
  have hcof_j1P : cofibrations C j1P := by
    rw [← hj1P_eq]
    exact MorphismProperty.RespectsIso.postcomp (cofibrations C) e_P.hom
      ((cyl.j₁ ≫ inlP) ≫ inP0) hcof_comp

  -- 3. Q = pushout j1 i
  haveI : HasPushout j1 i := IsCofibrationCategory.hasPushout _ _ hcof_j1
  let Q := pushout j1 i
  let inI_Q : cyl.I ⟶ Q := pushout.inl _ _
  let inB_Q : B ⟶ Q := pushout.inr _ _
  let hQ : IsPushout j1 i inI_Q inB_Q := IsPushout.of_hasPushout _ _
  have hwe_inB_Q : weakEquivalences C inB_Q :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      j1 i inI_Q inB_Q hQ hcof_j1 hwe_j1
  have hcof_inI_Q : cofibrations C inI_Q :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hQ) (hf := hi)
  let u : A ⟶ Q := j0 ≫ inI_Q
  have hcof_u : cofibrations C u :=
    IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hcof_j0 hcof_inI_Q

  -- Retraction ρ : Q ⟶ B
  have hagree_Q : j1 ≫ (p ≫ i) = i ≫ 𝟙 B := by
    calc j1 ≫ (p ≫ i) = (j1 ≫ p) ≫ i := by rw [← Category.assoc]
      _ = 𝟙 A ≫ i := by rw [hj1_p]
      _ = i := by rw [Category.id_comp]
      _ = i ≫ 𝟙 B := by rw [Category.comp_id]
  let ρ : Q ⟶ B := hQ.desc (p ≫ i) (𝟙 B) hagree_Q
  have hρ_inB : inB_Q ≫ ρ = 𝟙 B := hQ.inr_desc _ _ _
  have hρ_inI : inI_Q ≫ ρ = p ≫ i := hQ.inl_desc _ _ _
  have hwe_ρ : weakEquivalences C ρ :=
    MorphismProperty.of_precomp (weakEquivalences C) inB_Q ρ hwe_inB_Q (by
      rw [hρ_inB]
      exact we_id B)

  -- Objects and morphism in UnderCof A
  let Q_obj : UnderCof (C := C) A := ⟨Q, u, hcof_u⟩
  let B_obj : UnderCof (C := C) A := ⟨B, i, hi⟩
  have hu_ρ : u ≫ ρ = i := by
    calc u ≫ ρ = (j0 ≫ inI_Q) ≫ ρ := rfl
      _ = j0 ≫ (inI_Q ≫ ρ) := by rw [Category.assoc]
      _ = j0 ≫ (p ≫ i) := by rw [hρ_inI]
      _ = (j0 ≫ p) ≫ i := by rw [← Category.assoc]
      _ = 𝟙 A ≫ i := by rw [hj0_p]
      _ = i := by rw [Category.id_comp]
  let ρ_hom : Q_obj ⟶ B_obj := UnderCofHom.mk (X := Q_obj) (Y := B_obj) ρ hu_ρ
  have hwe_ρ_hom : weakEquivalences (UnderCof (C := C) A) ρ_hom := hwe_ρ

  -- wSharp preserves weak equivalences
  have hwe_wSharp := wSharp_preservesWE (C := C) (A := A) (B := X) f ρ_hom hwe_ρ_hom
  let d_map := (wSharpFunctor (C := C) (A := A) (B := X) f).map ρ_hom
  have hwe_d : weakEquivalences C d_map.hom := hwe_wSharp

  -- Pushout comparison pushout i f ≅ P
  haveI : HasPushout i f := IsCofibrationCategory.hasPushout _ _ hi
  let hP_if : IsPushout i f (pushout.inl i f) (pushout.inr i f) :=
    IsPushout.of_hasPushout i f
  let e_BP : pushout i f ≅ P := hP_if.isoIsPushout _ _ h
  have he_BP_inl : pushout.inl i f ≫ e_BP.hom = k :=
    hP_if.inl_isoIsPushout_hom _ _ h
  have hwe_e_BP : weakEquivalences C e_BP.hom :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _
      (MorphismProperty.isomorphisms.infer_property e_BP.hom)

  -- S1 = pushout i j1P
  haveI : HasPushout i j1P := IsCofibrationCategory.hasPushout _ _ hi
  let S1 := pushout i j1P
  let inB_S1 : B ⟶ S1 := pushout.inl _ _
  let inP_S1 : Pcyl ⟶ S1 := pushout.inr _ _
  let hS1 : IsPushout i j1P inB_S1 inP_S1 := IsPushout.of_hasPushout _ _
  have hwe_inB_S1 : weakEquivalences C inB_S1 :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      j1P i inP_S1 inB_S1 hS1.flip hcof_j1P hwe_j1P

  -- S2 = pushout u f
  haveI : HasPushout u f := IsCofibrationCategory.hasPushout _ _ hcof_u
  let S2 := pushout u f
  let inQ_S2 : Q ⟶ S2 := pushout.inl _ _
  let inX_S2 : X ⟶ S2 := pushout.inr _ _
  let hS2 : IsPushout u f inQ_S2 inX_S2 := IsPushout.of_hasPushout _ _

  -- Map psi12 : S1 ⟶ S2
  have hagree_phiP : j0 ≫ (inI_Q ≫ inQ_S2) = f ≫ inX_S2 := by
    calc j0 ≫ (inI_Q ≫ inQ_S2) = (j0 ≫ inI_Q) ≫ inQ_S2 := by rw [← Category.assoc]
      _ = u ≫ inQ_S2 := rfl
      _ = f ≫ inX_S2 := hS2.w
  let phiP : Pcyl ⟶ S2 := hPcyl.desc (inI_Q ≫ inQ_S2) inX_S2 hagree_phiP
  have hphiP_inI : inI_P ≫ phiP = inI_Q ≫ inQ_S2 := hPcyl.inl_desc _ _ _
  have hphiP_inX : inX_P ≫ phiP = inX_S2 := hPcyl.inr_desc _ _ _
  have hagree_psi12 : i ≫ (inB_Q ≫ inQ_S2) = j1P ≫ phiP := by
    calc i ≫ (inB_Q ≫ inQ_S2) = (i ≫ inB_Q) ≫ inQ_S2 := by rw [← Category.assoc]
      _ = (j1 ≫ inI_Q) ≫ inQ_S2 := by rw [hQ.w]
      _ = j1 ≫ (inI_Q ≫ inQ_S2) := by rw [Category.assoc]
      _ = j1 ≫ (inI_P ≫ phiP) := by rw [← hphiP_inI]
      _ = (j1 ≫ inI_P) ≫ phiP := by rw [← Category.assoc]
      _ = j1P ≫ phiP := rfl
  let psi12 : S1 ⟶ S2 := hS1.desc (inB_Q ≫ inQ_S2) phiP hagree_psi12
  have hpsi12_inB : inB_S1 ≫ psi12 = inB_Q ≫ inQ_S2 := hS1.inl_desc _ _ _
  have hpsi12_inP : inP_S1 ≫ psi12 = phiP := hS1.inr_desc _ _ _

  -- Map psi21 : S2 ⟶ S1
  have hagree_phiQ : j1 ≫ (inI_P ≫ inP_S1) = i ≫ inB_S1 := by
    calc j1 ≫ (inI_P ≫ inP_S1) = (j1 ≫ inI_P) ≫ inP_S1 := by rw [← Category.assoc]
      _ = j1P ≫ inP_S1 := rfl
      _ = i ≫ inB_S1 := hS1.w.symm
  let phiQ : Q ⟶ S1 := hQ.desc (inI_P ≫ inP_S1) inB_S1 hagree_phiQ
  have hphiQ_inI : inI_Q ≫ phiQ = inI_P ≫ inP_S1 := hQ.inl_desc _ _ _
  have hphiQ_inB : inB_Q ≫ phiQ = inB_S1 := hQ.inr_desc _ _ _
  have hagree_psi21 : u ≫ phiQ = f ≫ (inX_P ≫ inP_S1) := by
    calc u ≫ phiQ = (j0 ≫ inI_Q) ≫ phiQ := rfl
      _ = j0 ≫ (inI_Q ≫ phiQ) := by rw [Category.assoc]
      _ = j0 ≫ (inI_P ≫ inP_S1) := by rw [hphiQ_inI]
      _ = (j0 ≫ inI_P) ≫ inP_S1 := by rw [← Category.assoc]
      _ = (f ≫ inX_P) ≫ inP_S1 := by rw [hPcyl.w]
      _ = f ≫ (inX_P ≫ inP_S1) := by rw [Category.assoc]
  let psi21 : S2 ⟶ S1 := hS2.desc phiQ (inX_P ≫ inP_S1) hagree_psi21
  have hpsi21_inl : inQ_S2 ≫ psi21 = phiQ := hS2.inl_desc _ _ _
  have hpsi21_inr : inX_S2 ≫ psi21 = inX_P ≫ inP_S1 := hS2.inr_desc _ _ _

  -- Inverses: psi12 ≫ psi21 = 𝟙 S1
  have hinv1 : psi12 ≫ psi21 = 𝟙 S1 := by
    apply hS1.hom_ext
    · calc inB_S1 ≫ (psi12 ≫ psi21) = (inB_S1 ≫ psi12) ≫ psi21 := by rw [Category.assoc]
        _ = (inB_Q ≫ inQ_S2) ≫ psi21 := by rw [hpsi12_inB]
        _ = inB_Q ≫ (inQ_S2 ≫ psi21) := by rw [Category.assoc]
        _ = inB_Q ≫ phiQ := by rw [hpsi21_inl]
        _ = inB_S1 := hphiQ_inB
        _ = inB_S1 ≫ 𝟙 S1 := by rw [Category.comp_id]
    · apply hPcyl.hom_ext
      · calc inI_P ≫ inP_S1 ≫ (psi12 ≫ psi21)
            = inI_P ≫ (inP_S1 ≫ psi12) ≫ psi21 := by rw [Category.assoc inP_S1]
          _ = inI_P ≫ phiP ≫ psi21 := by rw [hpsi12_inP]
          _ = (inI_P ≫ phiP) ≫ psi21 := by rw [← Category.assoc]
          _ = (inI_Q ≫ inQ_S2) ≫ psi21 := by rw [hphiP_inI]
          _ = inI_Q ≫ (inQ_S2 ≫ psi21) := by rw [Category.assoc]
          _ = inI_Q ≫ phiQ := by rw [hpsi21_inl]
          _ = inI_P ≫ inP_S1 := hphiQ_inI
          _ = inI_P ≫ inP_S1 ≫ 𝟙 S1 := by rw [Category.comp_id]
      · calc inX_P ≫ inP_S1 ≫ (psi12 ≫ psi21)
            = inX_P ≫ (inP_S1 ≫ psi12) ≫ psi21 := by rw [Category.assoc inP_S1]
          _ = inX_P ≫ phiP ≫ psi21 := by rw [hpsi12_inP]
          _ = (inX_P ≫ phiP) ≫ psi21 := by rw [← Category.assoc]
          _ = inX_S2 ≫ psi21 := by rw [hphiP_inX]
          _ = inX_P ≫ inP_S1 := hpsi21_inr
          _ = inX_P ≫ inP_S1 ≫ 𝟙 S1 := by rw [Category.comp_id]

  -- Inverses: psi21 ≫ psi12 = 𝟙 S2
  have hinv2 : psi21 ≫ psi12 = 𝟙 S2 := by
    apply hS2.hom_ext
    · apply hQ.hom_ext
      · calc inI_Q ≫ inQ_S2 ≫ (psi21 ≫ psi12)
            = inI_Q ≫ (inQ_S2 ≫ psi21) ≫ psi12 := by rw [Category.assoc inQ_S2]
          _ = inI_Q ≫ phiQ ≫ psi12 := by rw [hpsi21_inl]
          _ = (inI_Q ≫ phiQ) ≫ psi12 := by rw [← Category.assoc]
          _ = (inI_P ≫ inP_S1) ≫ psi12 := by rw [hphiQ_inI]
          _ = inI_P ≫ (inP_S1 ≫ psi12) := by rw [Category.assoc]
          _ = inI_P ≫ phiP := by rw [hpsi12_inP]
          _ = inI_Q ≫ inQ_S2 := hphiP_inI
          _ = inI_Q ≫ inQ_S2 ≫ 𝟙 S2 := by rw [Category.comp_id]
      · calc inB_Q ≫ inQ_S2 ≫ (psi21 ≫ psi12)
            = inB_Q ≫ (inQ_S2 ≫ psi21) ≫ psi12 := by rw [Category.assoc inQ_S2]
          _ = inB_Q ≫ phiQ ≫ psi12 := by rw [hpsi21_inl]
          _ = (inB_Q ≫ phiQ) ≫ psi12 := by rw [← Category.assoc]
          _ = inB_S1 ≫ psi12 := by rw [hphiQ_inB]
          _ = inB_Q ≫ inQ_S2 := hpsi12_inB
          _ = inB_Q ≫ inQ_S2 ≫ 𝟙 S2 := by rw [Category.comp_id]
    · calc inX_S2 ≫ (psi21 ≫ psi12) = (inX_S2 ≫ psi21) ≫ psi12 := by rw [Category.assoc]
        _ = (inX_P ≫ inP_S1) ≫ psi12 := by rw [hpsi21_inr]
        _ = inX_P ≫ (inP_S1 ≫ psi12) := by rw [Category.assoc]
        _ = inX_P ≫ phiP := by rw [hpsi12_inP]
        _ = inX_S2 := hphiP_inX
        _ = inX_S2 ≫ 𝟙 S2 := by rw [Category.comp_id]

  let iso12 : S1 ≅ S2 := ⟨psi12, psi21, hinv1, hinv2⟩
  haveI : IsIso psi12 := Iso.isIso_hom iso12
  have hwe_psi12 : weakEquivalences C psi12 :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _
      (MorphismProperty.isomorphisms.infer_property psi12)

  let d : S2 ⟶ pushout i f := d_map.hom
  have hd_inl : inQ_S2 ≫ d = ρ ≫ pushout.inl i f := by
    show pushout.inl u f ≫ d_map.hom = ρ ≫ pushout.inl i f
    exact (IsPushout.of_hasPushout u f).inl_desc _ _ _

  have hk_factor : inB_S1 ≫ psi12 ≫ d ≫ e_BP.hom = k := by
    calc inB_S1 ≫ psi12 ≫ d ≫ e_BP.hom
        = (inB_S1 ≫ psi12) ≫ (d ≫ e_BP.hom) := by rw [← Category.assoc]
      _ = (inB_Q ≫ inQ_S2) ≫ (d ≫ e_BP.hom) := by rw [hpsi12_inB]
      _ = inB_Q ≫ (inQ_S2 ≫ (d ≫ e_BP.hom)) := by rw [Category.assoc]
      _ = inB_Q ≫ ((inQ_S2 ≫ d) ≫ e_BP.hom) := by rw [← Category.assoc inQ_S2 d e_BP.hom]
      _ = inB_Q ≫ ((ρ ≫ pushout.inl i f) ≫ e_BP.hom) := by rw [hd_inl]
      _ = inB_Q ≫ (ρ ≫ (pushout.inl i f ≫ e_BP.hom)) := by rw [Category.assoc ρ (pushout.inl i f) e_BP.hom]
      _ = (inB_Q ≫ ρ) ≫ (pushout.inl i f ≫ e_BP.hom) := by rw [← Category.assoc inB_Q ρ]
      _ = (𝟙 B) ≫ (pushout.inl i f ≫ e_BP.hom) := by rw [hρ_inB]
      _ = pushout.inl i f ≫ e_BP.hom := by rw [Category.id_comp]
      _ = k := he_BP_inl

  have hwe12 : weakEquivalences C (inB_S1 ≫ psi12) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe_inB_S1 hwe_psi12
  have hwe123 : weakEquivalences C ((inB_S1 ≫ psi12) ≫ d) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe12 hwe_d
  have hwe_all : weakEquivalences C (((inB_S1 ≫ psi12) ≫ d) ≫ e_BP.hom) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe123 hwe_e_BP
  have hk_eq : (((inB_S1 ≫ psi12) ≫ d) ≫ e_BP.hom) = k := by
    calc (((inB_S1 ≫ psi12) ≫ d) ≫ e_BP.hom)
        = (inB_S1 ≫ psi12) ≫ (d ≫ e_BP.hom) := by rw [Category.assoc]
      _ = inB_S1 ≫ psi12 ≫ d ≫ e_BP.hom := by rw [Category.assoc]
      _ = k := hk_factor
  rw [← hk_eq]
  exact hwe_all

#print axioms weakEquivalence_cobaseChange_proof

end HomotopyHypothesis.Cylinder.PreCylinderCategory
