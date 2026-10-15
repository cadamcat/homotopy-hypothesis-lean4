import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Brown
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Cor
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- Objects of the coslice `C(A)`: cofibrations out of `A` (H Cor 2.2.3, H:518). -/
structure UnderCof (A : C) where
  obj : C
  hom : A ⟶ obj
  cof : cofibrations C hom

variable {C} {A : C}

/-- Morphisms of `C(A)`: triangles under `A`. -/
structure UnderCofHom (X Y : UnderCof (C := C) A) where
  hom : X.obj ⟶ Y.obj
  w : X.hom ≫ hom = Y.hom

namespace UnderCof

instance : Category (UnderCof (C := C) A) where
  Hom X Y := UnderCofHom X Y
  id X := ⟨𝟙 X.obj, Category.comp_id _⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.w, g.w]⟩

@[simp]
theorem id_hom (X : UnderCof (C := C) A) : (𝟙 X : UnderCofHom X X).hom = 𝟙 X.obj :=
  rfl

@[simp]
theorem comp_hom {X Y Z : UnderCof (C := C) A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : UnderCofHom X Z).hom = f.hom ≫ g.hom :=
  rfl

/-- Equality of morphisms in `C(A)` follows from equality of underlying maps. -/
theorem hom_ext {X Y : UnderCof (C := C) A} {f g : UnderCofHom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f with
  | mk hom1 w1 =>
    cases g with
    | mk hom2 w2 =>
      simp only at h ⊢
      subst h
      rfl

/-- The forgetful functor `C(A) ⥤ C`. -/
@[simps]
def forget : UnderCof (C := C) A ⥤ C where
  obj X := X.obj
  map f := f.hom

instance : CategoryWithCofibrations (UnderCof (C := C) A) where
  cofibrations := fun _ _ f => cofibrations C f.hom

instance : CategoryWithWeakEquivalences (UnderCof (C := C) A) where
  weakEquivalences := fun _ _ f => weakEquivalences C f.hom

theorem cof_iff {X Y : UnderCof (C := C) A} (f : X ⟶ Y) :
    cofibrations (UnderCof (C := C) A) f ↔ cofibrations C f.hom :=
  Iff.rfl

theorem we_iff {X Y : UnderCof (C := C) A} (f : X ⟶ Y) :
    weakEquivalences (UnderCof (C := C) A) f ↔ weakEquivalences C f.hom :=
  Iff.rfl

/-- Isomorphisms in `C(A)` have underlying isomorphisms in `C`. -/
theorem isIso_hom_of_isIso {X Y : UnderCof (C := C) A} (f : X ⟶ Y) [IsIso f] :
    IsIso f.hom := by
  have hg1 : f ≫ inv f = 𝟙 X := IsIso.hom_inv_id f
  have hg2 : inv f ≫ f = 𝟙 Y := IsIso.inv_hom_id f
  have e1 : f.hom ≫ (inv f).hom = 𝟙 X.obj :=
    congrArg UnderCofHom.hom hg1
  have e2 : (inv f).hom ≫ f.hom = 𝟙 Y.obj :=
    congrArg UnderCofHom.hom hg2
  exact ⟨⟨(inv f).hom, e1, e2⟩⟩

variable [IsCylinderCategory C]

/-- The initial object of `C(A)`: `(A, 𝟙 A)`. -/
def initObj : UnderCof (C := C) A :=
  ⟨A, 𝟙 A, IsCofibrationCategory.isomorphisms_le _
    (MorphismProperty.isomorphisms.infer_property (f := 𝟙 A))⟩

def initObj_isInitial : IsInitial (initObj (C := C) (A := A)) := by
  apply IsInitial.ofUniqueHom
    (fun Y => UnderCofHom.mk Y.hom (by show (𝟙 A) ≫ Y.hom = Y.hom; rw [Category.id_comp]))
  intro Y m
  have h1 : (𝟙 A) ≫ m.hom = Y.hom := m.w
  have h2 : (𝟙 A) ≫ m.hom = m.hom := Category.id_comp _
  have hm : m.hom = Y.hom := h2.symm.trans h1
  have heq : (UnderCofHom.mk m.hom m.w : UnderCofHom _ _) = m := rfl
  rw [← heq]
  apply hom_ext
  exact hm

/-- Pushouts in `C(A)` from pushouts in `C`: given `i : X ⟶ Y` cof and `f : X ⟶ Z`,
the pushout in `C` with structure map via `Z` is a pushout in `C(A)`. -/
theorem pushout_isPushout {X Y Z : UnderCof (C := C) A} (i : X ⟶ Y) (f : X ⟶ Z)
    (hcof : cofibrations C i.hom) {P₀ : C} {inl : Y.obj ⟶ P₀} {inr : Z.obj ⟶ P₀}
    (hP : IsPushout i.hom f.hom inl inr) :
    ∃ (P : UnderCof (C := C) A) (k : Y ⟶ P) (j : Z ⟶ P),
      IsPushout i f k j := by
  classical
  have hcof_inr : cofibrations C inr := by
    exact (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hP.flip) (hf := hcof)
  have hcof_A : cofibrations C (Z.hom ≫ inr) :=
    IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ Z.cof hcof_inr
  have hY : Y.hom ≫ inl = Z.hom ≫ inr := by
    calc Y.hom ≫ inl
        = (X.hom ≫ i.hom) ≫ inl := by rw [i.w]
      _ = X.hom ≫ (i.hom ≫ inl) := by rw [← Category.assoc]
      _ = X.hom ≫ (f.hom ≫ inr) := by rw [hP.w]
      _ = (X.hom ≫ f.hom) ≫ inr := by rw [Category.assoc]
      _ = Z.hom ≫ inr := by rw [f.w]
  refine ⟨(⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A),
    UnderCofHom.mk (X := Y) (Y := ((⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A))) inl hY,
    UnderCofHom.mk (X := Z) (Y := ((⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A))) inr rfl,
    ?_⟩
  have hcomm : i ≫ UnderCofHom.mk (X := Y)
        (Y := ((⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A))) inl hY
      = f ≫ UnderCofHom.mk (X := Z)
        (Y := ((⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A))) inr
        (rfl : Z.hom ≫ inr
          = ((⟨P₀, Z.hom ≫ inr, hcof_A⟩ : UnderCof (C := C) A)).hom) := by
    apply hom_ext
    show i.hom ≫ inl = f.hom ≫ inr
    exact hP.w
  apply IsPushout.mk' hcomm
  · intro T φ φ' hφ hφ'
    apply hom_ext
    have e1 : inl ≫ φ.hom = inl ≫ φ'.hom := congrArg UnderCofHom.hom hφ
    have e2 : inr ≫ φ.hom = inr ≫ φ'.hom := congrArg UnderCofHom.hom hφ'
    exact hP.hom_ext e1 e2
  · intro T a b hab
    have habC : i.hom ≫ a.hom = f.hom ≫ b.hom :=
      congrArg UnderCofHom.hom hab
    obtain ⟨d, hd1, hd2⟩ := hP.exists_desc a.hom b.hom habC
    have hdT : (Z.hom ≫ inr) ≫ d = T.hom := by
      calc (Z.hom ≫ inr) ≫ d
          = Z.hom ≫ (inr ≫ d) := by rw [← Category.assoc]
        _ = Z.hom ≫ b.hom := by rw [hd2]
        _ = T.hom := b.w
    refine ⟨UnderCofHom.mk d hdT, ?_, ?_⟩
    · apply hom_ext
      show inl ≫ d = a.hom
      exact hd1
    · apply hom_ext
      show inr ≫ d = b.hom
      exact hd2

instance instCofCat : IsCofibrationCategory (UnderCof (C := C) A) where
  isomorphisms_le := by
    intro X Y f hf
    show cofibrations C f.hom
    haveI : IsIso f := hf
    have h : IsIso f.hom := isIso_hom_of_isIso (C := C) (A := A) f
    exact IsCofibrationCategory.isomorphisms_le (C := C) _ h
  isMultiplicative := by
    haveI := IsCofibrationCategory.isMultiplicative (C := C)
    exact inferInstanceAs (((cofibrations C).inverseImage (forget (C := C) (A := A))).IsMultiplicative)
  exists_initial := ⟨initObj, ⟨initObj_isInitial⟩⟩
  initial_cofibration := by
    intro I hI X
    show cofibrations C (hI.to X).hom
    let e : I ≅ initObj (C := C) (A := A) := hI.uniqueUpToIso initObj_isInitial
    have h_eq : hI.to X = e.hom ≫ (initObj_isInitial.to X) := hI.hom_ext _ _
    have h_eqC : (hI.to X).hom
        = e.hom.hom ≫ (initObj_isInitial.to X).hom :=
      congrArg UnderCofHom.hom h_eq
    have hcof_e : cofibrations C e.hom.hom := by
      haveI : IsIso e.hom := inferInstance
      have h := isIso_hom_of_isIso (C := C) (A := A) e.hom
      exact IsCofibrationCategory.isomorphisms_le (C := C) _ h
    have hcof_init : cofibrations C (initObj_isInitial.to X).hom := X.cof
    have hcomp : cofibrations C (e.hom.hom ≫ (initObj_isInitial.to X).hom) :=
      IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
        _ _ hcof_e hcof_init
    rw [← h_eqC] at hcomp
    exact hcomp
  hasPushout := by
    intro X Y Z i f hcof
    have hcofC : cofibrations C i.hom := hcof
    haveI : HasPushout i.hom f.hom :=
      IsCofibrationCategory.hasPushout _ _ hcofC
    obtain ⟨P, k, j, hpush⟩ := pushout_isPushout (C := C) (A := A) i f hcofC
      (IsPushout.of_hasPushout i.hom f.hom)
    exact ⟨⟨_, hpush.isColimit⟩⟩
  isStableUnderCobaseChange := by
    refine ⟨?_⟩
    intro A₀ A₁ B₀ P₀ f₀ g₀ f₁ g₁ sq hf
    show cofibrations C f₁.hom
    have hfC : cofibrations C f₀.hom := hf
    haveI : HasPushout f₀.hom g₀.hom :=
      IsCofibrationCategory.hasPushout _ _ hfC
    let Q₀ : C := pushout f₀.hom g₀.hom
    let inl₀ : A₁.obj ⟶ Q₀ := pushout.inl _ _
    let inr₀ : B₀.obj ⟶ Q₀ := pushout.inr _ _
    have hQ₀ : IsPushout f₀.hom g₀.hom inl₀ inr₀ :=
      IsPushout.of_hasPushout _ _
    have hcof_inr₀ : cofibrations C inr₀ :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
        (sq := hQ₀.flip) (hf := hfC)
    have hcof_A : cofibrations C (B₀.hom ≫ inr₀) :=
      IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
        _ _ B₀.cof hcof_inr₀
    have hY : A₁.hom ≫ inl₀ = B₀.hom ≫ inr₀ := by
      calc A₁.hom ≫ inl₀
          = (A₀.hom ≫ f₀.hom) ≫ inl₀ := by rw [f₀.w]
        _ = A₀.hom ≫ (f₀.hom ≫ inl₀) := by rw [← Category.assoc]
        _ = A₀.hom ≫ (g₀.hom ≫ inr₀) := by rw [hQ₀.w]
        _ = (A₀.hom ≫ g₀.hom) ≫ inr₀ := by rw [Category.assoc]
        _ = B₀.hom ≫ inr₀ := by rw [g₀.w]
    let P' : UnderCof (C := C) A :=
      ⟨Q₀, B₀.hom ≫ inr₀, hcof_A⟩
    let k' : A₁ ⟶ P' :=
      UnderCofHom.mk (X := A₁) (Y := P') inl₀ hY
    let j' : B₀ ⟶ P' :=
      UnderCofHom.mk (X := B₀) (Y := P') inr₀ rfl
    have hcomm' : f₀ ≫ k' = g₀ ≫ j' := by
      apply hom_ext
      show f₀.hom ≫ inl₀ = g₀.hom ≫ inr₀
      exact hQ₀.w
    have hpush' : IsPushout f₀ g₀ k' j' := by
      apply IsPushout.mk' hcomm'
      · intro T φ φ' hφ hφ'
        apply hom_ext
        have e1 : inl₀ ≫ φ.hom = inl₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ
        have e2 : inr₀ ≫ φ.hom = inr₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ'
        exact hQ₀.hom_ext e1 e2
      · intro T a b hab
        have habC : f₀.hom ≫ a.hom = g₀.hom ≫ b.hom :=
          congrArg UnderCofHom.hom hab
        obtain ⟨d, hd1, hd2⟩ := hQ₀.exists_desc a.hom b.hom habC
        have hdT : (B₀.hom ≫ inr₀) ≫ d = T.hom := by
          calc (B₀.hom ≫ inr₀) ≫ d
              = B₀.hom ≫ (inr₀ ≫ d) := by rw [← Category.assoc]
            _ = B₀.hom ≫ b.hom := by rw [hd2]
            _ = T.hom := b.w
        refine ⟨UnderCofHom.mk d hdT, ?_, ?_⟩
        · apply hom_ext
          show inl₀ ≫ d = a.hom
          exact hd1
        · apply hom_ext
          show inr₀ ≫ d = b.hom
          exact hd2
    have hpushFlip : IsPushout g₀ f₀ j' k' := hpush'.flip
    let e : P₀ ≅ P' := sq.isoIsPushout _ _ hpushFlip
    have heq : f₁ ≫ e.hom = j' := sq.inl_isoIsPushout_hom _ _ hpushFlip
    have heqC : f₁.hom ≫ e.hom.hom = j'.hom :=
      congrArg UnderCofHom.hom heq
    have hcof_j' : cofibrations C j'.hom := hcof_inr₀
    have hiso_e : IsIso e.hom.hom := isIso_hom_of_isIso (C := C) (A := A) e.hom
    have hcof_inv : cofibrations C (inv e.hom.hom) :=
      IsCofibrationCategory.isomorphisms_le (C := C) _
        (MorphismProperty.isomorphisms.infer_property (f := inv e.hom.hom))
    have h_eq : f₁.hom = j'.hom ≫ inv e.hom.hom := by
      calc f₁.hom
          = f₁.hom ≫ 𝟙 _ := by rw [Category.comp_id]
        _ = f₁.hom ≫ (e.hom.hom ≫ inv e.hom.hom) := by rw [IsIso.hom_inv_id]
        _ = (f₁.hom ≫ e.hom.hom) ≫ inv e.hom.hom := by rw [← Category.assoc]
        _ = j'.hom ≫ inv e.hom.hom := by rw [heqC]
    rw [h_eq]
    exact IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hcof_j' hcof_inv

instance instCylCat : IsCylinderCategory (UnderCof (C := C) A) where
  toIsCofibrationCategory := instCofCat
  isomorphisms_le_weakEquivalences := by
    intro X Y f hf
    show weakEquivalences C f.hom
    haveI : IsIso f := hf
    have h : IsIso f.hom := isIso_hom_of_isIso (C := C) (A := A) f
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) _ h
  weakEquivalences_isMultiplicative := by
    haveI := IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)
    exact inferInstanceAs (((weakEquivalences C).inverseImage (forget (C := C) (A := A))).IsMultiplicative)
  twoOutOfSix := by
    intro X Y Z T f g h hfg hgh
    show weakEquivalences C f.hom ∧ weakEquivalences C g.hom ∧
      weakEquivalences C h.hom ∧ weakEquivalences C (f ≫ g ≫ h).hom
    have hfgC : weakEquivalences C (f.hom ≫ g.hom) := hfg
    have hghC : weakEquivalences C (g.hom ≫ h.hom) := hgh
    have hcomp : (f ≫ g ≫ h).hom = f.hom ≫ g.hom ≫ h.hom := rfl
    have := IsCylinderCategory.twoOutOfSix (C := C) f.hom g.hom h.hom hfgC hghC
    exact ⟨this.1, this.2.1, this.2.2.1, by rw [hcomp]; exact this.2.2.2⟩
  trivialCofibration_cobaseChange := by
    intro A₀ B₀ X₀ P₀ i₀ f₀ k₀ j₀ sq hcof hwe
    show weakEquivalences C j₀.hom
    have hcofC : cofibrations C i₀.hom := hcof
    have hweC : weakEquivalences C i₀.hom := hwe
    haveI : HasPushout i₀.hom f₀.hom :=
      IsCofibrationCategory.hasPushout _ _ hcofC
    let Q₀ : C := pushout i₀.hom f₀.hom
    let inl₀ : B₀.obj ⟶ Q₀ := pushout.inl _ _
    let inr₀ : X₀.obj ⟶ Q₀ := pushout.inr _ _
    have hQ₀ : IsPushout i₀.hom f₀.hom inl₀ inr₀ :=
      IsPushout.of_hasPushout _ _
    have hwe_inr₀ : weakEquivalences C inr₀ :=
      IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
        i₀.hom f₀.hom inl₀ inr₀ hQ₀ hcofC hweC
    have hcof_inr₀ : cofibrations C inr₀ :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
        (sq := hQ₀.flip) (hf := hcofC)
    have hcof_A : cofibrations C (X₀.hom ≫ inr₀) :=
      IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
        _ _ X₀.cof hcof_inr₀
    have hY : B₀.hom ≫ inl₀ = X₀.hom ≫ inr₀ := by
      calc B₀.hom ≫ inl₀
          = (A₀.hom ≫ i₀.hom) ≫ inl₀ := by rw [i₀.w]
        _ = A₀.hom ≫ (i₀.hom ≫ inl₀) := by rw [← Category.assoc]
        _ = A₀.hom ≫ (f₀.hom ≫ inr₀) := by rw [hQ₀.w]
        _ = (A₀.hom ≫ f₀.hom) ≫ inr₀ := by rw [Category.assoc]
        _ = X₀.hom ≫ inr₀ := by rw [f₀.w]
    let P' : UnderCof (C := C) A :=
      ⟨Q₀, X₀.hom ≫ inr₀, hcof_A⟩
    let k' : B₀ ⟶ P' :=
      UnderCofHom.mk (X := B₀) (Y := P') inl₀ hY
    let j' : X₀ ⟶ P' :=
      UnderCofHom.mk (X := X₀) (Y := P') inr₀ rfl
    have hcomm' : i₀ ≫ k' = f₀ ≫ j' := by
      apply hom_ext
      show i₀.hom ≫ inl₀ = f₀.hom ≫ inr₀
      exact hQ₀.w
    have hpush' : IsPushout i₀ f₀ k' j' := by
      apply IsPushout.mk' hcomm'
      · intro T φ φ' hφ hφ'
        apply hom_ext
        have e1 : inl₀ ≫ φ.hom = inl₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ
        have e2 : inr₀ ≫ φ.hom = inr₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ'
        exact hQ₀.hom_ext e1 e2
      · intro T a b hab
        have habC : i₀.hom ≫ a.hom = f₀.hom ≫ b.hom :=
          congrArg UnderCofHom.hom hab
        obtain ⟨d, hd1, hd2⟩ := hQ₀.exists_desc a.hom b.hom habC
        have hdT : (X₀.hom ≫ inr₀) ≫ d = T.hom := by
          calc (X₀.hom ≫ inr₀) ≫ d
              = X₀.hom ≫ (inr₀ ≫ d) := by rw [← Category.assoc]
            _ = X₀.hom ≫ b.hom := by rw [hd2]
            _ = T.hom := b.w
        refine ⟨UnderCofHom.mk d hdT, ?_, ?_⟩
        · apply hom_ext
          show inl₀ ≫ d = a.hom
          exact hd1
        · apply hom_ext
          show inr₀ ≫ d = b.hom
          exact hd2
    let e : P₀ ≅ P' := sq.isoIsPushout _ _ hpush'
    have heq : j₀ ≫ e.hom = j' := sq.inr_isoIsPushout_hom _ _ hpush'
    have heqC : j₀.hom ≫ e.hom.hom = j'.hom :=
      congrArg UnderCofHom.hom heq
    have hwe_j' : weakEquivalences C j'.hom := hwe_inr₀
    have hiso_e : IsIso e.hom.hom := isIso_hom_of_isIso (C := C) (A := A) e.hom
    haveI := we_twoOutOfThree (C := C)
    have hwe_iso : weakEquivalences C e.hom.hom :=
      IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) _ hiso_e
    have hfg : weakEquivalences C (j₀.hom ≫ e.hom.hom) := by
      rw [heqC]
      exact hwe_j'
    have hwe_j₀ : weakEquivalences C j₀.hom :=
      MorphismProperty.of_postcomp (weakEquivalences C) _ _ hwe_iso hfg
    exact hwe_j₀
  exists_cylinder := by
    intro I hI X
    let i : I ⟶ X := hI.to X
    have hcof_i : cofibrations C i.hom := instCofCat.initial_cofibration hI X
    haveI : HasPushout i.hom i.hom :=
      IsCofibrationCategory.hasPushout _ _ hcof_i
    let P₀ : C := pushout i.hom i.hom
    let inl₀ : X.obj ⟶ P₀ := pushout.inl _ _
    let inr₀ : X.obj ⟶ P₀ := pushout.inr _ _
    have hP₀ : IsPushout i.hom i.hom inl₀ inr₀ :=
      IsPushout.of_hasPushout _ _
    have hcof_inl₀ : cofibrations C inl₀ :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
        (sq := hP₀) (hf := hcof_i)
    have hcof_inr₀ : cofibrations C inr₀ :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
        (sq := hP₀.flip) (hf := hcof_i)
    have hcof_P : cofibrations C (X.hom ≫ inr₀) :=
      IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
        _ _ X.cof hcof_inr₀
    have hY : X.hom ≫ inl₀ = X.hom ≫ inr₀ := by
      calc X.hom ≫ inl₀
          = (I.hom ≫ i.hom) ≫ inl₀ := by rw [i.w]
        _ = I.hom ≫ (i.hom ≫ inl₀) := by rw [← Category.assoc]
        _ = I.hom ≫ (i.hom ≫ inr₀) := by rw [hP₀.w]
        _ = (I.hom ≫ i.hom) ≫ inr₀ := by rw [Category.assoc]
        _ = X.hom ≫ inr₀ := by rw [i.w]
    let δ : P₀ ⟶ X.obj := hP₀.desc (𝟙 X.obj) (𝟙 X.obj) rfl
    have hδl : inl₀ ≫ δ = 𝟙 X.obj := hP₀.inl_desc _ _ _
    have hδr : inr₀ ≫ δ = 𝟙 X.obj := hP₀.inr_desc _ _ _
    let P : UnderCof (C := C) A :=
      ⟨P₀, X.hom ≫ inr₀, hcof_P⟩
    let j₀ : X ⟶ P :=
      UnderCofHom.mk (X := X) (Y := P) inl₀ hY
    let j₁ : X ⟶ P :=
      UnderCofHom.mk (X := X) (Y := P) inr₀ rfl
    have hcomm : i ≫ j₀ = i ≫ j₁ := by
      apply hom_ext
      show i.hom ≫ inl₀ = i.hom ≫ inr₀
      exact hP₀.w
    have hpush : IsPushout i i j₀ j₁ := by
      apply IsPushout.mk' hcomm
      · intro T φ φ' hφ hφ'
        apply hom_ext
        have e1 : inl₀ ≫ φ.hom = inl₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ
        have e2 : inr₀ ≫ φ.hom = inr₀ ≫ φ'.hom := congrArg UnderCofHom.hom hφ'
        exact hP₀.hom_ext e1 e2
      · intro T a b hab
        have habC : i.hom ≫ a.hom = i.hom ≫ b.hom :=
          congrArg UnderCofHom.hom hab
        obtain ⟨d, hd1, hd2⟩ := hP₀.exists_desc a.hom b.hom habC
        have hdT : (X.hom ≫ inr₀) ≫ d = T.hom := by
          calc (X.hom ≫ inr₀) ≫ d
              = X.hom ≫ (inr₀ ≫ d) := by rw [← Category.assoc]
            _ = X.hom ≫ b.hom := by rw [hd2]
            _ = T.hom := b.w
        refine ⟨UnderCofHom.mk d hdT, ?_, ?_⟩
        · apply hom_ext
          show inl₀ ≫ d = a.hom
          exact hd1
        · apply hom_ext
          show inr₀ ≫ d = b.hom
          exact hd2
    obtain ⟨bf⟩ := brown_factorization (C := C) δ
    have hcof_Q : cofibrations C (P.hom ≫ bf.i) :=
      IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
        _ _ P.cof bf.cof_i
    let Q : UnderCof (C := C) A :=
      ⟨bf.P, P.hom ≫ bf.i, hcof_Q⟩
    let cc : P ⟶ Q :=
      UnderCofHom.mk (X := P) (Y := Q) bf.i rfl
    have hpT : (P.hom ≫ bf.i) ≫ bf.p = X.hom := by
      calc (P.hom ≫ bf.i) ≫ bf.p
          = P.hom ≫ (bf.i ≫ bf.p) := by rw [← Category.assoc]
        _ = P.hom ≫ δ := by rw [bf.fac]
        _ = (X.hom ≫ inr₀) ≫ δ := rfl
        _ = X.hom ≫ (inr₀ ≫ δ) := by rw [← Category.assoc]
        _ = X.hom ≫ 𝟙 X.obj := by rw [hδr]
        _ = X.hom := by rw [Category.comp_id]
    let pp : Q ⟶ X :=
      UnderCofHom.mk (X := Q) (Y := X) bf.p hpT
    have hc_mem : cofibrations (UnderCof (C := C) A) cc := bf.cof_i
    have hp_mem : weakEquivalences (UnderCof (C := C) A) pp := bf.we_p
    have hj0 : j₀ ≫ cc ≫ pp = 𝟙 X := by
      apply hom_ext
      show inl₀ ≫ bf.i ≫ bf.p = 𝟙 X.obj
      calc inl₀ ≫ bf.i ≫ bf.p
          = inl₀ ≫ (bf.i ≫ bf.p) := by rw [← Category.assoc]
        _ = inl₀ ≫ δ := by rw [bf.fac]
        _ = 𝟙 X.obj := hδl
    have hj1 : j₁ ≫ cc ≫ pp = 𝟙 X := by
      apply hom_ext
      show inr₀ ≫ bf.i ≫ bf.p = 𝟙 X.obj
      calc inr₀ ≫ bf.i ≫ bf.p
          = inr₀ ≫ (bf.i ≫ bf.p) := by rw [← Category.assoc]
        _ = inr₀ ≫ δ := by rw [bf.fac]
        _ = 𝟙 X.obj := hδr
    exact ⟨P, j₀, j₁, hpush, Q, cc, pp, hc_mem, hp_mem, hj0, hj1⟩
  exists_retraction := by
    intro X Y i hcof hwe
    show ∃ r : Y ⟶ X, i ≫ r = 𝟙 X
    have hcofC : cofibrations C i.hom := hcof
    have hweC : weakEquivalences C i.hom := hwe
    obtain ⟨r₀, hr₀⟩ := IsCylinderCategory.exists_retraction (C := C) i.hom hcofC hweC
    have hrT : Y.hom ≫ r₀ = X.hom := by
      calc Y.hom ≫ r₀
          = (X.hom ≫ i.hom) ≫ r₀ := by rw [i.w]
        _ = X.hom ≫ (i.hom ≫ r₀) := by rw [← Category.assoc]
        _ = X.hom ≫ 𝟙 X.obj := by rw [hr₀]
        _ = X.hom := by rw [Category.comp_id]
    refine ⟨UnderCofHom.mk r₀ hrT, ?_⟩
    apply hom_ext
    show i.hom ≫ r₀ = 𝟙 X.obj
    exact hr₀

end UnderCof

end HomotopyHypothesis.Cylinder.PreCylinderCategory
