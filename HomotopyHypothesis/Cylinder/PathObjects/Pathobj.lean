import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part1
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicTwoOutOfSix
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsPreCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.RelHomotopicEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceCobaseChange
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Cylinder.PathObjects

universe u v

open HomotopyHypothesis.Henry

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [hC : IsCylinderCategory C]

private theorem isPushout_prod
    {A₁ B₁ X₁ P₁ A₂ B₂ X₂ P₂ : C}
    {f₁ : A₁ ⟶ B₁} {g₁ : A₁ ⟶ X₁} {k₁ : B₁ ⟶ P₁} {j₁ : X₁ ⟶ P₁}
    {f₂ : A₂ ⟶ B₂} {g₂ : A₂ ⟶ X₂} {k₂ : B₂ ⟶ P₂} {j₂ : X₂ ⟶ P₂}
    (h₁ : IsPushout f₁ g₁ k₁ j₁) (h₂ : IsPushout f₂ g₂ k₂ j₂) :
    IsPushout (C := C × C) ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
      ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂))
      ((k₁, k₂) : (B₁, B₂) ⟶ (P₁, P₂))
      ((j₁, j₂) : (X₁, X₂) ⟶ (P₁, P₂)) := by
  apply IsPushout.mk'
  · ext
    · exact h₁.w
    · exact h₂.w
  · intro T φ ψ hφ hψ
    apply Prod.ext
    · have hφ₁ : k₁ ≫ φ.1 = k₁ ≫ ψ.1 := by
        simpa using congrArg (fun m => m.1) hφ
      have hψ₁ : j₁ ≫ φ.1 = j₁ ≫ ψ.1 := by
        simpa using congrArg (fun m => m.1) hψ
      exact PushoutCocone.IsColimit.hom_ext h₁.isColimit hφ₁ hψ₁
    · have hφ₂ : k₂ ≫ φ.2 = k₂ ≫ ψ.2 := by
        simpa using congrArg (fun m => m.2) hφ
      have hψ₂ : j₂ ≫ φ.2 = j₂ ≫ ψ.2 := by
        simpa using congrArg (fun m => m.2) hψ
      exact PushoutCocone.IsColimit.hom_ext h₂.isColimit hφ₂ hψ₂
  · intro T a b hab
    have hab₁ : f₁ ≫ a.1 = g₁ ≫ b.1 := by
      simpa using congrArg (fun m => m.1) hab
    have hab₂ : f₂ ≫ a.2 = g₂ ≫ b.2 := by
      simpa using congrArg (fun m => m.2) hab
    let c₁ : PushoutCocone f₁ g₁ := PushoutCocone.mk a.1 b.1 hab₁
    let c₂ : PushoutCocone f₂ g₂ := PushoutCocone.mk a.2 b.2 hab₂
    let m : (P₁, P₂) ⟶ T := (h₁.isColimit.desc c₁, h₂.isColimit.desc c₂)
    refine ⟨m, ?_, ?_⟩
    · change (k₁, k₂) ≫ m = a
      apply Prod.ext
      · exact h₁.isColimit.fac c₁ WalkingSpan.left
      · exact h₂.isColimit.fac c₂ WalkingSpan.left
    · change (j₁, j₂) ≫ m = b
      apply Prod.ext
      · exact h₁.isColimit.fac c₁ WalkingSpan.right
      · exact h₂.isColimit.fac c₂ WalkingSpan.right

private theorem hasPushout_prod
    {A₁ B₁ X₁ A₂ B₂ X₂ : C}
    (f₁ : A₁ ⟶ B₁) (g₁ : A₁ ⟶ X₁) (f₂ : A₂ ⟶ B₂) (g₂ : A₂ ⟶ X₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    HasPushout (C := C × C) ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
      ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂)) :=
  (isPushout_prod (IsPushout.of_hasPushout f₁ g₁) (IsPushout.of_hasPushout f₂ g₂)).hasPushout

private theorem isPushout_prod_fst
    {A₁ B₁ X₁ P₁ A₂ B₂ X₂ P₂ : C}
    {f₁ : A₁ ⟶ B₁} {g₁ : A₁ ⟶ X₁} {k₁ : B₁ ⟶ P₁} {j₁ : X₁ ⟶ P₁}
    {f₂ : A₂ ⟶ B₂} {g₂ : A₂ ⟶ X₂} {k₂ : B₂ ⟶ P₂} {j₂ : X₂ ⟶ P₂}
    (h : IsPushout (C := C × C) ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
      ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂))
      ((k₁, k₂) : (B₁, B₂) ⟶ (P₁, P₂))
      ((j₁, j₂) : (X₁, X₂) ⟶ (P₁, P₂)))
    [HasPushout f₂ g₂] : IsPushout f₁ g₁ k₁ j₁ := by
  apply IsPushout.mk'
  · simpa using congrArg (fun m => m.1) h.w
  · intro T φ ψ hφ hψ
    let c : PushoutCocone (C := C × C)
        ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
        ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂)) :=
      PushoutCocone.mk
        ((k₁ ≫ φ, pushout.inl f₂ g₂) : (B₁, B₂) ⟶ (T, pushout f₂ g₂))
        ((j₁ ≫ φ, pushout.inr f₂ g₂) : (X₁, X₂) ⟶ (T, pushout f₂ g₂))
        (by
          ext
          · simpa [Category.assoc] using congrArg (fun m => m ≫ φ)
              (show f₁ ≫ k₁ = g₁ ≫ j₁ from by
                simpa using congrArg (fun m => m.1) h.w)
          · exact pushout.condition)
    let m : h.cocone.pt ⟶ (T, pushout f₂ g₂) := h.isColimit.desc c
    let mφ : h.cocone.pt ⟶ (T, pushout f₂ g₂) := (φ, m.2)
    let mψ : h.cocone.pt ⟶ (T, pushout f₂ g₂) := (ψ, m.2)
    have hm : mφ = mψ := by
      have hlin : h.cocone.inl ≫ mφ = h.cocone.inl ≫ mψ := by
        change ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ mφ =
          ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ mψ
        exact Prod.ext hφ rfl
      have hrin : h.cocone.inr ≫ mφ = h.cocone.inr ≫ mψ := by
        change ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ mφ =
          ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ mψ
        exact Prod.ext hψ rfl
      exact PushoutCocone.IsColimit.hom_ext h.isColimit hlin hrin
    exact congrArg (fun n => n.1) hm
  · intro T a b hab
    let c : PushoutCocone (C := C × C)
        ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
        ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂)) :=
      PushoutCocone.mk
        ((a, pushout.inl f₂ g₂) : (B₁, B₂) ⟶ (T, pushout f₂ g₂))
        ((b, pushout.inr f₂ g₂) : (X₁, X₂) ⟶ (T, pushout f₂ g₂))
        (by
          ext
          · exact hab
          · exact pushout.condition)
    let m : h.cocone.pt ⟶ (T, pushout f₂ g₂) := h.isColimit.desc c
    refine ⟨m.1, ?_, ?_⟩
    · have hm := h.isColimit.fac c WalkingSpan.left
      change ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ m =
        ((a, pushout.inl f₂ g₂) : (B₁, B₂) ⟶ (T, pushout f₂ g₂)) at hm
      exact congrArg (fun n => n.1) hm
    · have hm := h.isColimit.fac c WalkingSpan.right
      change ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ m =
        ((b, pushout.inr f₂ g₂) : (X₁, X₂) ⟶ (T, pushout f₂ g₂)) at hm
      exact congrArg (fun n => n.1) hm

private theorem isPushout_prod_snd
    {A₁ B₁ X₁ P₁ A₂ B₂ X₂ P₂ : C}
    {f₁ : A₁ ⟶ B₁} {g₁ : A₁ ⟶ X₁} {k₁ : B₁ ⟶ P₁} {j₁ : X₁ ⟶ P₁}
    {f₂ : A₂ ⟶ B₂} {g₂ : A₂ ⟶ X₂} {k₂ : B₂ ⟶ P₂} {j₂ : X₂ ⟶ P₂}
    (h : IsPushout (C := C × C) ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
      ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂))
      ((k₁, k₂) : (B₁, B₂) ⟶ (P₁, P₂))
      ((j₁, j₂) : (X₁, X₂) ⟶ (P₁, P₂)))
    [HasPushout f₁ g₁] : IsPushout f₂ g₂ k₂ j₂ := by
  apply IsPushout.mk'
  · simpa using congrArg (fun m => m.2) h.w
  · intro T φ ψ hφ hψ
    let c : PushoutCocone (C := C × C)
        ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
        ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂)) :=
      PushoutCocone.mk
        ((pushout.inl f₁ g₁, k₂ ≫ φ) : (B₁, B₂) ⟶ (pushout f₁ g₁, T))
        ((pushout.inr f₁ g₁, j₂ ≫ φ) : (X₁, X₂) ⟶ (pushout f₁ g₁, T))
        (by
          ext
          · exact pushout.condition
          · simpa [Category.assoc] using congrArg (fun m => m ≫ φ)
              (show f₂ ≫ k₂ = g₂ ≫ j₂ from by
                simpa using congrArg (fun m => m.2) h.w))
    let m : h.cocone.pt ⟶ (pushout f₁ g₁, T) := h.isColimit.desc c
    let mφ : h.cocone.pt ⟶ (pushout f₁ g₁, T) := (m.1, φ)
    let mψ : h.cocone.pt ⟶ (pushout f₁ g₁, T) := (m.1, ψ)
    have hm : mφ = mψ := by
      have hlin : h.cocone.inl ≫ mφ = h.cocone.inl ≫ mψ := by
        change ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ mφ =
          ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ mψ
        exact Prod.ext rfl hφ
      have hrin : h.cocone.inr ≫ mφ = h.cocone.inr ≫ mψ := by
        change ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ mφ =
          ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ mψ
        exact Prod.ext rfl hψ
      exact PushoutCocone.IsColimit.hom_ext h.isColimit hlin hrin
    exact congrArg (fun n => n.2) hm
  · intro T a b hab
    let c : PushoutCocone (C := C × C)
        ((f₁, f₂) : (A₁, A₂) ⟶ (B₁, B₂))
        ((g₁, g₂) : (A₁, A₂) ⟶ (X₁, X₂)) :=
      PushoutCocone.mk
        ((pushout.inl f₁ g₁, a) : (B₁, B₂) ⟶ (pushout f₁ g₁, T))
        ((pushout.inr f₁ g₁, b) : (X₁, X₂) ⟶ (pushout f₁ g₁, T))
        (by
          ext
          · exact pushout.condition
          · exact hab)
    let m : h.cocone.pt ⟶ (pushout f₁ g₁, T) := h.isColimit.desc c
    refine ⟨m.2, ?_, ?_⟩
    · have hm := h.isColimit.fac c WalkingSpan.left
      change ((k₁, k₂) : (B₁, B₂) ⟶ h.cocone.pt) ≫ m =
        ((pushout.inl f₁ g₁, a) : (B₁, B₂) ⟶ (pushout f₁ g₁, T)) at hm
      exact congrArg (fun n => n.2) hm
    · have hm := h.isColimit.fac c WalkingSpan.right
      change ((j₁, j₂) : (X₁, X₂) ⟶ h.cocone.pt) ≫ m =
        ((pushout.inr f₁ g₁, b) : (X₁, X₂) ⟶ (pushout f₁ g₁, T)) at hm
      exact congrArg (fun n => n.2) hm

private def prod_isInitial {I₁ I₂ : C} (h₁ : IsInitial I₁) (h₂ : IsInitial I₂) :
    IsInitial (I₁, I₂) := by
  refine IsInitial.ofUniqueHom (fun X => (h₁.to X.1, h₂.to X.2)) ?_
  intro X f
  apply Prod.ext
  · exact h₁.hom_ext f.1 (h₁.to X.1)
  · exact h₂.hom_ext f.2 (h₂.to X.2)

private def isInitial_fst_of_prod {I₁ I₂ : C} (h : IsInitial (I₁, I₂)) :
    IsInitial I₁ := by
  refine IsInitial.ofUniqueHom (fun X => (h.to (X, I₂)).1) ?_
  intro X f
  let f' : (I₁, I₂) ⟶ (X, I₂) := (f, 𝟙 I₂)
  let g' : (I₁, I₂) ⟶ (X, I₂) := h.to (X, I₂)
  have heq : f' = g' := IsInitial.hom_ext h f' g'
  exact congrArg (fun m => m.1) heq

private def isInitial_snd_of_prod {I₁ I₂ : C} (h : IsInitial (I₁, I₂)) :
    IsInitial I₂ := by
  refine IsInitial.ofUniqueHom (fun X => (h.to (I₁, X)).2) ?_
  intro X f
  let f' : (I₁, I₂) ⟶ (I₁, X) := (𝟙 I₁, f)
  let g' : (I₁, I₂) ⟶ (I₁, X) := h.to (I₁, X)
  have heq : f' = g' := IsInitial.hom_ext h f' g'
  exact congrArg (fun m => m.2) heq

private theorem prod_isCylinderCategory : IsCylinderCategory (C × C) := by
  classical
  letI : CategoryWithCofibrations (C × C) := inferInstance
  letI : CategoryWithWeakEquivalences (C × C) := inferInstance
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  have hII : IsInitial (I, I) := prod_isInitial hI hI
  refine
    { toIsCofibrationCategory := ?_
      isomorphisms_le_weakEquivalences := ?_
      weakEquivalences_isMultiplicative := ?_
      twoOutOfSix := ?_
      trivialCofibration_cobaseChange := ?_
      exists_cylinder := ?_
      exists_retraction := ?_ }
  · refine
      { isomorphisms_le := ?_
        isMultiplicative := ?_
        exists_initial := ⟨(I, I), ⟨hII⟩⟩
        initial_cofibration := ?_
        hasPushout := ?_
        isStableUnderCobaseChange := ?_ }
    · intro X Y f hf
      change IsIso f at hf
      letI : IsIso f := hf
      change cofibrations C f.1 ∧ cofibrations C f.2
      constructor
      · apply hC.toIsCofibrationCategory.isomorphisms_le
        exact Functor.map_isIso (CategoryTheory.Prod.fst C C) f
      · apply hC.toIsCofibrationCategory.isomorphisms_le
        exact Functor.map_isIso (CategoryTheory.Prod.snd C C) f
    · refine
        { id_mem := ?_
          comp_mem := ?_ }
      · intro X
        change cofibrations C (𝟙 X.1) ∧ cofibrations C (𝟙 X.2)
        exact ⟨hC.toIsCofibrationCategory.isMultiplicative.id_mem X.1,
          hC.toIsCofibrationCategory.isMultiplicative.id_mem X.2⟩
      · intro X Y Z f g hf hg
        change cofibrations C f.1 ∧ cofibrations C f.2 at hf
        change cofibrations C g.1 ∧ cofibrations C g.2 at hg
        change cofibrations C (f.1 ≫ g.1) ∧ cofibrations C (f.2 ≫ g.2)
        exact ⟨hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hf.1 hg.1,
          hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hf.2 hg.2⟩
    · intro I' hI' X
      change cofibrations C ((hI'.to X).1) ∧ cofibrations C ((hI'.to X).2)
      have hI₁ := isInitial_fst_of_prod hI'
      have hI₂ := isInitial_snd_of_prod hI'
      have e₁ : hI₁.to X.1 = (hI'.to X).1 := hI₁.hom_ext _ _
      have e₂ : hI₂.to X.2 = (hI'.to X).2 := hI₂.hom_ext _ _
      have h₁ := hC.initial_cofibration hI₁ X.1
      have h₂ := hC.initial_cofibration hI₂ X.2
      exact ⟨by rw [← e₁]; exact h₁, by rw [← e₂]; exact h₂⟩
    · intro A B X i f hi
      change cofibrations C i.1 ∧ cofibrations C i.2 at hi
      letI : HasPushout i.1 f.1 := hC.hasPushout i.1 f.1 hi.1
      letI : HasPushout i.2 f.2 := hC.hasPushout i.2 f.2 hi.2
      exact hasPushout_prod i.1 f.1 i.2 f.2
    · refine ⟨?_⟩
      intro A A' B B' f g f' g' sq hf
      change cofibrations C f.1 ∧ cofibrations C f.2 at hf
      letI : HasPushout f.1 g.1 := hC.hasPushout f.1 g.1 hf.1
      letI : HasPushout f.2 g.2 := hC.hasPushout f.2 g.2 hf.2
      letI : HasPushout g.1 f.1 := (IsPushout.of_hasPushout f.1 g.1).flip.hasPushout
      letI : HasPushout g.2 f.2 := (IsPushout.of_hasPushout f.2 g.2).flip.hasPushout
      have hfst : IsPushout g.1 f.1 f'.1 g'.1 := isPushout_prod_fst sq
      have hsnd : IsPushout g.2 f.2 f'.2 g'.2 := isPushout_prod_snd sq
      exact ⟨hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hfst hf.1,
        hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hsnd hf.2⟩
  · intro X Y f hf
    change IsIso f at hf
    letI : IsIso f := hf
    have hf₁ : IsIso f.1 := Functor.map_isIso (CategoryTheory.Prod.fst C C) f
    have hf₂ : IsIso f.2 := Functor.map_isIso (CategoryTheory.Prod.snd C C) f
    change weakEquivalences C f.1 ∧ weakEquivalences C f.2
    exact ⟨hC.isomorphisms_le_weakEquivalences f.1 hf₁,
      hC.isomorphisms_le_weakEquivalences f.2 hf₂⟩
  · refine
      { id_mem := ?_
        comp_mem := ?_ }
    · intro X
      change weakEquivalences C (𝟙 X.1) ∧ weakEquivalences C (𝟙 X.2)
      exact ⟨hC.weakEquivalences_isMultiplicative.id_mem X.1,
        hC.weakEquivalences_isMultiplicative.id_mem X.2⟩
    · intro X Y Z f g hf hg
      change weakEquivalences C f.1 ∧ weakEquivalences C f.2 at hf
      change weakEquivalences C g.1 ∧ weakEquivalences C g.2 at hg
      change weakEquivalences C (f.1 ≫ g.1) ∧ weakEquivalences C (f.2 ≫ g.2)
      exact ⟨hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf.1 hg.1,
        hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf.2 hg.2⟩
  · intro X Y Z T f g k hf hg
    change weakEquivalences C (f.1 ≫ g.1) ∧ weakEquivalences C (f.2 ≫ g.2) at hf
    change weakEquivalences C (g.1 ≫ k.1) ∧ weakEquivalences C (g.2 ≫ k.2) at hg
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hC.twoOutOfSix f.1 g.1 k.1 hf.1 hg.1
    obtain ⟨h₁', h₂', h₃', h₄'⟩ := hC.twoOutOfSix f.2 g.2 k.2 hf.2 hg.2
    exact ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩, ⟨h₃, h₃'⟩, ⟨h₄, h₄'⟩⟩
  · intro A B X P i f k j h hi hwi
    change cofibrations C i.1 ∧ cofibrations C i.2 at hi
    change weakEquivalences C i.1 ∧ weakEquivalences C i.2 at hwi
    letI : HasPushout i.1 f.1 := hC.hasPushout i.1 f.1 hi.1
    letI : HasPushout i.2 f.2 := hC.hasPushout i.2 f.2 hi.2
    have hfst : IsPushout i.1 f.1 k.1 j.1 := isPushout_prod_fst h
    have hsnd : IsPushout i.2 f.2 k.2 j.2 := isPushout_prod_snd h
    exact ⟨hC.trivialCofibration_cobaseChange i.1 f.1 k.1 j.1 hfst hi.1 hwi.1,
      hC.trivialCofibration_cobaseChange i.2 f.2 k.2 j.2 hsnd hi.2 hwi.2⟩
  · intro I' hI' X
    have hI₁ := isInitial_fst_of_prod hI'
    have hI₂ := isInitial_snd_of_prod hI'
    have hsrc₁ : hI₁.to X.1 = (hI'.to X).1 := hI₁.hom_ext _ _
    have hsrc₂ : hI₂.to X.2 = (hI'.to X).2 := hI₂.hom_ext _ _
    obtain ⟨cyl₁⟩ := hC.exists_cylinder hI₁ X.1
    obtain ⟨cyl₂⟩ := hC.exists_cylinder hI₂ X.2
    have h₁ : RelativeCylinder ((hI'.to X).1) := by simpa [hsrc₁] using cyl₁
    have h₂ : RelativeCylinder ((hI'.to X).2) := by simpa [hsrc₂] using cyl₂
    exact ⟨⟨(h₁.P, h₂.P), (h₁.j₀, h₂.j₀), (h₁.j₁, h₂.j₁),
      isPushout_prod h₁.isPushout h₂.isPushout, (h₁.I, h₂.I), (h₁.c, h₂.c),
      (h₁.p, h₂.p), ⟨h₁.c_mem, h₂.c_mem⟩, ⟨h₁.p_mem, h₂.p_mem⟩,
      by
        ext
        · exact h₁.j₀_c_p
        · exact h₂.j₀_c_p,
      by
        ext
        · exact h₁.j₁_c_p
        · exact h₂.j₁_c_p⟩⟩
  · intro A B i hi hwi
    change cofibrations C i.1 ∧ cofibrations C i.2 at hi
    change weakEquivalences C i.1 ∧ weakEquivalences C i.2 at hwi
    obtain ⟨r₁, hr₁⟩ := hC.exists_retraction i.1 hi.1 hwi.1
    obtain ⟨r₂, hr₂⟩ := hC.exists_retraction i.2 hi.2 hwi.2
    refine ⟨(r₁, r₂), ?_⟩
    ext
    · exact hr₁
    · exact hr₂

private theorem cofibrantGluing_changeInitial {I J B X T : C}
    (hI : IsInitial I) (hJ : IsInitial J) {u : B ⟶ T} {w : X ⟶ T}
    (h : IsCofibrantGluing (hJ.to B) (hJ.to X) u w) :
    IsCofibrantGluing (hI.to B) (hI.to X) u w := by
  classical
  obtain ⟨P, k, j, hP, m, hkm, hjm, hcof⟩ := h
  let e : I ≅ J := hI.uniqueUpToIso hJ
  have hP' : IsPushout (hI.to B) (hI.to X) k j :=
    hP.of_iso' e (Iso.refl B) (Iso.refl X) (Iso.refl P)
      (by exact hI.hom_ext _ _) (by exact hI.hom_ext _ _) (by simp) (by simp)
  exact ⟨P, k, j, hP', m, hkm, hjm, hcof⟩

private noncomputable def pathInitialObject {I : C} (hI : IsInitial I) : PathObj C := by
  classical
  have hTo : hI.to I = 𝟙 I := hI.hom_ext _ _
  have hIdCof : cofibrations C (𝟙 I) :=
    hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance)
  have hIdPair : IsCofibrantPair (𝟙 I) (𝟙 I) := by
    refine ⟨I, hI, ?_⟩
    have hG : IsCofibrantGluing (𝟙 I) (𝟙 I) (𝟙 I) (𝟙 I) :=
      ⟨I, 𝟙 I, 𝟙 I, IsPushout.of_id_fst, 𝟙 I, by simp, by simp, hIdCof⟩
    simpa [hTo] using hG
  refine ⟨I, I, I, 𝟙 I, 𝟙 I, hIdPair, ?_, ?_⟩
  · exact hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  · exact hC.isomorphisms_le_weakEquivalences _ (by infer_instance)

private def pathObjCenter : PathObj C ⥤ C where
  obj X := X.c
  map f := f.c
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem pathObj_isIso_cof {X Y : PathObj C} (f : X ⟶ Y) (hf : IsIso f) :
    cofibrations (PathObj C) f := by
  letI : IsIso f := hf
  have hfl : IsIso f.l := Functor.map_isIso (PathObj.left C) f
  have hfr : IsIso f.r := Functor.map_isIso (PathObj.right C) f
  have hfc : IsIso f.c := by
    change IsIso (pathObjCenter.map f)
    exact Functor.map_isIso pathObjCenter f
  letI := hfl
  letI := hfr
  letI := hfc
  have hP : IsPushout X.il f.l f.c Y.il := by
    apply IsPushout.mk'
    · exact f.il_c
    · intro T φ ψ hφ hψ
      exact (cancel_epi f.c).1 hφ
    · intro T φ ψ hφψ
      have hinvIl : Y.il ≫ inv f.c = inv f.l ≫ X.il := by
        apply (cancel_epi f.l).1
        calc
          f.l ≫ (Y.il ≫ inv f.c) = (f.l ≫ Y.il) ≫ inv f.c := by
            simp [Category.assoc]
          _ = (X.il ≫ f.c) ≫ inv f.c := congrArg (fun t => t ≫ inv f.c) f.il_c.symm
          _ = X.il := by simp [Category.assoc]
          _ = f.l ≫ (inv f.l ≫ X.il) := by simp [Category.assoc]
      let d : Y.c ⟶ T := inv f.c ≫ φ
      refine ⟨d, ?_, ?_⟩
      · simp [d, Category.assoc]
      · calc
          Y.il ≫ d = (Y.il ≫ inv f.c) ≫ φ := by simp [d, Category.assoc]
          _ = (inv f.l ≫ X.il) ≫ φ := congrArg (fun t => t ≫ φ) hinvIl
          _ = inv f.l ≫ (X.il ≫ φ) := Category.assoc _ _ _
          _ = inv f.l ≫ (f.l ≫ ψ) := congrArg (fun t => inv f.l ≫ t) hφψ
          _ = (inv f.l ≫ f.l) ≫ ψ := (Category.assoc _ _ _).symm
          _ = ψ := by simp [Category.assoc]
  have hQ : IsPushout (X.ir ≫ f.c) f.r (𝟙 Y.c) Y.ir := by
    apply IsPushout.mk'
    · calc
        (X.ir ≫ f.c) ≫ 𝟙 Y.c = X.ir ≫ f.c := by simp
        _ = f.r ≫ Y.ir := f.ir_c
    · intro T φ ψ hφ hψ
      simpa using hφ
    · intro T φ ψ hφψ
      refine ⟨φ, ?_, ?_⟩
      · simp
      · apply (cancel_epi f.r).1
        calc
          f.r ≫ (Y.ir ≫ φ) = (f.r ≫ Y.ir) ≫ φ :=
            (Category.assoc _ _ _).symm
          _ = (X.ir ≫ f.c) ≫ φ := congrArg (fun t => t ≫ φ) f.ir_c.symm
          _ = f.r ≫ ψ := hφψ
  have hIdCof : cofibrations C (𝟙 Y.c) :=
    hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance)
  have hG : IsCofibrantGluing (X.ir ≫ f.c) f.r (𝟙 Y.c) Y.ir :=
    ⟨Y.c, 𝟙 Y.c, Y.ir, hQ, 𝟙 Y.c, by simp, by simp, hIdCof⟩
  refine ⟨hC.toIsCofibrationCategory.isomorphisms_le _ hfl,
    hC.toIsCofibrationCategory.isomorphisms_le _ hfr,
    Y.c, f.c, Y.il, hP, 𝟙 Y.c, by simp, by simp, hG⟩

private noncomputable def pathInitialHom {I : C} (hI : IsInitial I) (X : PathObj C) :
    (pathInitialObject hI) ⟶ X where
  l := hI.to X.l
  r := hI.to X.r
  c := hI.to X.c
  il_c := by
    change (𝟙 I) ≫ hI.to X.c = hI.to X.l ≫ X.il
    simpa using hI.hom_ext (hI.to X.c) (hI.to X.l ≫ X.il)
  ir_c := by
    change (𝟙 I) ≫ hI.to X.c = hI.to X.r ≫ X.ir
    simpa using hI.hom_ext (hI.to X.c) (hI.to X.r ≫ X.ir)

private noncomputable def pathInitial_isInitial {I : C} (hI : IsInitial I) :
    IsInitial (pathInitialObject hI) := by
  refine IsInitial.ofUniqueHom (pathInitialHom hI) ?_
  intro X f
  apply PathObj.Hom.ext
  · exact hI.hom_ext f.l (hI.to X.l)
  · exact hI.hom_ext f.r (hI.to X.r)
  · exact hI.hom_ext f.c (hI.to X.c)

private theorem pathInitial_cofibration {I : C} (hI : IsInitial I) (X : PathObj C) :
    cofibrations (PathObj C) (pathInitialHom hI X) := by
  classical
  let hMap := pathInitialHom hI X
  have hTo : hI.to I = 𝟙 I := hI.hom_ext _ _
  have hG : IsCofibrantGluing (hI.to X.l) (hI.to X.r) X.il X.ir := by
    obtain ⟨J, hJ, hX⟩ := X.cofibrant
    exact cofibrantGluing_changeInitial hI hJ hX
  have hG' : IsCofibrantGluing ((𝟙 I) ≫ hMap.l) hMap.r X.il X.ir := by
    simpa [pathInitialObject, pathInitialHom, hMap, hTo] using hG
  have hPush : IsPushout ((pathInitialObject hI).il) hMap.l hMap.l (𝟙 X.l) := by
    simpa [pathInitialObject, hMap] using (IsPushout.of_id_fst (f := hMap.l))
  constructor
  · exact hC.initial_cofibration hI X.l
  constructor
  · exact hC.initial_cofibration hI X.r
  · refine ⟨X.l, hMap.l, 𝟙 X.l, ?_, X.il, ?_, ?_, ?_⟩
    · exact hPush
    · simpa [pathInitialObject, hMap] using hMap.il_c.symm
    · simp
    · simpa [pathInitialObject, hMap] using hG'

private theorem pathInitial_map_cofibration {J : PathObj C} (hJ : IsInitial J)
    (X : PathObj C) : cofibrations (PathObj C) (hJ.to X) := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let J₀ := pathInitialObject hI
  have hJ₀ : IsInitial J₀ := pathInitial_isInitial hI
  let e : J ≅ J₀ := hJ.uniqueUpToIso hJ₀
  let eL : J.l ≅ I := (PathObj.left C).mapIso e
  let eR : J.r ≅ I := (PathObj.right C).mapIso e
  let eC : J.c ≅ I := by
    change pathObjCenter.obj J ≅ pathObjCenter.obj J₀
    exact pathObjCenter.mapIso e
  have hJl : IsInitial J.l := IsInitial.ofIso hI eL.symm
  have hJr : IsInitial J.r := IsInitial.ofIso hI eR.symm
  have hJc : IsInitial J.c := IsInitial.ofIso hI eC.symm
  let eIl : J.l ≅ J.c := hJl.uniqueUpToIso hJc
  let eIr : J.r ≅ J.c := hJr.uniqueUpToIso hJc
  have hJil : J.il = eIl.hom := hJl.hom_ext _ _
  have hJir : J.ir = eIr.hom := hJr.hom_ext _ _
  letI : IsIso J.il := by rw [hJil]; infer_instance
  letI : IsIso J.ir := by rw [hJir]; infer_instance
  let hMap : J ⟶ X := hJ.to X
  have hMapL : hJl.to X.l = hMap.l := hJl.hom_ext _ _
  have hMapR : hJr.to X.r = hMap.r := hJr.hom_ext _ _
  let k : J.c ⟶ X.l := hJc.to X.l
  have hP : IsPushout J.il hMap.l k (𝟙 X.l) := by
    apply IsPushout.mk'
    · exact hJl.hom_ext _ _
    · intro T φ ψ hφ hψ
      simpa using hψ
    · intro T φ ψ hφψ
      refine ⟨ψ, ?_, ?_⟩
      · apply (cancel_epi J.il).1
        calc
          J.il ≫ (k ≫ ψ) = (J.il ≫ k) ≫ ψ := (Category.assoc _ _ _).symm
          _ = hMap.l ≫ ψ := hJl.hom_ext _ _
          _ = J.il ≫ φ := hφψ.symm
      · simp
  obtain ⟨Iₓ, hIₓ, hGₓ⟩ := X.cofibrant
  have hG₀ : IsCofibrantGluing (hJr.to X.l) (hJr.to X.r) X.il X.ir :=
    cofibrantGluing_changeInitial hJr hIₓ hGₓ
  have hkR : J.ir ≫ k = hJr.to X.l := hJr.hom_ext _ _
  have hmapR : hMap.r = hJr.to X.r := hJr.hom_ext _ _
  have hG : IsCofibrantGluing (J.ir ≫ k) hMap.r X.il X.ir := by
    rw [hkR, hmapR]
    exact hG₀
  refine ⟨?_, ?_, X.l, k, 𝟙 X.l, hP, X.il, ?_, ?_, hG⟩
  · rw [← hMapL]
    exact hC.initial_cofibration hJl X.l
  · rw [← hMapR]
    exact hC.initial_cofibration hJr X.r
  · exact hJc.hom_ext _ _
  · simp

private theorem pathObj_cof_middle {X Y : PathObj C} (f : X ⟶ Y)
    (hf : cofibrations (PathObj C) f) : cofibrations C f.c := by
  rcases hf with ⟨hfl, hfr, P, k, j, hP, m, hkm, hjm, hG⟩
  have hk : cofibrations C k :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hP hfl
  rcases hG with ⟨Q, a, b, hQ, n, han, hbn, hn⟩
  have ha : cofibrations C a :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hQ hfr
  have hm : cofibrations C m := by
    rw [← han]
    exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ ha hn
  rw [← hkm]
  exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hk hm

private structure PathBoundaryData {I : C} (hI : IsInitial I) (X : PathObj C) where
  P : C
  inl : X.l ⟶ P
  inr : X.r ⟶ P
  isPushout : IsPushout (hI.to X.l) (hI.to X.r) inl inr
  toCenter : P ⟶ X.c
  inl_toCenter : inl ≫ toCenter = X.il
  inr_toCenter : inr ≫ toCenter = X.ir
  toCenter_mem : cofibrations C toCenter

private noncomputable def pathBoundaryData {I : C} (hI : IsInitial I) (X : PathObj C) :
    PathBoundaryData hI X := by
  classical
  have hNonempty : Nonempty (PathBoundaryData hI X) := by
    obtain ⟨J, hJ, hX⟩ := X.cofibrant
    obtain ⟨P, k, j, hP, m, hkm, hjm, hcof⟩ := cofibrantGluing_changeInitial hI hJ hX
    exact ⟨⟨P, k, j, hP, m, hkm, hjm, hcof⟩⟩
  exact Classical.choice hNonempty

private theorem pathBoundaryMap_cof {I : C} (hI : IsInitial I)
    {Y Z : PathObj C} (g : Y ⟶ Z) (hgL : cofibrations C g.l) (hgR : cofibrations C g.r)
    (bY : PathBoundaryData hI Y) (bZ : PathBoundaryData hI Z) :
    ∃ a : bY.P ⟶ bZ.P,
      bY.inl ≫ a = g.l ≫ bZ.inl ∧ bY.inr ≫ a = g.r ≫ bZ.inr ∧ cofibrations C a := by
  classical
  have hcompat : hI.to Y.l ≫ (g.l ≫ bZ.inl) = hI.to Y.r ≫ (g.r ≫ bZ.inr) :=
    hI.hom_ext _ _
  let a : bY.P ⟶ bZ.P := bY.isPushout.desc (g.l ≫ bZ.inl) (g.r ≫ bZ.inr) hcompat
  have haL : bY.inl ≫ a = g.l ≫ bZ.inl :=
    bY.isPushout.inl_desc _ _ hcompat
  have haR : bY.inr ≫ a = g.r ≫ bZ.inr :=
    bY.isPushout.inr_desc _ _ hcompat
  letI : HasPushout g.l bY.inl := hC.hasPushout g.l bY.inl hgL
  let R₁ := pushout g.l bY.inl
  let z₁ : Z.l ⟶ R₁ := pushout.inl g.l bY.inl
  let u₁ : bY.P ⟶ R₁ := pushout.inr g.l bY.inl
  have h₁ : IsPushout g.l bY.inl z₁ u₁ := IsPushout.of_hasPushout _ _
  have hu₁ : cofibrations C u₁ :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout h₁.flip hgL
  let uYr : Y.r ⟶ R₁ := bY.inr ≫ u₁
  letI : HasPushout g.r uYr := hC.hasPushout g.r uYr hgR
  let R₂ := pushout g.r uYr
  let z₂ : Z.r ⟶ R₂ := pushout.inl g.r uYr
  let u₂ : R₁ ⟶ R₂ := pushout.inr g.r uYr
  have h₂ : IsPushout g.r uYr z₂ u₂ := IsPushout.of_hasPushout _ _
  have hu₂ : cofibrations C u₂ :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout h₂.flip hgR
  let zL : Z.l ⟶ R₂ := z₁ ≫ u₂
  let zR : Z.r ⟶ R₂ := z₂
  have hLBoundary : bY.inl ≫ u₁ ≫ u₂ = g.l ≫ z₁ ≫ u₂ := by
    simpa [Category.assoc] using congrArg (fun t => t ≫ u₂) h₁.w.symm
  have hRBoundary : bY.inr ≫ u₁ ≫ u₂ = g.r ≫ z₂ := by
    simpa [uYr, Category.assoc] using h₂.w.symm
  have hR₂ : IsPushout (hI.to Z.l) (hI.to Z.r) zL zR := by
    apply IsPushout.mk'
    · exact hI.hom_ext _ _
    · intro T φ ψ hφ hψ
      have hu₂φ : u₂ ≫ φ = u₂ ≫ ψ := by
        apply h₁.hom_ext
        · simpa [zL, Category.assoc] using hφ
        · apply bY.isPushout.hom_ext
          · calc
              bY.inl ≫ u₁ ≫ u₂ ≫ φ = (g.l ≫ z₁ ≫ u₂) ≫ φ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hLBoundary
              _ = g.l ≫ (zL ≫ φ) := by simp [zL, Category.assoc]
              _ = g.l ≫ (zL ≫ ψ) := congrArg (fun t => g.l ≫ t) hφ
              _ = (g.l ≫ z₁ ≫ u₂) ≫ ψ := by simp [zL, Category.assoc]
              _ = bY.inl ≫ u₁ ≫ u₂ ≫ ψ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hLBoundary.symm
          · calc
              bY.inr ≫ u₁ ≫ u₂ ≫ φ = (g.r ≫ z₂) ≫ φ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hRBoundary
              _ = g.r ≫ (zR ≫ φ) := by simp [zR, Category.assoc]
              _ = g.r ≫ (zR ≫ ψ) := congrArg (fun t => g.r ≫ t) hψ
              _ = (g.r ≫ z₂) ≫ ψ := by simp [zR, Category.assoc]
              _ = bY.inr ≫ u₁ ≫ u₂ ≫ ψ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hRBoundary.symm
      exact h₂.hom_ext hψ hu₂φ
    · intro T φ ψ hφψ
      let dY : bY.P ⟶ T := bY.isPushout.desc (g.l ≫ φ) (g.r ≫ ψ)
        (hI.hom_ext _ _)
      have hdYL : bY.inl ≫ dY = g.l ≫ φ :=
        bY.isPushout.inl_desc _ _ (hI.hom_ext _ _)
      have hdYR : bY.inr ≫ dY = g.r ≫ ψ :=
        bY.isPushout.inr_desc _ _ (hI.hom_ext _ _)
      have hR₁Compat : g.l ≫ φ = bY.inl ≫ dY := hdYL.symm
      let d₁ : R₁ ⟶ T := h₁.desc φ dY hR₁Compat
      have hd₁Z : z₁ ≫ d₁ = φ := h₁.inl_desc φ dY hR₁Compat
      have hd₁Y : u₁ ≫ d₁ = dY := h₁.inr_desc φ dY hR₁Compat
      have hR₂Compat : g.r ≫ ψ = uYr ≫ d₁ := by
        calc
          g.r ≫ ψ = bY.inr ≫ dY := hdYR.symm
          _ = bY.inr ≫ (u₁ ≫ d₁) := congrArg (fun t => bY.inr ≫ t) hd₁Y.symm
          _ = (bY.inr ≫ u₁) ≫ d₁ := (Category.assoc _ _ _).symm
          _ = uYr ≫ d₁ := by simpa [uYr, Category.assoc]
      let d₂ : R₂ ⟶ T := h₂.desc ψ d₁ hR₂Compat
      have hd₂Z : z₂ ≫ d₂ = ψ := h₂.inl_desc ψ d₁ hR₂Compat
      have hd₂R₁ : u₂ ≫ d₂ = d₁ := h₂.inr_desc ψ d₁ hR₂Compat
      have hDesc : zL ≫ d₂ = φ := by
        calc
          zL ≫ d₂ = z₁ ≫ (u₂ ≫ d₂) := Category.assoc _ _ _
          _ = z₁ ≫ d₁ := congrArg (fun t => z₁ ≫ t) hd₂R₁
          _ = φ := hd₁Z
      exact ⟨d₂, hDesc, hd₂Z⟩
  let e : bZ.P ≅ R₂ := bZ.isPushout.isColimit.coconePointUniqueUpToIso hR₂.isColimit
  have heL : bZ.inl ≫ e.hom = zL := by
    dsimp [e, zL]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      bZ.isPushout.isColimit hR₂.isColimit WalkingSpan.left
  have heR : bZ.inr ≫ e.hom = zR := by
    dsimp [e, zR]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      bZ.isPushout.isColimit hR₂.isColimit WalkingSpan.right
  let a₁₂ : bY.P ⟶ R₂ := u₁ ≫ u₂
  have ha₁₂L : bY.inl ≫ a₁₂ = g.l ≫ zL := by
    dsimp [a₁₂, zL]
    calc
      bY.inl ≫ u₁ ≫ u₂ = (bY.inl ≫ u₁) ≫ u₂ := by simp [Category.assoc]
      _ = (g.l ≫ z₁) ≫ u₂ := congrArg (fun t => t ≫ u₂) h₁.w.symm
      _ = g.l ≫ (z₁ ≫ u₂) := Category.assoc _ _ _
  have ha₁₂R : bY.inr ≫ a₁₂ = g.r ≫ zR := by
    dsimp [a₁₂, uYr, zR]
    calc
      bY.inr ≫ u₁ ≫ u₂ = uYr ≫ u₂ := by simpa [uYr, Category.assoc]
      _ = g.r ≫ z₂ := h₂.w.symm
  have hAe : a ≫ e.hom = a₁₂ := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ a ≫ e.hom = g.l ≫ bZ.inl ≫ e.hom := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ e.hom) haL
        _ = g.l ≫ zL := congrArg (fun t => g.l ≫ t) heL
        _ = bY.inl ≫ a₁₂ := ha₁₂L.symm
    · calc
        bY.inr ≫ a ≫ e.hom = g.r ≫ bZ.inr ≫ e.hom := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ e.hom) haR
        _ = g.r ≫ zR := congrArg (fun t => g.r ≫ t) heR
        _ = bY.inr ≫ a₁₂ := ha₁₂R.symm
  have ha₁₂ : cofibrations C a₁₂ :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hu₁ hu₂
  have heInv : cofibrations C e.inv :=
    hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance)
  have hae : a = a₁₂ ≫ e.inv := by
    calc
      a = a ≫ (e.hom ≫ e.inv) := by simp
      _ = (a ≫ e.hom) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = a₁₂ ≫ e.inv := congrArg (fun t => t ≫ e.inv) hAe
  refine ⟨a, haL, haR, ?_⟩
  rw [hae]
  exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ ha₁₂ heInv

private theorem boundary_cobasePushout
    {I Xl Xr Yl Yr Zl Zr Wl Wr PX PY PZ PW : C} (hI : IsInitial I)
    {xL : Xl ⟶ PX} {xR : Xr ⟶ PX} {yL : Yl ⟶ PY} {yR : Yr ⟶ PY}
    {zL : Zl ⟶ PZ} {zR : Zr ⟶ PZ} {wL : Wl ⟶ PW} {wR : Wr ⟶ PW}
    (hX : IsPushout (hI.to Xl) (hI.to Xr) xL xR)
    (hY : IsPushout (hI.to Yl) (hI.to Yr) yL yR)
    (hZ : IsPushout (hI.to Zl) (hI.to Zr) zL zR)
    (hW : IsPushout (hI.to Wl) (hI.to Wr) wL wR)
    {fL : Xl ⟶ Yl} {gL : Xl ⟶ Zl} {kL : Yl ⟶ Wl} {jL : Zl ⟶ Wl}
    (hWL : IsPushout fL gL kL jL)
    {fR : Xr ⟶ Yr} {gR : Xr ⟶ Zr} {kR : Yr ⟶ Wr} {jR : Zr ⟶ Wr}
    (hWR : IsPushout fR gR kR jR)
    {a : PX ⟶ PY} {b : PX ⟶ PZ} {pY : PY ⟶ PW} {pZ : PZ ⟶ PW}
    (haL : xL ≫ a = fL ≫ yL) (haR : xR ≫ a = fR ≫ yR)
    (hbL : xL ≫ b = gL ≫ zL) (hbR : xR ≫ b = gR ≫ zR)
    (hpYL : yL ≫ pY = kL ≫ wL) (hpYR : yR ≫ pY = kR ≫ wR)
    (hpZL : zL ≫ pZ = jL ≫ wL) (hpZR : zR ≫ pZ = jR ≫ wR) :
    IsPushout a b pY pZ := by
  apply IsPushout.mk'
  · apply hX.hom_ext
    · calc
        xL ≫ (a ≫ pY) = (xL ≫ a) ≫ pY := (Category.assoc xL a pY).symm
        _ = (fL ≫ yL) ≫ pY := congrArg (fun t => t ≫ pY) haL
        _ = fL ≫ (yL ≫ pY) := Category.assoc fL yL pY
        _ = fL ≫ (kL ≫ wL) := congrArg (fun t => fL ≫ t) hpYL
        _ = (fL ≫ kL) ≫ wL := (Category.assoc fL kL wL).symm
        _ = (gL ≫ jL) ≫ wL := congrArg (fun t => t ≫ wL) hWL.w
        _ = gL ≫ (jL ≫ wL) := Category.assoc gL jL wL
        _ = gL ≫ (zL ≫ pZ) := congrArg (fun t => gL ≫ t) hpZL.symm
        _ = (gL ≫ zL) ≫ pZ := (Category.assoc gL zL pZ).symm
        _ = (xL ≫ b) ≫ pZ := congrArg (fun t => t ≫ pZ) hbL.symm
        _ = xL ≫ (b ≫ pZ) := Category.assoc xL b pZ
    · calc
        xR ≫ (a ≫ pY) = (xR ≫ a) ≫ pY := (Category.assoc xR a pY).symm
        _ = (fR ≫ yR) ≫ pY := congrArg (fun t => t ≫ pY) haR
        _ = fR ≫ (yR ≫ pY) := Category.assoc fR yR pY
        _ = fR ≫ (kR ≫ wR) := congrArg (fun t => fR ≫ t) hpYR
        _ = (fR ≫ kR) ≫ wR := (Category.assoc fR kR wR).symm
        _ = (gR ≫ jR) ≫ wR := congrArg (fun t => t ≫ wR) hWR.w
        _ = gR ≫ (jR ≫ wR) := Category.assoc gR jR wR
        _ = gR ≫ (zR ≫ pZ) := congrArg (fun t => gR ≫ t) hpZR.symm
        _ = (gR ≫ zR) ≫ pZ := (Category.assoc gR zR pZ).symm
        _ = (xR ≫ b) ≫ pZ := congrArg (fun t => t ≫ pZ) hbR.symm
        _ = xR ≫ (b ≫ pZ) := Category.assoc xR b pZ
  · intro T φ ψ hφ hψ
    have hWl : kL ≫ wL ≫ φ = kL ≫ wL ≫ ψ := by
      calc
        kL ≫ wL ≫ φ = (kL ≫ wL) ≫ φ := (Category.assoc kL wL φ).symm
        _ = (yL ≫ pY) ≫ φ := congrArg (fun t => t ≫ φ) hpYL.symm
        _ = yL ≫ (pY ≫ φ) := Category.assoc yL pY φ
        _ = yL ≫ (pY ≫ ψ) := congrArg (fun t => yL ≫ t) hφ
        _ = (yL ≫ pY) ≫ ψ := (Category.assoc yL pY ψ).symm
        _ = (kL ≫ wL) ≫ ψ := congrArg (fun t => t ≫ ψ) hpYL
        _ = kL ≫ wL ≫ ψ := Category.assoc kL wL ψ
    have hZl : jL ≫ wL ≫ φ = jL ≫ wL ≫ ψ := by
      calc
        jL ≫ wL ≫ φ = (jL ≫ wL) ≫ φ := (Category.assoc jL wL φ).symm
        _ = (zL ≫ pZ) ≫ φ := congrArg (fun t => t ≫ φ) hpZL.symm
        _ = zL ≫ (pZ ≫ φ) := Category.assoc zL pZ φ
        _ = zL ≫ (pZ ≫ ψ) := congrArg (fun t => zL ≫ t) hψ
        _ = (zL ≫ pZ) ≫ ψ := (Category.assoc zL pZ ψ).symm
        _ = (jL ≫ wL) ≫ ψ := congrArg (fun t => t ≫ ψ) hpZL
        _ = jL ≫ wL ≫ ψ := Category.assoc jL wL ψ
    have heqL : wL ≫ φ = wL ≫ ψ := hWL.hom_ext hWl hZl
    have hWr : kR ≫ wR ≫ φ = kR ≫ wR ≫ ψ := by
      calc
        kR ≫ wR ≫ φ = (kR ≫ wR) ≫ φ := (Category.assoc kR wR φ).symm
        _ = (yR ≫ pY) ≫ φ := congrArg (fun t => t ≫ φ) hpYR.symm
        _ = yR ≫ (pY ≫ φ) := Category.assoc yR pY φ
        _ = yR ≫ (pY ≫ ψ) := congrArg (fun t => yR ≫ t) hφ
        _ = (yR ≫ pY) ≫ ψ := (Category.assoc yR pY ψ).symm
        _ = (kR ≫ wR) ≫ ψ := congrArg (fun t => t ≫ ψ) hpYR
        _ = kR ≫ wR ≫ ψ := Category.assoc kR wR ψ
    have hZr : jR ≫ wR ≫ φ = jR ≫ wR ≫ ψ := by
      calc
        jR ≫ wR ≫ φ = (jR ≫ wR) ≫ φ := (Category.assoc jR wR φ).symm
        _ = (zR ≫ pZ) ≫ φ := congrArg (fun t => t ≫ φ) hpZR.symm
        _ = zR ≫ (pZ ≫ φ) := Category.assoc zR pZ φ
        _ = zR ≫ (pZ ≫ ψ) := congrArg (fun t => zR ≫ t) hψ
        _ = (zR ≫ pZ) ≫ ψ := (Category.assoc zR pZ ψ).symm
        _ = (jR ≫ wR) ≫ ψ := congrArg (fun t => t ≫ ψ) hpZR
        _ = jR ≫ wR ≫ ψ := Category.assoc jR wR ψ
    exact hW.hom_ext heqL (hWR.hom_ext hWr hZr)
  · intro T φ ψ hφ
    have hcompatL : fL ≫ (yL ≫ φ) = gL ≫ (zL ≫ ψ) := by
      calc
        fL ≫ (yL ≫ φ) = (fL ≫ yL) ≫ φ := (Category.assoc fL yL φ).symm
        _ = (xL ≫ a) ≫ φ := congrArg (fun t => t ≫ φ) haL.symm
        _ = xL ≫ (a ≫ φ) := Category.assoc xL a φ
        _ = xL ≫ (b ≫ ψ) := congrArg (fun t => xL ≫ t) hφ
        _ = (xL ≫ b) ≫ ψ := (Category.assoc xL b ψ).symm
        _ = (gL ≫ zL) ≫ ψ := congrArg (fun t => t ≫ ψ) hbL
        _ = gL ≫ (zL ≫ ψ) := Category.assoc gL zL ψ
    have hcompatR : fR ≫ (yR ≫ φ) = gR ≫ (zR ≫ ψ) := by
      calc
        fR ≫ (yR ≫ φ) = (fR ≫ yR) ≫ φ := (Category.assoc fR yR φ).symm
        _ = (xR ≫ a) ≫ φ := congrArg (fun t => t ≫ φ) haR.symm
        _ = xR ≫ (a ≫ φ) := Category.assoc xR a φ
        _ = xR ≫ (b ≫ ψ) := congrArg (fun t => xR ≫ t) hφ
        _ = (xR ≫ b) ≫ ψ := (Category.assoc xR b ψ).symm
        _ = (gR ≫ zR) ≫ ψ := congrArg (fun t => t ≫ ψ) hbR
        _ = gR ≫ (zR ≫ ψ) := Category.assoc gR zR ψ
    let dL : Wl ⟶ T := hWL.desc (yL ≫ φ) (zL ≫ ψ) hcompatL
    let dR : Wr ⟶ T := hWR.desc (yR ≫ φ) (zR ≫ ψ) hcompatR
    have hInitial : hI.to Wl ≫ dL = hI.to Wr ≫ dR := hI.hom_ext _ _
    let d : PW ⟶ T := hW.desc dL dR hInitial
    refine ⟨d, ?_, ?_⟩
    · apply hY.hom_ext
      · calc
          yL ≫ pY ≫ d = (yL ≫ pY) ≫ d := (Category.assoc yL pY d).symm
          _ = (kL ≫ wL) ≫ d := congrArg (fun t => t ≫ d) hpYL
          _ = kL ≫ (wL ≫ d) := Category.assoc kL wL d
          _ = kL ≫ dL := congrArg (fun t => kL ≫ t) (hW.inl_desc dL dR hInitial)
          _ = yL ≫ φ := hWL.inl_desc (yL ≫ φ) (zL ≫ ψ) hcompatL
      · calc
          yR ≫ pY ≫ d = (yR ≫ pY) ≫ d := (Category.assoc yR pY d).symm
          _ = (kR ≫ wR) ≫ d := congrArg (fun t => t ≫ d) hpYR
          _ = kR ≫ (wR ≫ d) := Category.assoc kR wR d
          _ = kR ≫ dR := congrArg (fun t => kR ≫ t) (hW.inr_desc dL dR hInitial)
          _ = yR ≫ φ := hWR.inl_desc (yR ≫ φ) (zR ≫ ψ) hcompatR
    · apply hZ.hom_ext
      · calc
          zL ≫ pZ ≫ d = (zL ≫ pZ) ≫ d := (Category.assoc zL pZ d).symm
          _ = (jL ≫ wL) ≫ d := congrArg (fun t => t ≫ d) hpZL
          _ = jL ≫ (wL ≫ d) := Category.assoc jL wL d
          _ = jL ≫ dL := congrArg (fun t => jL ≫ t) (hW.inl_desc dL dR hInitial)
          _ = zL ≫ ψ := hWL.inr_desc (yL ≫ φ) (zL ≫ ψ) hcompatL
      · calc
          zR ≫ pZ ≫ d = (zR ≫ pZ) ≫ d := (Category.assoc zR pZ d).symm
          _ = (jR ≫ wR) ≫ d := congrArg (fun t => t ≫ d) hpZR
          _ = jR ≫ (wR ≫ d) := Category.assoc jR wR d
          _ = jR ≫ dR := congrArg (fun t => jR ≫ t) (hW.inr_desc dL dR hInitial)
          _ = zR ≫ ψ := hWR.inr_desc (yR ≫ φ) (zR ≫ ψ) hcompatR

private structure PathObjCofibrationData {X Y : PathObj C} (f : X ⟶ Y) where
  left_mem : cofibrations C f.l
  right_mem : cofibrations C f.r
  P : C
  k : X.c ⟶ P
  j : Y.l ⟶ P
  pushout₁ : IsPushout X.il f.l k j
  m : P ⟶ Y.c
  km : k ≫ m = f.c
  jm : j ≫ m = Y.il
  Q : C
  k₂ : P ⟶ Q
  j₂ : Y.r ⟶ Q
  pushout₂ : IsPushout (X.ir ≫ k) f.r k₂ j₂
  n : Q ⟶ Y.c
  k₂n : k₂ ≫ n = m
  j₂n : j₂ ≫ n = Y.ir
  n_mem : cofibrations C n

private noncomputable def pathObjCofibrationData {X Y : PathObj C} (f : X ⟶ Y)
    (hf : cofibrations (PathObj C) f) : PathObjCofibrationData f := by
  classical
  have hNonempty : Nonempty (PathObjCofibrationData f) := by
    rcases hf with ⟨hfl, hfr, P, k, j, hP, m, hkm, hjm, hG⟩
    rcases hG with ⟨Q, k₂, j₂, hQ, n, hkn, hjn, hn⟩
    exact ⟨⟨hfl, hfr, P, k, j, hP, m, hkm, hjm, Q, k₂, j₂, hQ, n, hkn, hjn, hn⟩⟩
  exact Classical.choice hNonempty

private theorem pathObj_cofBoundaryPushout {I : C} (hI : IsInitial I)
    {Y Z : PathObj C} (g : Y ⟶ Z) (G : PathObjCofibrationData g)
    (bY : PathBoundaryData hI Y) (bZ : PathBoundaryData hI Z)
    (a : bY.P ⟶ bZ.P)
    (haL : bY.inl ≫ a = g.l ≫ bZ.inl) (haR : bY.inr ≫ a = g.r ≫ bZ.inr) :
    IsPushout bY.toCenter a (G.k ≫ G.k₂)
      (bZ.isPushout.desc (G.j ≫ G.k₂) G.j₂ (hI.hom_ext _ _)) := by
  let mY : Y.c ⟶ G.Q := G.k ≫ G.k₂
  let pZ : bZ.P ⟶ G.Q := bZ.isPushout.desc (G.j ≫ G.k₂) G.j₂ (hI.hom_ext _ _)
  have hpZL : bZ.inl ≫ pZ = G.j ≫ G.k₂ :=
    bZ.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have hpZR : bZ.inr ≫ pZ = G.j₂ :=
    bZ.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  have hCompat : bY.toCenter ≫ mY = a ≫ pZ := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ bY.toCenter ≫ mY =
            (bY.inl ≫ bY.toCenter) ≫ mY := by simp [Category.assoc]
        _ = Y.il ≫ mY := congrArg (fun t => t ≫ mY) bY.inl_toCenter
        _ = Y.il ≫ (G.k ≫ G.k₂) := rfl
        _ = (Y.il ≫ G.k) ≫ G.k₂ := (Category.assoc _ _ _).symm
        _ = (g.l ≫ G.j) ≫ G.k₂ := congrArg (fun t => t ≫ G.k₂) G.pushout₁.w
        _ = g.l ≫ (G.j ≫ G.k₂) := Category.assoc _ _ _
        _ = g.l ≫ (bZ.inl ≫ pZ) := congrArg (fun t => g.l ≫ t) hpZL.symm
        _ = (g.l ≫ bZ.inl) ≫ pZ := (Category.assoc _ _ _).symm
        _ = (bY.inl ≫ a) ≫ pZ := congrArg (fun t => t ≫ pZ) haL.symm
        _ = bY.inl ≫ (a ≫ pZ) := Category.assoc _ _ _
    · calc
        bY.inr ≫ bY.toCenter ≫ mY =
            (bY.inr ≫ bY.toCenter) ≫ mY := by simp [Category.assoc]
        _ = Y.ir ≫ mY := congrArg (fun t => t ≫ mY) bY.inr_toCenter
        _ = Y.ir ≫ (G.k ≫ G.k₂) := rfl
        _ = (Y.ir ≫ G.k) ≫ G.k₂ := (Category.assoc _ _ _).symm
        _ = g.r ≫ G.j₂ := G.pushout₂.w
        _ = g.r ≫ (bZ.inr ≫ pZ) := congrArg (fun t => g.r ≫ t) hpZR.symm
        _ = (g.r ≫ bZ.inr) ≫ pZ := (Category.assoc _ _ _).symm
        _ = (bY.inr ≫ a) ≫ pZ := congrArg (fun t => t ≫ pZ) haR.symm
        _ = bY.inr ≫ (a ≫ pZ) := Category.assoc _ _ _
  apply IsPushout.mk'
  · exact hCompat
  · intro T φ ψ hφ hψ
    have h₂j : G.j₂ ≫ φ = G.j₂ ≫ ψ := by
      calc
        G.j₂ ≫ φ = (bZ.inr ≫ pZ) ≫ φ :=
          congrArg (fun t => t ≫ φ) hpZR.symm
        _ = bZ.inr ≫ (pZ ≫ φ) := Category.assoc _ _ _
        _ = bZ.inr ≫ (pZ ≫ ψ) := congrArg (fun t => bZ.inr ≫ t) hψ
        _ = (bZ.inr ≫ pZ) ≫ ψ := (Category.assoc _ _ _).symm
        _ = G.j₂ ≫ ψ := congrArg (fun t => t ≫ ψ) hpZR
    have h₂k : G.k₂ ≫ φ = G.k₂ ≫ ψ := by
      apply G.pushout₁.hom_ext
      · simpa [mY, Category.assoc] using hφ
      · calc
          G.j ≫ G.k₂ ≫ φ = (bZ.inl ≫ pZ) ≫ φ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hpZL.symm
          _ = bZ.inl ≫ (pZ ≫ φ) := Category.assoc _ _ _
          _ = bZ.inl ≫ (pZ ≫ ψ) := congrArg (fun t => bZ.inl ≫ t) hψ
          _ = (bZ.inl ≫ pZ) ≫ ψ := (Category.assoc _ _ _).symm
          _ = G.j ≫ G.k₂ ≫ ψ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hpZL
    exact G.pushout₂.hom_ext h₂k h₂j
  · intro T φ ψ hφψ
    have hYlCompat : Y.il ≫ φ = g.l ≫ (bZ.inl ≫ ψ) := by
      calc
        Y.il ≫ φ = (bY.inl ≫ bY.toCenter) ≫ φ :=
          congrArg (fun t => t ≫ φ) bY.inl_toCenter.symm
        _ = bY.inl ≫ (bY.toCenter ≫ φ) := by simp [Category.assoc]
        _ = bY.inl ≫ (a ≫ ψ) := congrArg (fun t => bY.inl ≫ t) hφψ
        _ = (bY.inl ≫ a) ≫ ψ := by simp [Category.assoc]
        _ = (g.l ≫ bZ.inl) ≫ ψ := congrArg (fun t => t ≫ ψ) haL
        _ = g.l ≫ (bZ.inl ≫ ψ) := by simp [Category.assoc]
    have hYrCompat : Y.ir ≫ φ = g.r ≫ (bZ.inr ≫ ψ) := by
      calc
        Y.ir ≫ φ = (bY.inr ≫ bY.toCenter) ≫ φ :=
          congrArg (fun t => t ≫ φ) bY.inr_toCenter.symm
        _ = bY.inr ≫ (bY.toCenter ≫ φ) := by simp [Category.assoc]
        _ = bY.inr ≫ (a ≫ ψ) := congrArg (fun t => bY.inr ≫ t) hφψ
        _ = (bY.inr ≫ a) ≫ ψ := by simp [Category.assoc]
        _ = (g.r ≫ bZ.inr) ≫ ψ := congrArg (fun t => t ≫ ψ) haR
        _ = g.r ≫ (bZ.inr ≫ ψ) := by simp [Category.assoc]
    let dP : G.P ⟶ T := G.pushout₁.desc φ (bZ.inl ≫ ψ) hYlCompat
    have hdPk : G.k ≫ dP = φ := G.pushout₁.inl_desc φ (bZ.inl ≫ ψ) hYlCompat
    have hdPj : G.j ≫ dP = bZ.inl ≫ ψ :=
      G.pushout₁.inr_desc φ (bZ.inl ≫ ψ) hYlCompat
    have hQCompat : (Y.ir ≫ G.k) ≫ dP = g.r ≫ (bZ.inr ≫ ψ) := by
      calc
        (Y.ir ≫ G.k) ≫ dP = Y.ir ≫ (G.k ≫ dP) := Category.assoc _ _ _
        _ = Y.ir ≫ φ := congrArg (fun t => Y.ir ≫ t) hdPk
        _ = g.r ≫ (bZ.inr ≫ ψ) := hYrCompat
    let dQ : G.Q ⟶ T := G.pushout₂.desc dP (bZ.inr ≫ ψ) hQCompat
    have hdQp : G.k₂ ≫ dQ = dP := G.pushout₂.inl_desc dP _ hQCompat
    have hdQr : G.j₂ ≫ dQ = bZ.inr ≫ ψ := G.pushout₂.inr_desc dP _ hQCompat
    have hdM : mY ≫ dQ = φ := by
      dsimp [mY]
      calc
        (G.k ≫ G.k₂) ≫ dQ = G.k ≫ (G.k₂ ≫ dQ) := Category.assoc _ _ _
        _ = G.k ≫ dP := congrArg (fun t => G.k ≫ t) hdQp
        _ = φ := hdPk
    have hdBoundary : pZ ≫ dQ = ψ := by
      apply bZ.isPushout.hom_ext
      · calc
          bZ.inl ≫ pZ ≫ dQ = (bZ.inl ≫ pZ) ≫ dQ := (Category.assoc _ _ _).symm
          _ = (G.j ≫ G.k₂) ≫ dQ := congrArg (fun t => t ≫ dQ) hpZL
          _ = G.j ≫ (G.k₂ ≫ dQ) := Category.assoc _ _ _
          _ = G.j ≫ dP := congrArg (fun t => G.j ≫ t) hdQp
          _ = bZ.inl ≫ ψ := hdPj
      · calc
          bZ.inr ≫ pZ ≫ dQ = (bZ.inr ≫ pZ) ≫ dQ := (Category.assoc _ _ _).symm
          _ = G.j₂ ≫ dQ := congrArg (fun t => t ≫ dQ) hpZR
          _ = bZ.inr ≫ ψ := hdQr
    exact ⟨dQ, hdM, hdBoundary⟩

private theorem pathObj_cof_comp {X Y Z : PathObj C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : cofibrations (PathObj C) f) (hg : cofibrations (PathObj C) g) :
    cofibrations (PathObj C) (f ≫ g) := by
  classical
  let F := pathObjCofibrationData f hf
  let G := pathObjCofibrationData g hg
  have hflgL : cofibrations C (f.l ≫ g.l) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ F.left_mem G.left_mem
  have hflgR : cofibrations C (f.r ≫ g.r) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ F.right_mem G.right_mem
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let bY := pathBoundaryData hI Y
  let bZ := pathBoundaryData hI Z
  obtain ⟨a, haL, haR, haCof⟩ :=
    pathBoundaryMap_cof hI g G.left_mem G.right_mem bY bZ
  letI : HasPushout g.l F.j := hC.hasPushout g.l F.j G.left_mem
  let Pₕ := pushout g.l F.j
  let aP : F.P ⟶ Pₕ := pushout.inr g.l F.j
  let bP : Z.l ⟶ Pₕ := pushout.inl g.l F.j
  have hAddL : IsPushout F.j g.l aP bP :=
    (IsPushout.of_hasPushout g.l F.j).flip
  have hPₕ : IsPushout X.il (f.l ≫ g.l) (F.k ≫ aP) bP :=
    F.pushout₁.paste_vert hAddL
  let kₕ : X.c ⟶ Pₕ := F.k ≫ aP
  have hmₕCompat : F.j ≫ (F.m ≫ g.c) = g.l ≫ Z.il := by
    calc
      F.j ≫ (F.m ≫ g.c) = (F.j ≫ F.m) ≫ g.c := (Category.assoc _ _ _).symm
      _ = Y.il ≫ g.c := congrArg (fun t => t ≫ g.c) F.jm
      _ = g.l ≫ Z.il := g.il_c
  let mₕ : Pₕ ⟶ Z.c := hAddL.desc (F.m ≫ g.c) Z.il hmₕCompat
  have haPmₕ : aP ≫ mₕ = F.m ≫ g.c :=
    hAddL.inl_desc (F.m ≫ g.c) Z.il hmₕCompat
  have hbPmₕ : bP ≫ mₕ = Z.il :=
    hAddL.inr_desc (F.m ≫ g.c) Z.il hmₕCompat
  have hkₕmₕ : kₕ ≫ mₕ = f.c ≫ g.c := by
    calc
      kₕ ≫ mₕ = F.k ≫ (aP ≫ mₕ) := by simp [kₕ, Category.assoc]
      _ = F.k ≫ (F.m ≫ g.c) := congrArg (fun t => F.k ≫ t) haPmₕ
      _ = (F.k ≫ F.m) ≫ g.c := (Category.assoc _ _ _).symm
      _ = f.c ≫ g.c := congrArg (fun t => t ≫ g.c) F.km
  let qYl : Y.l ⟶ F.Q := F.j ≫ F.k₂
  let qYr : Y.r ⟶ F.Q := F.j₂
  let pF : bY.P ⟶ F.Q := bY.isPushout.desc qYl qYr (hI.hom_ext _ _)
  have hpFYl : bY.inl ≫ pF = qYl := bY.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have hpFYr : bY.inr ≫ pF = qYr := bY.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  letI : HasPushout a pF := hC.hasPushout a pF haCof
  let Qₕ := pushout a pF
  let qZ : bZ.P ⟶ Qₕ := pushout.inl a pF
  let qF : F.Q ⟶ Qₕ := pushout.inr a pF
  have hQₕBase : IsPushout a pF qZ qF := IsPushout.of_hasPushout a pF
  have hYlToQ : qYl ≫ qF = g.l ≫ (bZ.inl ≫ qZ) := by
    calc
      qYl ≫ qF = (bY.inl ≫ pF) ≫ qF := congrArg (fun t => t ≫ qF) hpFYl.symm
      _ = bY.inl ≫ (pF ≫ qF) := Category.assoc _ _ _
      _ = bY.inl ≫ (a ≫ qZ) := congrArg (fun t => bY.inl ≫ t) hQₕBase.w.symm
      _ = (bY.inl ≫ a) ≫ qZ := (Category.assoc _ _ _).symm
      _ = (g.l ≫ bZ.inl) ≫ qZ := congrArg (fun t => t ≫ qZ) haL
      _ = g.l ≫ (bZ.inl ≫ qZ) := Category.assoc _ _ _
  have hYrToQ : qYr ≫ qF = g.r ≫ (bZ.inr ≫ qZ) := by
    calc
      qYr ≫ qF = (bY.inr ≫ pF) ≫ qF := congrArg (fun t => t ≫ qF) hpFYr.symm
      _ = bY.inr ≫ (pF ≫ qF) := Category.assoc _ _ _
      _ = bY.inr ≫ (a ≫ qZ) := congrArg (fun t => bY.inr ≫ t) hQₕBase.w.symm
      _ = (bY.inr ≫ a) ≫ qZ := (Category.assoc _ _ _).symm
      _ = (g.r ≫ bZ.inr) ≫ qZ := congrArg (fun t => t ≫ qZ) haR
      _ = g.r ≫ (bZ.inr ≫ qZ) := Category.assoc _ _ _
  have hPₕQCompat : F.j ≫ (F.k₂ ≫ qF) = g.l ≫ (bZ.inl ≫ qZ) := by
    simpa [qYl, Category.assoc] using hYlToQ
  let pₕ : Pₕ ⟶ Qₕ := hAddL.desc (F.k₂ ≫ qF) (bZ.inl ≫ qZ) hPₕQCompat
  have hpₕP : aP ≫ pₕ = F.k₂ ≫ qF :=
    hAddL.inl_desc (F.k₂ ≫ qF) (bZ.inl ≫ qZ) hPₕQCompat
  have hpₕZl : bP ≫ pₕ = bZ.inl ≫ qZ :=
    hAddL.inr_desc (F.k₂ ≫ qF) (bZ.inl ≫ qZ) hPₕQCompat
  let qZr : Z.r ⟶ Qₕ := bZ.inr ≫ qZ
  have hTotalCompat : (X.ir ≫ kₕ) ≫ pₕ = (f.r ≫ g.r) ≫ qZr := by
    calc
      (X.ir ≫ kₕ) ≫ pₕ = (X.ir ≫ F.k ≫ F.k₂) ≫ qF := by
        simp [kₕ, Category.assoc, hpₕP]
      _ = ((X.ir ≫ F.k) ≫ F.k₂) ≫ qF := by simp [Category.assoc]
      _ = (f.r ≫ F.j₂) ≫ qF := congrArg (fun t => t ≫ qF) F.pushout₂.w
      _ = f.r ≫ (qYr ≫ qF) := Category.assoc _ _ _
      _ = f.r ≫ (g.r ≫ qZr) := by
        simpa [qYr, qZr, Category.assoc] using congrArg (fun t => f.r ≫ t) hYrToQ
      _ = (f.r ≫ g.r) ≫ qZr := (Category.assoc _ _ _).symm
  have hTotal : IsPushout (X.ir ≫ kₕ) (f.r ≫ g.r) pₕ qZr := by
    apply IsPushout.mk'
    · exact hTotalCompat
    · intro T φ ψ hφ hψ
      have hZQ : qZ ≫ φ = qZ ≫ ψ := by
        apply bZ.isPushout.hom_ext
        · calc
            bZ.inl ≫ qZ ≫ φ = bP ≫ pₕ ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hpₕZl.symm
            _ = bP ≫ pₕ ≫ ψ := congrArg (fun t => bP ≫ t) hφ
            _ = bZ.inl ≫ qZ ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hpₕZl
        · calc
            bZ.inr ≫ qZ ≫ φ = qZr ≫ φ := by simpa [qZr, Category.assoc]
            _ = qZr ≫ ψ := hψ
            _ = bZ.inr ≫ qZ ≫ ψ := by simpa [qZr, Category.assoc]
      have hFQ : qF ≫ φ = qF ≫ ψ := by
        apply F.pushout₂.hom_ext
        · calc
            F.k₂ ≫ qF ≫ φ = aP ≫ pₕ ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hpₕP.symm
            _ = aP ≫ pₕ ≫ ψ := congrArg (fun t => aP ≫ t) hφ
            _ = F.k₂ ≫ qF ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hpₕP
        · calc
            F.j₂ ≫ qF ≫ φ = g.r ≫ qZr ≫ φ := by
              simpa [qYr, qZr, Category.assoc] using congrArg (fun t => t ≫ φ) hYrToQ
            _ = g.r ≫ qZr ≫ ψ := congrArg (fun t => g.r ≫ t) hψ
            _ = F.j₂ ≫ qF ≫ ψ := by
              simpa [qYr, qZr, Category.assoc] using congrArg (fun t => t ≫ ψ) hYrToQ.symm
      exact hQₕBase.hom_ext hZQ hFQ
    · intro T φ ψ hφψ
      let dZ : bZ.P ⟶ T := bZ.isPushout.desc (bP ≫ φ) ψ (hI.hom_ext _ _)
      have hdZl : bZ.inl ≫ dZ = bP ≫ φ := bZ.isPushout.inl_desc _ _ (hI.hom_ext _ _)
      have hdZr : bZ.inr ≫ dZ = ψ := bZ.isPushout.inr_desc _ _ (hI.hom_ext _ _)
      have hFCompat : (X.ir ≫ F.k) ≫ (aP ≫ φ) = f.r ≫ (g.r ≫ ψ) := by
        calc
          (X.ir ≫ F.k) ≫ (aP ≫ φ) = (X.ir ≫ kₕ) ≫ φ := by simp [kₕ, Category.assoc]
          _ = (f.r ≫ g.r) ≫ ψ := hφψ
          _ = f.r ≫ (g.r ≫ ψ) := Category.assoc _ _ _
      let dF : F.Q ⟶ T := F.pushout₂.desc (aP ≫ φ) (g.r ≫ ψ) hFCompat
      have hdFk : F.k₂ ≫ dF = aP ≫ φ :=
        F.pushout₂.inl_desc (aP ≫ φ) (g.r ≫ ψ) hFCompat
      have hdFj : F.j₂ ≫ dF = g.r ≫ ψ :=
        F.pushout₂.inr_desc (aP ≫ φ) (g.r ≫ ψ) hFCompat
      have hBoundaryCompat : a ≫ dZ = pF ≫ dF := by
        apply bY.isPushout.hom_ext
        · calc
            bY.inl ≫ a ≫ dZ = (g.l ≫ bZ.inl) ≫ dZ := by
              calc
                bY.inl ≫ a ≫ dZ = (bY.inl ≫ a) ≫ dZ := (Category.assoc _ _ _).symm
                _ = (g.l ≫ bZ.inl) ≫ dZ := congrArg (fun t => t ≫ dZ) haL
            _ = g.l ≫ (bP ≫ φ) := by
              simpa [Category.assoc] using congrArg (fun t => g.l ≫ t) hdZl
            _ = (F.j ≫ aP) ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hAddL.w.symm
            _ = F.j ≫ (aP ≫ φ) := Category.assoc _ _ _
            _ = F.j ≫ (F.k₂ ≫ dF) := congrArg (fun t => F.j ≫ t) hdFk.symm
            _ = (F.j ≫ F.k₂) ≫ dF := (Category.assoc _ _ _).symm
            _ = (bY.inl ≫ pF) ≫ dF := congrArg (fun t => t ≫ dF) hpFYl.symm
            _ = bY.inl ≫ pF ≫ dF := Category.assoc _ _ _
        · calc
            bY.inr ≫ a ≫ dZ = (g.r ≫ bZ.inr) ≫ dZ := by
              calc
                bY.inr ≫ a ≫ dZ = (bY.inr ≫ a) ≫ dZ := (Category.assoc _ _ _).symm
                _ = (g.r ≫ bZ.inr) ≫ dZ := congrArg (fun t => t ≫ dZ) haR
            _ = g.r ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => g.r ≫ t) hdZr
            _ = F.j₂ ≫ dF := hdFj.symm
            _ = (bY.inr ≫ pF) ≫ dF := congrArg (fun t => t ≫ dF) hpFYr.symm
            _ = bY.inr ≫ pF ≫ dF := Category.assoc _ _ _
      let dH : Qₕ ⟶ T := hQₕBase.desc dZ dF hBoundaryCompat
      have hdHZ : qZ ≫ dH = dZ := hQₕBase.inl_desc dZ dF hBoundaryCompat
      have hdHF : qF ≫ dH = dF := hQₕBase.inr_desc dZ dF hBoundaryCompat
      have hdPₕ : pₕ ≫ dH = φ := by
        apply hAddL.hom_ext
        · calc
            aP ≫ pₕ ≫ dH = F.k₂ ≫ qF ≫ dH := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ dH) hpₕP
            _ = F.k₂ ≫ dF := congrArg (fun t => F.k₂ ≫ t) hdHF
            _ = aP ≫ φ := hdFk
        · calc
            bP ≫ pₕ ≫ dH = bZ.inl ≫ qZ ≫ dH := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ dH) hpₕZl
            _ = bZ.inl ≫ dZ := congrArg (fun t => bZ.inl ≫ t) hdHZ
            _ = bP ≫ φ := hdZl
      have hdZrH : qZr ≫ dH = ψ := by
        calc
          qZr ≫ dH = (bZ.inr ≫ qZ) ≫ dH := rfl
          _ = bZ.inr ≫ dZ := by
            calc
              (bZ.inr ≫ qZ) ≫ dH = bZ.inr ≫ (qZ ≫ dH) := Category.assoc _ _ _
              _ = bZ.inr ≫ dZ := congrArg (fun t => bZ.inr ≫ t) hdHZ
          _ = ψ := hdZr
      exact ⟨dH, hdPₕ, hdZrH⟩
  let mYg : Y.c ⟶ G.Q := G.k ≫ G.k₂
  let pZg : bZ.P ⟶ G.Q :=
    bZ.isPushout.desc (G.j ≫ G.k₂) G.j₂ (hI.hom_ext _ _)
  have hpZgL : bZ.inl ≫ pZg = G.j ≫ G.k₂ :=
    bZ.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have hpZgR : bZ.inr ≫ pZg = G.j₂ :=
    bZ.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  have hGBoundary : IsPushout bY.toCenter a mYg pZg :=
    pathObj_cofBoundaryPushout hI g G bY bZ a haL haR
  letI : HasPushout F.n qF := hC.hasPushout F.n qF F.n_mem
  let S := pushout F.n qF
  let mYS : Y.c ⟶ S := pushout.inl F.n qF
  let qHS : Qₕ ⟶ S := pushout.inr F.n qF
  have hNf : IsPushout F.n qF mYS qHS := IsPushout.of_hasPushout F.n qF
  have hqHS_mem : cofibrations C qHS :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hNf.flip F.n_mem
  have hpFnF : pF ≫ F.n = bY.toCenter := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ pF ≫ F.n = (bY.inl ≫ pF) ≫ F.n := (Category.assoc _ _ _).symm
        _ = qYl ≫ F.n := congrArg (fun t => t ≫ F.n) hpFYl
        _ = F.j ≫ (F.k₂ ≫ F.n) := by simp [qYl, Category.assoc]
        _ = F.j ≫ F.m := congrArg (fun t => F.j ≫ t) F.k₂n
        _ = Y.il := F.jm
        _ = bY.inl ≫ bY.toCenter := bY.inl_toCenter.symm
    · calc
        bY.inr ≫ pF ≫ F.n = (bY.inr ≫ pF) ≫ F.n := (Category.assoc _ _ _).symm
        _ = qYr ≫ F.n := congrArg (fun t => t ≫ F.n) hpFYr
        _ = Y.ir := F.j₂n
        _ = bY.inr ≫ bY.toCenter := bY.inr_toCenter.symm
  have hSRaw : IsPushout (pF ≫ F.n) a mYS (qZ ≫ qHS) :=
    hQₕBase.flip.paste_horiz hNf
  have hSBoundary : IsPushout bY.toCenter a mYS (qZ ≫ qHS) := by
    simpa [hpFnF] using hSRaw
  have hBg : bY.toCenter ≫ g.c = a ≫ bZ.toCenter := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ bY.toCenter ≫ g.c = (bY.inl ≫ bY.toCenter) ≫ g.c := by
          simp [Category.assoc]
        _ = Y.il ≫ g.c := congrArg (fun t => t ≫ g.c) bY.inl_toCenter
        _ = g.l ≫ Z.il := g.il_c
        _ = g.l ≫ (bZ.inl ≫ bZ.toCenter) :=
          congrArg (fun t => g.l ≫ t) bZ.inl_toCenter.symm
        _ = (g.l ≫ bZ.inl) ≫ bZ.toCenter := (Category.assoc _ _ _).symm
        _ = (bY.inl ≫ a) ≫ bZ.toCenter :=
          congrArg (fun t => t ≫ bZ.toCenter) haL.symm
        _ = bY.inl ≫ (a ≫ bZ.toCenter) := Category.assoc _ _ _
    · calc
        bY.inr ≫ bY.toCenter ≫ g.c = (bY.inr ≫ bY.toCenter) ≫ g.c := by
          simp [Category.assoc]
        _ = Y.ir ≫ g.c := congrArg (fun t => t ≫ g.c) bY.inr_toCenter
        _ = g.r ≫ Z.ir := g.ir_c
        _ = g.r ≫ (bZ.inr ≫ bZ.toCenter) :=
          congrArg (fun t => g.r ≫ t) bZ.inr_toCenter.symm
        _ = (g.r ≫ bZ.inr) ≫ bZ.toCenter := (Category.assoc _ _ _).symm
        _ = (bY.inr ≫ a) ≫ bZ.toCenter :=
          congrArg (fun t => t ≫ bZ.toCenter) haR.symm
        _ = bY.inr ≫ (a ≫ bZ.toCenter) := Category.assoc _ _ _
  let mS : S ⟶ Z.c := hSBoundary.desc g.c bZ.toCenter hBg
  have hmSY : mYS ≫ mS = g.c := hSBoundary.inl_desc g.c bZ.toCenter hBg
  have hmSPZ : (qZ ≫ qHS) ≫ mS = bZ.toCenter :=
    hSBoundary.inr_desc g.c bZ.toCenter hBg
  let eS : S ≅ G.Q := hSBoundary.isColimit.coconePointUniqueUpToIso hGBoundary.isColimit
  have heSY : mYS ≫ eS.hom = mYg := by
    dsimp [eS]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hSBoundary.isColimit hGBoundary.isColimit WalkingSpan.left
  have heSPZ : (qZ ≫ qHS) ≫ eS.hom = pZg := by
    change (qZ ≫ qHS) ≫
      (hSBoundary.isColimit.coconePointUniqueUpToIso hGBoundary.isColimit).hom = pZg
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hSBoundary.isColimit hGBoundary.isColimit WalkingSpan.right
  have hpZgN : pZg ≫ G.n = bZ.toCenter := by
    apply bZ.isPushout.hom_ext
    · calc
        bZ.inl ≫ pZg ≫ G.n = (bZ.inl ≫ pZg) ≫ G.n := (Category.assoc _ _ _).symm
        _ = (G.j ≫ G.k₂) ≫ G.n := congrArg (fun t => t ≫ G.n) hpZgL
        _ = G.j ≫ (G.k₂ ≫ G.n) := Category.assoc _ _ _
        _ = G.j ≫ G.m := congrArg (fun t => G.j ≫ t) G.k₂n
        _ = Z.il := G.jm
        _ = bZ.inl ≫ bZ.toCenter := bZ.inl_toCenter.symm
    · calc
        bZ.inr ≫ pZg ≫ G.n = (bZ.inr ≫ pZg) ≫ G.n := (Category.assoc _ _ _).symm
        _ = G.j₂ ≫ G.n := congrArg (fun t => t ≫ G.n) hpZgR
        _ = Z.ir := G.j₂n
        _ = bZ.inr ≫ bZ.toCenter := bZ.inr_toCenter.symm
  have hfactorS : mS = eS.hom ≫ G.n := by
    apply hSBoundary.hom_ext
    · calc
        mYS ≫ mS = g.c := hmSY
        _ = mYg ≫ G.n := by
          calc
            g.c = G.k ≫ G.m := G.km.symm
            _ = G.k ≫ (G.k₂ ≫ G.n) := congrArg (fun t => G.k ≫ t) G.k₂n.symm
            _ = mYg ≫ G.n := by simp [mYg, Category.assoc]
        _ = mYS ≫ eS.hom ≫ G.n := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ G.n) heSY.symm
    · calc
        (qZ ≫ qHS) ≫ mS = bZ.toCenter := hmSPZ
        _ = pZg ≫ G.n := hpZgN.symm
        _ = (qZ ≫ qHS) ≫ eS.hom ≫ G.n := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ G.n) heSPZ.symm
  have hmS_mem : cofibrations C mS := by
    rw [hfactorS]
    exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _
      (hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance)) G.n_mem
  have hnH_mem : cofibrations C (qHS ≫ mS) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hqHS_mem hmS_mem
  let nH : Qₕ ⟶ Z.c := qHS ≫ mS
  have hpHnH : pₕ ≫ nH = mₕ := by
    apply hAddL.hom_ext
    · calc
        aP ≫ pₕ ≫ nH = (aP ≫ pₕ) ≫ qHS ≫ mS := by simp [nH, Category.assoc]
        _ = (F.k₂ ≫ qF) ≫ qHS ≫ mS := congrArg (fun t => t ≫ qHS ≫ mS) hpₕP
        _ = F.k₂ ≫ F.n ≫ mYS ≫ mS := by
          calc
            (F.k₂ ≫ qF) ≫ qHS ≫ mS = F.k₂ ≫ ((qF ≫ qHS) ≫ mS) := by
              simp [Category.assoc]
            _ = F.k₂ ≫ ((F.n ≫ mYS) ≫ mS) :=
              congrArg (fun t => F.k₂ ≫ t)
                (congrArg (fun t => t ≫ mS) hNf.w.symm)
            _ = F.k₂ ≫ F.n ≫ mYS ≫ mS := by simp [Category.assoc]
        _ = F.k₂ ≫ F.n ≫ g.c := by
          simpa [Category.assoc] using congrArg (fun t => F.k₂ ≫ F.n ≫ t) hmSY
        _ = F.m ≫ g.c := by simpa [Category.assoc] using congrArg (fun t => t ≫ g.c) F.k₂n
        _ = aP ≫ mₕ := haPmₕ.symm
    · calc
        bP ≫ pₕ ≫ nH = (bP ≫ pₕ) ≫ qHS ≫ mS := by simp [nH, Category.assoc]
        _ = (bZ.inl ≫ qZ) ≫ qHS ≫ mS := congrArg (fun t => t ≫ qHS ≫ mS) hpₕZl
        _ = bZ.inl ≫ ((qZ ≫ qHS) ≫ mS) := by simp [Category.assoc]
        _ = bZ.inl ≫ bZ.toCenter := congrArg (fun t => bZ.inl ≫ t) hmSPZ
        _ = Z.il := bZ.inl_toCenter
        _ = bP ≫ mₕ := hbPmₕ.symm
  have hqZrnH : qZr ≫ nH = Z.ir := by
    dsimp [nH, qZr]
    calc
      (bZ.inr ≫ qZ) ≫ (qHS ≫ mS) = bZ.inr ≫ ((qZ ≫ qHS) ≫ mS) := by
        simp [Category.assoc]
      _ = bZ.inr ≫ bZ.toCenter := congrArg (fun t => bZ.inr ≫ t) hmSPZ
      _ = Z.ir := bZ.inr_toCenter
  have hCompGlue : IsCofibrantGluing (X.ir ≫ kₕ) (f.r ≫ g.r) mₕ Z.ir :=
    ⟨Qₕ, pₕ, qZr, hTotal, nH, hpHnH, hqZrnH, hnH_mem⟩
  refine ⟨hflgL, hflgR, Pₕ, kₕ, bP, hPₕ, mₕ, hkₕmₕ, hbPmₕ, hCompGlue⟩

private structure PathObjPushoutData {X Y Z : PathObj C} (f : X ⟶ Y) (g : X ⟶ Z) where
  obj : PathObj C
  inl : Y ⟶ obj
  inr : Z ⟶ obj
  left_isPushout : IsPushout f.l g.l inl.l inr.l
  right_isPushout : IsPushout f.r g.r inl.r inr.r
  center_isPushout : IsPushout f.c g.c inl.c inr.c
  isPushout : IsPushout f g inl inr
  inr_mem : cofibrations (PathObj C) inr

private noncomputable def pathObj_pushout_object {X Y Z : PathObj C}
    (f : X ⟶ Y) (g : X ⟶ Z) (hf : cofibrations (PathObj C) f) : PathObjPushoutData f g := by
  classical
  have hfc := pathObj_cof_middle f hf
  let reedy := pathObjCofibrationData f hf
  let P := reedy.P
  let k := reedy.k
  let j := reedy.j
  let hP := reedy.pushout₁
  let m := reedy.m
  let hkm := reedy.km
  let hjm := reedy.jm
  let Q := reedy.Q
  let k₂ := reedy.k₂
  let j₂ := reedy.j₂
  let hQ := reedy.pushout₂
  let n := reedy.n
  let hk₂n := reedy.k₂n
  let hj₂n := reedy.j₂n
  let hnCof := reedy.n_mem
  letI : HasPushout f.l g.l := hC.hasPushout f.l g.l hf.1
  letI : HasPushout f.r g.r := hC.hasPushout f.r g.r hf.2.1
  letI : HasPushout f.c g.c := hC.hasPushout f.c g.c hfc
  let Wl := pushout f.l g.l
  let Wr := pushout f.r g.r
  let hL : IsPushout f.l g.l (pushout.inl f.l g.l) (pushout.inr f.l g.l) :=
    IsPushout.of_hasPushout f.l g.l
  let hR : IsPushout f.r g.r (pushout.inl f.r g.r) (pushout.inr f.r g.r) :=
    IsPushout.of_hasPushout f.r g.r
  let hCof : IsPushout f.c g.c (pushout.inl f.c g.c) (pushout.inr f.c g.c) :=
    IsPushout.of_hasPushout f.c g.c
  let I : C := Classical.choose hC.exists_initial
  have hInonempty : Nonempty (IsInitial I) := Classical.choose_spec hC.exists_initial
  let hI : IsInitial I := Classical.choice hInonempty
  let bX := pathBoundaryData hI X
  let bY := pathBoundaryData hI Y
  let bZ := pathBoundaryData hI Z
  letI : HasPushout (hI.to Wl) (hI.to Wr) := hC.hasPushout (hI.to Wl) (hI.to Wr)
    (hC.initial_cofibration hI Wl)
  let PW := pushout (hI.to Wl) (hI.to Wr)
  let wL : Wl ⟶ PW := pushout.inl (hI.to Wl) (hI.to Wr)
  let wR : Wr ⟶ PW := pushout.inr (hI.to Wl) (hI.to Wr)
  have hPW : IsPushout (hI.to Wl) (hI.to Wr) wL wR := IsPushout.of_hasPushout _ _
  let a : bX.P ⟶ bY.P := bX.isPushout.desc (f.l ≫ bY.inl) (f.r ≫ bY.inr)
    (hI.hom_ext _ _)
  let b : bX.P ⟶ bZ.P := bX.isPushout.desc (g.l ≫ bZ.inl) (g.r ≫ bZ.inr)
    (hI.hom_ext _ _)
  have haL : bX.inl ≫ a = f.l ≫ bY.inl :=
    bX.isPushout.inl_desc (f.l ≫ bY.inl) (f.r ≫ bY.inr) (hI.hom_ext _ _)
  have haR : bX.inr ≫ a = f.r ≫ bY.inr :=
    bX.isPushout.inr_desc (f.l ≫ bY.inl) (f.r ≫ bY.inr) (hI.hom_ext _ _)
  have hbL : bX.inl ≫ b = g.l ≫ bZ.inl :=
    bX.isPushout.inl_desc (g.l ≫ bZ.inl) (g.r ≫ bZ.inr) (hI.hom_ext _ _)
  have hbR : bX.inr ≫ b = g.r ≫ bZ.inr :=
    bX.isPushout.inr_desc (g.l ≫ bZ.inl) (g.r ≫ bZ.inr) (hI.hom_ext _ _)
  let pY : bY.P ⟶ PW := bY.isPushout.desc
    (pushout.inl f.l g.l ≫ wL) (pushout.inl f.r g.r ≫ wR) (hI.hom_ext _ _)
  let pZ : bZ.P ⟶ PW := bZ.isPushout.desc
    (pushout.inr f.l g.l ≫ wL) (pushout.inr f.r g.r ≫ wR) (hI.hom_ext _ _)
  have hpYL : bY.inl ≫ pY = pushout.inl f.l g.l ≫ wL :=
    bY.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have hpYR : bY.inr ≫ pY = pushout.inl f.r g.r ≫ wR :=
    bY.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  have hpZL : bZ.inl ≫ pZ = pushout.inr f.l g.l ≫ wL :=
    bZ.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have hpZR : bZ.inr ≫ pZ = pushout.inr f.r g.r ≫ wR :=
    bZ.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  have hBoundary : IsPushout a b pY pZ :=
    boundary_cobasePushout hI bX.isPushout bY.isPushout bZ.isPushout hPW hL hR
      (a := a) (b := b) (pY := pY) (pZ := pZ) haL haR hbL hbR
      hpYL hpYR hpZL hpZR
  have hspanL : f.l ≫ bY.inl ≫ pY = g.l ≫ bZ.inl ≫ pZ := by
    calc
      f.l ≫ bY.inl ≫ pY = (f.l ≫ bY.inl) ≫ pY := (Category.assoc _ _ _).symm
      _ = (bX.inl ≫ a) ≫ pY := congrArg (fun t => t ≫ pY) haL.symm
      _ = bX.inl ≫ (a ≫ pY) := Category.assoc _ _ _
      _ = bX.inl ≫ (b ≫ pZ) := congrArg (fun t => bX.inl ≫ t) hBoundary.w
      _ = (bX.inl ≫ b) ≫ pZ := (Category.assoc _ _ _).symm
      _ = (g.l ≫ bZ.inl) ≫ pZ := congrArg (fun t => t ≫ pZ) hbL
      _ = g.l ≫ bZ.inl ≫ pZ := Category.assoc _ _ _
  have hspanR : f.r ≫ bY.inr ≫ pY = g.r ≫ bZ.inr ≫ pZ := by
    calc
      f.r ≫ bY.inr ≫ pY = (f.r ≫ bY.inr) ≫ pY := (Category.assoc _ _ _).symm
      _ = (bX.inr ≫ a) ≫ pY := congrArg (fun t => t ≫ pY) haR.symm
      _ = bX.inr ≫ (a ≫ pY) := Category.assoc _ _ _
      _ = bX.inr ≫ (b ≫ pZ) := congrArg (fun t => bX.inr ≫ t) hBoundary.w
      _ = (bX.inr ≫ b) ≫ pZ := (Category.assoc _ _ _).symm
      _ = (g.r ≫ bZ.inr) ≫ pZ := congrArg (fun t => t ≫ pZ) hbR
      _ = g.r ≫ bZ.inr ≫ pZ := Category.assoc _ _ _
  letI : HasPushout bZ.toCenter pZ := hC.hasPushout bZ.toCenter pZ bZ.toCenter_mem
  let V := pushout bZ.toCenter pZ
  let vZ : Z.c ⟶ V := pushout.inl bZ.toCenter pZ
  let vB : PW ⟶ V := pushout.inr bZ.toCenter pZ
  have hV : IsPushout bZ.toCenter pZ vZ vB := IsPushout.of_hasPushout _ _
  have hPCompat : X.il ≫ (g.c ≫ vZ) = f.l ≫ (bY.inl ≫ pY ≫ vB) := by
    calc
      X.il ≫ (g.c ≫ vZ) = (X.il ≫ g.c) ≫ vZ := (Category.assoc _ _ _).symm
      _ = (g.l ≫ Z.il) ≫ vZ := congrArg (fun t => t ≫ vZ) g.il_c
      _ = g.l ≫ (Z.il ≫ vZ) := Category.assoc _ _ _
      _ = g.l ≫ (bZ.inl ≫ (bZ.toCenter ≫ vZ)) := by
        rw [← bZ.inl_toCenter]
        simp [Category.assoc]
      _ = g.l ≫ (bZ.inl ≫ (pZ ≫ vB)) := congrArg (fun t => g.l ≫ (bZ.inl ≫ t)) hV.w
      _ = (g.l ≫ bZ.inl ≫ pZ) ≫ vB := by simp [Category.assoc]
      _ = f.l ≫ (bY.inl ≫ pY ≫ vB) := by
        simpa [Category.assoc] using congrArg (fun t => t ≫ vB) hspanL.symm
  let eP : P ⟶ V := hP.desc (g.c ≫ vZ) (bY.inl ≫ pY ≫ vB) hPCompat
  have hQCompat : (X.ir ≫ k) ≫ eP = f.r ≫ (bY.inr ≫ pY ≫ vB) := by
    calc
      (X.ir ≫ k) ≫ eP = X.ir ≫ (k ≫ eP) := Category.assoc _ _ _
      _ = X.ir ≫ (g.c ≫ vZ) := congrArg (fun t => X.ir ≫ t) (hP.inl_desc _ _ hPCompat)
      _ = (X.ir ≫ g.c) ≫ vZ := (Category.assoc _ _ _).symm
      _ = (g.r ≫ Z.ir) ≫ vZ := congrArg (fun t => t ≫ vZ) g.ir_c
      _ = g.r ≫ (Z.ir ≫ vZ) := Category.assoc _ _ _
      _ = g.r ≫ (bZ.inr ≫ (bZ.toCenter ≫ vZ)) := by
        rw [← bZ.inr_toCenter]
        simp [Category.assoc]
      _ = g.r ≫ (bZ.inr ≫ (pZ ≫ vB)) := congrArg (fun t => g.r ≫ (bZ.inr ≫ t)) hV.w
      _ = (g.r ≫ bZ.inr ≫ pZ) ≫ vB := by simp [Category.assoc]
      _ = f.r ≫ (bY.inr ≫ pY ≫ vB) := by
        simpa [Category.assoc] using congrArg (fun t => t ≫ vB) hspanR.symm
  let qX : X.c ⟶ Q := k ≫ k₂
  let qYl : Y.l ⟶ Q := j ≫ k₂
  let qYr : Y.r ⟶ Q := j₂
  let eYr : Y.r ⟶ V := bY.inr ≫ pY ≫ vB
  let eQ : Q ⟶ V := hQ.desc eP eYr hQCompat
  have hqXe : qX ≫ eQ = g.c ≫ vZ := by
    dsimp [qX]
    calc
      (k ≫ k₂) ≫ eQ = k ≫ (k₂ ≫ eQ) := Category.assoc _ _ _
      _ = k ≫ eP := congrArg (fun t => k ≫ t) (hQ.inl_desc eP eYr hQCompat)
      _ = g.c ≫ vZ := hP.inl_desc (g.c ≫ vZ) (bY.inl ≫ pY ≫ vB) hPCompat
  have hqYle : qYl ≫ eQ = bY.inl ≫ pY ≫ vB := by
    dsimp [qYl]
    calc
      (j ≫ k₂) ≫ eQ = j ≫ (k₂ ≫ eQ) := Category.assoc _ _ _
      _ = j ≫ eP := congrArg (fun t => j ≫ t) (hQ.inl_desc eP eYr hQCompat)
      _ = bY.inl ≫ pY ≫ vB := hP.inr_desc (g.c ≫ vZ) (bY.inl ≫ pY ≫ vB) hPCompat
  have hqYre : qYr ≫ eQ = eYr := hQ.inr_desc eP eYr hQCompat
  have hqXn : qX ≫ n = f.c := by
    dsimp [qX]
    calc
      (k ≫ k₂) ≫ n = k ≫ (k₂ ≫ n) := Category.assoc _ _ _
      _ = k ≫ m := congrArg (fun t => k ≫ t) hk₂n
      _ = f.c := hkm
  have hqYln : qYl ≫ n = Y.il := by
    dsimp [qYl]
    calc
      (j ≫ k₂) ≫ n = j ≫ (k₂ ≫ n) := Category.assoc _ _ _
      _ = j ≫ m := congrArg (fun t => j ≫ t) hk₂n
      _ = Y.il := hjm
  have hqYrn : qYr ≫ n = Y.ir := hj₂n
  have hcompatL : f.l ≫ (Y.il ≫ pushout.inl f.c g.c) =
      g.l ≫ (Z.il ≫ pushout.inr f.c g.c) := by
    calc
      f.l ≫ (Y.il ≫ pushout.inl f.c g.c) = (f.l ≫ Y.il) ≫ pushout.inl f.c g.c := by
        simp [Category.assoc]
      _ = (X.il ≫ f.c) ≫ pushout.inl f.c g.c := by rw [← f.il_c]
      _ = X.il ≫ (f.c ≫ pushout.inl f.c g.c) := by simp [Category.assoc]
      _ = X.il ≫ (g.c ≫ pushout.inr f.c g.c) := by rw [pushout.condition]
      _ = (X.il ≫ g.c) ≫ pushout.inr f.c g.c := by simp [Category.assoc]
      _ = (g.l ≫ Z.il) ≫ pushout.inr f.c g.c := by rw [g.il_c]
      _ = g.l ≫ (Z.il ≫ pushout.inr f.c g.c) := by simp [Category.assoc]
  have hcompatR : f.r ≫ (Y.ir ≫ pushout.inl f.c g.c) =
      g.r ≫ (Z.ir ≫ pushout.inr f.c g.c) := by
    calc
      f.r ≫ (Y.ir ≫ pushout.inl f.c g.c) = (f.r ≫ Y.ir) ≫ pushout.inl f.c g.c := by
        simp [Category.assoc]
      _ = (X.ir ≫ f.c) ≫ pushout.inl f.c g.c := by rw [← f.ir_c]
      _ = X.ir ≫ (f.c ≫ pushout.inl f.c g.c) := by simp [Category.assoc]
      _ = X.ir ≫ (g.c ≫ pushout.inr f.c g.c) := by rw [pushout.condition]
      _ = (X.ir ≫ g.c) ≫ pushout.inr f.c g.c := by simp [Category.assoc]
      _ = (g.r ≫ Z.ir) ≫ pushout.inr f.c g.c := by rw [g.ir_c]
      _ = g.r ≫ (Z.ir ≫ pushout.inr f.c g.c) := by simp [Category.assoc]
  let Wc := pushout f.c g.c
  let il : Wl ⟶ Wc := hL.desc (Y.il ≫ pushout.inl f.c g.c)
    (Z.il ≫ pushout.inr f.c g.c) hcompatL
  let ir : Wr ⟶ Wc := hR.desc (Y.ir ≫ pushout.inl f.c g.c)
    (Z.ir ≫ pushout.inr f.c g.c) hcompatR
  have hilL : pushout.inl f.l g.l ≫ il = Y.il ≫ pushout.inl f.c g.c := by
    simpa [il] using hL.inl_desc (Y.il ≫ pushout.inl f.c g.c)
      (Z.il ≫ pushout.inr f.c g.c) hcompatL
  have hilR : pushout.inr f.l g.l ≫ il = Z.il ≫ pushout.inr f.c g.c := by
    simpa [il] using hL.inr_desc (Y.il ≫ pushout.inl f.c g.c)
      (Z.il ≫ pushout.inr f.c g.c) hcompatL
  have hirL : pushout.inl f.r g.r ≫ ir = Y.ir ≫ pushout.inl f.c g.c := by
    simpa [ir] using hR.inl_desc (Y.ir ≫ pushout.inl f.c g.c)
      (Z.ir ≫ pushout.inr f.c g.c) hcompatR
  have hirR : pushout.inr f.r g.r ≫ ir = Z.ir ≫ pushout.inr f.c g.c := by
    simpa [ir] using hR.inr_desc (Y.ir ≫ pushout.inl f.c g.c)
      (Z.ir ≫ pushout.inr f.c g.c) hcompatR
  have hInitialW : hI.to Wl ≫ il = hI.to Wr ≫ ir := hI.hom_ext _ _
  let mW : PW ⟶ Wc := hPW.desc il ir hInitialW
  have hPZtoW : pZ ≫ mW = bZ.toCenter ≫ pushout.inr f.c g.c := by
    apply bZ.isPushout.hom_ext
    · calc
        bZ.inl ≫ pZ ≫ mW = (bZ.inl ≫ pZ) ≫ mW := (Category.assoc bZ.inl pZ mW).symm
        _ = (pushout.inr f.l g.l ≫ wL) ≫ mW := congrArg (fun t => t ≫ mW) hpZL
        _ = pushout.inr f.l g.l ≫ (wL ≫ mW) := Category.assoc _ _ _
        _ = pushout.inr f.l g.l ≫ il := congrArg (fun t => pushout.inr f.l g.l ≫ t)
          (hPW.inl_desc il ir hInitialW)
        _ = Z.il ≫ pushout.inr f.c g.c := hilR
        _ = (bZ.inl ≫ bZ.toCenter) ≫ pushout.inr f.c g.c :=
          congrArg (fun t => t ≫ pushout.inr f.c g.c) bZ.inl_toCenter.symm
        _ = bZ.inl ≫ (bZ.toCenter ≫ pushout.inr f.c g.c) := Category.assoc _ _ _
    · calc
        bZ.inr ≫ pZ ≫ mW = (bZ.inr ≫ pZ) ≫ mW := (Category.assoc bZ.inr pZ mW).symm
        _ = (pushout.inr f.r g.r ≫ wR) ≫ mW := congrArg (fun t => t ≫ mW) hpZR
        _ = pushout.inr f.r g.r ≫ (wR ≫ mW) := Category.assoc _ _ _
        _ = pushout.inr f.r g.r ≫ ir := congrArg (fun t => pushout.inr f.r g.r ≫ t)
          (hPW.inr_desc il ir hInitialW)
        _ = Z.ir ≫ pushout.inr f.c g.c := hirR
        _ = (bZ.inr ≫ bZ.toCenter) ≫ pushout.inr f.c g.c :=
          congrArg (fun t => t ≫ pushout.inr f.c g.c) bZ.inr_toCenter.symm
        _ = bZ.inr ≫ (bZ.toCenter ≫ pushout.inr f.c g.c) := Category.assoc _ _ _
  have hPYtoW : pY ≫ mW = bY.toCenter ≫ pushout.inl f.c g.c := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ pY ≫ mW = (bY.inl ≫ pY) ≫ mW := (Category.assoc _ _ _).symm
        _ = (pushout.inl f.l g.l ≫ wL) ≫ mW := congrArg (fun t => t ≫ mW) hpYL
        _ = pushout.inl f.l g.l ≫ (wL ≫ mW) := Category.assoc _ _ _
        _ = pushout.inl f.l g.l ≫ il := congrArg (fun t => pushout.inl f.l g.l ≫ t)
          (hPW.inl_desc il ir hInitialW)
        _ = Y.il ≫ pushout.inl f.c g.c := hilL
        _ = (bY.inl ≫ bY.toCenter) ≫ pushout.inl f.c g.c :=
          congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inl_toCenter.symm
        _ = bY.inl ≫ (bY.toCenter ≫ pushout.inl f.c g.c) := Category.assoc _ _ _
    · calc
        bY.inr ≫ pY ≫ mW = (bY.inr ≫ pY) ≫ mW := (Category.assoc _ _ _).symm
        _ = (pushout.inl f.r g.r ≫ wR) ≫ mW := congrArg (fun t => t ≫ mW) hpYR
        _ = pushout.inl f.r g.r ≫ (wR ≫ mW) := Category.assoc _ _ _
        _ = pushout.inl f.r g.r ≫ ir := congrArg (fun t => pushout.inl f.r g.r ≫ t)
          (hPW.inr_desc il ir hInitialW)
        _ = Y.ir ≫ pushout.inl f.c g.c := hirL
        _ = (bY.inr ≫ bY.toCenter) ≫ pushout.inl f.c g.c :=
          congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inr_toCenter.symm
        _ = bY.inr ≫ (bY.toCenter ≫ pushout.inl f.c g.c) := Category.assoc _ _ _
  let vToW : V ⟶ Wc := hV.desc (pushout.inr f.c g.c) mW hPZtoW.symm
  have hvZToW : vZ ≫ vToW = pushout.inr f.c g.c :=
    hV.inl_desc (pushout.inr f.c g.c) mW hPZtoW.symm
  have hvBToW : vB ≫ vToW = mW :=
    hV.inr_desc (pushout.inr f.c g.c) mW hPZtoW.symm
  have hYlToW : bY.inl ≫ pY ≫ vB ≫ vToW = Y.il ≫ pushout.inl f.c g.c := by
    calc
      bY.inl ≫ pY ≫ vB ≫ vToW = bY.inl ≫ pY ≫ mW := by
        rw [hvBToW]
      _ = bY.inl ≫ bY.toCenter ≫ pushout.inl f.c g.c := by
        rw [hPYtoW]
      _ = Y.il ≫ pushout.inl f.c g.c := by
        calc
          bY.inl ≫ bY.toCenter ≫ pushout.inl f.c g.c =
              (bY.inl ≫ bY.toCenter) ≫ pushout.inl f.c g.c := by
            simp [Category.assoc]
          _ = Y.il ≫ pushout.inl f.c g.c :=
            congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inl_toCenter
  have hYrToW : bY.inr ≫ pY ≫ vB ≫ vToW = Y.ir ≫ pushout.inl f.c g.c := by
    calc
      bY.inr ≫ pY ≫ vB ≫ vToW = bY.inr ≫ pY ≫ mW := by
        rw [hvBToW]
      _ = bY.inr ≫ bY.toCenter ≫ pushout.inl f.c g.c := by
        rw [hPYtoW]
      _ = Y.ir ≫ pushout.inl f.c g.c := by
        calc
          bY.inr ≫ bY.toCenter ≫ pushout.inl f.c g.c =
              (bY.inr ≫ bY.toCenter) ≫ pushout.inl f.c g.c := by
            simp [Category.assoc]
          _ = Y.ir ≫ pushout.inl f.c g.c :=
            congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inr_toCenter
  have htotalCompat : n ≫ pushout.inl f.c g.c = eQ ≫ vToW := by
    apply hQ.hom_ext
    · apply hP.hom_ext
      · calc
          k ≫ (k₂ ≫ n ≫ pushout.inl f.c g.c) = f.c ≫ pushout.inl f.c g.c := by
            simpa [qX, Category.assoc] using congrArg
              (fun t => t ≫ pushout.inl f.c g.c) hqXn
          _ = g.c ≫ pushout.inr f.c g.c := pushout.condition
          _ = k ≫ (k₂ ≫ eQ ≫ vToW) := by
            calc
              g.c ≫ pushout.inr f.c g.c = g.c ≫ (vZ ≫ vToW) :=
                congrArg (fun t => g.c ≫ t) hvZToW.symm
              _ = (g.c ≫ vZ) ≫ vToW := (Category.assoc _ _ _).symm
              _ = (qX ≫ eQ) ≫ vToW := congrArg (fun t => t ≫ vToW) hqXe.symm
              _ = k ≫ (k₂ ≫ eQ ≫ vToW) := by simp [qX, Category.assoc]
      · calc
          j ≫ (k₂ ≫ n ≫ pushout.inl f.c g.c) = Y.il ≫ pushout.inl f.c g.c := by
            simpa [qYl, Category.assoc] using congrArg
              (fun t => t ≫ pushout.inl f.c g.c) hqYln
          _ = (bY.inl ≫ pY ≫ vB) ≫ vToW := by
            simpa [Category.assoc] using hYlToW.symm
          _ = j ≫ (k₂ ≫ eQ ≫ vToW) := by
            simpa [qYl, Category.assoc] using congrArg
              (fun t => t ≫ vToW) hqYle.symm
    · calc
        j₂ ≫ n ≫ pushout.inl f.c g.c = Y.ir ≫ pushout.inl f.c g.c := by
          simpa [qYr, Category.assoc] using congrArg
            (fun t => t ≫ pushout.inl f.c g.c) hqYrn
        _ = (bY.inr ≫ pY ≫ vB) ≫ vToW := by
          simpa [Category.assoc] using hYrToW.symm
        _ = j₂ ≫ eQ ≫ vToW := by
          simpa [qYr, eYr, Category.assoc] using congrArg
            (fun t => t ≫ vToW) hqYre.symm
  have hYbL : bY.inl ≫ pY ≫ mW = Y.il ≫ pushout.inl f.c g.c := by
    calc
      bY.inl ≫ pY ≫ mW = bY.inl ≫ (pY ≫ mW) := rfl
      _ = bY.inl ≫ (bY.toCenter ≫ pushout.inl f.c g.c) :=
        congrArg (fun t => bY.inl ≫ t) hPYtoW
      _ = (bY.inl ≫ bY.toCenter) ≫ pushout.inl f.c g.c :=
        (Category.assoc _ _ _).symm
      _ = Y.il ≫ pushout.inl f.c g.c :=
        congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inl_toCenter
  have hYbR : bY.inr ≫ pY ≫ mW = Y.ir ≫ pushout.inl f.c g.c := by
    calc
      bY.inr ≫ pY ≫ mW = bY.inr ≫ (pY ≫ mW) := rfl
      _ = bY.inr ≫ (bY.toCenter ≫ pushout.inl f.c g.c) :=
        congrArg (fun t => bY.inr ≫ t) hPYtoW
      _ = (bY.inr ≫ bY.toCenter) ≫ pushout.inl f.c g.c :=
        (Category.assoc _ _ _).symm
      _ = Y.ir ≫ pushout.inl f.c g.c :=
        congrArg (fun t => t ≫ pushout.inl f.c g.c) bY.inr_toCenter
  have hZbL : bZ.inl ≫ pZ ≫ mW = Z.il ≫ pushout.inr f.c g.c := by
    calc
      bZ.inl ≫ pZ ≫ mW = bZ.inl ≫ (pZ ≫ mW) := rfl
      _ = bZ.inl ≫ (bZ.toCenter ≫ pushout.inr f.c g.c) :=
        congrArg (fun t => bZ.inl ≫ t) hPZtoW
      _ = (bZ.inl ≫ bZ.toCenter) ≫ pushout.inr f.c g.c :=
        (Category.assoc _ _ _).symm
      _ = Z.il ≫ pushout.inr f.c g.c :=
        congrArg (fun t => t ≫ pushout.inr f.c g.c) bZ.inl_toCenter
  have hZbR : bZ.inr ≫ pZ ≫ mW = Z.ir ≫ pushout.inr f.c g.c := by
    calc
      bZ.inr ≫ pZ ≫ mW = bZ.inr ≫ (pZ ≫ mW) := rfl
      _ = bZ.inr ≫ (bZ.toCenter ≫ pushout.inr f.c g.c) :=
        congrArg (fun t => bZ.inr ≫ t) hPZtoW
      _ = (bZ.inr ≫ bZ.toCenter) ≫ pushout.inr f.c g.c :=
        (Category.assoc _ _ _).symm
      _ = Z.ir ≫ pushout.inr f.c g.c :=
        congrArg (fun t => t ≫ pushout.inr f.c g.c) bZ.inr_toCenter
  have htotalPushout : IsPushout n eQ (pushout.inl f.c g.c) vToW := by
    apply IsPushout.mk'
    · exact htotalCompat
    · intro T φ ψ hφ hψ
      apply hCof.hom_ext
      · exact hφ
      · calc
          pushout.inr f.c g.c ≫ φ = (vZ ≫ vToW) ≫ φ :=
            congrArg (fun t => t ≫ φ) hvZToW.symm
          _ = vZ ≫ vToW ≫ φ := Category.assoc _ _ _
          _ = vZ ≫ vToW ≫ ψ := by rw [hψ]
          _ = (vZ ≫ vToW) ≫ ψ := (Category.assoc _ _ _).symm
          _ = pushout.inr f.c g.c ≫ ψ := congrArg (fun t => t ≫ ψ) hvZToW
    · intro T φ ψ hφψ
      have hfg : f.c ≫ φ = g.c ≫ (vZ ≫ ψ) := by
        calc
          f.c ≫ φ = (qX ≫ n) ≫ φ := congrArg (fun t => t ≫ φ) hqXn.symm
          _ = qX ≫ (n ≫ φ) := Category.assoc _ _ _
          _ = qX ≫ (eQ ≫ ψ) := congrArg (fun t => qX ≫ t) hφψ
          _ = (qX ≫ eQ) ≫ ψ := (Category.assoc _ _ _).symm
          _ = g.c ≫ (vZ ≫ ψ) := by
            rw [hqXe]
            simp [Category.assoc]
      let d : Wc ⟶ T := hCof.desc φ (vZ ≫ ψ) hfg
      have hdL : pushout.inl f.c g.c ≫ d = φ :=
        hCof.inl_desc φ (vZ ≫ ψ) hfg
      have hdR : pushout.inr f.c g.c ≫ d = vZ ≫ ψ :=
        hCof.inr_desc φ (vZ ≫ ψ) hfg
      have hYlCompat : Y.il ≫ φ = bY.inl ≫ pY ≫ vB ≫ ψ := by
        calc
          Y.il ≫ φ = (qYl ≫ n) ≫ φ := congrArg (fun t => t ≫ φ) hqYln.symm
          _ = qYl ≫ (n ≫ φ) := Category.assoc _ _ _
          _ = qYl ≫ (eQ ≫ ψ) := congrArg (fun t => qYl ≫ t) hφψ
          _ = (qYl ≫ eQ) ≫ ψ := (Category.assoc _ _ _).symm
          _ = (bY.inl ≫ pY ≫ vB) ≫ ψ := congrArg (fun t => t ≫ ψ) hqYle
          _ = bY.inl ≫ pY ≫ vB ≫ ψ := by simp [Category.assoc]
      have hYrCompat : Y.ir ≫ φ = bY.inr ≫ pY ≫ vB ≫ ψ := by
        calc
          Y.ir ≫ φ = (qYr ≫ n) ≫ φ := congrArg (fun t => t ≫ φ) hqYrn.symm
          _ = qYr ≫ (n ≫ φ) := Category.assoc _ _ _
          _ = qYr ≫ (eQ ≫ ψ) := congrArg (fun t => qYr ≫ t) hφψ
          _ = (qYr ≫ eQ) ≫ ψ := (Category.assoc _ _ _).symm
          _ = (bY.inr ≫ pY ≫ vB) ≫ ψ := congrArg (fun t => t ≫ ψ) hqYre
          _ = bY.inr ≫ pY ≫ vB ≫ ψ := by simp [eYr, Category.assoc]
      have hZlBase : (bZ.inl ≫ bZ.toCenter) ≫ vZ = bZ.inl ≫ pZ ≫ vB := by
        calc
          (bZ.inl ≫ bZ.toCenter) ≫ vZ = bZ.inl ≫ (bZ.toCenter ≫ vZ) :=
            Category.assoc _ _ _
          _ = bZ.inl ≫ (pZ ≫ vB) := congrArg (fun t => bZ.inl ≫ t) hV.w
          _ = bZ.inl ≫ pZ ≫ vB := by simp [Category.assoc]
      have hZrBase : (bZ.inr ≫ bZ.toCenter) ≫ vZ = bZ.inr ≫ pZ ≫ vB := by
        calc
          (bZ.inr ≫ bZ.toCenter) ≫ vZ = bZ.inr ≫ (bZ.toCenter ≫ vZ) :=
            Category.assoc _ _ _
          _ = bZ.inr ≫ (pZ ≫ vB) := congrArg (fun t => bZ.inr ≫ t) hV.w
          _ = bZ.inr ≫ pZ ≫ vB := by simp [Category.assoc]
      have hZlCompat : Z.il ≫ vZ ≫ ψ = pushout.inr f.l g.l ≫ wL ≫ vB ≫ ψ := by
        calc
          Z.il ≫ vZ ≫ ψ = ((bZ.inl ≫ bZ.toCenter) ≫ vZ) ≫ ψ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ vZ ≫ ψ)
              bZ.inl_toCenter.symm
          _ = (bZ.inl ≫ pZ ≫ vB) ≫ ψ := congrArg (fun t => t ≫ ψ) hZlBase
          _ = pushout.inr f.l g.l ≫ wL ≫ vB ≫ ψ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ vB ≫ ψ) hpZL
      have hZrCompat : Z.ir ≫ vZ ≫ ψ = pushout.inr f.r g.r ≫ wR ≫ vB ≫ ψ := by
        calc
          Z.ir ≫ vZ ≫ ψ = ((bZ.inr ≫ bZ.toCenter) ≫ vZ) ≫ ψ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ vZ ≫ ψ)
              bZ.inr_toCenter.symm
          _ = (bZ.inr ≫ pZ ≫ vB) ≫ ψ := congrArg (fun t => t ≫ ψ) hZrBase
          _ = pushout.inr f.r g.r ≫ wR ≫ vB ≫ ψ := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ vB ≫ ψ) hpZR
      have hmW : mW ≫ d = vB ≫ ψ := by
        apply hPW.hom_ext
        · apply hL.hom_ext
          · calc
              pushout.inl f.l g.l ≫ wL ≫ mW ≫ d =
                  bY.inl ≫ pY ≫ mW ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ mW ≫ d) hpYL.symm
              _ = Y.il ≫ pushout.inl f.c g.c ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ d) hYbL
              _ = Y.il ≫ φ := by rw [hdL]
              _ = bY.inl ≫ pY ≫ vB ≫ ψ := hYlCompat
              _ = pushout.inl f.l g.l ≫ wL ≫ vB ≫ ψ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ vB ≫ ψ) hpYL
          · calc
              pushout.inr f.l g.l ≫ wL ≫ mW ≫ d =
                  bZ.inl ≫ pZ ≫ mW ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ mW ≫ d) hpZL.symm
              _ = Z.il ≫ pushout.inr f.c g.c ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ d) hZbL
              _ = Z.il ≫ vZ ≫ ψ := by rw [hdR]
              _ = pushout.inr f.l g.l ≫ wL ≫ vB ≫ ψ := hZlCompat
        · apply hR.hom_ext
          · calc
              pushout.inl f.r g.r ≫ wR ≫ mW ≫ d =
                  bY.inr ≫ pY ≫ mW ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ mW ≫ d) hpYR.symm
              _ = Y.ir ≫ pushout.inl f.c g.c ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ d) hYbR
              _ = Y.ir ≫ φ := by rw [hdL]
              _ = bY.inr ≫ pY ≫ vB ≫ ψ := hYrCompat
              _ = pushout.inl f.r g.r ≫ wR ≫ vB ≫ ψ := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ vB ≫ ψ) hpYR
          · calc
              pushout.inr f.r g.r ≫ wR ≫ mW ≫ d =
                  bZ.inr ≫ pZ ≫ mW ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ mW ≫ d) hpZR.symm
              _ = Z.ir ≫ pushout.inr f.c g.c ≫ d := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ d) hZbR
              _ = Z.ir ≫ vZ ≫ ψ := by rw [hdR]
              _ = pushout.inr f.r g.r ≫ wR ≫ vB ≫ ψ := hZrCompat
      refine ⟨d, hdL, ?_⟩
      apply hV.hom_ext
      · calc
          vZ ≫ vToW ≫ d = (vZ ≫ vToW) ≫ d := (Category.assoc _ _ _).symm
          _ = pushout.inr f.c g.c ≫ d := congrArg (fun t => t ≫ d) hvZToW
          _ = vZ ≫ ψ := hdR
      · calc
          vB ≫ vToW ≫ d = (vB ≫ vToW) ≫ d := (Category.assoc _ _ _).symm
          _ = mW ≫ d := congrArg (fun t => t ≫ d) hvBToW
          _ = vB ≫ ψ := hmW
  have hvB_mem : cofibrations C vB :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hV.flip bZ.toCenter_mem
  have hvToW_mem : cofibrations C vToW :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout htotalPushout.flip hnCof
  have hmW_mem : cofibrations C mW := by
    rw [← hvBToW]
    exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hvB_mem hvToW_mem
  have hpre : IsPreCylinderCategory C := Packages.isPreCylinderCategory (C := C)
  have hWEil : weakEquivalences C il :=
    hpre.gluing f.l g.l (pushout.inl f.l g.l) (pushout.inr f.l g.l)
      f.c g.c (pushout.inl f.c g.c) (pushout.inr f.c g.c)
      X.il Y.il Z.il il hL hCof hf.1 hfc X.il_mem Y.il_mem Z.il_mem
      (by simpa using f.il_c.symm) (by simpa using g.il_c.symm) hilL hilR
  have hWEir : weakEquivalences C ir :=
    hpre.gluing f.r g.r (pushout.inl f.r g.r) (pushout.inr f.r g.r)
      f.c g.c (pushout.inl f.c g.c) (pushout.inr f.c g.c)
      X.ir Y.ir Z.ir ir hR hCof hf.2.1 hfc X.ir_mem Y.ir_mem Z.ir_mem
      (by simpa using f.ir_c.symm) (by simpa using g.ir_c.symm) hirL hirR
  let Wobj : PathObj C := ⟨Wl, Wr, Wc, il, ir,
    ⟨I, hI, PW, wL, wR, hPW, mW, hPW.inl_desc il ir hInitialW,
      hPW.inr_desc il ir hInitialW, hmW_mem⟩, hWEil, hWEir⟩
  let wY : Y ⟶ Wobj := ⟨pushout.inl f.l g.l, pushout.inl f.r g.r,
    pushout.inl f.c g.c, hilL.symm, hirL.symm⟩
  let wZ : Z ⟶ Wobj := ⟨pushout.inr f.l g.l, pushout.inr f.r g.r,
    pushout.inr f.c g.c, hilR.symm, hirR.symm⟩
  have hwZl : cofibrations C wZ.l :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hL.flip hf.1
  have hwZr : cofibrations C wZ.r :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hR.flip hf.2.1
  letI : HasPushout wZ.l Z.il := hC.hasPushout wZ.l Z.il hwZl
  let P₁ := pushout wZ.l Z.il
  let kZ : Z.c ⟶ P₁ := pushout.inr wZ.l Z.il
  let jZ : Wl ⟶ P₁ := pushout.inl wZ.l Z.il
  have hP₁ : IsPushout Z.il wZ.l kZ jZ :=
    (IsPushout.of_hasPushout wZ.l Z.il).flip
  let qLY : Y.l ⟶ V := bY.inl ≫ pY ≫ vB
  let qLZ : Z.l ⟶ V := bZ.inl ≫ pZ ≫ vB
  let qRY : Y.r ⟶ V := bY.inr ≫ pY ≫ vB
  let qRZ : Z.r ⟶ V := bZ.inr ≫ pZ ≫ vB
  have hqL : f.l ≫ qLY = g.l ≫ qLZ := by
    simpa [qLY, qLZ, Category.assoc] using congrArg (fun t => t ≫ vB) hspanL
  have hqR : f.r ≫ qRY = g.r ≫ qRZ := by
    simpa [qRY, qRZ, Category.assoc] using congrArg (fun t => t ≫ vB) hspanR
  let jL : Wl ⟶ V := hL.desc qLY qLZ hqL
  let jR : Wr ⟶ V := hR.desc qRY qRZ hqR
  have hjLY : pushout.inl f.l g.l ≫ jL = qLY := hL.inl_desc qLY qLZ hqL
  have hjLZ : pushout.inr f.l g.l ≫ jL = qLZ := hL.inr_desc qLY qLZ hqL
  have hjRY : pushout.inl f.r g.r ≫ jR = qRY := hR.inl_desc qRY qRZ hqR
  have hjRZ : pushout.inr f.r g.r ≫ jR = qRZ := hR.inr_desc qRY qRZ hqR
  have hZlV : Z.il ≫ vZ = qLZ := by
    calc
      Z.il ≫ vZ = (bZ.inl ≫ bZ.toCenter) ≫ vZ :=
        congrArg (fun t => t ≫ vZ) bZ.inl_toCenter.symm
      _ = bZ.inl ≫ (bZ.toCenter ≫ vZ) := Category.assoc _ _ _
      _ = bZ.inl ≫ (pZ ≫ vB) := congrArg (fun t => bZ.inl ≫ t) hV.w
      _ = qLZ := rfl
  have hZrV : Z.ir ≫ vZ = qRZ := by
    calc
      Z.ir ≫ vZ = (bZ.inr ≫ bZ.toCenter) ≫ vZ :=
        congrArg (fun t => t ≫ vZ) bZ.inr_toCenter.symm
      _ = bZ.inr ≫ (bZ.toCenter ≫ vZ) := Category.assoc _ _ _
      _ = bZ.inr ≫ (pZ ≫ vB) := congrArg (fun t => bZ.inr ≫ t) hV.w
      _ = qRZ := rfl
  have hP₁Compat : Z.il ≫ vZ = wZ.l ≫ jL := by
    change Z.il ≫ vZ = pushout.inr f.l g.l ≫ jL
    exact hZlV.trans hjLZ.symm
  let p₁ : P₁ ⟶ V := hP₁.desc vZ jL hP₁Compat
  have hp₁Z : kZ ≫ p₁ = vZ := hP₁.inl_desc vZ jL hP₁Compat
  have hp₁L : jZ ≫ p₁ = jL := hP₁.inr_desc vZ jL hP₁Compat
  have hP₂Compat : (Z.ir ≫ kZ) ≫ p₁ = wZ.r ≫ jR := by
    calc
      (Z.ir ≫ kZ) ≫ p₁ = Z.ir ≫ (kZ ≫ p₁) := Category.assoc _ _ _
      _ = Z.ir ≫ vZ := congrArg (fun t => Z.ir ≫ t) hp₁Z
      _ = qRZ := hZrV
      _ = wZ.r ≫ jR := by
        change qRZ = pushout.inr f.r g.r ≫ jR
        exact hjRZ.symm
  have hWlV : wL ≫ vB = jZ ≫ p₁ := by
    apply hL.hom_ext
    · calc
        pushout.inl f.l g.l ≫ wL ≫ vB = qLY := by
          simpa [qLY, Category.assoc] using congrArg (fun t => t ≫ vB) hpYL.symm
        _ = pushout.inl f.l g.l ≫ jZ ≫ p₁ := by
          calc
            qLY = pushout.inl f.l g.l ≫ jL := hjLY.symm
            _ = pushout.inl f.l g.l ≫ jZ ≫ p₁ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inl f.l g.l ≫ t) hp₁L.symm
    · calc
        pushout.inr f.l g.l ≫ wL ≫ vB = qLZ := by
          simpa [qLZ, Category.assoc] using congrArg (fun t => t ≫ vB) hpZL.symm
        _ = pushout.inr f.l g.l ≫ jZ ≫ p₁ := by
          calc
            qLZ = pushout.inr f.l g.l ≫ jL := hjLZ.symm
            _ = pushout.inr f.l g.l ≫ jZ ≫ p₁ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inr f.l g.l ≫ t) hp₁L.symm
  have hWrV : wR ≫ vB = jR := by
    apply hR.hom_ext
    · calc
        pushout.inl f.r g.r ≫ wR ≫ vB = qRY := by
          simpa [qRY, Category.assoc] using congrArg (fun t => t ≫ vB) hpYR.symm
        _ = pushout.inl f.r g.r ≫ jR := hjRY.symm
    · calc
        pushout.inr f.r g.r ≫ wR ≫ vB = qRZ := by
          simpa [qRZ, Category.assoc] using congrArg (fun t => t ≫ vB) hpZR.symm
        _ = pushout.inr f.r g.r ≫ jR := hjRZ.symm
  have hP₂ : IsPushout (Z.ir ≫ kZ) wZ.r p₁ jR := by
    apply IsPushout.mk'
    · exact hP₂Compat
    · intro T φ ψ hφ hψ
      apply hV.hom_ext
      · calc
          vZ ≫ φ = (kZ ≫ p₁) ≫ φ := congrArg (fun t => t ≫ φ) hp₁Z.symm
          _ = kZ ≫ (p₁ ≫ φ) := Category.assoc _ _ _
          _ = kZ ≫ (p₁ ≫ ψ) := congrArg (fun t => kZ ≫ t) hφ
          _ = (kZ ≫ p₁) ≫ ψ := (Category.assoc _ _ _).symm
          _ = vZ ≫ ψ := congrArg (fun t => t ≫ ψ) hp₁Z
      · apply hPW.hom_ext
        · calc
            wL ≫ vB ≫ φ = (jZ ≫ p₁) ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hWlV
            _ = jZ ≫ (p₁ ≫ φ) := Category.assoc _ _ _
            _ = jZ ≫ (p₁ ≫ ψ) := congrArg (fun t => jZ ≫ t) hφ
            _ = (jZ ≫ p₁) ≫ ψ := (Category.assoc _ _ _).symm
            _ = wL ≫ vB ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hWlV.symm
        · calc
            wR ≫ vB ≫ φ = jR ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hWrV
            _ = jR ≫ ψ := hψ
            _ = wR ≫ vB ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hWrV.symm
    · intro T φ ψ hφψ
      let dPW : PW ⟶ T := hPW.desc (jZ ≫ φ) ψ (hI.hom_ext _ _)
      let dC : Z.c ⟶ T := kZ ≫ φ
      have hdPWl : wL ≫ dPW = jZ ≫ φ := hPW.inl_desc _ _ (hI.hom_ext _ _)
      have hdPWr : wR ≫ dPW = ψ := hPW.inr_desc _ _ (hI.hom_ext _ _)
      have hVcompat : bZ.toCenter ≫ dC = pZ ≫ dPW := by
        apply bZ.isPushout.hom_ext
        · calc
            bZ.inl ≫ bZ.toCenter ≫ dC =
                (bZ.inl ≫ bZ.toCenter) ≫ dC := by simp [Category.assoc]
            _ = Z.il ≫ dC := congrArg (fun t => t ≫ dC) bZ.inl_toCenter
            _ = Z.il ≫ (kZ ≫ φ) := rfl
            _ = (Z.il ≫ kZ) ≫ φ := (Category.assoc _ _ _).symm
            _ = (wZ.l ≫ jZ) ≫ φ := congrArg (fun t => t ≫ φ) hP₁.w
            _ = wZ.l ≫ (jZ ≫ φ) := Category.assoc _ _ _
            _ = wZ.l ≫ (wL ≫ dPW) := congrArg (fun t => wZ.l ≫ t) hdPWl.symm
            _ = (wZ.l ≫ wL) ≫ dPW := (Category.assoc _ _ _).symm
            _ = (pushout.inr f.l g.l ≫ wL) ≫ dPW := rfl
            _ = (bZ.inl ≫ pZ) ≫ dPW :=
              congrArg (fun t => t ≫ dPW) hpZL.symm
            _ = bZ.inl ≫ (pZ ≫ dPW) := Category.assoc _ _ _
        · calc
            bZ.inr ≫ bZ.toCenter ≫ dC =
                (bZ.inr ≫ bZ.toCenter) ≫ dC := by simp [Category.assoc]
            _ = Z.ir ≫ dC := congrArg (fun t => t ≫ dC) bZ.inr_toCenter
            _ = Z.ir ≫ (kZ ≫ φ) := rfl
            _ = (Z.ir ≫ kZ) ≫ φ := (Category.assoc _ _ _).symm
            _ = wZ.r ≫ ψ := hφψ
            _ = pushout.inr f.r g.r ≫ ψ := rfl
            _ = pushout.inr f.r g.r ≫ (wR ≫ dPW) :=
              congrArg (fun t => pushout.inr f.r g.r ≫ t) hdPWr.symm
            _ = (pushout.inr f.r g.r ≫ wR) ≫ dPW :=
              (Category.assoc _ _ _).symm
            _ = (bZ.inr ≫ pZ) ≫ dPW :=
              congrArg (fun t => t ≫ dPW) hpZR.symm
            _ = bZ.inr ≫ (pZ ≫ dPW) := Category.assoc _ _ _
      let dV : V ⟶ T := hV.desc dC dPW hVcompat
      have hdVZ : vZ ≫ dV = dC := hV.inl_desc dC dPW hVcompat
      have hdVB : vB ≫ dV = dPW := hV.inr_desc dC dPW hVcompat
      have hjLdV : jL ≫ dV = jZ ≫ φ := by
        apply hL.hom_ext
        · calc
            pushout.inl f.l g.l ≫ jL ≫ dV = qLY ≫ dV := by
              simpa [qLY, Category.assoc] using congrArg
                (fun t => t ≫ dV) hjLY
            _ = bY.inl ≫ pY ≫ vB ≫ dV := by simpa [qLY, Category.assoc]
            _ = bY.inl ≫ pY ≫ dPW := by
              calc
                bY.inl ≫ pY ≫ vB ≫ dV = bY.inl ≫ pY ≫ (vB ≫ dV) := by
                  simp [Category.assoc]
                _ = bY.inl ≫ pY ≫ dPW := congrArg
                  (fun t => bY.inl ≫ pY ≫ t) hdVB
            _ = pushout.inl f.l g.l ≫ wL ≫ dPW := by
              simpa [Category.assoc] using congrArg
                (fun t => t ≫ dPW) hpYL
            _ = pushout.inl f.l g.l ≫ jZ ≫ φ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inl f.l g.l ≫ t) hdPWl
        · calc
            pushout.inr f.l g.l ≫ jL ≫ dV = qLZ ≫ dV := by
              simpa [qLZ, Category.assoc] using congrArg
                (fun t => t ≫ dV) hjLZ
            _ = bZ.inl ≫ pZ ≫ vB ≫ dV := by simpa [qLZ, Category.assoc]
            _ = bZ.inl ≫ pZ ≫ dPW := by
              calc
                bZ.inl ≫ pZ ≫ vB ≫ dV = bZ.inl ≫ pZ ≫ (vB ≫ dV) := by
                  simp [Category.assoc]
                _ = bZ.inl ≫ pZ ≫ dPW := congrArg
                  (fun t => bZ.inl ≫ pZ ≫ t) hdVB
            _ = pushout.inr f.l g.l ≫ wL ≫ dPW := by
              simpa [Category.assoc] using congrArg
                (fun t => t ≫ dPW) hpZL
            _ = pushout.inr f.l g.l ≫ jZ ≫ φ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inr f.l g.l ≫ t) hdPWl
      have hjRdV : jR ≫ dV = ψ := by
        apply hR.hom_ext
        · calc
            pushout.inl f.r g.r ≫ jR ≫ dV = qRY ≫ dV := by
              simpa [qRY, Category.assoc] using congrArg
                (fun t => t ≫ dV) hjRY
            _ = bY.inr ≫ pY ≫ vB ≫ dV := by simpa [qRY, Category.assoc]
            _ = bY.inr ≫ pY ≫ dPW := by
              calc
                bY.inr ≫ pY ≫ vB ≫ dV = bY.inr ≫ pY ≫ (vB ≫ dV) := by
                  simp [Category.assoc]
                _ = bY.inr ≫ pY ≫ dPW := congrArg
                  (fun t => bY.inr ≫ pY ≫ t) hdVB
            _ = pushout.inl f.r g.r ≫ wR ≫ dPW := by
              simpa [Category.assoc] using congrArg
                (fun t => t ≫ dPW) hpYR
            _ = pushout.inl f.r g.r ≫ ψ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inl f.r g.r ≫ t) hdPWr
        · calc
            pushout.inr f.r g.r ≫ jR ≫ dV = qRZ ≫ dV := by
              simpa [qRZ, Category.assoc] using congrArg
                (fun t => t ≫ dV) hjRZ
            _ = bZ.inr ≫ pZ ≫ vB ≫ dV := by simpa [qRZ, Category.assoc]
            _ = bZ.inr ≫ pZ ≫ dPW := by
              calc
                bZ.inr ≫ pZ ≫ vB ≫ dV = bZ.inr ≫ pZ ≫ (vB ≫ dV) := by
                  simp [Category.assoc]
                _ = bZ.inr ≫ pZ ≫ dPW := congrArg
                  (fun t => bZ.inr ≫ pZ ≫ t) hdVB
            _ = pushout.inr f.r g.r ≫ wR ≫ dPW := by
              simpa [Category.assoc] using congrArg
                (fun t => t ≫ dPW) hpZR
            _ = pushout.inr f.r g.r ≫ ψ := by
              simpa [Category.assoc] using congrArg
                (fun t => pushout.inr f.r g.r ≫ t) hdPWr
      have hdP₁ : p₁ ≫ dV = φ := by
        apply hP₁.hom_ext
        · calc
            kZ ≫ p₁ ≫ dV = vZ ≫ dV := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ dV) hp₁Z
            _ = dC := hdVZ
            _ = kZ ≫ φ := rfl
        · calc
            jZ ≫ p₁ ≫ dV = jL ≫ dV := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ dV) hp₁L
            _ = jZ ≫ φ := hjLdV
      refine ⟨dV, hdP₁, hjRdV⟩
  have hm₁Compat : Z.il ≫ wZ.c = wZ.l ≫ Wobj.il := wZ.il_c
  let m₁ : P₁ ⟶ Wc := hP₁.desc wZ.c Wobj.il hm₁Compat
  have hP₁m₁ : kZ ≫ m₁ = wZ.c := hP₁.inl_desc wZ.c Wobj.il hm₁Compat
  have hjZm₁ : jZ ≫ m₁ = Wobj.il := hP₁.inr_desc wZ.c Wobj.il hm₁Compat
  have hp₁vToW : p₁ ≫ vToW = m₁ := by
    apply hP₁.hom_ext
    · calc
        kZ ≫ p₁ ≫ vToW = vZ ≫ vToW := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hp₁Z
        _ = wZ.c := by simpa [wZ] using hvZToW
        _ = kZ ≫ m₁ := hP₁m₁.symm
    · calc
        jZ ≫ p₁ ≫ vToW = jL ≫ vToW := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hp₁L
        _ = Wobj.il := by
          apply hL.hom_ext
          · calc
              pushout.inl f.l g.l ≫ jL ≫ vToW = qLY ≫ vToW := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hjLY
              _ = pushout.inl f.l g.l ≫ wL ≫ vB ≫ vToW := by
                simpa [qLY, Category.assoc] using congrArg
                  (fun t => t ≫ vB ≫ vToW) hpYL
              _ = pushout.inl f.l g.l ≫ wL ≫ mW := by rw [hvBToW]
              _ = pushout.inl f.l g.l ≫ il := by
                rw [hPW.inl_desc il ir hInitialW]
              _ = pushout.inl f.l g.l ≫ Wobj.il := rfl
          · calc
              pushout.inr f.l g.l ≫ jL ≫ vToW = qLZ ≫ vToW := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hjLZ
              _ = pushout.inr f.l g.l ≫ wL ≫ vB ≫ vToW := by
                simpa [qLZ, Category.assoc] using congrArg
                  (fun t => t ≫ vB ≫ vToW) hpZL
              _ = pushout.inr f.l g.l ≫ wL ≫ mW := by rw [hvBToW]
              _ = pushout.inr f.l g.l ≫ il := by
                rw [hPW.inl_desc il ir hInitialW]
              _ = pushout.inr f.l g.l ≫ Wobj.il := rfl
        _ = jZ ≫ m₁ := hjZm₁.symm
  have hjRvToW : jR ≫ vToW = Wobj.ir := by
    apply hR.hom_ext
    · calc
        pushout.inl f.r g.r ≫ jR ≫ vToW = qRY ≫ vToW := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hjRY
        _ = pushout.inl f.r g.r ≫ wR ≫ vB ≫ vToW := by
          simpa [qRY, Category.assoc] using congrArg
            (fun t => t ≫ vB ≫ vToW) hpYR
        _ = pushout.inl f.r g.r ≫ wR ≫ mW := by rw [hvBToW]
        _ = pushout.inl f.r g.r ≫ ir := by rw [hPW.inr_desc il ir hInitialW]
        _ = pushout.inl f.r g.r ≫ Wobj.ir := rfl
    · calc
        pushout.inr f.r g.r ≫ jR ≫ vToW = qRZ ≫ vToW := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ vToW) hjRZ
        _ = pushout.inr f.r g.r ≫ wR ≫ vB ≫ vToW := by
          simpa [qRZ, Category.assoc] using congrArg
            (fun t => t ≫ vB ≫ vToW) hpZR
        _ = pushout.inr f.r g.r ≫ wR ≫ mW := by rw [hvBToW]
        _ = pushout.inr f.r g.r ≫ ir := by rw [hPW.inr_desc il ir hInitialW]
        _ = pushout.inr f.r g.r ≫ Wobj.ir := rfl
  have hInr_mem : cofibrations (PathObj C) wZ := by
    change cofibrations C wZ.l ∧ cofibrations C wZ.r ∧
      (∃ (P : C) (k : Z.c ⟶ P) (j : Wobj.l ⟶ P)
        (hP : IsPushout Z.il wZ.l k j) (m : P ⟶ Wobj.c),
          k ≫ m = wZ.c ∧ j ≫ m = Wobj.il ∧
            IsCofibrantGluing (Z.ir ≫ k) wZ.r m Wobj.ir) at ⊢
    refine ⟨hwZl, hwZr, P₁, kZ, jZ, hP₁, m₁, hP₁m₁, hjZm₁, ?_⟩
    refine ⟨V, p₁, jR, hP₂, vToW, hp₁vToW, hjRvToW, hvToW_mem⟩
  refine ⟨Wobj, wY, wZ, hL, hR, hCof, ?_, hInr_mem⟩
  apply IsPushout.mk'
  · apply PathObj.Hom.ext
    · exact pushout.condition
    · exact pushout.condition
    · exact pushout.condition
  · intro T φ ψ hφ hψ
    have hφl := congrArg (fun m : Y ⟶ T => m.l) hφ
    have hψl := congrArg (fun m : Z ⟶ T => m.l) hψ
    have hφr := congrArg (fun m : Y ⟶ T => m.r) hφ
    have hψr := congrArg (fun m : Z ⟶ T => m.r) hψ
    have hφc := congrArg (fun m : Y ⟶ T => m.c) hφ
    have hψc := congrArg (fun m : Z ⟶ T => m.c) hψ
    change pushout.inl f.l g.l ≫ φ.l = pushout.inl f.l g.l ≫ ψ.l at hφl
    change pushout.inr f.l g.l ≫ φ.l = pushout.inr f.l g.l ≫ ψ.l at hψl
    change pushout.inl f.r g.r ≫ φ.r = pushout.inl f.r g.r ≫ ψ.r at hφr
    change pushout.inr f.r g.r ≫ φ.r = pushout.inr f.r g.r ≫ ψ.r at hψr
    change pushout.inl f.c g.c ≫ φ.c = pushout.inl f.c g.c ≫ ψ.c at hφc
    change pushout.inr f.c g.c ≫ φ.c = pushout.inr f.c g.c ≫ ψ.c at hψc
    apply PathObj.Hom.ext
    · exact hL.hom_ext hφl hψl
    · exact hR.hom_ext hφr hψr
    · exact hCof.hom_ext hφc hψc
  · intro T α β hαβ
    have hαl := congrArg (fun m : X ⟶ T => m.l) hαβ
    have hαr := congrArg (fun m : X ⟶ T => m.r) hαβ
    have hαc := congrArg (fun m : X ⟶ T => m.c) hαβ
    change f.l ≫ α.l = g.l ≫ β.l at hαl
    change f.r ≫ α.r = g.r ≫ β.r at hαr
    change f.c ≫ α.c = g.c ≫ β.c at hαc
    let dL : Wl ⟶ T.l := hL.desc α.l β.l hαl
    let dR : Wr ⟶ T.r := hR.desc α.r β.r hαr
    let dC : Wc ⟶ T.c := hCof.desc α.c β.c hαc
    have hdIl : il ≫ dC = dL ≫ T.il := by
      apply hL.hom_ext
      · calc
          pushout.inl f.l g.l ≫ il ≫ dC =
              (pushout.inl f.l g.l ≫ il) ≫ dC := by simp [Category.assoc]
          _ = (Y.il ≫ pushout.inl f.c g.c) ≫ dC := congrArg
            (fun t => t ≫ dC) hilL
          _ = Y.il ≫ (pushout.inl f.c g.c ≫ dC) := Category.assoc _ _ _
          _ = Y.il ≫ α.c := congrArg (fun t => Y.il ≫ t)
            (hCof.inl_desc α.c β.c hαc)
          _ = α.l ≫ T.il := α.il_c
          _ = (pushout.inl f.l g.l ≫ dL) ≫ T.il := congrArg
            (fun t => t ≫ T.il) (hL.inl_desc α.l β.l hαl).symm
          _ = pushout.inl f.l g.l ≫ (dL ≫ T.il) :=
            Category.assoc _ _ _
      · calc
          pushout.inr f.l g.l ≫ il ≫ dC =
              (pushout.inr f.l g.l ≫ il) ≫ dC := by simp [Category.assoc]
          _ = (Z.il ≫ pushout.inr f.c g.c) ≫ dC := congrArg
            (fun t => t ≫ dC) hilR
          _ = Z.il ≫ (pushout.inr f.c g.c ≫ dC) := Category.assoc _ _ _
          _ = Z.il ≫ β.c := congrArg (fun t => Z.il ≫ t)
            (hCof.inr_desc α.c β.c hαc)
          _ = β.l ≫ T.il := β.il_c
          _ = (pushout.inr f.l g.l ≫ dL) ≫ T.il := congrArg
            (fun t => t ≫ T.il) (hL.inr_desc α.l β.l hαl).symm
          _ = pushout.inr f.l g.l ≫ (dL ≫ T.il) :=
            Category.assoc _ _ _
    have hdIr : ir ≫ dC = dR ≫ T.ir := by
      apply hR.hom_ext
      · calc
          pushout.inl f.r g.r ≫ ir ≫ dC =
              (pushout.inl f.r g.r ≫ ir) ≫ dC := by simp [Category.assoc]
          _ = (Y.ir ≫ pushout.inl f.c g.c) ≫ dC := congrArg
            (fun t => t ≫ dC) hirL
          _ = Y.ir ≫ (pushout.inl f.c g.c ≫ dC) := Category.assoc _ _ _
          _ = Y.ir ≫ α.c := congrArg (fun t => Y.ir ≫ t)
            (hCof.inl_desc α.c β.c hαc)
          _ = α.r ≫ T.ir := α.ir_c
          _ = (pushout.inl f.r g.r ≫ dR) ≫ T.ir := congrArg
            (fun t => t ≫ T.ir) (hR.inl_desc α.r β.r hαr).symm
          _ = pushout.inl f.r g.r ≫ (dR ≫ T.ir) :=
            Category.assoc _ _ _
      · calc
          pushout.inr f.r g.r ≫ ir ≫ dC =
              (pushout.inr f.r g.r ≫ ir) ≫ dC := by simp [Category.assoc]
          _ = (Z.ir ≫ pushout.inr f.c g.c) ≫ dC := congrArg
            (fun t => t ≫ dC) hirR
          _ = Z.ir ≫ (pushout.inr f.c g.c ≫ dC) := Category.assoc _ _ _
          _ = Z.ir ≫ β.c := congrArg (fun t => Z.ir ≫ t)
            (hCof.inr_desc α.c β.c hαc)
          _ = β.r ≫ T.ir := β.ir_c
          _ = (pushout.inr f.r g.r ≫ dR) ≫ T.ir := congrArg
            (fun t => t ≫ T.ir) (hR.inr_desc α.r β.r hαr).symm
          _ = pushout.inr f.r g.r ≫ (dR ≫ T.ir) :=
            Category.assoc _ _ _
    let d : Wobj ⟶ T := ⟨dL, dR, dC, hdIl, hdIr⟩
    refine ⟨d, ?_, ?_⟩
    · apply PathObj.Hom.ext
      · exact hL.inl_desc α.l β.l hαl
      · exact hR.inl_desc α.r β.r hαr
      · exact hCof.inl_desc α.c β.c hαc
    · apply PathObj.Hom.ext
      · exact hL.inr_desc α.l β.l hαl
      · exact hR.inr_desc α.r β.r hαr
      · exact hCof.inr_desc α.c β.c hαc

private theorem pathObj_cof_cobaseChange {X Y Z W : PathObj C} (f : X ⟶ Y)
    (g : X ⟶ Z) (i : Y ⟶ W) (j : Z ⟶ W) (h : IsPushout f g i j)
    (hf : cofibrations (PathObj C) f) : cofibrations (PathObj C) j := by
  let P := pathObj_pushout_object f g hf
  let e : P.obj ≅ W := P.isPushout.isColimit.coconePointUniqueUpToIso h.isColimit
  have hRight : P.inr ≫ e.hom = j := by
    change P.inr ≫
      (P.isPushout.isColimit.coconePointUniqueUpToIso h.isColimit).hom = j
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      P.isPushout.isColimit h.isColimit WalkingSpan.right
  have hIso : cofibrations (PathObj C) e.hom :=
    pathObj_isIso_cof e.hom (by infer_instance)
  rw [← hRight]
  exact pathObj_cof_comp P.inr e.hom P.inr_mem hIso

private noncomputable def pathObj_isCofibrationCategory :
    IsCofibrationCategory (PathObj C) := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  refine
    { isomorphisms_le := ?_
      isMultiplicative := ?_
      exists_initial := ⟨pathInitialObject hI, ⟨pathInitial_isInitial hI⟩⟩
      initial_cofibration := ?_
      hasPushout := ?_
      isStableUnderCobaseChange := ?_ }
  · intro X Y f hf
    exact pathObj_isIso_cof f hf
  · refine { id_mem := ?_, comp_mem := ?_ }
    · intro X
      exact pathObj_isIso_cof (𝟙 X) (by infer_instance)
    · intro X Y Z f g hf hg
      exact pathObj_cof_comp f g hf hg
  · intro I' hI' X
    exact pathInitial_map_cofibration hI' X
  · intro A B X f g hf
    exact (pathObj_pushout_object f g hf).isPushout.hasPushout
  · refine ⟨?_⟩
    intro A A' B B' f g f' g' h hf
    exact pathObj_cof_cobaseChange f g g' f' h.flip hf

private theorem pathObj_pushout_components {X Y Z W : PathObj C}
    (f : X ⟶ Y) (g : X ⟶ Z) (i : Y ⟶ W) (j : Z ⟶ W)
    (h : IsPushout f g i j) (hf : cofibrations (PathObj C) f) :
    IsPushout f.l g.l i.l j.l ∧ IsPushout f.r g.r i.r j.r ∧
      IsPushout f.c g.c i.c j.c := by
  let P := pathObj_pushout_object f g hf
  let e : P.obj ≅ W := P.isPushout.isColimit.coconePointUniqueUpToIso h.isColimit
  let eL : P.obj.l ≅ W.l := (PathObj.left C).mapIso e
  let eR : P.obj.r ≅ W.r := (PathObj.right C).mapIso e
  let eC : P.obj.c ≅ W.c := pathObjCenter.mapIso e
  have hInl : P.inl ≫ e.hom = i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      P.isPushout.isColimit h.isColimit WalkingSpan.left
  have hInr : P.inr ≫ e.hom = j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      P.isPushout.isColimit h.isColimit WalkingSpan.right
  have hInlL : P.inl.l ≫ eL.hom = i.l := by
    change (P.inl ≫ e.hom).l = i.l
    exact congrArg (fun m : Y ⟶ W => m.l) hInl
  have hInrL : P.inr.l ≫ eL.hom = j.l := by
    change (P.inr ≫ e.hom).l = j.l
    exact congrArg (fun m : Z ⟶ W => m.l) hInr
  have hInlR : P.inl.r ≫ eR.hom = i.r := by
    change (P.inl ≫ e.hom).r = i.r
    exact congrArg (fun m : Y ⟶ W => m.r) hInl
  have hInrR : P.inr.r ≫ eR.hom = j.r := by
    change (P.inr ≫ e.hom).r = j.r
    exact congrArg (fun m : Z ⟶ W => m.r) hInr
  have hInlC : P.inl.c ≫ eC.hom = i.c := by
    change (P.inl ≫ e.hom).c = i.c
    exact congrArg (fun m : Y ⟶ W => m.c) hInl
  have hInrC : P.inr.c ≫ eC.hom = j.c := by
    change (P.inr ≫ e.hom).c = j.c
    exact congrArg (fun m : Z ⟶ W => m.c) hInr
  refine ⟨?_, ?_, ?_⟩
  · exact P.left_isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eL
      (by simp) (by simp) (by simpa using hInlL) (by simpa using hInrL)
  · exact P.right_isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eR
      (by simp) (by simp) (by simpa using hInlR) (by simpa using hInrR)
  · exact P.center_isPushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eC
      (by simp) (by simp) (by simpa using hInlC) (by simpa using hInrC)

private theorem pathObj_trivialCof_cobaseChange {X Y Z W : PathObj C}
    (i : X ⟶ Y) (f : X ⟶ Z) (k : Y ⟶ W) (j : Z ⟶ W)
    (h : IsPushout i f k j) (hi : cofibrations (PathObj C) i)
    (hwi : weakEquivalences (PathObj C) i) : weakEquivalences (PathObj C) j := by
  obtain ⟨hL, hR, hCenter⟩ := pathObj_pushout_components i f k j h hi
  change weakEquivalences C i.l ∧ weakEquivalences C i.r ∧ weakEquivalences C i.c at hwi
  change weakEquivalences C j.l ∧ weakEquivalences C j.r ∧ weakEquivalences C j.c
  exact ⟨hC.trivialCofibration_cobaseChange i.l f.l k.l j.l hL hi.1 hwi.1,
    hC.trivialCofibration_cobaseChange i.r f.r k.r j.r hR hi.2.1 hwi.2.1,
    hC.trivialCofibration_cobaseChange i.c f.c k.c j.c hCenter
      (pathObj_cof_middle i hi) hwi.2.2⟩

private theorem pathObj_isomorphisms_le_weakEquivalences {X Y : PathObj C}
    (f : X ⟶ Y) (hf : IsIso f) : weakEquivalences (PathObj C) f := by
  letI : IsIso f := hf
  have hfl : IsIso f.l := Functor.map_isIso (PathObj.left C) f
  have hfr : IsIso f.r := Functor.map_isIso (PathObj.right C) f
  have hfc : IsIso f.c := by
    change IsIso (pathObjCenter.map f)
    exact Functor.map_isIso pathObjCenter f
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c
  exact ⟨hC.isomorphisms_le_weakEquivalences f.l hfl,
    hC.isomorphisms_le_weakEquivalences f.r hfr,
    hC.isomorphisms_le_weakEquivalences f.c hfc⟩

private theorem pathObj_weakEquivalences_comp {X Y Z : PathObj C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : weakEquivalences (PathObj C) f)
    (hg : weakEquivalences (PathObj C) g) : weakEquivalences (PathObj C) (f ≫ g) := by
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c at hf
  change weakEquivalences C g.l ∧ weakEquivalences C g.r ∧ weakEquivalences C g.c at hg
  change weakEquivalences C (f.l ≫ g.l) ∧ weakEquivalences C (f.r ≫ g.r) ∧
    weakEquivalences C (f.c ≫ g.c)
  exact ⟨hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf.1 hg.1,
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf.2.1 hg.2.1,
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf.2.2 hg.2.2⟩

private theorem pathObj_weakEquivalences_twoOutOfSix :
    TwoOutOfSix (PathObj C) (weakEquivalences (PathObj C)) := by
  intro X Y Z T f g h hfg hgh
  change weakEquivalences C (f.l ≫ g.l) ∧ weakEquivalences C (f.r ≫ g.r) ∧
    weakEquivalences C (f.c ≫ g.c) at hfg
  change weakEquivalences C (g.l ≫ h.l) ∧ weakEquivalences C (g.r ≫ h.r) ∧
    weakEquivalences C (g.c ≫ h.c) at hgh
  obtain ⟨hfl, hgl, hhl, hlf⟩ := hC.twoOutOfSix f.l g.l h.l hfg.1 hgh.1
  obtain ⟨hfr, hgr, hhr, hrf⟩ := hC.twoOutOfSix f.r g.r h.r hfg.2.1 hgh.2.1
  obtain ⟨hfc, hgc, hhc, hcf⟩ := hC.twoOutOfSix f.c g.c h.c hfg.2.2 hgh.2.2
  exact ⟨⟨hfl, hfr, hfc⟩, ⟨hgl, hgr, hgc⟩, ⟨hhl, hhr, hhc⟩,
    ⟨hlf, hrf, hcf⟩⟩

private theorem cofibration_weak_equivalence_factorization {A B : C} (f : A ⟶ B) :
    ∃ (M : C) (i : A ⟶ M) (w : M ⟶ B),
      cofibrations C i ∧ weakEquivalences C w ∧ i ≫ w = f := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  obtain ⟨cyl⟩ := hC.exists_cylinder hI A
  letI : HasPushout (hI.to A) (hI.to B) := hC.hasPushout (hI.to A) (hI.to B)
    (hC.initial_cofibration hI A)
  let Q := pushout (hI.to A) (hI.to B)
  let iA : A ⟶ Q := pushout.inl (hI.to A) (hI.to B)
  let iB : B ⟶ Q := pushout.inr (hI.to A) (hI.to B)
  have hQ : IsPushout (hI.to A) (hI.to B) iA iB := by
    exact IsPushout.of_hasPushout _ _
  have hiA : cofibrations C iA := by
    exact hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hQ
      (hC.initial_cofibration hI B)
  have hJ0 : cofibrations C cyl.j₀ := by
    exact hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout cyl.isPushout
      (hC.initial_cofibration hI A)
  have hJ1 : cofibrations C cyl.j₁ := by
    exact hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout cyl.isPushout.flip
      (hC.initial_cofibration hI A)
  have hJ0c : cofibrations C (cyl.j₀ ≫ cyl.c) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hJ0 cyl.c_mem
  have hJ1c : cofibrations C (cyl.j₁ ≫ cyl.c) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hJ1 cyl.c_mem
  have hJ1id : weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
    have hid : weakEquivalences C (𝟙 A) :=
      hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
    have hleft : weakEquivalences C ((cyl.j₁ ≫ cyl.c) ≫ cyl.p) := by
      simpa [Category.assoc, cyl.j₁_c_p] using hid
    have hright : weakEquivalences C (cyl.p ≫ 𝟙 A) := by simpa using cyl.p_mem
    exact (hC.twoOutOfSix (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 A) hleft hright).1
  let coconeQ : PushoutCocone (hI.to A) (hI.to A) :=
    PushoutCocone.mk iA (f ≫ iB) (IsInitial.hom_ext hI _ _)
  let q : cyl.P ⟶ Q := cyl.isPushout.isColimit.desc coconeQ
  have hq0 : cyl.j₀ ≫ q = iA := by
    change cyl.j₀ ≫ q = iA
    exact cyl.isPushout.isColimit.fac coconeQ WalkingSpan.left
  have hq1 : cyl.j₁ ≫ q = f ≫ iB := by
    change cyl.j₁ ≫ q = f ≫ iB
    exact cyl.isPushout.isColimit.fac coconeQ WalkingSpan.right
  let coconeV : PushoutCocone (hI.to A) (hI.to B) :=
    PushoutCocone.mk f (𝟙 B) (IsInitial.hom_ext hI _ _)
  let v : Q ⟶ B := hQ.isColimit.desc coconeV
  have hvA : iA ≫ v = f := by
    change iA ≫ v = f
    exact hQ.isColimit.fac coconeV WalkingSpan.left
  have hvB : iB ≫ v = 𝟙 B := by
    change iB ≫ v = 𝟙 B
    exact hQ.isColimit.fac coconeV WalkingSpan.right
  have hcompat : cyl.c ≫ (cyl.p ≫ f) = q ≫ v := by
    apply PushoutCocone.IsColimit.hom_ext cyl.isPushout.isColimit
    · change cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = cyl.j₀ ≫ q ≫ v
      calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ f := by
          simp [Category.assoc]
        _ = f := by rw [cyl.j₀_c_p]; simp
        _ = iA ≫ v := hvA.symm
        _ = cyl.j₀ ≫ q ≫ v := by
          simpa [Category.assoc] using (congrArg (fun t => t ≫ v) hq0).symm
    · change cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = cyl.j₁ ≫ q ≫ v
      calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ f := by
          simp [Category.assoc]
        _ = f := by rw [cyl.j₁_c_p]; simp
        _ = f ≫ iB ≫ v := by
          simp [Category.assoc, hvB]
        _ = cyl.j₁ ≫ q ≫ v := by
          simpa [Category.assoc] using (congrArg (fun t => t ≫ v) hq1).symm
  letI : HasPushout cyl.c q := hC.hasPushout cyl.c q cyl.c_mem
  let M := pushout cyl.c q
  let i : A ⟶ M := iA ≫ pushout.inr cyl.c q
  let j : B ⟶ M := iB ≫ pushout.inr cyl.c q
  have hM : IsPushout cyl.c q (pushout.inl cyl.c q) (pushout.inr cyl.c q) :=
    IsPushout.of_hasPushout _ _
  have hiM : cofibrations C (pushout.inr cyl.c q) :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hM.flip cyl.c_mem
  have hi : cofibrations C i := by
    exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hiA hiM
  have hjPush : IsPushout (cyl.j₁ ≫ cyl.c) f (pushout.inl cyl.c q) j := by
    apply IsPushout.mk'
    · calc
        (cyl.j₁ ≫ cyl.c) ≫ pushout.inl cyl.c q = cyl.j₁ ≫ q ≫ pushout.inr cyl.c q := by
          calc
            (cyl.j₁ ≫ cyl.c) ≫ pushout.inl cyl.c q =
                cyl.j₁ ≫ (cyl.c ≫ pushout.inl cyl.c q) := by simp [Category.assoc]
            _ = cyl.j₁ ≫ (q ≫ pushout.inr cyl.c q) := by
              simpa [Category.assoc] using congrArg (fun t => cyl.j₁ ≫ t) hM.w
        _ = f ≫ j := by
          calc
            cyl.j₁ ≫ q ≫ pushout.inr cyl.c q =
                f ≫ iB ≫ pushout.inr cyl.c q := by
              simpa [Category.assoc] using
                congrArg (fun t => t ≫ pushout.inr cyl.c q) hq1
            _ = f ≫ j := by simp [j, Category.assoc]
    · intro T φ ψ hφ hψ
      apply PushoutCocone.IsColimit.hom_ext hM.isColimit hφ
      apply PushoutCocone.IsColimit.hom_ext hQ.isColimit
      · calc
          iA ≫ pushout.inr cyl.c q ≫ φ = cyl.j₀ ≫ cyl.c ≫ pushout.inl cyl.c q ≫ φ := by
            calc
              iA ≫ pushout.inr cyl.c q ≫ φ =
                  cyl.j₀ ≫ q ≫ pushout.inr cyl.c q ≫ φ := by
                simpa [Category.assoc] using
                  (congrArg (fun t => t ≫ pushout.inr cyl.c q ≫ φ) hq0).symm
              _ = cyl.j₀ ≫ cyl.c ≫ pushout.inl cyl.c q ≫ φ := by
                simpa [Category.assoc] using
                  congrArg (fun t => cyl.j₀ ≫ t ≫ φ) hM.w.symm
          _ = cyl.j₀ ≫ cyl.c ≫ pushout.inl cyl.c q ≫ ψ := by rw [hφ]
          _ = iA ≫ pushout.inr cyl.c q ≫ ψ := by
            calc
              cyl.j₀ ≫ cyl.c ≫ pushout.inl cyl.c q ≫ ψ =
                  cyl.j₀ ≫ q ≫ pushout.inr cyl.c q ≫ ψ := by
                simpa [Category.assoc] using congrArg (fun t => cyl.j₀ ≫ t ≫ ψ) hM.w
              _ = iA ≫ pushout.inr cyl.c q ≫ ψ := by
                simpa [Category.assoc] using
                  congrArg (fun t => t ≫ pushout.inr cyl.c q ≫ ψ) hq0
      · change iB ≫ pushout.inr cyl.c q ≫ φ = iB ≫ pushout.inr cyl.c q ≫ ψ
        simpa [j] using hψ
    · intro T x y hxy
      let a : A ⟶ T := cyl.j₀ ≫ cyl.c ≫ x
      let coconeD : PushoutCocone (hI.to A) (hI.to B) :=
        PushoutCocone.mk a y (IsInitial.hom_ext hI _ _)
      let d : Q ⟶ T := hQ.isColimit.desc coconeD
      have hdA : iA ≫ d = a := by
        change iA ≫ d = a
        exact hQ.isColimit.fac coconeD WalkingSpan.left
      have hdB : iB ≫ d = y := by
        change iB ≫ d = y
        exact hQ.isColimit.fac coconeD WalkingSpan.right
      have hqd : q ≫ d = cyl.c ≫ x := by
        apply PushoutCocone.IsColimit.hom_ext cyl.isPushout.isColimit
        · change cyl.j₀ ≫ q ≫ d = cyl.j₀ ≫ cyl.c ≫ x
          calc
            cyl.j₀ ≫ q ≫ d = iA ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) hq0
            _ = cyl.j₀ ≫ cyl.c ≫ x := by rw [hdA]
        · change cyl.j₁ ≫ q ≫ d = cyl.j₁ ≫ cyl.c ≫ x
          calc
            cyl.j₁ ≫ q ≫ d = f ≫ iB ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) hq1
            _ = f ≫ y := by simp [Category.assoc, hdB]
            _ = cyl.j₁ ≫ cyl.c ≫ x := by simpa [Category.assoc] using hxy.symm
      let coconeE : PushoutCocone cyl.c q := PushoutCocone.mk x d hqd.symm
      let z : M ⟶ T := hM.isColimit.desc coconeE
      have hzR : pushout.inr cyl.c q ≫ z = d := by
        change pushout.inr cyl.c q ≫ z = d
        exact hM.isColimit.fac coconeE WalkingSpan.right
      refine ⟨z, ?_, ?_⟩
      · change pushout.inl cyl.c q ≫ z = x
        exact hM.isColimit.fac coconeE WalkingSpan.left
      · change j ≫ z = y
        calc
          j ≫ z = iB ≫ d := by simp [j, Category.assoc, hzR]
          _ = y := hdB
  have hj : weakEquivalences C j :=
    hC.trivialCofibration_cobaseChange (cyl.j₁ ≫ cyl.c) f
      (pushout.inl cyl.c q) j hjPush hJ1c hJ1id
  let coconeW : PushoutCocone cyl.c q := PushoutCocone.mk (cyl.p ≫ f) v hcompat
  let w : M ⟶ B := hM.isColimit.desc coconeW
  have hwL : pushout.inl cyl.c q ≫ w = cyl.p ≫ f := by
    change pushout.inl cyl.c q ≫ w = cyl.p ≫ f
    exact hM.isColimit.fac coconeW WalkingSpan.left
  have hwR : pushout.inr cyl.c q ≫ w = v := by
    change pushout.inr cyl.c q ≫ w = v
    exact hM.isColimit.fac coconeW WalkingSpan.right
  have hiw : i ≫ w = f := by
    calc
      i ≫ w = iA ≫ v := by simp [i, Category.assoc, hwR]
      _ = f := hvA
  have hidB : weakEquivalences C (𝟙 B) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hleft : weakEquivalences C ((𝟙 B) ≫ j) := by simpa using hj
  have hjw : j ≫ w = 𝟙 B := by
    calc
      j ≫ w = iB ≫ v := by simp [j, Category.assoc, hwR]
      _ = 𝟙 B := hvB
  have hright : weakEquivalences C (j ≫ w) := by
    rw [hjw]
    exact hidB
  have hw : weakEquivalences C w := (hC.twoOutOfSix (𝟙 B) j w hleft hright).2.2.1
  exact ⟨M, i, w, hi, hw, hiw⟩

private theorem relativeCylinder_of_cofibration {A B : C} (i : A ⟶ B)
    (hi : cofibrations C i) : Nonempty (RelativeCylinder i) := by
  classical
  letI : HasPushout i i := hC.toIsCofibrationCategory.hasPushout i i hi
  let P := pushout i i
  let j0 : B ⟶ P := pushout.inl i i
  let j1 : B ⟶ P := pushout.inr i i
  have hP : IsPushout i i j0 j1 := IsPushout.of_hasPushout i i
  let fold : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  have hfold0 : j0 ≫ fold = 𝟙 B := hP.inl_desc _ _ (by simp)
  have hfold1 : j1 ≫ fold = 𝟙 B := hP.inr_desc _ _ (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ := cofibration_weak_equivalence_factorization fold
  have hc0 : j0 ≫ c ≫ p = 𝟙 B := by
    calc
      j0 ≫ c ≫ p = j0 ≫ (c ≫ p) := rfl
      _ = j0 ≫ fold := congrArg (fun t => j0 ≫ t) hcp
      _ = 𝟙 B := hfold0
  have hc1 : j1 ≫ c ≫ p = 𝟙 B := by
    calc
      j1 ≫ c ≫ p = j1 ≫ (c ≫ p) := rfl
      _ = j1 ≫ fold := congrArg (fun t => j1 ≫ t) hcp
      _ = 𝟙 B := hfold1
  exact ⟨⟨P, j0, j1, hP, I, c, p, hc, hp, hc0, hc1⟩⟩

private theorem cofibration_weakEquivalence_lift {A B X Y : C} (i : A ⟶ B)
    (u : A ⟶ X) (v : B ⟶ Y) (w : X ⟶ Y) (hi : cofibrations C i)
    (hw : weakEquivalences C w) (hcomm : i ≫ v = u ≫ w) :
    ∃ d : B ⟶ X, i ≫ d = u := by
  classical
  letI : HasPushout i u := hC.toIsCofibrationCategory.hasPushout i u hi
  let P := pushout i u
  let kB : B ⟶ P := pushout.inl i u
  let kX : X ⟶ P := pushout.inr i u
  have hP : IsPushout i u kB kX := IsPushout.of_hasPushout i u
  let q : P ⟶ Y := hP.desc v w hcomm
  have hqB : kB ≫ q = v := hP.inl_desc v w hcomm
  have hqX : kX ≫ q = w := hP.inr_desc v w hcomm
  obtain ⟨M, c, p, hc, hp, hcp⟩ := cofibration_weak_equivalence_factorization q
  have hkX : cofibrations C kX :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hP.flip hi
  let j : X ⟶ M := kX ≫ c
  have hj : cofibrations C j :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hkX hc
  have hjp : j ≫ p = w := by
    calc
      j ≫ p = kX ≫ (c ≫ p) := by simp [j, Category.assoc]
      _ = kX ≫ q := congrArg (fun t => kX ≫ t) hcp
      _ = w := hqX
  have hwjp : weakEquivalences C (j ≫ p) := by rw [hjp]; exact hw
  have hwpi : weakEquivalences C (p ≫ 𝟙 Y) := by simpa using hp
  have hjw : weakEquivalences C j := (hC.twoOutOfSix j p (𝟙 Y) hwjp hwpi).1
  obtain ⟨r, hr⟩ := hC.exists_retraction j hj hjw
  let k₀ : B ⟶ M := kB ≫ c
  let d : B ⟶ X := k₀ ≫ r
  refine ⟨d, ?_⟩
  calc
    i ≫ d = (i ≫ kB) ≫ c ≫ r := by simp [d, k₀, Category.assoc]
    _ = (u ≫ kX) ≫ c ≫ r := congrArg (fun t => t ≫ c ≫ r) hP.w
    _ = u ≫ (j ≫ r) := by simp [j, Category.assoc]
    _ = u := by rw [hr]; simp

private theorem relHomotopic_precompose {A B C₀ M T : C} (i : A ⟶ B)
    (u : A ⟶ C₀) (k : B ⟶ M) (j : C₀ ⟶ M)
    (hi : cofibrations C i) (hsq : i ≫ k = u ≫ j)
    {f g : M ⟶ T} (hfg : RelHomotopic j f g) :
    RelHomotopic i (k ≫ f) (k ≫ g) := by
  classical
  obtain ⟨cylJ, H, hJ0, hJ1⟩ := hfg
  obtain ⟨cylI⟩ := relativeCylinder_of_cofibration i hi
  have hCompat : i ≫ (k ≫ cylJ.j₀) = i ≫ (k ≫ cylJ.j₁) := by
    calc
      i ≫ (k ≫ cylJ.j₀) = (i ≫ k) ≫ cylJ.j₀ := (Category.assoc _ _ _).symm
      _ = (u ≫ j) ≫ cylJ.j₀ := congrArg (fun t => t ≫ cylJ.j₀) hsq
      _ = u ≫ (j ≫ cylJ.j₀) := Category.assoc _ _ _
      _ = u ≫ (j ≫ cylJ.j₁) := congrArg (fun t => u ≫ t) cylJ.isPushout.w
      _ = (u ≫ j) ≫ cylJ.j₁ := (Category.assoc _ _ _).symm
      _ = (i ≫ k) ≫ cylJ.j₁ := congrArg (fun t => t ≫ cylJ.j₁) hsq.symm
      _ = i ≫ (k ≫ cylJ.j₁) := Category.assoc _ _ _
  let φ : cylI.P ⟶ cylJ.P :=
    cylI.isPushout.desc (k ≫ cylJ.j₀) (k ≫ cylJ.j₁) hCompat
  have hφ0 : cylI.j₀ ≫ φ = k ≫ cylJ.j₀ :=
    cylI.isPushout.inl_desc _ _ hCompat
  have hφ1 : cylI.j₁ ≫ φ = k ≫ cylJ.j₁ :=
    cylI.isPushout.inr_desc _ _ hCompat
  have hRight0 : (cylI.j₀ ≫ (φ ≫ cylJ.c)) ≫ cylJ.p = k := by
    calc
      (cylI.j₀ ≫ (φ ≫ cylJ.c)) ≫ cylJ.p =
          k ≫ cylJ.j₀ ≫ cylJ.c ≫ cylJ.p := by
        simpa [Category.assoc] using
          congrArg (fun t => t ≫ cylJ.c ≫ cylJ.p) hφ0
      _ = k := by rw [cylJ.j₀_c_p]; simp
  have hRight1 : (cylI.j₁ ≫ (φ ≫ cylJ.c)) ≫ cylJ.p = k := by
    calc
      (cylI.j₁ ≫ (φ ≫ cylJ.c)) ≫ cylJ.p =
          k ≫ cylJ.j₁ ≫ cylJ.c ≫ cylJ.p := by
        simpa [Category.assoc] using
          congrArg (fun t => t ≫ cylJ.c ≫ cylJ.p) hφ1
      _ = k := by rw [cylJ.j₁_c_p]; simp
  have hRight0' : cylI.j₀ ≫ (φ ≫ cylJ.c) ≫ cylJ.p = k := by
    calc
      cylI.j₀ ≫ (φ ≫ cylJ.c) ≫ cylJ.p =
          (cylI.j₀ ≫ φ ≫ cylJ.c) ≫ cylJ.p :=
        (Category.assoc cylI.j₀ (φ ≫ cylJ.c) cylJ.p).symm
      _ = k := hRight0
  have hRight1' : cylI.j₁ ≫ (φ ≫ cylJ.c) ≫ cylJ.p = k := by
    calc
      cylI.j₁ ≫ (φ ≫ cylJ.c) ≫ cylJ.p =
          (cylI.j₁ ≫ φ ≫ cylJ.c) ≫ cylJ.p :=
        (Category.assoc cylI.j₁ (φ ≫ cylJ.c) cylJ.p).symm
      _ = k := hRight1
  have hComm : cylI.c ≫ (cylI.p ≫ k) = (φ ≫ cylJ.c) ≫ cylJ.p := by
    apply cylI.isPushout.hom_ext
    · calc
        cylI.j₀ ≫ cylI.c ≫ (cylI.p ≫ k) = k := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ k) cylI.j₀_c_p
        _ = cylI.j₀ ≫ (φ ≫ cylJ.c) ≫ cylJ.p := hRight0'.symm
    · calc
        cylI.j₁ ≫ cylI.c ≫ (cylI.p ≫ k) = k := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ k) cylI.j₁_c_p
        _ = cylI.j₁ ≫ (φ ≫ cylJ.c) ≫ cylJ.p := hRight1'.symm
  obtain ⟨t, ht⟩ := cofibration_weakEquivalence_lift cylI.c
    (φ ≫ cylJ.c) (cylI.p ≫ k) cylJ.p cylI.c_mem cylJ.p_mem hComm
  let H' : cylI.I ⟶ T := t ≫ H
  have h0 : cylI.j₀ ≫ cylI.c ≫ H' = k ≫ f := by
    calc
      cylI.j₀ ≫ cylI.c ≫ H' = cylI.j₀ ≫ (cylI.c ≫ t) ≫ H := by
        simp [H', Category.assoc]
      _ = cylI.j₀ ≫ (φ ≫ cylJ.c) ≫ H := congrArg (fun t => cylI.j₀ ≫ t ≫ H) ht
      _ = k ≫ (cylJ.j₀ ≫ cylJ.c ≫ H) := by
        simpa [Category.assoc] using congrArg (fun t => t ≫ cylJ.c ≫ H) hφ0
      _ = k ≫ f := congrArg (fun t => k ≫ t) hJ0
  have h1 : cylI.j₁ ≫ cylI.c ≫ H' = k ≫ g := by
    calc
      cylI.j₁ ≫ cylI.c ≫ H' = cylI.j₁ ≫ (cylI.c ≫ t) ≫ H := by
        simp [H', Category.assoc]
      _ = cylI.j₁ ≫ (φ ≫ cylJ.c) ≫ H := congrArg (fun t => cylI.j₁ ≫ t ≫ H) ht
      _ = k ≫ (cylJ.j₁ ≫ cylJ.c ≫ H) := by
        simpa [Category.assoc] using congrArg (fun t => t ≫ cylJ.c ≫ H) hφ1
      _ = k ≫ g := congrArg (fun t => k ≫ t) hJ1
  exact ⟨cylI, H', h0, h1⟩

private theorem relHomotopic_of_trivialCof {A B T : C} (i : A ⟶ B)
    (hi : cofibrations C i) (hwi : weakEquivalences C i)
    (f g : B ⟶ T) (hfg : i ≫ f = i ≫ g) : RelHomotopic i f g := by
  classical
  letI : HasPushout i i := hC.toIsCofibrationCategory.hasPushout i i hi
  let P := pushout i i
  let j0 : B ⟶ P := pushout.inl i i
  let j1 : B ⟶ P := pushout.inr i i
  have hP : IsPushout i i j0 j1 := IsPushout.of_hasPushout i i
  let fold : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  have hfold0 : j0 ≫ fold = 𝟙 B := hP.inl_desc _ _ (by simp)
  have hfold1 : j1 ≫ fold = 𝟙 B := hP.inr_desc _ _ (by simp)
  have hj0w : weakEquivalences C j0 :=
    hC.trivialCofibration_cobaseChange i i j1 j0 hP.flip hi hwi
  have hId : weakEquivalences C (𝟙 B) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hLeft : weakEquivalences C ((𝟙 B) ≫ j0) := by simpa using hj0w
  have hRight : weakEquivalences C (j0 ≫ fold) := by rw [hfold0]; exact hId
  have hFold : weakEquivalences C fold :=
    (hC.twoOutOfSix (𝟙 B) j0 fold hLeft hRight).2.2.1
  let cyl : RelativeCylinder i :=
    ⟨P, j0, j1, hP, P, 𝟙 P, fold,
      hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance), hFold,
      by simpa using hfold0, by simpa using hfold1⟩
  let H : P ⟶ T := hP.desc f g hfg
  have h0Base : j0 ≫ H = f := by
    dsimp [H]
    exact hP.inl_desc f g hfg
  have h1Base : j1 ≫ H = g := by
    dsimp [H]
    exact hP.inr_desc f g hfg
  have h0 : cyl.j₀ ≫ cyl.c ≫ H = f := by
    dsimp [cyl]
    simpa only [Category.id_comp] using h0Base
  have h1 : cyl.j₁ ≫ cyl.c ≫ H = g := by
    dsimp [cyl]
    simpa only [Category.id_comp] using h1Base
  exact ⟨cyl, H, h0, h1⟩

private theorem relHomotopic_to_homotopic {A B T : C} (i : A ⟶ B)
    {f g : B ⟶ T} (h : RelHomotopic i f g) : Homotopic f g := by
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  have hSquare : (hI.to B) ≫ (𝟙 B) = (hI.to A) ≫ i := hI.hom_ext _ _
  have hRel := relHomotopic_precompose (hI.to B) (hI.to A) (𝟙 B) i
    (hC.toIsCofibrationCategory.initial_cofibration hI B) hSquare h
  exact ⟨I, hI, by simpa using hRel⟩

private theorem homotopic_rebase_initial {I X Y : C} (hI : IsInitial I)
    {f g : X ⟶ Y} (h : Homotopic f g) : RelHomotopic (hI.to X) f g := by
  classical
  obtain ⟨J, hJ, hRel⟩ := h
  let e : I ≅ J := hI.uniqueUpToIso hJ
  have hSquare : hI.to X ≫ (𝟙 X) = e.hom ≫ hJ.to X := hI.hom_ext _ _
  simpa using relHomotopic_precompose (hI.to X) e.hom (𝟙 X) (hJ.to X)
    (hC.toIsCofibrationCategory.initial_cofibration hI X) hSquare hRel

private theorem homotopic_precompose {X Y Z : C} {f g : X ⟶ Y}
    (h : Homotopic f g) (u : Z ⟶ X) : Homotopic (u ≫ f) (u ≫ g) := by
  classical
  rcases h with ⟨I, hI, hRel⟩
  have hSquare : (hI.to Z) ≫ u = (𝟙 I) ≫ (hI.to X) := hI.hom_ext _ _
  have hRel' := relHomotopic_precompose (hI.to Z) (𝟙 I) u (hI.to X)
    (hC.toIsCofibrationCategory.initial_cofibration hI Z) hSquare hRel
  exact ⟨I, hI, by simpa using hRel'⟩

private theorem homotopic_postcompose {X Y Z : C} {f g : X ⟶ Y}
    (h : Homotopic f g) (u : Y ⟶ Z) : Homotopic (f ≫ u) (g ≫ u) := by
  rcases h with ⟨I, hI, cyl, H, h0, h1⟩
  refine ⟨I, hI, cyl, H ≫ u, ?_, ?_⟩
  · simpa [Category.assoc] using congrArg (fun t => t ≫ u) h0
  · simpa [Category.assoc] using congrArg (fun t => t ≫ u) h1

private theorem homotopic_symm {X Y : C} {f g : X ⟶ Y} (h : Homotopic f g) :
    Homotopic g f := by
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  have hRel := homotopic_rebase_initial hI h
  have hRelEquiv : Equivalence (RelHomotopic (X := Y) (hI.to X)) :=
    (Packages.relHomotopic_equivalence (C := C) (A := I) (B := X) (X := Y)
      (hI.to X) (hC.toIsCofibrationCategory.initial_cofibration hI X)).1
  exact ⟨I, hI, hRelEquiv.symm hRel⟩

private theorem homotopic_trans {X Y : C} {f g h : X ⟶ Y}
    (hfg : Homotopic f g) (hgh : Homotopic g h) : Homotopic f h := by
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  have hfg' := homotopic_rebase_initial hI hfg
  have hgh' := homotopic_rebase_initial hI hgh
  have hRelEquiv : Equivalence (RelHomotopic (X := Y) (hI.to X)) :=
    (Packages.relHomotopic_equivalence (C := C) (A := I) (B := X) (X := Y)
      (hI.to X) (hC.toIsCofibrationCategory.initial_cofibration hI X)).1
  exact ⟨I, hI, hRelEquiv.trans hfg' hgh'⟩

private theorem cofibration_weakEquivalence_lift_homotopy {A B X Y : C}
    (i : A ⟶ B) (u : A ⟶ X) (v : B ⟶ Y) (w : X ⟶ Y)
    (hi : cofibrations C i) (hw : weakEquivalences C w)
    (hcomm : i ≫ v = u ≫ w) :
    ∃ d : B ⟶ X, i ≫ d = u ∧ RelHomotopic i (d ≫ w) v := by
  classical
  letI : HasPushout i u := hC.toIsCofibrationCategory.hasPushout i u hi
  let P := pushout i u
  let kB : B ⟶ P := pushout.inl i u
  let kX : X ⟶ P := pushout.inr i u
  have hP : IsPushout i u kB kX := IsPushout.of_hasPushout i u
  let q : P ⟶ Y := hP.desc v w hcomm
  have hqB : kB ≫ q = v := hP.inl_desc v w hcomm
  have hqX : kX ≫ q = w := hP.inr_desc v w hcomm
  obtain ⟨M, c, p, hc, hp, hcp⟩ := cofibration_weak_equivalence_factorization q
  have hkX : cofibrations C kX :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hP.flip hi
  let j : X ⟶ M := kX ≫ c
  have hj : cofibrations C j :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hkX hc
  have hjp : j ≫ p = w := by
    calc
      j ≫ p = kX ≫ (c ≫ p) := by simp [j, Category.assoc]
      _ = kX ≫ q := congrArg (fun t => kX ≫ t) hcp
      _ = w := hqX
  have hwjp : weakEquivalences C (j ≫ p) := by rw [hjp]; exact hw
  have hwpi : weakEquivalences C (p ≫ 𝟙 Y) := by simpa using hp
  have hjw : weakEquivalences C j := (hC.twoOutOfSix j p (𝟙 Y) hwjp hwpi).1
  obtain ⟨r, hr⟩ := hC.exists_retraction j hj hjw
  let k₀ : B ⟶ M := kB ≫ c
  let d : B ⟶ X := k₀ ≫ r
  have hUpper : i ≫ d = u := by
    calc
      i ≫ d = (i ≫ kB) ≫ c ≫ r := by
        change i ≫ (kB ≫ c) ≫ r = (i ≫ kB) ≫ c ≫ r
        calc
          i ≫ (kB ≫ c) ≫ r = i ≫ (kB ≫ (c ≫ r)) := by
            exact congrArg (fun t => i ≫ t) (Category.assoc kB c r)
          _ = (i ≫ kB) ≫ (c ≫ r) := (Category.assoc i kB (c ≫ r)).symm
          _ = (i ≫ kB) ≫ c ≫ r := rfl
      _ = (u ≫ kX) ≫ c ≫ r := congrArg (fun t => t ≫ c ≫ r) hP.w
      _ = u ≫ (j ≫ r) := by simp [j, Category.assoc]
      _ = u := by rw [hr]; simp
  letI : HasPushout j j := hC.toIsCofibrationCategory.hasPushout j j hj
  let Pj := pushout j j
  let j0 : M ⟶ Pj := pushout.inl j j
  let j1 : M ⟶ Pj := pushout.inr j j
  have hPj : IsPushout j j j0 j1 := IsPushout.of_hasPushout j j
  let fold : Pj ⟶ M := hPj.desc (𝟙 M) (𝟙 M) (by simp)
  have hfold0 : j0 ≫ fold = 𝟙 M := hPj.inl_desc _ _ (by simp)
  have hfold1 : j1 ≫ fold = 𝟙 M := hPj.inr_desc _ _ (by simp)
  have hj0w : weakEquivalences C j0 :=
    hC.trivialCofibration_cobaseChange j j j1 j0 hPj.flip hj hjw
  have hIdM : weakEquivalences C (𝟙 M) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hIdj0 : weakEquivalences C ((𝟙 M) ≫ j0) := by simpa using hj0w
  have hj0fold : weakEquivalences C (j0 ≫ fold) := by rw [hfold0]; exact hIdM
  have hfoldW : weakEquivalences C fold :=
    (hC.twoOutOfSix (𝟙 M) j0 fold hIdj0 hj0fold).2.2.1
  let cylJ : RelativeCylinder j :=
    ⟨Pj, j0, j1, hPj, Pj, 𝟙 Pj, fold,
      hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance), hfoldW,
      by simpa using hfold0, by simpa using hfold1⟩
  have hCompatJ : j ≫ (r ≫ j) = j ≫ (𝟙 M) := by
    calc
      j ≫ (r ≫ j) = (j ≫ r) ≫ j := (Category.assoc _ _ _).symm
      _ = j := by rw [hr]; simp
      _ = j ≫ (𝟙 M) := by simp
  let HJ : Pj ⟶ M := hPj.desc (r ≫ j) (𝟙 M) hCompatJ
  have hJ0base : j0 ≫ HJ = r ≫ j := hPj.inl_desc (r ≫ j) (𝟙 M) hCompatJ
  have hJ1base : j1 ≫ HJ = 𝟙 M := hPj.inr_desc (r ≫ j) (𝟙 M) hCompatJ
  have hJ0 : cylJ.j₀ ≫ cylJ.c ≫ HJ = r ≫ j := by
    change j0 ≫ (𝟙 Pj) ≫ HJ = r ≫ j
    simpa using hJ0base
  have hJ1 : cylJ.j₁ ≫ cylJ.c ≫ HJ = 𝟙 M := by
    change j1 ≫ (𝟙 Pj) ≫ HJ = 𝟙 M
    simpa using hJ1base
  have hRelJ : RelHomotopic j (r ≫ j) (𝟙 M) := ⟨cylJ, HJ, hJ0, hJ1⟩
  have hSquare : i ≫ k₀ = u ≫ j := by
    calc
      i ≫ k₀ = (i ≫ kB) ≫ c := (Category.assoc _ _ _).symm
      _ = (u ≫ kX) ≫ c := congrArg (fun t => t ≫ c) hP.w
      _ = u ≫ j := by simp [j, Category.assoc]
  have hRelLower : RelHomotopic i (k₀ ≫ r ≫ j) k₀ := by
    simpa using relHomotopic_precompose i u k₀ j hi hSquare hRelJ
  have hWComp : j ≫ p = w := hjp
  have hVComp : k₀ ≫ p = v := by
    calc
      k₀ ≫ p = kB ≫ (c ≫ p) := by simp [k₀, Category.assoc]
      _ = kB ≫ q := congrArg (fun t => kB ≫ t) hcp
      _ = v := hqB
  have hLowerComp : (k₀ ≫ r ≫ j) ≫ p = d ≫ w := by
    calc
      (k₀ ≫ r ≫ j) ≫ p = k₀ ≫ ((r ≫ j) ≫ p) :=
        Category.assoc k₀ (r ≫ j) p
      _ = k₀ ≫ (r ≫ (j ≫ p)) :=
        congrArg (fun t => k₀ ≫ t) (Category.assoc r j p)
      _ = (k₀ ≫ r) ≫ (j ≫ p) :=
        (Category.assoc k₀ r (j ≫ p)).symm
      _ = (k₀ ≫ r) ≫ w := congrArg (fun t => (k₀ ≫ r) ≫ t) hWComp
      _ = d ≫ w := rfl
  rcases hRelLower with ⟨cyl, H, h0, h1⟩
  have h0' : cyl.j₀ ≫ cyl.c ≫ (H ≫ p) = d ≫ w := by
    calc
      cyl.j₀ ≫ cyl.c ≫ (H ≫ p) =
          (cyl.j₀ ≫ cyl.c ≫ H) ≫ p := by
        calc
          cyl.j₀ ≫ cyl.c ≫ (H ≫ p) = (cyl.j₀ ≫ cyl.c) ≫ (H ≫ p) :=
            (Category.assoc cyl.j₀ cyl.c (H ≫ p)).symm
          _ = ((cyl.j₀ ≫ cyl.c) ≫ H) ≫ p :=
            (Category.assoc (cyl.j₀ ≫ cyl.c) H p).symm
          _ = (cyl.j₀ ≫ cyl.c ≫ H) ≫ p :=
            congrArg (fun t => t ≫ p) (Category.assoc cyl.j₀ cyl.c H)
      _ = (k₀ ≫ r ≫ j) ≫ p := congrArg (fun t => t ≫ p) h0
      _ = d ≫ w := hLowerComp
  have h1' : cyl.j₁ ≫ cyl.c ≫ (H ≫ p) = v := by
    calc
      cyl.j₁ ≫ cyl.c ≫ (H ≫ p) =
          (cyl.j₁ ≫ cyl.c ≫ H) ≫ p := by
        calc
          cyl.j₁ ≫ cyl.c ≫ (H ≫ p) = (cyl.j₁ ≫ cyl.c) ≫ (H ≫ p) :=
            (Category.assoc cyl.j₁ cyl.c (H ≫ p)).symm
          _ = ((cyl.j₁ ≫ cyl.c) ≫ H) ≫ p :=
            (Category.assoc (cyl.j₁ ≫ cyl.c) H p).symm
          _ = (cyl.j₁ ≫ cyl.c ≫ H) ≫ p :=
            congrArg (fun t => t ≫ p) (Category.assoc cyl.j₁ cyl.c H)
      _ = k₀ ≫ p := congrArg (fun t => t ≫ p) h1
      _ = v := hVComp
  exact ⟨d, hUpper, ⟨cyl, H ≫ p, h0', h1'⟩⟩

private theorem cofibration_homotopy_extension {A B X : C} (i : A ⟶ B)
    (hi : cofibrations C i) {f : B ⟶ X} {g : A ⟶ X}
    (h : Homotopic (i ≫ f) g) :
    ∃ f' : B ⟶ X, i ≫ f' = g ∧ Homotopic f' f := by
  classical
  rcases h with ⟨I, hI, hRel⟩
  rcases hRel with ⟨cyl, H, h0, h1⟩
  let j0 : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let j1 : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  have hj0 : cofibrations C cyl.j₀ :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout cyl.isPushout
      (hC.toIsCofibrationCategory.initial_cofibration hI A)
  have hj0c : cofibrations C j0 :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hj0 cyl.c_mem
  have hj0p : j0 ≫ cyl.p = 𝟙 A := by
    simpa [j0, Category.assoc] using cyl.j₀_c_p
  have hIdA : weakEquivalences C (𝟙 A) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hj0pW : weakEquivalences C (j0 ≫ cyl.p) := by rw [hj0p]; exact hIdA
  have hpIdA : weakEquivalences C (cyl.p ≫ 𝟙 A) := by simpa using cyl.p_mem
  have hj0w : weakEquivalences C j0 :=
    (hC.twoOutOfSix j0 cyl.p (𝟙 A) hj0pW hpIdA).1
  letI : HasPushout i j0 := hC.toIsCofibrationCategory.hasPushout i j0 hi
  let P := pushout i j0
  let kB : B ⟶ P := pushout.inl i j0
  let kI : cyl.I ⟶ P := pushout.inr i j0
  have hP : IsPushout i j0 kB kI := IsPushout.of_hasPushout i j0
  have h0j : j0 ≫ H = i ≫ f := by
    dsimp [j0]
    exact (Category.assoc cyl.j₀ cyl.c H).trans h0
  have h1j : j1 ≫ H = g := by
    dsimp [j1]
    exact (Category.assoc cyl.j₁ cyl.c H).trans h1
  let q : P ⟶ X := hP.desc f H h0j.symm
  have hqB : kB ≫ q = f := hP.inl_desc f H h0j.symm
  have hqI : kI ≫ q = H := hP.inr_desc f H h0j.symm
  have hCompat : i ≫ 𝟙 B = j0 ≫ (cyl.p ≫ i) := by
    calc
      i ≫ 𝟙 B = i := by simp
      _ = (j0 ≫ cyl.p) ≫ i := by rw [hj0p]; simp
      _ = j0 ≫ (cyl.p ≫ i) := Category.assoc _ _ _
  let p : P ⟶ B := hP.desc (𝟙 B) (cyl.p ≫ i) hCompat
  have hkp : kB ≫ p = 𝟙 B := hP.inl_desc _ _ hCompat
  have hkip : kI ≫ p = cyl.p ≫ i := hP.inr_desc _ _ hCompat
  have hkBW : weakEquivalences C kB :=
    hC.trivialCofibration_cobaseChange j0 i kI kB hP.flip hj0c hj0w
  have hIdB : weakEquivalences C (𝟙 B) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hIdkB : weakEquivalences C ((𝟙 B) ≫ kB) := by simpa using hkBW
  have hkBp : weakEquivalences C (kB ≫ p) := by rw [hkp]; exact hIdB
  have hpW : weakEquivalences C p :=
    (hC.twoOutOfSix (𝟙 B) kB p hIdkB hkBp).2.2.1
  let j1p : A ⟶ P := j1 ≫ kI
  have hj1p : j1p ≫ p = i := by
    have hj1pRaw : j1 ≫ cyl.p = 𝟙 A := by
      dsimp [j1]
      exact (Category.assoc cyl.j₁ cyl.c cyl.p).trans cyl.j₁_c_p
    calc
      j1p ≫ p = j1 ≫ (kI ≫ p) := Category.assoc _ _ _
      _ = j1 ≫ (cyl.p ≫ i) := congrArg (fun t => j1 ≫ t) hkip
      _ = (j1 ≫ cyl.p) ≫ i := (Category.assoc _ _ _).symm
      _ = (𝟙 A) ≫ i := congrArg (fun t => t ≫ i) hj1pRaw
      _ = i := by simp
  have hcomm : i ≫ 𝟙 B = j1p ≫ p := by
    calc
      i ≫ 𝟙 B = i := by simp
      _ = j1p ≫ p := hj1p.symm
  obtain ⟨s, his, hsRel⟩ :=
    cofibration_weakEquivalence_lift_homotopy i j1p (𝟙 B) p hi hpW hcomm
  have hExt : i ≫ (s ≫ q) = g := by
    calc
      i ≫ (s ≫ q) = (i ≫ s) ≫ q := (Category.assoc _ _ _).symm
      _ = j1p ≫ q := congrArg (fun t => t ≫ q) his
      _ = j1 ≫ (kI ≫ q) := Category.assoc _ _ _
      _ = j1 ≫ H := congrArg (fun t => j1 ≫ t) hqI
      _ = g := h1j
  have hSP : Homotopic (s ≫ p) (𝟙 B) := relHomotopic_to_homotopic i hsRel
  obtain ⟨qInv, hpq, hqp⟩ := (Packages.weakEquivalence_iff (C := C) p).1 hpW
  have hSq : Homotopic (s ≫ p ≫ qInv) s := by
    simpa [Category.assoc] using homotopic_precompose hpq s
  have hSPq : Homotopic (s ≫ p ≫ qInv) qInv := by
    simpa [Category.assoc] using homotopic_postcompose hSP qInv
  have hsInv : Homotopic s qInv :=
    homotopic_trans (homotopic_symm hSq) hSPq
  have hkEq : kB ≫ p ≫ qInv = qInv := by
    calc
      kB ≫ p ≫ qInv = (kB ≫ p) ≫ qInv := (Category.assoc _ _ _).symm
      _ = (𝟙 B) ≫ qInv := congrArg (fun t => t ≫ qInv) hkp
      _ = qInv := by simp
  have hkInv : Homotopic qInv kB := by
    simpa only [hkEq, Category.comp_id] using homotopic_precompose hpq kB
  have hsk : Homotopic s kB := homotopic_trans hsInv hkInv
  have hfinal : Homotopic (s ≫ q) f := by
    simpa [Category.assoc, hqB] using homotopic_postcompose hsk q
  exact ⟨s ≫ q, hExt, hfinal⟩

private theorem pathObj_left_cofibration_extension {A : PathObj C} {Y : C}
    (v : A.l ⟶ Y) (hv : cofibrations C v) :
    ∃ (B : PathObj C) (e : B.l = Y) (j : A ⟶ B),
      cofibrations (PathObj C) j ∧ j.l = v ≫ eqToHom e.symm := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let bA := pathBoundaryData hI A
  letI : HasPushout v A.il := hC.toIsCofibrationCategory.hasPushout v A.il hv
  let P₁ := pushout v A.il
  let kA : A.c ⟶ P₁ := pushout.inr v A.il
  let yP : Y ⟶ P₁ := pushout.inl v A.il
  have hP₁ : IsPushout A.il v kA yP := (IsPushout.of_hasPushout v A.il).flip
  have hyP : weakEquivalences C yP :=
    Packages.weakEquivalence_cobaseChange v A.il yP kA hP₁.flip hv A.il_mem
  let fR : A.r ⟶ P₁ := A.ir ≫ kA
  obtain ⟨R, a, wR, ha, hwR, hawR⟩ := cofibration_weak_equivalence_factorization fR
  letI : HasPushout (hI.to Y) (hI.to R) :=
    hC.toIsCofibrationCategory.hasPushout (hI.to Y) (hI.to R)
      (hC.toIsCofibrationCategory.initial_cofibration hI Y)
  let E := pushout (hI.to Y) (hI.to R)
  let eY : Y ⟶ E := pushout.inl (hI.to Y) (hI.to R)
  let eR : R ⟶ E := pushout.inr (hI.to Y) (hI.to R)
  have hE : IsPushout (hI.to Y) (hI.to R) eY eR := IsPushout.of_hasPushout _ _
  have hCompatE : hI.to A.l ≫ (v ≫ eY) = hI.to A.r ≫ (a ≫ eR) := hI.hom_ext _ _
  let bE : bA.P ⟶ E := bA.isPushout.desc (v ≫ eY) (a ≫ eR) hCompatE
  have hbEL : bA.inl ≫ bE = v ≫ eY := bA.isPushout.inl_desc _ _ hCompatE
  have hbER : bA.inr ≫ bE = a ≫ eR := bA.isPushout.inr_desc _ _ hCompatE
  letI : HasPushout bA.toCenter bE :=
    hC.toIsCofibrationCategory.hasPushout bA.toCenter bE bA.toCenter_mem
  let T := pushout bA.toCenter bE
  let kC : A.c ⟶ T := pushout.inl bA.toCenter bE
  let kE : E ⟶ T := pushout.inr bA.toCenter bE
  have hT : IsPushout bA.toCenter bE kC kE := IsPushout.of_hasPushout _ _
  have hkE : cofibrations C kE :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hT.flip
      bA.toCenter_mem
  let yT : Y ⟶ T := eY ≫ kE
  let rT : R ⟶ T := eR ≫ kE
  have hCompatP₁ : A.il ≫ kC = v ≫ yT := by
    calc
      A.il ≫ kC = (bA.inl ≫ bA.toCenter) ≫ kC :=
        congrArg (fun t => t ≫ kC) bA.inl_toCenter.symm
      _ = bA.inl ≫ (bA.toCenter ≫ kC) := Category.assoc _ _ _
      _ = bA.inl ≫ (bE ≫ kE) := congrArg (fun t => bA.inl ≫ t) hT.w
      _ = (bA.inl ≫ bE) ≫ kE := (Category.assoc _ _ _).symm
      _ = (v ≫ eY) ≫ kE := congrArg (fun t => t ≫ kE) hbEL
      _ = v ≫ yT := by simp [yT, Category.assoc]
  let t₁ : P₁ ⟶ T := hP₁.desc kC yT hCompatP₁
  have ht₁kA : kA ≫ t₁ = kC := hP₁.inl_desc kC yT hCompatP₁
  have ht₁y : yP ≫ t₁ = yT := hP₁.inr_desc kC yT hCompatP₁
  have hCompatR : fR ≫ t₁ = a ≫ rT := by
    calc
      fR ≫ t₁ = A.ir ≫ (kA ≫ t₁) := by simp [fR, Category.assoc]
      _ = A.ir ≫ kC := congrArg (fun t => A.ir ≫ t) ht₁kA
      _ = (bA.inr ≫ bA.toCenter) ≫ kC :=
        congrArg (fun t => t ≫ kC) bA.inr_toCenter.symm
      _ = bA.inr ≫ (bA.toCenter ≫ kC) := Category.assoc _ _ _
      _ = bA.inr ≫ (bE ≫ kE) := congrArg (fun t => bA.inr ≫ t) hT.w
      _ = (bA.inr ≫ bE) ≫ kE := (Category.assoc _ _ _).symm
      _ = (a ≫ eR) ≫ kE := congrArg (fun t => t ≫ kE) hbER
      _ = a ≫ rT := by simp [rT, Category.assoc]
  have hSecond : IsPushout fR a t₁ rT := by
    apply IsPushout.mk'
    · exact hCompatR
    · intro Z φ ψ hφ hψ
      apply hT.hom_ext
      · calc
          kC ≫ φ = (kA ≫ t₁) ≫ φ := congrArg (fun t => t ≫ φ) ht₁kA.symm
          _ = kA ≫ (t₁ ≫ φ) := Category.assoc _ _ _
          _ = kA ≫ (t₁ ≫ ψ) := congrArg (fun t => kA ≫ t) hφ
          _ = (kA ≫ t₁) ≫ ψ := (Category.assoc _ _ _).symm
          _ = kC ≫ ψ := congrArg (fun t => t ≫ ψ) ht₁kA
      · apply hE.hom_ext
        · have hy : yT ≫ φ = yT ≫ ψ := by
            calc
              yT ≫ φ = (yP ≫ t₁) ≫ φ := congrArg (fun t => t ≫ φ) ht₁y.symm
              _ = yP ≫ (t₁ ≫ φ) := Category.assoc _ _ _
              _ = yP ≫ (t₁ ≫ ψ) := congrArg (fun t => yP ≫ t) hφ
              _ = (yP ≫ t₁) ≫ ψ := (Category.assoc _ _ _).symm
              _ = yT ≫ ψ := congrArg (fun t => t ≫ ψ) ht₁y
          simpa [yT, Category.assoc] using hy
        · simpa [rT, Category.assoc] using hψ
    · intro Z φ ψ hφψ
      let eD : E ⟶ Z := hE.desc (yP ≫ φ) ψ (hI.hom_ext _ _)
      have heDY : eY ≫ eD = yP ≫ φ := hE.inl_desc _ _ (hI.hom_ext _ _)
      have heDR : eR ≫ eD = ψ := hE.inr_desc _ _ (hI.hom_ext _ _)
      have hCompatD : bA.toCenter ≫ (kA ≫ φ) = bE ≫ eD := by
        apply bA.isPushout.hom_ext
        · calc
            bA.inl ≫ bA.toCenter ≫ (kA ≫ φ) =
                A.il ≫ (kA ≫ φ) := by
              calc
                bA.inl ≫ bA.toCenter ≫ (kA ≫ φ) =
                    (bA.inl ≫ bA.toCenter) ≫ (kA ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.il ≫ (kA ≫ φ) := congrArg (fun z => z ≫ (kA ≫ φ)) bA.inl_toCenter
            _ = v ≫ yP ≫ φ := by
              calc
                A.il ≫ (kA ≫ φ) = (A.il ≫ kA) ≫ φ := (Category.assoc _ _ _).symm
                _ = (v ≫ yP) ≫ φ := congrArg (fun t => t ≫ φ) hP₁.w
                _ = v ≫ yP ≫ φ := Category.assoc _ _ _
            _ = bA.inl ≫ bE ≫ eD := by
              calc
                v ≫ yP ≫ φ = v ≫ (yP ≫ φ) := rfl
                _ = v ≫ (eY ≫ eD) := congrArg (fun z => v ≫ z) heDY.symm
                _ = (v ≫ eY) ≫ eD := (Category.assoc _ _ _).symm
                _ = (bA.inl ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbEL.symm
                _ = bA.inl ≫ bE ≫ eD := Category.assoc _ _ _
        · calc
            bA.inr ≫ bA.toCenter ≫ (kA ≫ φ) =
                A.ir ≫ (kA ≫ φ) := by
              calc
                bA.inr ≫ bA.toCenter ≫ (kA ≫ φ) =
                    (bA.inr ≫ bA.toCenter) ≫ (kA ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.ir ≫ (kA ≫ φ) := congrArg (fun z => z ≫ (kA ≫ φ)) bA.inr_toCenter
            _ = fR ≫ φ := by simp [fR, Category.assoc]
            _ = a ≫ ψ := hφψ
            _ = bA.inr ≫ bE ≫ eD := by
              calc
                a ≫ ψ = a ≫ (eR ≫ eD) := congrArg (fun z => a ≫ z) heDR.symm
                _ = (a ≫ eR) ≫ eD := (Category.assoc _ _ _).symm
                _ = (bA.inr ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbER.symm
                _ = bA.inr ≫ bE ≫ eD := Category.assoc _ _ _
      let d : T ⟶ Z := hT.desc (kA ≫ φ) eD hCompatD
      have hdC : kC ≫ d = kA ≫ φ := hT.inl_desc _ _ hCompatD
      have hdE : kE ≫ d = eD := hT.inr_desc _ _ hCompatD
      have hd₁ : t₁ ≫ d = φ := by
        apply hP₁.hom_ext
        · calc
            kA ≫ t₁ ≫ d = kC ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) ht₁kA
            _ = kA ≫ φ := hdC
        · calc
            yP ≫ t₁ ≫ d = yT ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) ht₁y
            _ = eY ≫ eD := by simp [yT, Category.assoc, hdE]
            _ = yP ≫ φ := heDY
      have hd₂ : rT ≫ d = ψ := by
        calc
          rT ≫ d = eR ≫ (kE ≫ d) := by simp [rT, Category.assoc]
          _ = eR ≫ eD := congrArg (fun t => eR ≫ t) hdE
          _ = ψ := heDR
      exact ⟨d, hd₁, hd₂⟩
  have hTCompat : fR ≫ 𝟙 P₁ = a ≫ wR := by
    rw [hawR]
    simp
  let t : T ⟶ P₁ := hSecond.desc (𝟙 P₁) wR hTCompat
  have ht₁ : t₁ ≫ t = 𝟙 P₁ := hSecond.inl_desc _ _ hTCompat
  have ht₂ : rT ≫ t = wR := hSecond.inr_desc _ _ hTCompat
  obtain ⟨M, c, p, hc, hp, hcp⟩ := cofibration_weak_equivalence_factorization t
  have hYp : yT ≫ c ≫ p = yP := by
    calc
      yT ≫ c ≫ p = yT ≫ (c ≫ p) := rfl
      _ = yT ≫ t := congrArg (fun z => yT ≫ z) hcp
      _ = yP := by
        calc
          yT ≫ t = (yP ≫ t₁) ≫ t := congrArg (fun z => z ≫ t) ht₁y.symm
          _ = yP ≫ (t₁ ≫ t) := Category.assoc _ _ _
          _ = yP := by rw [ht₁]; simp
  have hRp : rT ≫ c ≫ p = wR := by
    calc
      rT ≫ c ≫ p = rT ≫ (c ≫ p) := rfl
      _ = rT ≫ t := congrArg (fun z => rT ≫ z) hcp
      _ = wR := ht₂
  have hyComp : weakEquivalences C ((yT ≫ c) ≫ p) := by
    rw [Category.assoc yT c p, hYp]
    exact hyP
  have hwiId : weakEquivalences C (p ≫ 𝟙 P₁) := by simpa using hp
  have hyWE : weakEquivalences C (yT ≫ c) :=
    (hC.twoOutOfSix (yT ≫ c) p (𝟙 P₁) hyComp hwiId).1
  have hrComp : weakEquivalences C ((rT ≫ c) ≫ p) := by
    rw [Category.assoc rT c p, hRp]
    exact hwR
  have hrWE : weakEquivalences C (rT ≫ c) :=
    (hC.twoOutOfSix (rT ≫ c) p (𝟙 P₁) hrComp hwiId).1
  have hCpair : IsCofibrantPair (yT ≫ c) (rT ≫ c) := by
    refine ⟨I, hI, E, eY, eR, hE, kE ≫ c, ?_, ?_, ?_⟩
    · simp [yT, Category.assoc]
    · simp [rT, Category.assoc]
    · exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hkE hc
  let B : PathObj C := ⟨Y, R, M, yT ≫ c, rT ≫ c, hCpair, hyWE, hrWE⟩
  let j : A ⟶ B := {
    l := v
    r := a
    c := kC ≫ c
    il_c := by
      calc
        A.il ≫ (kC ≫ c) = (A.il ≫ kC) ≫ c := (Category.assoc _ _ _).symm
        _ = (v ≫ yT) ≫ c := congrArg (fun z => z ≫ c) hCompatP₁
        _ = v ≫ (yT ≫ c) := Category.assoc _ _ _
    ir_c := by
      calc
        A.ir ≫ (kC ≫ c) = (A.ir ≫ kC) ≫ c := (Category.assoc _ _ _).symm
        _ = (a ≫ rT) ≫ c := congrArg (fun z => z ≫ c) (by
          calc
            A.ir ≫ kC = fR ≫ t₁ := by
              calc
                A.ir ≫ kC = A.ir ≫ (kA ≫ t₁) := congrArg (fun z => A.ir ≫ z) ht₁kA.symm
                _ = fR ≫ t₁ := by simp [fR, Category.assoc]
            _ = a ≫ rT := hCompatR)
        _ = a ≫ (rT ≫ c) := Category.assoc _ _ _
  }
  have hj : cofibrations (PathObj C) j := by
    refine ⟨hv, ha, P₁, kA, yP, hP₁, t₁ ≫ c, ?_, ?_, ?_⟩
    · calc
        kA ≫ (t₁ ≫ c) = (kA ≫ t₁) ≫ c := (Category.assoc _ _ _).symm
        _ = kC ≫ c := congrArg (fun z => z ≫ c) ht₁kA
    · calc
        yP ≫ (t₁ ≫ c) = (yP ≫ t₁) ≫ c := (Category.assoc _ _ _).symm
        _ = yT ≫ c := congrArg (fun z => z ≫ c) ht₁y
    · exact ⟨T, t₁, rT, hSecond, c, rfl, rfl, hc⟩
  exact ⟨B, rfl, j, hj, by simp [j]⟩

private theorem pathObj_right_cofibration_extension {A : PathObj C} {Y : C}
    (v : A.r ⟶ Y) (hv : cofibrations C v) :
    ∃ (B : PathObj C) (e : B.r = Y) (j : A ⟶ B),
      cofibrations (PathObj C) j ∧ j.r = v ≫ eqToHom e.symm := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let bA := pathBoundaryData hI A
  letI : HasPushout v A.ir := hC.toIsCofibrationCategory.hasPushout v A.ir hv
  let P₁ := pushout v A.ir
  let kA : A.c ⟶ P₁ := pushout.inr v A.ir
  let yP : Y ⟶ P₁ := pushout.inl v A.ir
  have hP₁ : IsPushout A.ir v kA yP := (IsPushout.of_hasPushout v A.ir).flip
  have hyP : weakEquivalences C yP :=
    Packages.weakEquivalence_cobaseChange v A.ir yP kA hP₁.flip hv A.ir_mem
  let fL : A.l ⟶ P₁ := A.il ≫ kA
  obtain ⟨L, a, wL, ha, hwL, hawL⟩ := cofibration_weak_equivalence_factorization fL
  letI : HasPushout (hI.to L) (hI.to Y) :=
    hC.toIsCofibrationCategory.hasPushout (hI.to L) (hI.to Y)
      (hC.toIsCofibrationCategory.initial_cofibration hI L)
  let E := pushout (hI.to L) (hI.to Y)
  let eL : L ⟶ E := pushout.inl (hI.to L) (hI.to Y)
  let eY : Y ⟶ E := pushout.inr (hI.to L) (hI.to Y)
  have hE : IsPushout (hI.to L) (hI.to Y) eL eY := IsPushout.of_hasPushout _ _
  have hCompatE : hI.to A.l ≫ (a ≫ eL) = hI.to A.r ≫ (v ≫ eY) := hI.hom_ext _ _
  let bE : bA.P ⟶ E := bA.isPushout.desc (a ≫ eL) (v ≫ eY) hCompatE
  have hbEL : bA.inl ≫ bE = a ≫ eL := bA.isPushout.inl_desc _ _ hCompatE
  have hbER : bA.inr ≫ bE = v ≫ eY := bA.isPushout.inr_desc _ _ hCompatE
  letI : HasPushout bA.toCenter bE :=
    hC.toIsCofibrationCategory.hasPushout bA.toCenter bE bA.toCenter_mem
  let T := pushout bA.toCenter bE
  let kC : A.c ⟶ T := pushout.inl bA.toCenter bE
  let kE : E ⟶ T := pushout.inr bA.toCenter bE
  have hT : IsPushout bA.toCenter bE kC kE := IsPushout.of_hasPushout _ _
  have hkE : cofibrations C kE :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hT.flip
      bA.toCenter_mem
  let lT : L ⟶ T := eL ≫ kE
  let yT : Y ⟶ T := eY ≫ kE
  have hCompatP₁ : A.ir ≫ kC = v ≫ yT := by
    calc
      A.ir ≫ kC = (bA.inr ≫ bA.toCenter) ≫ kC :=
        congrArg (fun t => t ≫ kC) bA.inr_toCenter.symm
      _ = bA.inr ≫ (bA.toCenter ≫ kC) := Category.assoc _ _ _
      _ = bA.inr ≫ (bE ≫ kE) := congrArg (fun t => bA.inr ≫ t) hT.w
      _ = (bA.inr ≫ bE) ≫ kE := (Category.assoc _ _ _).symm
      _ = (v ≫ eY) ≫ kE := congrArg (fun t => t ≫ kE) hbER
      _ = v ≫ yT := by simp [yT, Category.assoc]
  let t₁ : P₁ ⟶ T := hP₁.desc kC yT hCompatP₁
  have ht₁kA : kA ≫ t₁ = kC := hP₁.inl_desc kC yT hCompatP₁
  have ht₁y : yP ≫ t₁ = yT := hP₁.inr_desc kC yT hCompatP₁
  have hCompatL : fL ≫ t₁ = a ≫ lT := by
    calc
      fL ≫ t₁ = A.il ≫ (kA ≫ t₁) := by simp [fL, Category.assoc]
      _ = A.il ≫ kC := congrArg (fun t => A.il ≫ t) ht₁kA
      _ = (bA.inl ≫ bA.toCenter) ≫ kC :=
        congrArg (fun t => t ≫ kC) bA.inl_toCenter.symm
      _ = bA.inl ≫ (bA.toCenter ≫ kC) := Category.assoc _ _ _
      _ = bA.inl ≫ (bE ≫ kE) := congrArg (fun t => bA.inl ≫ t) hT.w
      _ = (bA.inl ≫ bE) ≫ kE := (Category.assoc _ _ _).symm
      _ = (a ≫ eL) ≫ kE := congrArg (fun t => t ≫ kE) hbEL
      _ = a ≫ lT := by simp [lT, Category.assoc]
  have hSecond : IsPushout fL a t₁ lT := by
    apply IsPushout.mk'
    · exact hCompatL
    · intro Z φ ψ hφ hψ
      apply hT.hom_ext
      · calc
          kC ≫ φ = (kA ≫ t₁) ≫ φ := congrArg (fun t => t ≫ φ) ht₁kA.symm
          _ = kA ≫ (t₁ ≫ φ) := Category.assoc _ _ _
          _ = kA ≫ (t₁ ≫ ψ) := congrArg (fun t => kA ≫ t) hφ
          _ = (kA ≫ t₁) ≫ ψ := (Category.assoc _ _ _).symm
          _ = kC ≫ ψ := congrArg (fun t => t ≫ ψ) ht₁kA
      · apply hE.hom_ext
        · have hl : lT ≫ φ = lT ≫ ψ := by
            simpa [lT, Category.assoc] using hψ
          simpa [lT, Category.assoc] using hl
        · have hy : yT ≫ φ = yT ≫ ψ := by
            calc
              yT ≫ φ = (yP ≫ t₁) ≫ φ := congrArg (fun t => t ≫ φ) ht₁y.symm
              _ = yP ≫ (t₁ ≫ φ) := Category.assoc _ _ _
              _ = yP ≫ (t₁ ≫ ψ) := congrArg (fun t => yP ≫ t) hφ
              _ = (yP ≫ t₁) ≫ ψ := (Category.assoc _ _ _).symm
              _ = yT ≫ ψ := congrArg (fun t => t ≫ ψ) ht₁y
          simpa [yT, Category.assoc] using hy
    · intro Z φ ψ hφψ
      let eD : E ⟶ Z := hE.desc ψ (yP ≫ φ) (hI.hom_ext _ _)
      have heDL : eL ≫ eD = ψ := hE.inl_desc _ _ (hI.hom_ext _ _)
      have heDY : eY ≫ eD = yP ≫ φ := hE.inr_desc _ _ (hI.hom_ext _ _)
      have hCompatD : bA.toCenter ≫ (kA ≫ φ) = bE ≫ eD := by
        apply bA.isPushout.hom_ext
        · calc
            bA.inl ≫ bA.toCenter ≫ (kA ≫ φ) =
                A.il ≫ (kA ≫ φ) := by
              calc
                bA.inl ≫ bA.toCenter ≫ (kA ≫ φ) =
                    (bA.inl ≫ bA.toCenter) ≫ (kA ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.il ≫ (kA ≫ φ) := congrArg (fun z => z ≫ (kA ≫ φ)) bA.inl_toCenter
            _ = fL ≫ φ := by simp [fL, Category.assoc]
            _ = a ≫ ψ := hφψ
            _ = bA.inl ≫ bE ≫ eD := by
              calc
                a ≫ ψ = a ≫ (eL ≫ eD) := congrArg (fun z => a ≫ z) heDL.symm
                _ = (a ≫ eL) ≫ eD := (Category.assoc _ _ _).symm
                _ = (bA.inl ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbEL.symm
                _ = bA.inl ≫ bE ≫ eD := Category.assoc _ _ _
        · calc
            bA.inr ≫ bA.toCenter ≫ (kA ≫ φ) =
                A.ir ≫ (kA ≫ φ) := by
              calc
                bA.inr ≫ bA.toCenter ≫ (kA ≫ φ) =
                    (bA.inr ≫ bA.toCenter) ≫ (kA ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.ir ≫ (kA ≫ φ) := congrArg (fun z => z ≫ (kA ≫ φ)) bA.inr_toCenter
            _ = v ≫ yP ≫ φ := by
              calc
                A.ir ≫ (kA ≫ φ) = (A.ir ≫ kA) ≫ φ := (Category.assoc _ _ _).symm
                _ = (v ≫ yP) ≫ φ := congrArg (fun z => z ≫ φ) hP₁.w
                _ = v ≫ yP ≫ φ := Category.assoc _ _ _
            _ = bA.inr ≫ bE ≫ eD := by
              calc
                v ≫ yP ≫ φ = v ≫ (yP ≫ φ) := rfl
                _ = v ≫ (eY ≫ eD) := congrArg (fun z => v ≫ z) heDY.symm
                _ = (v ≫ eY) ≫ eD := (Category.assoc _ _ _).symm
                _ = (bA.inr ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbER.symm
                _ = bA.inr ≫ bE ≫ eD := Category.assoc _ _ _
      let d : T ⟶ Z := hT.desc (kA ≫ φ) eD hCompatD
      have hdC : kC ≫ d = kA ≫ φ := hT.inl_desc _ _ hCompatD
      have hdE : kE ≫ d = eD := hT.inr_desc _ _ hCompatD
      have hd₁ : t₁ ≫ d = φ := by
        apply hP₁.hom_ext
        · calc
            kA ≫ t₁ ≫ d = kC ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) ht₁kA
            _ = kA ≫ φ := hdC
        · calc
            yP ≫ t₁ ≫ d = yT ≫ d := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d) ht₁y
            _ = eY ≫ eD := by simp [yT, Category.assoc, hdE]
            _ = yP ≫ φ := heDY
      have hd₂ : lT ≫ d = ψ := by
        calc
          lT ≫ d = eL ≫ (kE ≫ d) := by simp [lT, Category.assoc]
          _ = eL ≫ eD := congrArg (fun t => eL ≫ t) hdE
          _ = ψ := heDL
      exact ⟨d, hd₁, hd₂⟩
  letI : HasPushout a A.il := hC.toIsCofibrationCategory.hasPushout a A.il ha
  let Q₁ := pushout a A.il
  let kQ : A.c ⟶ Q₁ := pushout.inr a A.il
  let lQ : L ⟶ Q₁ := pushout.inl a A.il
  have hQ₁ : IsPushout A.il a kQ lQ := (IsPushout.of_hasPushout a A.il).flip
  have hCompatQ : A.il ≫ kC = a ≫ lT := by
    calc
      A.il ≫ kC = A.il ≫ (kA ≫ t₁) := congrArg (fun z => A.il ≫ z) ht₁kA.symm
      _ = fL ≫ t₁ := by simp [fL, Category.assoc]
      _ = a ≫ lT := hCompatL
  let tQ : Q₁ ⟶ T := hQ₁.desc kC lT hCompatQ
  have htQk : kQ ≫ tQ = kC := hQ₁.inl_desc kC lT hCompatQ
  have htQl : lQ ≫ tQ = lT := hQ₁.inr_desc kC lT hCompatQ
  have hCompatQ₂ : (A.ir ≫ kQ) ≫ tQ = v ≫ yT := by
    calc
      (A.ir ≫ kQ) ≫ tQ = A.ir ≫ (kQ ≫ tQ) := Category.assoc _ _ _
      _ = A.ir ≫ kC := congrArg (fun z => A.ir ≫ z) htQk
      _ = v ≫ yT := hCompatP₁
  have hSecondL : IsPushout (A.ir ≫ kQ) v tQ yT := by
    apply IsPushout.mk'
    · exact hCompatQ₂
    · intro Z φ ψ hφ hψ
      apply hT.hom_ext
      · calc
          kC ≫ φ = (kQ ≫ tQ) ≫ φ := congrArg (fun z => z ≫ φ) htQk.symm
          _ = kQ ≫ (tQ ≫ φ) := Category.assoc _ _ _
          _ = kQ ≫ (tQ ≫ ψ) := congrArg (fun z => kQ ≫ z) hφ
          _ = (kQ ≫ tQ) ≫ ψ := (Category.assoc _ _ _).symm
          _ = kC ≫ ψ := congrArg (fun z => z ≫ ψ) htQk
      · apply hE.hom_ext
        · calc
            eL ≫ kE ≫ φ = lT ≫ φ := by simp [lT, Category.assoc]
            _ = lT ≫ ψ := by
              calc
                lT ≫ φ = (lQ ≫ tQ) ≫ φ := congrArg (fun z => z ≫ φ) htQl.symm
                _ = lQ ≫ (tQ ≫ φ) := Category.assoc _ _ _
                _ = lQ ≫ (tQ ≫ ψ) := congrArg (fun z => lQ ≫ z) hφ
                _ = (lQ ≫ tQ) ≫ ψ := (Category.assoc _ _ _).symm
                _ = lT ≫ ψ := congrArg (fun z => z ≫ ψ) htQl
            _ = eL ≫ kE ≫ ψ := by simp [lT, Category.assoc]
        · calc
            eY ≫ kE ≫ φ = yT ≫ φ := by simp [yT, Category.assoc]
            _ = yT ≫ ψ := hψ
            _ = eY ≫ kE ≫ ψ := by simp [yT, Category.assoc]
    · intro Z φ ψ hφψ
      let eD : E ⟶ Z := hE.desc (lQ ≫ φ) ψ (hI.hom_ext _ _)
      have heDL : eL ≫ eD = lQ ≫ φ := hE.inl_desc _ _ (hI.hom_ext _ _)
      have heDY : eY ≫ eD = ψ := hE.inr_desc _ _ (hI.hom_ext _ _)
      have hCompatD : bA.toCenter ≫ (kQ ≫ φ) = bE ≫ eD := by
        apply bA.isPushout.hom_ext
        · calc
            bA.inl ≫ bA.toCenter ≫ (kQ ≫ φ) =
                A.il ≫ (kQ ≫ φ) := by
              calc
                bA.inl ≫ bA.toCenter ≫ (kQ ≫ φ) =
                    (bA.inl ≫ bA.toCenter) ≫ (kQ ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.il ≫ (kQ ≫ φ) := congrArg (fun z => z ≫ (kQ ≫ φ)) bA.inl_toCenter
            _ = a ≫ lQ ≫ φ := by
              calc
                A.il ≫ (kQ ≫ φ) = (A.il ≫ kQ) ≫ φ := (Category.assoc _ _ _).symm
                _ = (a ≫ lQ) ≫ φ := congrArg (fun z => z ≫ φ) hQ₁.w
                _ = a ≫ lQ ≫ φ := Category.assoc _ _ _
            _ = bA.inl ≫ bE ≫ eD := by
              calc
                a ≫ lQ ≫ φ = a ≫ (lQ ≫ φ) := rfl
                _ = a ≫ (eL ≫ eD) := congrArg (fun z => a ≫ z) heDL.symm
                _ = (a ≫ eL) ≫ eD := (Category.assoc _ _ _).symm
                _ = (bA.inl ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbEL.symm
                _ = bA.inl ≫ bE ≫ eD := Category.assoc _ _ _
        · calc
            bA.inr ≫ bA.toCenter ≫ (kQ ≫ φ) =
                A.ir ≫ (kQ ≫ φ) := by
              calc
                bA.inr ≫ bA.toCenter ≫ (kQ ≫ φ) =
                    (bA.inr ≫ bA.toCenter) ≫ (kQ ≫ φ) :=
                      (Category.assoc _ _ _).symm
                _ = A.ir ≫ (kQ ≫ φ) := congrArg (fun z => z ≫ (kQ ≫ φ)) bA.inr_toCenter
            _ = (A.ir ≫ kQ) ≫ φ := (Category.assoc _ _ _).symm
            _ = v ≫ ψ := hφψ
            _ = v ≫ (eY ≫ eD) := congrArg (fun z => v ≫ z) heDY.symm
            _ = (v ≫ eY) ≫ eD := (Category.assoc _ _ _).symm
            _ = (bA.inr ≫ bE) ≫ eD := congrArg (fun z => z ≫ eD) hbER.symm
            _ = bA.inr ≫ bE ≫ eD := Category.assoc _ _ _
      let d : T ⟶ Z := hT.desc (kQ ≫ φ) eD hCompatD
      have hdC : kC ≫ d = kQ ≫ φ := hT.inl_desc _ _ hCompatD
      have hdE : kE ≫ d = eD := hT.inr_desc _ _ hCompatD
      have hdQ : tQ ≫ d = φ := by
        apply hQ₁.hom_ext
        · calc
            kQ ≫ tQ ≫ d = kC ≫ d := by
              simpa [Category.assoc] using congrArg (fun z => z ≫ d) htQk
            _ = kQ ≫ φ := hdC
        · calc
            lQ ≫ tQ ≫ d = lT ≫ d := by
              simpa [Category.assoc] using congrArg (fun z => z ≫ d) htQl
            _ = eL ≫ eD := by simp [lT, Category.assoc, hdE]
            _ = lQ ≫ φ := heDL
      have hdY : yT ≫ d = ψ := by
        calc
          yT ≫ d = eY ≫ (kE ≫ d) := by simp [yT, Category.assoc]
          _ = eY ≫ eD := congrArg (fun z => eY ≫ z) hdE
          _ = ψ := heDY
      exact ⟨d, hdQ, hdY⟩
  have hTCompat : fL ≫ 𝟙 P₁ = a ≫ wL := by
    rw [hawL]
    simp
  let t : T ⟶ P₁ := hSecond.desc (𝟙 P₁) wL hTCompat
  have ht₁ : t₁ ≫ t = 𝟙 P₁ := hSecond.inl_desc _ _ hTCompat
  have ht₂ : lT ≫ t = wL := hSecond.inr_desc _ _ hTCompat
  obtain ⟨M, c, p, hc, hp, hcp⟩ := cofibration_weak_equivalence_factorization t
  have hLp : lT ≫ c ≫ p = wL := by
    calc
      lT ≫ c ≫ p = lT ≫ (c ≫ p) := rfl
      _ = lT ≫ t := congrArg (fun z => lT ≫ z) hcp
      _ = wL := ht₂
  have hYp : yT ≫ c ≫ p = yP := by
    calc
      yT ≫ c ≫ p = yT ≫ (c ≫ p) := rfl
      _ = yT ≫ t := congrArg (fun z => yT ≫ z) hcp
      _ = yP := by
        calc
          yT ≫ t = (yP ≫ t₁) ≫ t := congrArg (fun z => z ≫ t) ht₁y.symm
          _ = yP ≫ (t₁ ≫ t) := Category.assoc _ _ _
          _ = yP := by rw [ht₁]; simp
  have hwiId : weakEquivalences C (p ≫ 𝟙 P₁) := by simpa using hp
  have hLComp : weakEquivalences C ((lT ≫ c) ≫ p) := by
    rw [Category.assoc lT c p, hLp]
    exact hwL
  have hLWE : weakEquivalences C (lT ≫ c) :=
    (hC.twoOutOfSix (lT ≫ c) p (𝟙 P₁) hLComp hwiId).1
  have hYComp : weakEquivalences C ((yT ≫ c) ≫ p) := by
    rw [Category.assoc yT c p, hYp]
    exact hyP
  have hYWE : weakEquivalences C (yT ≫ c) :=
    (hC.twoOutOfSix (yT ≫ c) p (𝟙 P₁) hYComp hwiId).1
  have hCpair : IsCofibrantPair (lT ≫ c) (yT ≫ c) := by
    refine ⟨I, hI, E, eL, eY, hE, kE ≫ c, ?_, ?_, ?_⟩
    · simp [lT, Category.assoc]
    · simp [yT, Category.assoc]
    · exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hkE hc
  let B : PathObj C := ⟨L, Y, M, lT ≫ c, yT ≫ c, hCpair, hLWE, hYWE⟩
  let j : A ⟶ B := {
    l := a
    r := v
    c := kC ≫ c
    il_c := by
      calc
        A.il ≫ (kC ≫ c) = (A.il ≫ kC) ≫ c := (Category.assoc _ _ _).symm
        _ = (a ≫ lT) ≫ c := congrArg (fun z => z ≫ c) hCompatQ
        _ = a ≫ (lT ≫ c) := Category.assoc _ _ _
    ir_c := by
      calc
        A.ir ≫ (kC ≫ c) = (A.ir ≫ kC) ≫ c := (Category.assoc _ _ _).symm
        _ = (v ≫ yT) ≫ c := congrArg (fun z => z ≫ c) hCompatP₁
        _ = v ≫ (yT ≫ c) := Category.assoc _ _ _
  }
  have hj : cofibrations (PathObj C) j := by
    refine ⟨ha, hv, Q₁, kQ, lQ, hQ₁, tQ ≫ c, ?_, ?_, ?_⟩
    · calc
        kQ ≫ (tQ ≫ c) = (kQ ≫ tQ) ≫ c := (Category.assoc _ _ _).symm
        _ = kC ≫ c := congrArg (fun z => z ≫ c) htQk
    · calc
        lQ ≫ (tQ ≫ c) = (lQ ≫ tQ) ≫ c := (Category.assoc _ _ _).symm
        _ = lT ≫ c := congrArg (fun z => z ≫ c) htQl
    · exact ⟨T, tQ, yT, hSecondL, c, rfl, rfl, hc⟩
  exact ⟨B, rfl, j, hj, by simp [j]⟩

private theorem pathObj_left_reflects_weakEquivalence {X Y : PathObj C}
    (f : X ⟶ Y) (hf : weakEquivalences C f.l) :
    weakEquivalences (PathObj C) f := by
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c
  have hLeftComp : weakEquivalences C (f.l ≫ Y.il) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf Y.il_mem
  have hCenterComp : weakEquivalences C (X.il ≫ f.c) := by
    rw [f.il_c]
    exact hLeftComp
  have hIdXil : weakEquivalences C ((𝟙 X.l) ≫ X.il) := by simpa using X.il_mem
  have hfC : weakEquivalences C f.c :=
    (hC.twoOutOfSix (𝟙 X.l) X.il f.c hIdXil hCenterComp).2.2.1
  have hRightComp : weakEquivalences C (X.ir ≫ f.c) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ X.ir_mem hfC
  have hfRComp : weakEquivalences C (f.r ≫ Y.ir) := by
    rw [← f.ir_c]
    exact hRightComp
  have hIdY : weakEquivalences C (𝟙 Y.c) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hYirId : weakEquivalences C (Y.ir ≫ 𝟙 Y.c) := by simpa using Y.ir_mem
  have hfR : weakEquivalences C f.r :=
    (hC.twoOutOfSix f.r Y.ir (𝟙 Y.c) hfRComp hYirId).1
  exact ⟨hf, hfR, hfC⟩

private theorem pathObj_right_reflects_weakEquivalence {X Y : PathObj C}
    (f : X ⟶ Y) (hf : weakEquivalences C f.r) :
    weakEquivalences (PathObj C) f := by
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c
  have hRightComp : weakEquivalences C (f.r ≫ Y.ir) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ hf Y.ir_mem
  have hCenterComp : weakEquivalences C (X.ir ≫ f.c) := by
    rw [f.ir_c]
    exact hRightComp
  have hIdXir : weakEquivalences C ((𝟙 X.r) ≫ X.ir) := by simpa using X.ir_mem
  have hfC : weakEquivalences C f.c :=
    (hC.twoOutOfSix (𝟙 X.r) X.ir f.c hIdXir hCenterComp).2.2.1
  have hLeftComp : weakEquivalences C (X.il ≫ f.c) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ X.il_mem hfC
  have hfLComp : weakEquivalences C (f.l ≫ Y.il) := by
    rw [← f.il_c]
    exact hLeftComp
  have hYilId : weakEquivalences C (Y.il ≫ 𝟙 Y.c) := by simpa using Y.il_mem
  have hfL : weakEquivalences C f.l :=
    (hC.twoOutOfSix f.l Y.il (𝟙 Y.c) hfLComp hYilId).1
  exact ⟨hfL, hf, hfC⟩

private theorem pathObj_factorization_from_endpoints
    {X Y : PathObj C} {Ml Mr : C} (f : X ⟶ Y)
    (al : X.l ⟶ Ml) (bl : Ml ⟶ Y.l) (hal : cofibrations C al)
    (hbl : weakEquivalences C bl) (halbl : al ≫ bl = f.l)
    (ar : X.r ⟶ Mr) (br : Mr ⟶ Y.r) (har : cofibrations C ar)
    (hbr : weakEquivalences C br) (harbr : ar ≫ br = f.r) :
    ∃ (Z : PathObj C) (eL : Z.l = Ml) (eR : Z.r = Mr) (i : X ⟶ Z) (w : Z ⟶ Y),
      i.l = al ≫ eqToHom eL.symm ∧ i.r = ar ≫ eqToHom eR.symm ∧
        w.l = eqToHom eL ≫ bl ∧ w.r = eqToHom eR ≫ br ∧
        cofibrations (PathObj C) i ∧ weakEquivalences (PathObj C) w ∧ i ≫ w = f := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let bX := pathBoundaryData hI X
  letI : HasPushout (hI.to Ml) (hI.to Mr) :=
    hC.toIsCofibrationCategory.hasPushout (hI.to Ml) (hI.to Mr)
      (hC.toIsCofibrationCategory.initial_cofibration hI Ml)
  let BZ := pushout (hI.to Ml) (hI.to Mr)
  let zL : Ml ⟶ BZ := pushout.inl (hI.to Ml) (hI.to Mr)
  let zR : Mr ⟶ BZ := pushout.inr (hI.to Ml) (hI.to Mr)
  have hBZ : IsPushout (hI.to Ml) (hI.to Mr) zL zR :=
    IsPushout.of_hasPushout _ _
  let a : bX.P ⟶ BZ := bX.isPushout.desc (al ≫ zL) (ar ≫ zR) (hI.hom_ext _ _)
  have haL : bX.inl ≫ a = al ≫ zL :=
    bX.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have haR : bX.inr ≫ a = ar ≫ zR :=
    bX.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  letI : HasPushout al X.il := hC.toIsCofibrationCategory.hasPushout al X.il hal
  let P1 := pushout al X.il
  let k1 : Ml ⟶ P1 := pushout.inl al X.il
  let j1 : X.c ⟶ P1 := pushout.inr al X.il
  have hP1 : IsPushout X.il al j1 k1 := (IsPushout.of_hasPushout al X.il).flip
  letI : HasPushout ar (X.ir ≫ j1) :=
    hC.toIsCofibrationCategory.hasPushout ar (X.ir ≫ j1) har
  let P2 := pushout ar (X.ir ≫ j1)
  let k2 : Mr ⟶ P2 := pushout.inl ar (X.ir ≫ j1)
  let j2 : P1 ⟶ P2 := pushout.inr ar (X.ir ≫ j1)
  have hP2 : IsPushout (X.ir ≫ j1) ar j2 k2 :=
    (IsPushout.of_hasPushout ar (X.ir ≫ j1)).flip
  let zP : BZ ⟶ P2 := hBZ.desc (k1 ≫ j2) k2 (hI.hom_ext _ _)
  have hzPL : zL ≫ zP = k1 ≫ j2 :=
    hBZ.inl_desc (k1 ≫ j2) k2 (hI.hom_ext _ _)
  have hzPR : zR ≫ zP = k2 :=
    hBZ.inr_desc (k1 ≫ j2) k2 (hI.hom_ext _ _)
  let xP : X.c ⟶ P2 := j1 ≫ j2
  have hTotalCompat : bX.toCenter ≫ xP = a ≫ zP := by
    apply bX.isPushout.hom_ext
    · calc
        bX.inl ≫ bX.toCenter ≫ xP = X.il ≫ xP := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ xP) bX.inl_toCenter
        _ = X.il ≫ j1 ≫ j2 := rfl
        _ = al ≫ k1 ≫ j2 := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ j2) hP1.w
        _ = al ≫ (zL ≫ zP) := by rw [hzPL]
        _ = (al ≫ zL) ≫ zP := (Category.assoc _ _ _).symm
        _ = (bX.inl ≫ a) ≫ zP := congrArg (fun t => t ≫ zP) haL.symm
        _ = bX.inl ≫ (a ≫ zP) := Category.assoc _ _ _
    · calc
        bX.inr ≫ bX.toCenter ≫ xP = X.ir ≫ xP := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ xP) bX.inr_toCenter
        _ = X.ir ≫ j1 ≫ j2 := rfl
        _ = ar ≫ k2 := by simpa [Category.assoc] using hP2.w
        _ = ar ≫ (zR ≫ zP) := by rw [hzPR]
        _ = (ar ≫ zR) ≫ zP := (Category.assoc _ _ _).symm
        _ = (bX.inr ≫ a) ≫ zP := congrArg (fun t => t ≫ zP) haR.symm
        _ = bX.inr ≫ (a ≫ zP) := Category.assoc _ _ _
  have hTotal : IsPushout bX.toCenter a xP zP := by
    apply IsPushout.mk'
    · exact hTotalCompat
    · intro T φ ψ hφ hψ
      have hP1φ : j2 ≫ φ = j2 ≫ ψ := by
        apply hP1.hom_ext
        · simpa [xP, Category.assoc] using hφ
        · calc
            k1 ≫ j2 ≫ φ = (zL ≫ zP) ≫ φ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ φ) hzPL.symm
            _ = zL ≫ (zP ≫ φ) := Category.assoc _ _ _
            _ = zL ≫ (zP ≫ ψ) := congrArg (fun t => zL ≫ t) hψ
            _ = (zL ≫ zP) ≫ ψ := (Category.assoc _ _ _).symm
            _ = k1 ≫ j2 ≫ ψ := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ ψ) hzPL
      have hP2φ : k2 ≫ φ = k2 ≫ ψ := by
        calc
          k2 ≫ φ = (zR ≫ zP) ≫ φ := congrArg (fun t => t ≫ φ) hzPR.symm
          _ = zR ≫ (zP ≫ φ) := Category.assoc _ _ _
          _ = zR ≫ (zP ≫ ψ) := congrArg (fun t => zR ≫ t) hψ
          _ = (zR ≫ zP) ≫ ψ := (Category.assoc _ _ _).symm
          _ = k2 ≫ ψ := congrArg (fun t => t ≫ ψ) hzPR
      exact hP2.hom_ext hP1φ hP2φ
    · intro T φ ψ hφψ
      have hLeftCompat : X.il ≫ φ = al ≫ (zL ≫ ψ) := by
        calc
          X.il ≫ φ = (bX.inl ≫ bX.toCenter) ≫ φ :=
            congrArg (fun t => t ≫ φ) bX.inl_toCenter.symm
          _ = bX.inl ≫ (bX.toCenter ≫ φ) := Category.assoc _ _ _
          _ = bX.inl ≫ (a ≫ ψ) := congrArg (fun t => bX.inl ≫ t) hφψ
          _ = (bX.inl ≫ a) ≫ ψ := (Category.assoc _ _ _).symm
          _ = (al ≫ zL) ≫ ψ := congrArg (fun t => t ≫ ψ) haL
          _ = al ≫ (zL ≫ ψ) := Category.assoc _ _ _
      let d1 : P1 ⟶ T := hP1.desc φ (zL ≫ ψ) hLeftCompat
      have hd1j : j1 ≫ d1 = φ := hP1.inl_desc φ (zL ≫ ψ) hLeftCompat
      have hd1k : k1 ≫ d1 = zL ≫ ψ :=
        hP1.inr_desc φ (zL ≫ ψ) hLeftCompat
      have hRightCompat : (X.ir ≫ j1) ≫ d1 = ar ≫ (zR ≫ ψ) := by
        calc
          (X.ir ≫ j1) ≫ d1 = X.ir ≫ (j1 ≫ d1) := Category.assoc _ _ _
          _ = X.ir ≫ φ := congrArg (fun t => X.ir ≫ t) hd1j
          _ = (bX.inr ≫ bX.toCenter) ≫ φ :=
            congrArg (fun t => t ≫ φ) bX.inr_toCenter.symm
          _ = bX.inr ≫ (bX.toCenter ≫ φ) := Category.assoc _ _ _
          _ = bX.inr ≫ (a ≫ ψ) := congrArg (fun t => bX.inr ≫ t) hφψ
          _ = (bX.inr ≫ a) ≫ ψ := (Category.assoc _ _ _).symm
          _ = (ar ≫ zR) ≫ ψ := congrArg (fun t => t ≫ ψ) haR
          _ = ar ≫ (zR ≫ ψ) := Category.assoc _ _ _
      let d2 : P2 ⟶ T := hP2.desc d1 (zR ≫ ψ) hRightCompat
      have hd2j : j2 ≫ d2 = d1 := hP2.inl_desc d1 (zR ≫ ψ) hRightCompat
      have hd2k : k2 ≫ d2 = zR ≫ ψ :=
        hP2.inr_desc d1 (zR ≫ ψ) hRightCompat
      have hd2z : zP ≫ d2 = ψ := by
        apply hBZ.hom_ext
        · calc
            zL ≫ zP ≫ d2 = (zL ≫ zP) ≫ d2 := (Category.assoc _ _ _).symm
            _ = k1 ≫ j2 ≫ d2 := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ d2) hzPL
            _ = k1 ≫ d1 := congrArg (fun t => k1 ≫ t) hd2j
            _ = zL ≫ ψ := hd1k
        · calc
            zR ≫ zP ≫ d2 = (zR ≫ zP) ≫ d2 := (Category.assoc _ _ _).symm
            _ = k2 ≫ d2 := congrArg (fun t => t ≫ d2) hzPR
            _ = zR ≫ ψ := hd2k
      refine ⟨d2, ?_, hd2z⟩
      calc
        xP ≫ d2 = j1 ≫ (j2 ≫ d2) := Category.assoc _ _ _
        _ = j1 ≫ d1 := congrArg (fun t => j1 ≫ t) hd2j
        _ = φ := hd1j
  let qB : BZ ⟶ Y.c := hBZ.desc (bl ≫ Y.il) (br ≫ Y.ir) (hI.hom_ext _ _)
  have hqBL : zL ≫ qB = bl ≫ Y.il :=
    hBZ.inl_desc (bl ≫ Y.il) (br ≫ Y.ir) (hI.hom_ext _ _)
  have hqBR : zR ≫ qB = br ≫ Y.ir :=
    hBZ.inr_desc (bl ≫ Y.il) (br ≫ Y.ir) (hI.hom_ext _ _)
  have hCompat : bX.toCenter ≫ f.c = a ≫ qB := by
    apply bX.isPushout.hom_ext
    · calc
        bX.inl ≫ bX.toCenter ≫ f.c = X.il ≫ f.c := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ f.c) bX.inl_toCenter
        _ = f.l ≫ Y.il := f.il_c
        _ = (al ≫ bl) ≫ Y.il := congrArg (fun t => t ≫ Y.il) halbl.symm
        _ = al ≫ (bl ≫ Y.il) := Category.assoc _ _ _
        _ = al ≫ (zL ≫ qB) := congrArg (fun t => al ≫ t) hqBL.symm
        _ = (al ≫ zL) ≫ qB := (Category.assoc _ _ _).symm
        _ = (bX.inl ≫ a) ≫ qB := congrArg (fun t => t ≫ qB) haL.symm
        _ = bX.inl ≫ (a ≫ qB) := Category.assoc _ _ _
    · calc
        bX.inr ≫ bX.toCenter ≫ f.c = X.ir ≫ f.c := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ f.c) bX.inr_toCenter
        _ = f.r ≫ Y.ir := f.ir_c
        _ = (ar ≫ br) ≫ Y.ir := congrArg (fun t => t ≫ Y.ir) harbr.symm
        _ = ar ≫ (br ≫ Y.ir) := Category.assoc _ _ _
        _ = ar ≫ (zR ≫ qB) := congrArg (fun t => ar ≫ t) hqBR.symm
        _ = (ar ≫ zR) ≫ qB := (Category.assoc _ _ _).symm
        _ = (bX.inr ≫ a) ≫ qB := congrArg (fun t => t ≫ qB) haR.symm
        _ = bX.inr ≫ (a ≫ qB) := Category.assoc _ _ _
  let q : P2 ⟶ Y.c := hTotal.desc f.c qB hCompat
  have hqX : xP ≫ q = f.c := hTotal.inl_desc f.c qB hCompat
  have hqZ : zP ≫ q = qB := hTotal.inr_desc f.c qB hCompat
  obtain ⟨Mc, n, w, hn, hw, hnw⟩ :=
    cofibration_weak_equivalence_factorization q
  let zIl : Ml ⟶ Mc := zL ≫ zP ≫ n
  let zIr : Mr ⟶ Mc := zR ≫ zP ≫ n
  have hzIlw : zIl ≫ w = bl ≫ Y.il := by
    calc
      zIl ≫ w = zL ≫ (zP ≫ (n ≫ w)) := by simp [zIl, Category.assoc]
      _ = zL ≫ (zP ≫ q) := congrArg (fun t => zL ≫ (zP ≫ t)) hnw
      _ = zL ≫ qB := by
        simpa [Category.assoc] using congrArg (fun t => zL ≫ t) hqZ
      _ = bl ≫ Y.il := hqBL
  have hzIrw : zIr ≫ w = br ≫ Y.ir := by
    calc
      zIr ≫ w = zR ≫ (zP ≫ (n ≫ w)) := by simp [zIr, Category.assoc]
      _ = zR ≫ (zP ≫ q) := congrArg (fun t => zR ≫ (zP ≫ t)) hnw
      _ = zR ≫ qB := by
        simpa [Category.assoc] using congrArg (fun t => zR ≫ t) hqZ
      _ = br ≫ Y.ir := hqBR
  have hzIl : weakEquivalences C zIl := by
    have hcomp : weakEquivalences C (zIl ≫ w) := by
      rw [hzIlw]
      exact hC.weakEquivalences_isMultiplicative.comp_mem _ _ hbl Y.il_mem
    have hid : weakEquivalences C (𝟙 Y.c) :=
      hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
    have hright : weakEquivalences C (w ≫ 𝟙 Y.c) := by simpa using hw
    exact (hC.twoOutOfSix zIl w (𝟙 Y.c) hcomp hright).1
  have hzIr : weakEquivalences C zIr := by
    have hcomp : weakEquivalences C (zIr ≫ w) := by
      rw [hzIrw]
      exact hC.weakEquivalences_isMultiplicative.comp_mem _ _ hbr Y.ir_mem
    have hid : weakEquivalences C (𝟙 Y.c) :=
      hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
    have hright : weakEquivalences C (w ≫ 𝟙 Y.c) := by simpa using hw
    exact (hC.twoOutOfSix zIr w (𝟙 Y.c) hcomp hright).1
  have hzP_mem : cofibrations C zP :=
    hC.toIsCofibrationCategory.isStableUnderCobaseChange.of_isPushout hTotal.flip
      bX.toCenter_mem
  let mZ : BZ ⟶ Mc := zP ≫ n
  have hmZ : cofibrations C mZ :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hzP_mem hn
  have hZPair : IsCofibrantPair zIl zIr := by
    refine ⟨I, hI, BZ, zL, zR, hBZ, mZ, ?_, ?_, hmZ⟩
    · rfl
    · rfl
  let Z : PathObj C := ⟨Ml, Mr, Mc, zIl, zIr, hZPair, hzIl, hzIr⟩
  let i : X ⟶ Z := {
    l := al
    r := ar
    c := xP ≫ n
    il_c := by
      calc
        X.il ≫ (xP ≫ n) = X.il ≫ j1 ≫ j2 ≫ n := by simp [xP, Category.assoc]
        _ = al ≫ k1 ≫ j2 ≫ n := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ j2 ≫ n) hP1.w
        _ = al ≫ zIl := by
          change al ≫ (k1 ≫ (j2 ≫ n)) = al ≫ zIl
          calc
            al ≫ (k1 ≫ (j2 ≫ n)) = al ≫ ((k1 ≫ j2) ≫ n) :=
              congrArg (fun t => al ≫ t) (Category.assoc _ _ _).symm
            _ = al ≫ ((zL ≫ zP) ≫ n) :=
              congrArg (fun t => al ≫ (t ≫ n)) hzPL.symm
            _ = al ≫ zIl := by simp [zIl, Category.assoc]
    ir_c := by
      calc
        X.ir ≫ (xP ≫ n) = X.ir ≫ j1 ≫ j2 ≫ n := by simp [xP, Category.assoc]
        _ = ar ≫ k2 ≫ n := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ n) hP2.w
        _ = ar ≫ zIr := by
          change ar ≫ (k2 ≫ n) = ar ≫ zIr
          calc
            ar ≫ (k2 ≫ n) = ar ≫ ((zR ≫ zP) ≫ n) :=
              congrArg (fun t => ar ≫ (t ≫ n)) hzPR.symm
            _ = ar ≫ zIr := by simp [zIr, Category.assoc]
  }
  let wPath : Z ⟶ Y := {
    l := bl
    r := br
    c := w
    il_c := hzIlw
    ir_c := hzIrw
  }
  have hi : cofibrations (PathObj C) i := by
    refine ⟨hal, har, P1, j1, k1, hP1, j2 ≫ n, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).symm
    · simpa [zIl, Category.assoc] using congrArg (fun t => t ≫ n) hzPL.symm
    · refine ⟨P2, j2, k2, hP2, n, rfl, ?_, hn⟩
      simpa [zIr, Category.assoc] using congrArg (fun t => t ≫ n) hzPR.symm
  have hwPath : weakEquivalences (PathObj C) wPath := ⟨hbl, hbr, hw⟩
  have hiw : i ≫ wPath = f := by
    apply PathObj.Hom.ext
    · exact halbl
    · exact harbr
    · calc
        (xP ≫ n) ≫ w = xP ≫ (n ≫ w) := Category.assoc _ _ _
        _ = xP ≫ q := congrArg (fun t => xP ≫ t) hnw
        _ = f.c := hqX
  refine ⟨Z, rfl, rfl, i, wPath, ?_, ?_, ?_, ?_, hi, hwPath, hiw⟩
  · simpa using (show i.l = al by rfl)
  · simpa using (show i.r = ar by rfl)
  · simpa using (show wPath.l = bl by rfl)
  · simpa using (show wPath.r = br by rfl)

private theorem pathObj_cofibration_weak_equivalence_factorization
    {X Y : PathObj C} (f : X ⟶ Y) :
    ∃ (Z : PathObj C) (i : X ⟶ Z) (w : Z ⟶ Y),
      cofibrations (PathObj C) i ∧ weakEquivalences (PathObj C) w ∧ i ≫ w = f := by
  classical
  obtain ⟨Ml, al, bl, hal, hbl, halbl⟩ :=
    cofibration_weak_equivalence_factorization f.l
  obtain ⟨Mr, ar, br, har, hbr, harbr⟩ :=
    cofibration_weak_equivalence_factorization f.r
  obtain ⟨Z, _, _, i, w, _, _, _, _, hi, hw, hiw⟩ :=
    pathObj_factorization_from_endpoints f al bl hal hbl halbl ar br har hbr harbr
  exact ⟨Z, i, w, hi, hw, hiw⟩

private theorem pathObj_exists_cylinder {I : PathObj C} (hI : IsInitial I)
    (X : PathObj C) : Nonempty (RelativeCylinder (hI.to X)) := by
  classical
  let hPathCof := pathObj_isCofibrationCategory (C := C)
  letI : IsCofibrationCategory (PathObj C) := hPathCof
  letI : HasPushout (hI.to X) (hI.to X) :=
    hPathCof.hasPushout (hI.to X) (hI.to X) (pathInitial_map_cofibration hI X)
  let P := pushout (hI.to X) (hI.to X)
  let j0 : X ⟶ P := pushout.inl (hI.to X) (hI.to X)
  let j1 : X ⟶ P := pushout.inr (hI.to X) (hI.to X)
  have hP : IsPushout (hI.to X) (hI.to X) j0 j1 := IsPushout.of_hasPushout _ _
  let fold : P ⟶ X := hP.desc (𝟙 X) (𝟙 X) (hI.hom_ext _ _)
  have hfold0 : j0 ≫ fold = 𝟙 X := hP.inl_desc _ _ (hI.hom_ext _ _)
  have hfold1 : j1 ≫ fold = 𝟙 X := hP.inr_desc _ _ (hI.hom_ext _ _)
  obtain ⟨Y, c, p, hc, hp, hcp⟩ :=
    pathObj_cofibration_weak_equivalence_factorization fold
  have hc0 : j0 ≫ c ≫ p = 𝟙 X := by
    calc
      j0 ≫ c ≫ p = j0 ≫ (c ≫ p) := rfl
      _ = j0 ≫ fold := congrArg (fun t => j0 ≫ t) hcp
      _ = 𝟙 X := hfold0
  have hc1 : j1 ≫ c ≫ p = 𝟙 X := by
    calc
      j1 ≫ c ≫ p = j1 ≫ (c ≫ p) := rfl
      _ = j1 ≫ fold := congrArg (fun t => j1 ≫ t) hcp
      _ = 𝟙 X := hfold1
  exact ⟨⟨P, j0, j1, hP, Y, c, p, hc, hp, hc0, hc1⟩⟩

private theorem pathObj_retraction_from_endpoints {X Y : PathObj C} (f : X ⟶ Y)
    (hf : cofibrations (PathObj C) f) (hW : weakEquivalences (PathObj C) f)
    (rL : Y.l ⟶ X.l) (hrL : f.l ≫ rL = 𝟙 X.l)
    (rR : Y.r ⟶ X.r) (hrR : f.r ≫ rR = 𝟙 X.r) :
    ∃ r : Y ⟶ X, r.l = rL ∧ r.r = rR ∧ f ≫ r = 𝟙 X := by
  classical
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c at hW
  let F := pathObjCofibrationData f hf
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  let bX := pathBoundaryData hI X
  let bY := pathBoundaryData hI Y
  obtain ⟨a, haL, haR, haCof⟩ := pathBoundaryMap_cof hI f hf.1 hf.2.1 bX bY
  have hPre : IsPreCylinderCategory C := Packages.isPreCylinderCategory (C := C)
  have hIdI : weakEquivalences C (𝟙 I) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have haWeak : weakEquivalences C a :=
    hPre.gluing (hI.to X.l) (hI.to X.r) bX.inl bX.inr
      (hI.to Y.l) (hI.to Y.r) bY.inl bY.inr
      (𝟙 I) f.l f.r a bX.isPushout bY.isPushout
      (hC.toIsCofibrationCategory.initial_cofibration hI X.l)
      (hC.toIsCofibrationCategory.initial_cofibration hI Y.l)
      hIdI hW.1 hW.2.1
      (hI.hom_ext _ _) (hI.hom_ext _ _) haL haR
  letI : HasPushout bX.toCenter a :=
    hC.toIsCofibrationCategory.hasPushout bX.toCenter a bX.toCenter_mem
  let P := pushout bX.toCenter a
  let jX : X.c ⟶ P := pushout.inl bX.toCenter a
  let kB : bY.P ⟶ P := pushout.inr bX.toCenter a
  have hTotal : IsPushout bX.toCenter a jX kB := IsPushout.of_hasPushout _ _
  let pF : bY.P ⟶ F.Q :=
    bY.isPushout.desc (F.j ≫ F.k₂) F.j₂ (hI.hom_ext _ _)
  have hFBoundary : IsPushout bX.toCenter a (F.k ≫ F.k₂) pF := by
    simpa [pF] using pathObj_cofBoundaryPushout hI f F bX bY a haL haR
  let e : F.Q ≅ P := hFBoundary.isoIsPushout X.c bY.P hTotal
  have heLeft : (F.k ≫ F.k₂) ≫ e.hom = jX :=
    hFBoundary.inl_isoIsPushout_hom X.c bY.P hTotal
  have heRight : pF ≫ e.hom = kB :=
    hFBoundary.inr_isoIsPushout_hom X.c bY.P hTotal
  have hjXInv : jX ≫ e.inv = F.k ≫ F.k₂ := by
    calc
      jX ≫ e.inv = ((F.k ≫ F.k₂) ≫ e.hom) ≫ e.inv :=
        congrArg (fun t => t ≫ e.inv) heLeft.symm
      _ = F.k ≫ F.k₂ := by simp [Category.assoc]
  have hkBInv : kB ≫ e.inv = pF := by
    calc
      kB ≫ e.inv = (pF ≫ e.hom) ≫ e.inv := congrArg (fun t => t ≫ e.inv) heRight.symm
      _ = pF := by simp [Category.assoc]
  have hpFL : bY.inl ≫ pF = F.j ≫ F.k₂ :=
    bY.isPushout.inl_desc (F.j ≫ F.k₂) F.j₂ (hI.hom_ext _ _)
  have hpFR : bY.inr ≫ pF = F.j₂ :=
    bY.isPushout.inr_desc (F.j ≫ F.k₂) F.j₂ (hI.hom_ext _ _)
  have hpFn : pF ≫ F.n = bY.toCenter := by
    apply bY.isPushout.hom_ext
    · calc
        bY.inl ≫ pF ≫ F.n = (bY.inl ≫ pF) ≫ F.n := (Category.assoc _ _ _).symm
        _ = (F.j ≫ F.k₂) ≫ F.n := congrArg (fun t => t ≫ F.n) hpFL
        _ = F.j ≫ (F.k₂ ≫ F.n) := Category.assoc _ _ _
        _ = F.j ≫ F.m := congrArg (fun t => F.j ≫ t) F.k₂n
        _ = Y.il := F.jm
        _ = bY.inl ≫ bY.toCenter := bY.inl_toCenter.symm
    · calc
        bY.inr ≫ pF ≫ F.n = (bY.inr ≫ pF) ≫ F.n := (Category.assoc _ _ _).symm
        _ = F.j₂ ≫ F.n := congrArg (fun t => t ≫ F.n) hpFR
        _ = Y.ir := F.j₂n
        _ = bY.inr ≫ bY.toCenter := bY.inr_toCenter.symm
  let m : P ⟶ Y.c := e.inv ≫ F.n
  have hmLeft : jX ≫ m = f.c := by
    calc
      jX ≫ m = (jX ≫ e.inv) ≫ F.n := by simp [m, Category.assoc]
      _ = (F.k ≫ F.k₂) ≫ F.n := congrArg (fun t => t ≫ F.n) hjXInv
      _ = F.k ≫ (F.k₂ ≫ F.n) := Category.assoc _ _ _
      _ = F.k ≫ F.m := congrArg (fun t => F.k ≫ t) F.k₂n
      _ = f.c := F.km
  have hmRight : kB ≫ m = bY.toCenter := by
    calc
      kB ≫ m = (kB ≫ e.inv) ≫ F.n := by simp [m, Category.assoc]
      _ = pF ≫ F.n := congrArg (fun t => t ≫ F.n) hkBInv
      _ = bY.toCenter := hpFn
  have hCompat : bX.toCenter ≫ f.c = a ≫ bY.toCenter := by
    apply bX.isPushout.hom_ext
    · calc
        bX.inl ≫ bX.toCenter ≫ f.c = X.il ≫ f.c := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ f.c) bX.inl_toCenter
        _ = f.l ≫ Y.il := f.il_c
        _ = f.l ≫ (bY.inl ≫ bY.toCenter) :=
          congrArg (fun t => f.l ≫ t) bY.inl_toCenter.symm
        _ = (f.l ≫ bY.inl) ≫ bY.toCenter := (Category.assoc _ _ _).symm
        _ = (bX.inl ≫ a) ≫ bY.toCenter :=
          congrArg (fun t => t ≫ bY.toCenter) haL.symm
        _ = bX.inl ≫ (a ≫ bY.toCenter) := Category.assoc _ _ _
    · calc
        bX.inr ≫ bX.toCenter ≫ f.c = X.ir ≫ f.c := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ f.c) bX.inr_toCenter
        _ = f.r ≫ Y.ir := f.ir_c
        _ = f.r ≫ (bY.inr ≫ bY.toCenter) :=
          congrArg (fun t => f.r ≫ t) bY.inr_toCenter.symm
        _ = (f.r ≫ bY.inr) ≫ bY.toCenter := (Category.assoc _ _ _).symm
        _ = (bX.inr ≫ a) ≫ bY.toCenter :=
          congrArg (fun t => t ≫ bY.toCenter) haR.symm
        _ = bX.inr ≫ (a ≫ bY.toCenter) := Category.assoc _ _ _
  have hSqY : IsPushout bY.toCenter (𝟙 bY.P) (𝟙 Y.c) bY.toCenter :=
    IsPushout.of_id_snd (f := bY.toCenter)
  have hidBY : weakEquivalences C (𝟙 bY.P) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hmWeak : weakEquivalences C m :=
    hPre.gluing bX.toCenter a jX kB bY.toCenter (𝟙 bY.P) (𝟙 Y.c) bY.toCenter
      a f.c (𝟙 bY.P) m hTotal hSqY bX.toCenter_mem bY.toCenter_mem
      haWeak hW.2.2 hidBY hCompat (by simp) (by simpa using hmLeft) (by simpa using hmRight)
  have hmCof : cofibrations C m := by
    have heInv : cofibrations C e.inv :=
      hC.toIsCofibrationCategory.isomorphisms_le _ (by infer_instance)
    exact hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ heInv F.n_mem
  obtain ⟨rM, hrM⟩ := hC.exists_retraction m hmCof hmWeak
  let aInv : bY.P ⟶ bX.P :=
    bY.isPushout.desc (rL ≫ bX.inl) (rR ≫ bX.inr) (hI.hom_ext _ _)
  have haInvL : bY.inl ≫ aInv = rL ≫ bX.inl :=
    bY.isPushout.inl_desc _ _ (hI.hom_ext _ _)
  have haInvR : bY.inr ≫ aInv = rR ≫ bX.inr :=
    bY.isPushout.inr_desc _ _ (hI.hom_ext _ _)
  have hAAInv : a ≫ aInv = 𝟙 bX.P := by
    apply bX.isPushout.hom_ext
    · calc
        bX.inl ≫ a ≫ aInv = (bX.inl ≫ a) ≫ aInv := (Category.assoc _ _ _).symm
        _ = (f.l ≫ bY.inl) ≫ aInv := congrArg (fun t => t ≫ aInv) haL
        _ = f.l ≫ (bY.inl ≫ aInv) := Category.assoc _ _ _
        _ = f.l ≫ (rL ≫ bX.inl) := congrArg (fun t => f.l ≫ t) haInvL
        _ = (f.l ≫ rL) ≫ bX.inl := (Category.assoc _ _ _).symm
        _ = bX.inl := by rw [hrL]; simp
        _ = bX.inl ≫ 𝟙 bX.P := by simp
    · calc
        bX.inr ≫ a ≫ aInv = (bX.inr ≫ a) ≫ aInv := (Category.assoc _ _ _).symm
        _ = (f.r ≫ bY.inr) ≫ aInv := congrArg (fun t => t ≫ aInv) haR
        _ = f.r ≫ (bY.inr ≫ aInv) := Category.assoc _ _ _
        _ = f.r ≫ (rR ≫ bX.inr) := congrArg (fun t => f.r ≫ t) haInvR
        _ = (f.r ≫ rR) ≫ bX.inr := (Category.assoc _ _ _).symm
        _ = bX.inr := by rw [hrR]; simp
        _ = bX.inr ≫ 𝟙 bX.P := by simp
  let dB : bY.P ⟶ X.c := aInv ≫ bX.toCenter
  have hSCompat : bX.toCenter ≫ 𝟙 X.c = a ≫ dB := by
    calc
      bX.toCenter ≫ 𝟙 X.c = bX.toCenter := by simp
      _ = (a ≫ aInv) ≫ bX.toCenter := by
        simpa using congrArg (fun t => t ≫ bX.toCenter) hAAInv.symm
      _ = a ≫ dB := Category.assoc _ _ _
  let s : P ⟶ X.c := hTotal.desc (𝟙 X.c) dB hSCompat
  have hsLeft : jX ≫ s = 𝟙 X.c := hTotal.inl_desc (𝟙 X.c) dB hSCompat
  have hsRight : kB ≫ s = dB := hTotal.inr_desc (𝟙 X.c) dB hSCompat
  have hmRightRet : bY.toCenter ≫ rM = kB := by
    calc
      bY.toCenter ≫ rM = (kB ≫ m) ≫ rM := congrArg (fun t => t ≫ rM) hmRight.symm
      _ = kB := by simp [Category.assoc, hrM]
  let rC : Y.c ⟶ X.c := rM ≫ s
  have hrIl : Y.il ≫ rC = rL ≫ X.il := by
    calc
      Y.il ≫ rC = (bY.inl ≫ bY.toCenter) ≫ rC :=
        congrArg (fun t => t ≫ rC) bY.inl_toCenter.symm
      _ = bY.inl ≫ (bY.toCenter ≫ rM) ≫ s := by simp [rC, Category.assoc]
      _ = bY.inl ≫ kB ≫ s := congrArg (fun t => bY.inl ≫ t ≫ s) hmRightRet
      _ = bY.inl ≫ dB := by rw [hsRight]
      _ = (bY.inl ≫ aInv) ≫ bX.toCenter := (Category.assoc _ _ _).symm
      _ = (rL ≫ bX.inl) ≫ bX.toCenter := congrArg (fun t => t ≫ bX.toCenter) haInvL
      _ = rL ≫ (bX.inl ≫ bX.toCenter) := Category.assoc _ _ _
      _ = rL ≫ X.il := congrArg (fun t => rL ≫ t) bX.inl_toCenter
  have hrIr : Y.ir ≫ rC = rR ≫ X.ir := by
    calc
      Y.ir ≫ rC = (bY.inr ≫ bY.toCenter) ≫ rC :=
        congrArg (fun t => t ≫ rC) bY.inr_toCenter.symm
      _ = bY.inr ≫ (bY.toCenter ≫ rM) ≫ s := by simp [rC, Category.assoc]
      _ = bY.inr ≫ kB ≫ s := congrArg (fun t => bY.inr ≫ t ≫ s) hmRightRet
      _ = bY.inr ≫ dB := by rw [hsRight]
      _ = (bY.inr ≫ aInv) ≫ bX.toCenter := (Category.assoc _ _ _).symm
      _ = (rR ≫ bX.inr) ≫ bX.toCenter := congrArg (fun t => t ≫ bX.toCenter) haInvR
      _ = rR ≫ (bX.inr ≫ bX.toCenter) := Category.assoc _ _ _
      _ = rR ≫ X.ir := congrArg (fun t => rR ≫ t) bX.inr_toCenter
  have hrCenter : f.c ≫ rC = 𝟙 X.c := by
    calc
      f.c ≫ rC = (jX ≫ m) ≫ rC := congrArg (fun t => t ≫ rC) hmLeft.symm
      _ = jX ≫ (m ≫ (rM ≫ s)) := by simp [rC, Category.assoc]
      _ = jX ≫ ((m ≫ rM) ≫ s) := by simp [Category.assoc]
      _ = jX ≫ s := by rw [hrM]; simp
      _ = 𝟙 X.c := hsLeft
  let r : Y ⟶ X := ⟨rL, rR, rC, hrIl, hrIr⟩
  refine ⟨r, rfl, rfl, ?_⟩
  apply PathObj.Hom.ext
  · exact hrL
  · exact hrR
  · exact hrCenter

private theorem pathObj_exists_retraction {X Y : PathObj C} (f : X ⟶ Y)
    (hf : cofibrations (PathObj C) f) (hW : weakEquivalences (PathObj C) f) :
    ∃ r : Y ⟶ X, f ≫ r = 𝟙 X := by
  change weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c at hW
  obtain ⟨rL, hrL⟩ := hC.exists_retraction f.l hf.1 hW.1
  obtain ⟨rR, hrR⟩ := hC.exists_retraction f.r hf.2.1 hW.2.1
  obtain ⟨r, _, _, hr⟩ := pathObj_retraction_from_endpoints f hf hW rL hrL rR hrR
  exact ⟨r, hr⟩

private theorem pathObj_left_retraction_lift {X Y : PathObj C} (i : X ⟶ Y)
    (hi : cofibrations (PathObj C) i) {r : Y.l ⟶ X.l} (hr : i.l ≫ r = 𝟙 X.l) :
    ∃ s : Y ⟶ X, i ≫ s = 𝟙 X ∧ RelHomotopic i.l s.l r := by
  classical
  obtain ⟨Q, a, w, ha, hw, haw⟩ := cofibration_weak_equivalence_factorization r
  have hComp : weakEquivalences C ((i.l ≫ a) ≫ w) := by
    have hEq : (i.l ≫ a) ≫ w = 𝟙 X.l := by
      calc
        (i.l ≫ a) ≫ w = i.l ≫ (a ≫ w) := Category.assoc _ _ _
        _ = i.l ≫ r := congrArg (fun z => i.l ≫ z) haw
        _ = 𝟙 X.l := hr
    rw [hEq]
    exact hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hwId : weakEquivalences C (w ≫ 𝟙 X.l) := by simpa using hw
  have hIA : weakEquivalences C (i.l ≫ a) :=
    (hC.twoOutOfSix (i.l ≫ a) w (𝟙 X.l) hComp hwId).1
  have hIAcof : cofibrations C (i.l ≫ a) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hi.1 ha
  obtain ⟨P, eP, j, hj, hjL⟩ := pathObj_left_cofibration_extension (A := Y) a ha
  let t : X ⟶ P := i ≫ j
  have htcofFull : cofibrations (PathObj C) t := pathObj_cof_comp i j hi hj
  have htcofKeep : cofibrations (PathObj C) t := htcofFull
  rcases htcofFull with ⟨htLcof, _, _⟩
  let rT : P.l ⟶ X.l := eqToHom eP ≫ w
  have htr : t.l ≫ rT = 𝟙 X.l := by
    change (i.l ≫ j.l) ≫ (eqToHom eP ≫ w) = 𝟙 X.l
    rw [hjL]
    simp [rT, Category.assoc, haw, hr]
  have heP : weakEquivalences C (eqToHom eP) := by
    apply hC.isomorphisms_le_weakEquivalences
    infer_instance
  have hrTW : weakEquivalences C rT :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ heP hw
  have hIdX : weakEquivalences C (𝟙 X.l) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have htrW : weakEquivalences C (t.l ≫ rT) := by rw [htr]; exact hIdX
  have hrTId : weakEquivalences C (rT ≫ 𝟙 X.l) := by simpa using hrTW
  have htL : weakEquivalences C t.l :=
    (hC.twoOutOfSix t.l rT (𝟙 X.l) htrW hrTId).1
  have htW : weakEquivalences (PathObj C) t := pathObj_left_reflects_weakEquivalence t htL
  obtain ⟨s, hs⟩ := pathObj_exists_retraction t htcofKeep htW
  have hts : t.l ≫ s.l = 𝟙 X.l := by
    change (t ≫ s).l = (𝟙 X : X ⟶ X).l
    exact congrArg (fun m : X ⟶ X => m.l) hs
  have hEq : t.l ≫ s.l = t.l ≫ rT := hts.trans htr.symm
  have hRelT : RelHomotopic t.l s.l rT :=
    relHomotopic_of_trivialCof t.l htLcof htL s.l rT hEq
  have hSquare : i.l ≫ j.l = (𝟙 X.l) ≫ t.l := by
    calc
      i.l ≫ j.l = (i ≫ j).l := rfl
      _ = (𝟙 X.l) ≫ t.l := by simp [t]
  have hRel := relHomotopic_precompose i.l (𝟙 X.l) j.l t.l hi.1 hSquare hRelT
  have hjr : j.l ≫ rT = r := by
    rw [hjL]
    simp [rT, Category.assoc, haw]
  let s' : Y ⟶ X := j ≫ s
  have hs' : i ≫ s' = 𝟙 X := by
    calc
      i ≫ s' = (i ≫ j) ≫ s := (Category.assoc _ _ _).symm
      _ = t ≫ s := rfl
      _ = 𝟙 X := hs
  have hRel' : RelHomotopic i.l s'.l r := by
    change RelHomotopic i.l (j.l ≫ s.l) r
    simpa only [hjr] using hRel
  exact ⟨s', hs', hRel'⟩

private theorem pathObj_right_retraction_lift {X Y : PathObj C} (i : X ⟶ Y)
    (hi : cofibrations (PathObj C) i) {r : Y.r ⟶ X.r} (hr : i.r ≫ r = 𝟙 X.r) :
    ∃ s : Y ⟶ X, i ≫ s = 𝟙 X ∧ RelHomotopic i.r s.r r := by
  classical
  obtain ⟨Q, a, w, ha, hw, haw⟩ := cofibration_weak_equivalence_factorization r
  have hComp : weakEquivalences C ((i.r ≫ a) ≫ w) := by
    have hEq : (i.r ≫ a) ≫ w = 𝟙 X.r := by
      calc
        (i.r ≫ a) ≫ w = i.r ≫ (a ≫ w) := Category.assoc _ _ _
        _ = i.r ≫ r := congrArg (fun z => i.r ≫ z) haw
        _ = 𝟙 X.r := hr
    rw [hEq]
    exact hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hwId : weakEquivalences C (w ≫ 𝟙 X.r) := by simpa using hw
  have hIA : weakEquivalences C (i.r ≫ a) :=
    (hC.twoOutOfSix (i.r ≫ a) w (𝟙 X.r) hComp hwId).1
  have hIAcof : cofibrations C (i.r ≫ a) :=
    hC.toIsCofibrationCategory.isMultiplicative.comp_mem _ _ hi.2.1 ha
  obtain ⟨P, eP, j, hj, hjR⟩ := pathObj_right_cofibration_extension (A := Y) a ha
  let t : X ⟶ P := i ≫ j
  have htcofFull : cofibrations (PathObj C) t := pathObj_cof_comp i j hi hj
  have htcofKeep : cofibrations (PathObj C) t := htcofFull
  rcases htcofFull with ⟨_, htRcof, _⟩
  let rT : P.r ⟶ X.r := eqToHom eP ≫ w
  have htr : t.r ≫ rT = 𝟙 X.r := by
    change (i.r ≫ j.r) ≫ (eqToHom eP ≫ w) = 𝟙 X.r
    rw [hjR]
    simp [rT, Category.assoc, haw, hr]
  have heP : weakEquivalences C (eqToHom eP) := by
    apply hC.isomorphisms_le_weakEquivalences
    infer_instance
  have hrTW : weakEquivalences C rT :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _ heP hw
  have hIdX : weakEquivalences C (𝟙 X.r) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have htrW : weakEquivalences C (t.r ≫ rT) := by rw [htr]; exact hIdX
  have hrTId : weakEquivalences C (rT ≫ 𝟙 X.r) := by simpa using hrTW
  have htR : weakEquivalences C t.r :=
    (hC.twoOutOfSix t.r rT (𝟙 X.r) htrW hrTId).1
  have htW : weakEquivalences (PathObj C) t := pathObj_right_reflects_weakEquivalence t htR
  obtain ⟨s, hs⟩ := pathObj_exists_retraction t htcofKeep htW
  have hts : t.r ≫ s.r = 𝟙 X.r := by
    change (t ≫ s).r = (𝟙 X : X ⟶ X).r
    exact congrArg (fun m : X ⟶ X => m.r) hs
  have hEq : t.r ≫ s.r = t.r ≫ rT := hts.trans htr.symm
  have hRelT : RelHomotopic t.r s.r rT :=
    relHomotopic_of_trivialCof t.r htRcof htR s.r rT hEq
  have hSquare : i.r ≫ j.r = (𝟙 X.r) ≫ t.r := by
    calc
      i.r ≫ j.r = (i ≫ j).r := rfl
      _ = (𝟙 X.r) ≫ t.r := by simp [t]
  have hRel := relHomotopic_precompose i.r (𝟙 X.r) j.r t.r hi.2.1 hSquare hRelT
  have hjr : j.r ≫ rT = r := by
    rw [hjR]
    simp [rT, Category.assoc, haw]
  let s' : Y ⟶ X := j ≫ s
  have hs' : i ≫ s' = 𝟙 X := by
    calc
      i ≫ s' = (i ≫ j) ≫ s := (Category.assoc _ _ _).symm
      _ = t ≫ s := rfl
      _ = 𝟙 X := hs
  have hRel' : RelHomotopic i.r s'.r r := by
    change RelHomotopic i.r (j.r ≫ s.r) r
    simpa only [hjr] using hRel
  exact ⟨s', hs', hRel'⟩

private theorem pathObj_left_isHomotopyFullyFaithful :
    IsHomotopyFullyFaithful (PathObj.left C) := by
  classical
  let hPathCof := pathObj_isCofibrationCategory (C := C)
  letI : IsCofibrationCategory (PathObj C) := hPathCof
  intro A B X i hi x v hv
  change i.l ≫ v = x.l at hv
  letI : HasPushout i x := hPathCof.hasPushout i x hi
  let P := pushout i x
  let kB : B ⟶ P := pushout.inl i x
  let kX : X ⟶ P := pushout.inr i x
  have hP : IsPushout i x kB kX := IsPushout.of_hasPushout i x
  obtain ⟨hPL, _, _⟩ := pathObj_pushout_components i x kB kX hP hi
  have hComp : i.l ≫ v = x.l ≫ 𝟙 X.l := by simpa using hv
  let r : P.l ⟶ X.l := hPL.desc v (𝟙 X.l) hComp
  have hrB : kB.l ≫ r = v := hPL.inl_desc v (𝟙 X.l) hComp
  have hrX : kX.l ≫ r = 𝟙 X.l := hPL.inr_desc v (𝟙 X.l) hComp
  have hkXcof : cofibrations (PathObj C) kX :=
    hPathCof.isStableUnderCobaseChange.of_isPushout hP.flip hi
  obtain ⟨s, hs, hRel⟩ := pathObj_left_retraction_lift kX hkXcof hrX
  let v' : B ⟶ X := kB ≫ s
  have hv' : i ≫ v' = x := by
    calc
      i ≫ v' = (i ≫ kB) ≫ s := (Category.assoc _ _ _).symm
      _ = (x ≫ kX) ≫ s := congrArg (fun z => z ≫ s) hP.w
      _ = x ≫ (kX ≫ s) := Category.assoc _ _ _
      _ = x := by rw [hs]; simp
  have hSquare : i.l ≫ kB.l = x.l ≫ kX.l := by
    change (i ≫ kB).l = (x ≫ kX).l
    exact congrArg (fun m : A ⟶ P => m.l) hP.w
  have hRel' := relHomotopic_precompose i.l x.l kB.l kX.l hi.1 hSquare hRel
  have hRelGoal : RelHomotopic i.l v'.l v := by
    change RelHomotopic i.l (kB.l ≫ s.l) v
    simpa [hrB] using hRel'
  exact ⟨v', hv', hRelGoal⟩

private theorem pathObj_right_isHomotopyFullyFaithful :
    IsHomotopyFullyFaithful (PathObj.right C) := by
  classical
  let hPathCof := pathObj_isCofibrationCategory (C := C)
  letI : IsCofibrationCategory (PathObj C) := hPathCof
  intro A B X i hi x v hv
  change i.r ≫ v = x.r at hv
  letI : HasPushout i x := hPathCof.hasPushout i x hi
  let P := pushout i x
  let kB : B ⟶ P := pushout.inl i x
  let kX : X ⟶ P := pushout.inr i x
  have hP : IsPushout i x kB kX := IsPushout.of_hasPushout i x
  obtain ⟨_, hPR, _⟩ := pathObj_pushout_components i x kB kX hP hi
  have hComp : i.r ≫ v = x.r ≫ 𝟙 X.r := by simpa using hv
  let r : P.r ⟶ X.r := hPR.desc v (𝟙 X.r) hComp
  have hrB : kB.r ≫ r = v := hPR.inl_desc v (𝟙 X.r) hComp
  have hrX : kX.r ≫ r = 𝟙 X.r := hPR.inr_desc v (𝟙 X.r) hComp
  have hkXcof : cofibrations (PathObj C) kX :=
    hPathCof.isStableUnderCobaseChange.of_isPushout hP.flip hi
  obtain ⟨s, hs, hRel⟩ := pathObj_right_retraction_lift kX hkXcof hrX
  let v' : B ⟶ X := kB ≫ s
  have hv' : i ≫ v' = x := by
    calc
      i ≫ v' = (i ≫ kB) ≫ s := (Category.assoc _ _ _).symm
      _ = (x ≫ kX) ≫ s := congrArg (fun z => z ≫ s) hP.w
      _ = x ≫ (kX ≫ s) := Category.assoc _ _ _
      _ = x := by rw [hs]; simp
  have hSquare : i.r ≫ kB.r = x.r ≫ kX.r := by
    change (i ≫ kB).r = (x ≫ kX).r
    exact congrArg (fun m : A ⟶ P => m.r) hP.w
  have hRel' := relHomotopic_precompose i.r x.r kB.r kX.r hi.2.1 hSquare hRel
  have hRelGoal : RelHomotopic i.r v'.r v := by
    change RelHomotopic i.r (kB.r ≫ s.r) v
    simpa [hrB] using hRel'
  exact ⟨v', hv', hRelGoal⟩

private noncomputable def pathObj_isCylinderCategory : IsCylinderCategory (PathObj C) := by
  classical
  let hPathCof := pathObj_isCofibrationCategory (C := C)
  letI : IsCofibrationCategory (PathObj C) := hPathCof
  refine
    { toIsCofibrationCategory := hPathCof
      isomorphisms_le_weakEquivalences := ?_
      weakEquivalences_isMultiplicative := ?_
      twoOutOfSix := pathObj_weakEquivalences_twoOutOfSix
      trivialCofibration_cobaseChange := pathObj_trivialCof_cobaseChange
      exists_cylinder := pathObj_exists_cylinder
      exists_retraction := pathObj_exists_retraction }
  · intro X Y f hf
    exact pathObj_isomorphisms_le_weakEquivalences f hf
  · refine { id_mem := ?_, comp_mem := ?_ }
    · intro X
      exact pathObj_isomorphisms_le_weakEquivalences (𝟙 X) (by infer_instance)
    · intro X Y Z f g hf hg
      exact pathObj_weakEquivalences_comp f g hf hg

private theorem pathObj_initial_endpoints {I : PathObj C} (hI : IsInitial I) :
    Nonempty (IsInitial I.l) ∧ Nonempty (IsInitial I.r) := by
  obtain ⟨I₀, ⟨hI₀⟩⟩ := hC.exists_initial
  let J₀ := pathInitialObject hI₀
  have hJ₀ : IsInitial J₀ := pathInitial_isInitial hI₀
  let e : I ≅ J₀ := hI.uniqueUpToIso hJ₀
  let eL : I.l ≅ I₀ := (PathObj.left C).mapIso e
  let eR : I.r ≅ I₀ := (PathObj.right C).mapIso e
  exact ⟨⟨IsInitial.ofIso hI₀ eL.symm⟩, ⟨IsInitial.ofIso hI₀ eR.symm⟩⟩

private theorem pathObj_proj_isCylinderMorphism :
    IsCylinderMorphism (PathObj.proj C) := by
  classical
  refine
    { toIsCofibrationMorphism :=
        { map_cofibration := ?_
          map_initial := ?_
          map_isPushout := ?_ }
      map_weakEquivalence := ?_ }
  · intro X Y f hf
    change cofibrations C f.l ∧ cofibrations C f.r
    exact ⟨hf.1, hf.2.1⟩
  · intro I hI
    obtain ⟨⟨hIL⟩, ⟨hIR⟩⟩ := pathObj_initial_endpoints hI
    exact ⟨prod_isInitial hIL hIR⟩
  · intro A B X P i f k j h hi
    obtain ⟨hL, hR, _⟩ := pathObj_pushout_components i f k j h hi
    change IsPushout (C := C × C)
      ((i.l, i.r) : (A.l, A.r) ⟶ (B.l, B.r))
      ((f.l, f.r) : (A.l, A.r) ⟶ (X.l, X.r))
      ((k.l, k.r) : (B.l, B.r) ⟶ (P.l, P.r))
      ((j.l, j.r) : (X.l, X.r) ⟶ (P.l, P.r))
    exact isPushout_prod hL hR
  · intro X Y f hf
    change weakEquivalences C f.l ∧ weakEquivalences C f.r
    exact ⟨hf.1, hf.2.1⟩

private theorem pathObj_left_isCylinderMorphism : IsCylinderMorphism (PathObj.left C) := by
  refine
    { toIsCofibrationMorphism :=
        { map_cofibration := ?_
          map_initial := ?_
          map_isPushout := ?_ }
      map_weakEquivalence := ?_ }
  · intro X Y f hf
    exact hf.1
  · intro I hI
    exact (pathObj_initial_endpoints hI).1
  · intro A B X P f g k j h hf
    obtain ⟨hL, _, _⟩ := pathObj_pushout_components f g k j h hf
    exact hL
  · intro X Y f hf
    exact hf.1

private theorem pathObj_right_isCylinderMorphism : IsCylinderMorphism (PathObj.right C) := by
  refine
    { toIsCofibrationMorphism :=
        { map_cofibration := ?_
          map_initial := ?_
          map_isPushout := ?_ }
      map_weakEquivalence := ?_ }
  · intro X Y f hf
    exact hf.2.1
  · intro I hI
    exact (pathObj_initial_endpoints hI).2
  · intro A B X P f g k j h hf
    obtain ⟨_, hR, _⟩ := pathObj_pushout_components f g k j h hf
    exact hR
  · intro X Y f hf
    exact hf.2.1

private theorem pathObj_proj_isPreFibration : IsPreFibration (PathObj.proj C) := by
  classical
  refine { lift_retraction := ?_, lift_factorization := ?_ }
  · intro A B s hs hW r hr
    change (s.l ≫ r.1, s.r ≫ r.2) = (𝟙 A.l, 𝟙 A.r) at hr
    have hrL : s.l ≫ r.1 = 𝟙 A.l := by
      have h := congrArg Prod.fst hr
      simpa using h
    have hrR : s.r ≫ r.2 = 𝟙 A.r := by
      have h := congrArg Prod.snd hr
      simpa using h
    obtain ⟨r', hrL', hrR', hr'⟩ := pathObj_retraction_from_endpoints s hs hW r.1 hrL r.2 hrR
    refine ⟨r', hr', ?_⟩
    change (r'.l, r'.r) = r
    exact Prod.ext hrL' hrR'
  · intro A B f Q i w hi hw hcomp
    change cofibrations C i.1 ∧ cofibrations C i.2 at hi
    change weakEquivalences C w.1 ∧ weakEquivalences C w.2 at hw
    change (i.1 ≫ w.1, i.2 ≫ w.2) = (f.l, f.r) at hcomp
    have hCompL : i.1 ≫ w.1 = f.l := by
      have h := congrArg Prod.fst hcomp
      simpa using h
    have hCompR : i.2 ≫ w.2 = f.r := by
      have h := congrArg Prod.snd hcomp
      simpa using h
    obtain ⟨Z, eL, eR, i', w', hiL, hiR, hwL, hwR, hcof, hweq, hFactor⟩ :=
      pathObj_factorization_from_endpoints f i.1 w.1 hi.1 hw.1 hCompL
        i.2 w.2 hi.2 hw.2 hCompR
    let e : (PathObj.proj C).obj Z = Q := Prod.ext eL eR
    have heL : congrArg Prod.fst e = eL := Subsingleton.elim _ _
    have heR : congrArg Prod.snd e = eR := Subsingleton.elim _ _
    have heLInv : congrArg Prod.fst e.symm = eL.symm := Subsingleton.elim _ _
    have heRInv : congrArg Prod.snd e.symm = eR.symm := Subsingleton.elim _ _
    have hiL' : i'.l = i.1 ≫ eqToHom (congrArg Prod.fst e.symm) := by
      rw [heLInv]
      exact hiL
    have hiR' : i'.r = i.2 ≫ eqToHom (congrArg Prod.snd e.symm) := by
      rw [heRInv]
      exact hiR
    have hwL' : w'.l = eqToHom (congrArg Prod.fst e) ≫ w.1 := by
      rw [heL]
      exact hwL
    have hwR' : w'.r = eqToHom (congrArg Prod.snd e) ≫ w.2 := by
      rw [heR]
      exact hwR
    refine ⟨Z, i', w', e, hcof, hweq, hFactor, ?_, ?_⟩
    · change (i'.l, i'.r) = i ≫ eqToHom e.symm
      apply Prod.ext
      · simpa using hiL'
      · simpa using hiR'
    · change (w'.l, w'.r) = eqToHom e ≫ w
      apply Prod.ext
      · simpa using hwL'
      · simpa using hwR'

private theorem pathObj_exists_cospan_with_equal_endpoints (A : C) :
    ∃ X : PathObj C, X.l = A ∧ X.r = A := by
  classical
  obtain ⟨I, ⟨hI⟩⟩ := hC.exists_initial
  obtain ⟨cyl⟩ := hC.exists_cylinder hI A
  let u0 : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let u1 : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  have hId : weakEquivalences C (𝟙 A) :=
    hC.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hu0p : weakEquivalences C (u0 ≫ cyl.p) := by
    simpa [u0, Category.assoc, cyl.j₀_c_p] using hId
  have hpId : weakEquivalences C (cyl.p ≫ 𝟙 A) := by simpa using cyl.p_mem
  have hu0 : weakEquivalences C u0 := (hC.twoOutOfSix u0 cyl.p (𝟙 A) hu0p hpId).1
  have hu1p : weakEquivalences C (u1 ≫ cyl.p) := by
    simpa [u1, Category.assoc, cyl.j₁_c_p] using hId
  have hu1 : weakEquivalences C u1 := (hC.twoOutOfSix u1 cyl.p (𝟙 A) hu1p hpId).1
  have hPair : IsCofibrantPair u0 u1 := by
    refine ⟨I, hI, cyl.P, cyl.j₀, cyl.j₁, cyl.isPushout, cyl.c, ?_, ?_, cyl.c_mem⟩
    · rfl
    · rfl
  let X : PathObj C := ⟨A, A, cyl.I, u0, u1, hPair, hu0, hu1⟩
  exact ⟨X, rfl, rfl⟩

private theorem pathObj_endpoints_homotopySurjective :
    IsHomotopySurjective (PathObj.left C) ∧ IsHomotopySurjective (PathObj.right C) := by
  constructor
  · intro A
    obtain ⟨X, hXl, _⟩ := pathObj_exists_cospan_with_equal_endpoints A
    refine ⟨X, eqToHom hXl.symm, ?_⟩
    have hIso : IsIso (eqToHom hXl.symm) := by infer_instance
    exact hC.isomorphisms_le_weakEquivalences _ hIso
  · intro A
    obtain ⟨X, _, hXr⟩ := pathObj_exists_cospan_with_equal_endpoints A
    refine ⟨X, eqToHom hXr.symm, ?_⟩
    have hIso : IsIso (eqToHom hXr.symm) := by infer_instance
    exact hC.isomorphisms_le_weakEquivalences _ hIso

private theorem pathObj_liftingTarget_core :
    IsCylinderCategory (PathObj C) ∧ IsCylinderCategory (C × C) ∧
      IsCylinderMorphism (PathObj.proj C) ∧ IsPreFibration (PathObj.proj C) := by
  exact ⟨pathObj_isCylinderCategory, prod_isCylinderCategory,
    pathObj_proj_isCylinderMorphism, pathObj_proj_isPreFibration⟩

private theorem isCofibrantPair_precompose_isos {B B' X X' T : C}
    (eB : B ≅ B') (eX : X ≅ X') {u : B' ⟶ T} {w : X' ⟶ T}
    (h : IsCofibrantPair (eB.hom ≫ u) (eX.hom ≫ w)) :
    IsCofibrantPair u w := by
  obtain ⟨I, hI, P, k, j, hP, m, hkm, hjm, hcof⟩ := h
  let k' : B' ⟶ P := eB.inv ≫ k
  let j' : X' ⟶ P := eX.inv ≫ j
  have hP' : IsPushout (hI.to B') (hI.to X') k' j' := by
    apply hP.of_iso' (Iso.refl I) eB.symm eX.symm (Iso.refl P)
    · exact (hI.hom_ext _ _).symm
    · exact (hI.hom_ext _ _).symm
    · simp [k']
    · simp [j']
  refine ⟨I, hI, P, k', j', hP', m, ?_, ?_, hcof⟩
  · calc
      k' ≫ m = eB.inv ≫ (k ≫ m) := by simp [k', Category.assoc]
      _ = eB.inv ≫ (eB.hom ≫ u) := by rw [hkm]
      _ = u := by simp [Category.assoc]
  · calc
      j' ≫ m = eX.inv ≫ (j ≫ m) := by simp [j', Category.assoc]
      _ = eX.inv ≫ (eX.hom ≫ w) := by rw [hjm]
      _ = w := by simp [Category.assoc]

private theorem pathObj_proj_isIsofibration : IsIsofibration (PathObj.proj C) := by
  intro X y e
  dsimp [PathObj.proj] at e
  rcases y with ⟨yL, yR⟩
  let eL : X.l ≅ yL := (CategoryTheory.Prod.fst C C).mapIso e
  let eR : X.r ≅ yR := (CategoryTheory.Prod.snd C C).mapIso e
  have hCof : IsCofibrantPair (eL.hom ≫ (eL.inv ≫ X.il))
      (eR.hom ≫ (eR.inv ≫ X.ir)) := by
    simpa [Category.assoc] using X.cofibrant
  have hCof' : IsCofibrantPair (eL.inv ≫ X.il) (eR.inv ≫ X.ir) :=
    isCofibrantPair_precompose_isos eL eR hCof
  have hIl : weakEquivalences C (eL.inv ≫ X.il) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _
      (hC.isomorphisms_le_weakEquivalences _ (by infer_instance)) X.il_mem
  have hIr : weakEquivalences C (eR.inv ≫ X.ir) :=
    hC.weakEquivalences_isMultiplicative.comp_mem _ _
      (hC.isomorphisms_le_weakEquivalences _ (by infer_instance)) X.ir_mem
  let X' : PathObj C := ⟨yL, yR, X.c, eL.inv ≫ X.il, eR.inv ≫ X.ir,
    hCof', hIl, hIr⟩
  let f : X ⟶ X' := ⟨eL.hom, eR.hom, 𝟙 X.c,
    by simp [X', Category.assoc], by simp [X', Category.assoc]⟩
  let g : X' ⟶ X := ⟨eL.inv, eR.inv, 𝟙 X.c,
    by simp [X', Category.assoc], by simp [X', Category.assoc]⟩
  have hfg : f ≫ g = 𝟙 X := by
    apply PathObj.Hom.ext
    · change eL.hom ≫ eL.inv = 𝟙 X.l
      exact eL.hom_inv_id
    · change eR.hom ≫ eR.inv = 𝟙 X.r
      exact eR.hom_inv_id
    · change (𝟙 X.c) ≫ (𝟙 X.c) = 𝟙 X.c
      simp
  have hgf : g ≫ f = 𝟙 X' := by
    apply PathObj.Hom.ext
    · change eL.inv ≫ eL.hom = 𝟙 X'.l
      exact eL.inv_hom_id
    · change eR.inv ≫ eR.hom = 𝟙 X'.r
      exact eR.inv_hom_id
    · change (𝟙 X.c) ≫ (𝟙 X.c) = 𝟙 X.c
      simp
  let e' : X ≅ X' := ⟨f, g, hfg, hgf⟩
  have hX' : (PathObj.proj C).obj X' = (yL, yR) := by
    dsimp [PathObj.proj, X']
  refine ⟨X', e', hX', ?_⟩
  dsimp [PathObj.proj, X', e', f]
  apply Prod.ext
  · change eL.hom = e.hom.1 ≫ (eqToHom hX'.symm).1
    rw [CategoryTheory.eqToHom_fst]
    dsimp [eL, Functor.mapIso, CategoryTheory.Prod.fst]
    simp [hX', PathObj.proj, X']
  · change eR.hom = e.hom.2 ≫ (eqToHom hX'.symm).2
    rw [CategoryTheory.eqToHom_snd]
    dsimp [eR, Functor.mapIso, CategoryTheory.Prod.snd]
    simp [hX', PathObj.proj, X']

theorem pathObj_isLiftingTarget_proof :
    IsLiftingTarget false (PathObj C) (C × C) (PathObj.proj C) ∧
      IsAcyclic (PathObj.left C) ∧ IsAcyclic (PathObj.right C) := by
  rcases pathObj_liftingTarget_core (C := C) with ⟨hPath, hProd, hProj, hPre⟩
  rcases pathObj_endpoints_homotopySurjective (C := C) with ⟨hLeftSurj, hRightSurj⟩
  have hFalse : false = true → IsAcyclic (PathObj.proj C) := by
    intro h
    cases h
  exact ⟨⟨hPath, hProd, hProj, hPre, pathObj_proj_isIsofibration, hFalse⟩,
    ⟨hLeftSurj, pathObj_left_isHomotopyFullyFaithful⟩,
    ⟨hRightSurj, pathObj_right_isHomotopyFullyFaithful⟩⟩

#print axioms HomotopyHypothesis.Cylinder.PathObjects.pathObj_isLiftingTarget_proof

private def pairFunctor {D : Type (u + 1)} [Category.{u} D]
    (F G : C ⥤ D) : C ⥤ D × D where
  obj X := (F.obj X, G.obj X)
  map f := (F.map f, G.map f)
  map_id X := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

private theorem pairFunctor_isCylinderMorphism {D : Type (u + 1)} [Category.{u} D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
    [IsCylinderCategory D]
    {F G : C ⥤ D} (hF : IsCylinderMorphism F) (hG : IsCylinderMorphism G) :
    IsCylinderMorphism (pairFunctor F G) := by
  refine
    { toIsCofibrationMorphism :=
        { map_cofibration := ?_
          map_initial := ?_
          map_isPushout := ?_ }
      map_weakEquivalence := ?_ }
  · intro X Y f hf
    change cofibrations D (F.map f) ∧ cofibrations D (G.map f)
    exact ⟨hF.map_cofibration f hf, hG.map_cofibration f hf⟩
  · intro I hI
    obtain ⟨hFI⟩ := hF.map_initial hI
    obtain ⟨hGI⟩ := hG.map_initial hI
    refine ⟨IsInitial.ofUniqueHom (fun X => (hFI.to X.1, hGI.to X.2)) ?_⟩
    intro X f
    apply Prod.ext
    · exact hFI.hom_ext f.1 (hFI.to X.1)
    · exact hGI.hom_ext f.2 (hGI.to X.2)
  · intro A B X P i f k j h hi
    exact isPushout_prod (C := D)
      (hF.map_isPushout i f k j h hi) (hG.map_isPushout i f k j h hi)
  · intro X Y f hf
    change weakEquivalences D (F.map f) ∧ weakEquivalences D (G.map f)
    exact ⟨hF.map_weakEquivalence f hf, hG.map_weakEquivalence f hf⟩

private theorem isAcyclic_iff_of_isAcyclic_postcomp
    {D E : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    [Category.{u} E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [IsCylinderCategory E] {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsCylinderMorphism F) (hG : IsCylinderMorphism G) (hGac : IsAcyclic G) :
    IsAcyclic F ↔ IsAcyclic (F ⋙ G) := by
  constructor
  · intro hFac
    exact HomotopyHypothesis.Henry.isAcyclic_comp hF hG hFac hGac
  · intro hFG
    have hGid : IsAcyclic (G ⋙ 𝟭 E) := by simpa [Functor.comp_id] using hGac
    exact (Packages.isAcyclic_twoOutOfSix F G (𝟭 E) hF hG
      IsCylinderMorphism.id hFG hGid).1

omit [IsCylinderCategory C] in
theorem isAcyclic_iff_of_isCylinderCoherator_proof {o : C}
    (hCoh : IsCylinderCoherator.{u + 1, u} C o)
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D] {G G' : C ⥤ D}
    (hG : IsCylinderMorphism G) (hG' : IsCylinderMorphism G') {X : D}
    (w : G.obj o ⟶ X) (w' : G'.obj o ⟶ X)
    (hw : weakEquivalences D w) (hw' : weakEquivalences D w') :
    IsAcyclic G ↔ IsAcyclic G' := by
  classical
  letI : IsCylinderCategory C := hCoh.1
  have hD : IsCylinderCategory D := inferInstance
  obtain ⟨I, ⟨hI⟩⟩ := hD.exists_initial
  letI : HasPushout (hI.to (G.obj o)) (hI.to (G'.obj o)) :=
    hD.toIsCofibrationCategory.hasPushout (hI.to (G.obj o)) (hI.to (G'.obj o))
      (hD.toIsCofibrationCategory.initial_cofibration hI (G.obj o))
  let Q₀ := pushout (hI.to (G.obj o)) (hI.to (G'.obj o))
  let qL : G.obj o ⟶ Q₀ := pushout.inl (hI.to (G.obj o)) (hI.to (G'.obj o))
  let qR : G'.obj o ⟶ Q₀ := pushout.inr (hI.to (G.obj o)) (hI.to (G'.obj o))
  have hQ₀ : IsPushout (hI.to (G.obj o)) (hI.to (G'.obj o)) qL qR :=
    IsPushout.of_hasPushout _ _
  have hCompat : hI.to (G.obj o) ≫ w = hI.to (G'.obj o) ≫ w' := hI.hom_ext _ _
  let q : Q₀ ⟶ X := hQ₀.desc w w' hCompat
  have hqL : qL ≫ q = w := hQ₀.inl_desc _ _ hCompat
  have hqR : qR ≫ q = w' := hQ₀.inr_desc _ _ hCompat
  obtain ⟨M, c, p, hc, hp, hcp⟩ :=
    cofibration_weak_equivalence_factorization (C := D) q
  have hLeftCompEq : (qL ≫ c) ≫ p = w := by
    calc
      (qL ≫ c) ≫ p = qL ≫ (c ≫ p) := Category.assoc _ _ _
      _ = qL ≫ q := congrArg (fun z => qL ≫ z) hcp
      _ = w := hqL
  have hRightCompEq : (qR ≫ c) ≫ p = w' := by
    calc
      (qR ≫ c) ≫ p = qR ≫ (c ≫ p) := Category.assoc _ _ _
      _ = qR ≫ q := congrArg (fun z => qR ≫ z) hcp
      _ = w' := hqR
  have hLeftComp : weakEquivalences D ((qL ≫ c) ≫ p) := by
    rw [hLeftCompEq]
    exact hw
  have hRightComp : weakEquivalences D ((qR ≫ c) ≫ p) := by
    rw [hRightCompEq]
    exact hw'
  have hIdX : weakEquivalences D (𝟙 X) :=
    hD.isomorphisms_le_weakEquivalences _ (by infer_instance)
  have hpId : weakEquivalences D (p ≫ 𝟙 X) := by simpa using hp
  have hIL : weakEquivalences D (qL ≫ c) :=
    (hD.twoOutOfSix (qL ≫ c) p (𝟙 X) hLeftComp hpId).1
  have hIR : weakEquivalences D (qR ≫ c) :=
    (hD.twoOutOfSix (qR ≫ c) p (𝟙 X) hRightComp hpId).1
  have hPair : IsCofibrantPair (qL ≫ c) (qR ≫ c) := by
    refine ⟨I, hI, Q₀, qL, qR, hQ₀, c, rfl, rfl, hc⟩
  let T : PathObj D := ⟨G.obj o, G'.obj o, M, qL ≫ c, qR ≫ c, hPair, hIL, hIR⟩
  let Gpair : C ⥤ D × D := pairFunctor G G'
  have hGpair : IsCylinderMorphism Gpair := pairFunctor_isCylinderMorphism hG hG'
  have hTarget : IsLiftingTarget false (PathObj D) (D × D) (PathObj.proj D) :=
    (pathObj_isLiftingTarget_proof (C := D)).1
  have hPairObj : Gpair.obj o = (PathObj.proj D).obj T := rfl
  obtain ⟨Ψ, hΨ, hΨproj, _⟩ :=
    hCoh.2 (PathObj D) (D × D) (PathObj.proj D) hTarget T trivial Gpair hGpair hPairObj
  have hLeftEq : Ψ ⋙ PathObj.left D = G := by
    have hObj : ∀ A, (Ψ ⋙ PathObj.left D).obj A = G.obj A := by
      intro A
      have hPairA : ((Ψ.obj A).l, (Ψ.obj A).r) = (G.obj A, G'.obj A) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj A
      change (Ψ.obj A).l = G.obj A
      exact Eq.ndrec (motive := fun z : D × D => (Ψ.obj A).l = z.1) rfl hPairA
    have hMap : ∀ A B (f : A ⟶ B),
        (Ψ ⋙ PathObj.left D).map f =
          eqToHom (hObj A) ≫ G.map f ≫ eqToHom (hObj B).symm := by
      intro A B f
      have h := Functor.congr_hom hΨproj f
      have hPairA : ((Ψ.obj A).l, (Ψ.obj A).r) = (G.obj A, G'.obj A) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj A
      have hPairB : ((Ψ.obj B).l, (Ψ.obj B).r) = (G.obj B, G'.obj B) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj B
      have hfst := congrArg Prod.fst h
      change ((Ψ ⋙ PathObj.proj D).map f).1 =
        (eqToHom (Functor.congr_obj hΨproj A)).1 ≫ (Gpair.map f).1 ≫
          (eqToHom (Functor.congr_obj hΨproj B).symm).1 at hfst
      rw [CategoryTheory.eqToHom_fst (Functor.congr_obj hΨproj A),
        CategoryTheory.eqToHom_fst (Functor.congr_obj hΨproj B).symm] at hfst
      simpa [PathObj.left, PathObj.proj, pairFunctor, Gpair, hObj] using hfst
    exact CategoryTheory.Functor.ext hObj hMap
  have hRightEq : Ψ ⋙ PathObj.right D = G' := by
    have hObj : ∀ A, (Ψ ⋙ PathObj.right D).obj A = G'.obj A := by
      intro A
      have hPairA : ((Ψ.obj A).l, (Ψ.obj A).r) = (G.obj A, G'.obj A) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj A
      change (Ψ.obj A).r = G'.obj A
      exact Eq.ndrec (motive := fun z : D × D => (Ψ.obj A).r = z.2) rfl hPairA
    have hMap : ∀ A B (f : A ⟶ B),
        (Ψ ⋙ PathObj.right D).map f =
          eqToHom (hObj A) ≫ G'.map f ≫ eqToHom (hObj B).symm := by
      intro A B f
      have h := Functor.congr_hom hΨproj f
      have hPairA : ((Ψ.obj A).l, (Ψ.obj A).r) = (G.obj A, G'.obj A) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj A
      have hPairB : ((Ψ.obj B).l, (Ψ.obj B).r) = (G.obj B, G'.obj B) := by
        simpa [PathObj.proj, pairFunctor, Gpair] using Functor.congr_obj hΨproj B
      have hsnd := congrArg Prod.snd h
      change ((Ψ ⋙ PathObj.proj D).map f).2 =
        (eqToHom (Functor.congr_obj hΨproj A)).2 ≫ (Gpair.map f).2 ≫
          (eqToHom (Functor.congr_obj hΨproj B).symm).2 at hsnd
      rw [CategoryTheory.eqToHom_snd (Functor.congr_obj hΨproj A),
        CategoryTheory.eqToHom_snd (Functor.congr_obj hΨproj B).symm] at hsnd
      simpa [PathObj.right, PathObj.proj, pairFunctor, Gpair, hObj] using hsnd
    exact CategoryTheory.Functor.ext hObj hMap
  letI : IsCylinderCategory (PathObj D) := pathObj_isCylinderCategory (C := D)
  have hLeftAC : IsAcyclic (PathObj.left D) :=
    (pathObj_isLiftingTarget_proof (C := D)).2.1
  have hRightAC : IsAcyclic (PathObj.right D) :=
    (pathObj_isLiftingTarget_proof (C := D)).2.2
  have hLeftMor : IsCylinderMorphism (Ψ ⋙ PathObj.left D) :=
    IsCylinderMorphism.comp hΨ (pathObj_left_isCylinderMorphism (C := D))
  have hRightMor : IsCylinderMorphism (Ψ ⋙ PathObj.right D) :=
    IsCylinderMorphism.comp hΨ (pathObj_right_isCylinderMorphism (C := D))
  have hLeftIff : IsAcyclic Ψ ↔ IsAcyclic G := by
    simpa only [hLeftEq] using
      isAcyclic_iff_of_isAcyclic_postcomp hΨ
        (pathObj_left_isCylinderMorphism (C := D)) hLeftAC
  have hRightIff : IsAcyclic Ψ ↔ IsAcyclic G' := by
    simpa only [hRightEq] using
      isAcyclic_iff_of_isAcyclic_postcomp hΨ
        (pathObj_right_isCylinderMorphism (C := D)) hRightAC
  exact hLeftIff.symm.trans hRightIff

#print axioms HomotopyHypothesis.Cylinder.PathObjects.isAcyclic_iff_of_isCylinderCoherator_proof

end HomotopyHypothesis.Cylinder.PathObjects
