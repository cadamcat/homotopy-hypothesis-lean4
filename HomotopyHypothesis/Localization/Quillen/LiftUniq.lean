import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.Quillen.KenBrown
open CategoryTheory Limits HomotopyHypothesis.Henry MorphismProperty

namespace HomotopyHypothesis.Localization.Quillen

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {cofC fibC WC : MorphismProperty C} {cofD fibD WD : MorphismProperty D}

structure CofRepl (hC : IsSemiModelCategory C cofC fibC WC) [HasInitial C] (X : C) where
  Q : C
  i : ⊥_ C ⟶ Q
  p : Q ⟶ X
  hi : cofC i
  hp_fib : fibC p
  hp_W : WC p
  fac : i ≫ p = initial.to X

noncomputable def makeCofRepl (hC : IsSemiModelCategory C cofC fibC WC) [HasInitial C] (X : C) :
    CofRepl hC X :=
  let h := hC.factor_cof_trivFib (initial.to X)
  let Q := Classical.choose h
  let hQ := Classical.choose_spec h
  let i := Classical.choose hQ
  let hi := Classical.choose_spec hQ
  let p := Classical.choose hi
  let hp := Classical.choose_spec hi
  ⟨Q, i, p, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

lemma cofRepl_isCof (hC : IsSemiModelCategory C cofC fibC WC) [HasInitial C] (X : C) :
    IsCofibrantFor cofC (makeCofRepl hC X).Q :=
  isCofibrantFor_of_initial hC _ (makeCofRepl hC X).hi

lemma cofC_eq_llp (hC : IsSemiModelCategory C cofC fibC WC) :
    cofC = (fibC ⊓ WC).llp := by
  have h_le : cofC ≤ (fibC ⊓ WC).llp := by
    rw [MorphismProperty.le_llp_iff_le_rlp]
    exact hC.lift_cof_trivFib
  have : HasFactorization cofC (fibC ⊓ WC) := ⟨fun f ↦ by
    obtain ⟨Z, i, p, hi, hp_fib, hp_W, hfac⟩ := hC.factor_cof_trivFib f
    exact ⟨⟨Z, i, p, hfac, hi, ⟨hp_fib, hp_W⟩⟩⟩⟩
  have : cofC.IsStableUnderRetracts := hC.cof_retracts
  exact (MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts h_le).symm

lemma cofC_comp (hC : IsSemiModelCategory C cofC fibC WC)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : cofC f) (hg : cofC g) :
    cofC (f ≫ g) := by
  have heq := cofC_eq_llp hC
  rw [heq] at hf hg ⊢
  exact MorphismProperty.comp_mem _ _ _ hf hg

lemma cofC_pushout_inl (hC : IsSemiModelCategory C cofC fibC WC)
    [HasInitial C] {X : C} (hi : cofC (initial.to X)) [HasPushout (initial.to X) (initial.to X)] :
    cofC (pushout.inl (f := initial.to X) (g := initial.to X)) := by
  have heq := cofC_eq_llp hC
  rw [heq] at hi ⊢
  have hp := IsPushout.of_hasPushout (initial.to X) (initial.to X)
  have : (fibC ⊓ WC).llp.IsStableUnderCobaseChange := inferInstance
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp hi

lemma WD_id (hD : IsSemiModelCategory D cofD fibD WD) (Y : D) :
    WD (𝟙 Y) := by
  obtain ⟨Z, i, p, hi, hp_fib, hp_W, hfac⟩ := hD.factor_cof_trivFib (𝟙 Y)
  have : WD.HasTwoOutOfThreeProperty := hD.twoOutOfThree
  have hp_comp : WD (p ≫ 𝟙 Y) := by simpa using hp_W
  exact WD.of_precomp p (𝟙 Y) hp_W hp_comp

lemma L_map_trivFib_WD
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {A B : C} (hA : IsCofibrantFor cofC A) (hB : IsCofibrantFor cofC B)
    (f : A ⟶ B) (hf_W : WC f) :
    WD (L.map f) := by
  have h_fib_LB : IsFibrantFor fibD (L.obj B) := hfib (L.obj B)
  have h_adj_id : WC (adj.unit.app B) := by
    have h_id_WD : WD (𝟙 (L.obj B)) := WD_id hD (L.obj B)
    have h_rw := (hQ.weakEquivalence_iff (𝟙 (L.obj B)) hB h_fib_LB).mp h_id_WD
    rwa [adj.homEquiv_id] at h_rw
  have h_comp_W : WC (f ≫ adj.unit.app B) := by
    have : WC.HasTwoOutOfThreeProperty := hC.twoOutOfThree
    exact WC.comp_mem f (adj.unit.app B) hf_W h_adj_id
  have h_nat : adj.homEquiv A (L.obj B) (L.map f) = f ≫ adj.unit.app B := by
    rw [adj.homEquiv_unit, adj.unit_naturality]
  rw [hQ.weakEquivalence_iff (L.map f) hA h_fib_LB]
  rw [h_nat]
  exact h_comp_W

lemma lift_uniq [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} [Category.{v₃} H₁]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD]
    {X Y : C} (g₁ g₂ : (makeCofRepl hC X).Q ⟶ (makeCofRepl hC Y).Q)
    (h : g₁ ≫ (makeCofRepl hC Y).p = g₂ ≫ (makeCofRepl hC Y).p) :
    L₁.map (L.map g₁) = L₁.map (L.map g₂) := by
  have : HasFiniteColimits C := hC.hasFiniteColimits
  let QX := (makeCofRepl hC X).Q
  let QY := (makeCofRepl hC Y).Q
  let pY := (makeCofRepl hC Y).p
  have hQX : IsCofibrantFor cofC QX := cofRepl_isCof hC X
  have hQY : IsCofibrantFor cofC QY := cofRepl_isCof hC Y
  have hiX : cofC (initial.to QX) := hQX initialIsInitial
  have : HasPushout (initial.to QX) (initial.to QX) := inferInstance
  let P := pushout (initial.to QX) (initial.to QX)
  let i0 : QX ⟶ P := pushout.inl (f := initial.to QX) (g := initial.to QX)
  let i1 : QX ⟶ P := pushout.inr (f := initial.to QX) (g := initial.to QX)

  have hj0 : cofC i0 := cofC_pushout_inl hC hiX
  have hinit_P : cofC (initial.to P) := by
    have heq : initial.to P = initial.to QX ≫ i0 := by
      apply initial.hom_ext
    rw [heq]
    exact cofC_comp hC _ _ hiX hj0
  have hP : IsCofibrantFor cofC P :=
    isCofibrantFor_of_initial hC _ hinit_P
  let nabla : P ⟶ QX :=
    pushout.desc (𝟙 QX) (𝟙 QX) (by apply initial.hom_ext)
  obtain ⟨I, j, π, hj, hπ_fib, hπ_W, hfac⟩ := hC.factor_cof_trivFib nabla
  have hinit_I : cofC (initial.to I) := by
    have heq : initial.to I = initial.to P ≫ j := by
      apply initial.hom_ext
    rw [heq]
    exact cofC_comp hC _ _ hinit_P hj
  have hI : IsCofibrantFor cofC I := isCofibrantFor_of_initial hC _ hinit_I
  have hπ_WD : WD (L.map π) := L_map_trivFib_WD hC hD hfib adj hQ hI hQX π hπ_W
  have : IsIso (L₁.map (L.map π)) := Localization.inverts L₁ WD _ hπ_WD
  have hfac_assoc : ∀ {Z : C} (k : QX ⟶ Z), j ≫ π ≫ k = nabla ≫ k :=
    fun k ↦ by rw [← Category.assoc, hfac]
  have hj0_assoc : ∀ {Z : C} (k : QX ⟶ Z), i0 ≫ j ≫ π ≫ k = k :=
    fun k ↦ by rw [hfac_assoc, pushout.inl_desc_assoc, Category.id_comp]
  have hj1_assoc : ∀ {Z : C} (k : QX ⟶ Z), i1 ≫ j ≫ π ≫ k = k :=
    fun k ↦ by rw [hfac_assoc, pushout.inr_desc_assoc, Category.id_comp]
  have hj0_π : (i0 ≫ j) ≫ π = 𝟙 QX := by
    rw [Category.assoc, hfac, pushout.inl_desc]
  have hj1_π : (i1 ≫ j) ≫ π = 𝟙 QX := by
    rw [Category.assoc, hfac, pushout.inr_desc]
  have h0 : L₁.map (L.map (i0 ≫ j)) ≫ L₁.map (L.map π) = 𝟙 _ := by
    rw [← L₁.map_comp, ← L.map_comp, hj0_π, L.map_id, L₁.map_id]
  have h1 : L₁.map (L.map (i1 ≫ j)) ≫ L₁.map (L.map π) = 𝟙 _ := by
    rw [← L₁.map_comp, ← L.map_comp, hj1_π, L.map_id, L₁.map_id]
  have h_eq_L1 : L₁.map (L.map (i0 ≫ j)) = L₁.map (L.map (i1 ≫ j)) := by
    apply (cancel_mono (L₁.map (L.map π))).1
    rw [h0, h1]
  let g : P ⟶ QY :=
    pushout.desc g₁ g₂ (by apply initial.hom_ext)
  have h_sq : CommSq g j pY (π ≫ g₁ ≫ pY) := ⟨by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, hj0_assoc]
    · rw [pushout.inr_desc_assoc, hj1_assoc, ← h]⟩
  have hpY_triv : (fibC ⊓ WC) pY := ⟨(makeCofRepl hC Y).hp_fib, (makeCofRepl hC Y).hp_W⟩
  have h_lift_prop : HasLiftingProperty j pY := hC.lift_cof_trivFib pY hpY_triv j hj
  have : HasLiftingProperty j pY := h_lift_prop
  let H : I ⟶ QY := CommSq.lift h_sq
  have hH : j ≫ H = g := CommSq.fac_left h_sq
  have hg1 : g₁ = (i0 ≫ j) ≫ H := by
    rw [Category.assoc, hH, pushout.inl_desc]
  have hg2 : g₂ = (i1 ≫ j) ≫ H := by
    rw [Category.assoc, hH, pushout.inr_desc]
  have h_comp (i : QX ⟶ P) : L₁.map (L.map ((i ≫ j) ≫ H)) = L₁.map (L.map (i ≫ j)) ≫ L₁.map (L.map H) := by
    rw [L.map_comp, L₁.map_comp]
  rw [hg1, hg2, h_comp, h_comp, h_eq_L1]

end HomotopyHypothesis.Localization.Quillen
