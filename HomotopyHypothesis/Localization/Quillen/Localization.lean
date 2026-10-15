import Mathlib.CategoryTheory.Localization.Predicate
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.Quillen.KenBrown
import HomotopyHypothesis.Localization.Quillen.LiftUniq
open CategoryTheory Limits HomotopyHypothesis.Henry MorphismProperty

namespace HomotopyHypothesis.Localization.Quillen

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {cofC fibC WC : MorphismProperty C} {cofD fibD WD : MorphismProperty D}

theorem cofReplLiftSq [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    {X Y : C} (f : X ⟶ Y) :
    CommSq (initial.to (makeCofRepl hC Y).Q) (initial.to (makeCofRepl hC X).Q)
      (makeCofRepl hC Y).p ((makeCofRepl hC X).p ≫ f) :=
  ⟨initial.hom_ext _ _⟩

noncomputable def cofReplLift [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    {X Y : C} (f : X ⟶ Y) :
    (makeCofRepl hC X).Q ⟶ (makeCofRepl hC Y).Q := by
  have hpY_triv : (fibC ⊓ WC) (makeCofRepl hC Y).p :=
    ⟨(makeCofRepl hC Y).hp_fib, (makeCofRepl hC Y).hp_W⟩
  have : HasLiftingProperty (initial.to (makeCofRepl hC X).Q) (makeCofRepl hC Y).p :=
    hC.lift_cof_trivFib _ hpY_triv _ (cofRepl_isCof hC X initialIsInitial)
  exact CommSq.lift (cofReplLiftSq hC f)

lemma cofReplLift_fac [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    {X Y : C} (f : X ⟶ Y) :
    cofReplLift hC f ≫ (makeCofRepl hC Y).p = (makeCofRepl hC X).p ≫ f := by
  have hpY_triv : (fibC ⊓ WC) (makeCofRepl hC Y).p :=
    ⟨(makeCofRepl hC Y).hp_fib, (makeCofRepl hC Y).hp_W⟩
  have : HasLiftingProperty (initial.to (makeCofRepl hC X).Q) (makeCofRepl hC Y).p :=
    hC.lift_cof_trivFib _ hpY_triv _ (cofRepl_isCof hC X initialIsInitial)
  exact CommSq.fac_right (cofReplLiftSq hC f)

noncomputable def functorF [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} [Category.{v₃} H₁]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD] : C ⥤ H₁ where
  obj X := L₁.obj (L.obj (makeCofRepl hC X).Q)
  map f := L₁.map (L.map (cofReplLift hC f))
  map_id X := by
    have h1 : cofReplLift hC (𝟙 X) ≫ (makeCofRepl hC X).p = 𝟙 _ ≫ (makeCofRepl hC X).p := by
      rw [cofReplLift_fac, Category.comp_id, Category.id_comp]
    have h_eq := lift_uniq hC hD hfib adj hQ L₁ (cofReplLift hC (𝟙 X)) (𝟙 _) h1
    rw [h_eq, L.map_id, L₁.map_id]
  map_comp {X Y Z} f g := by
    have h1 : cofReplLift hC (f ≫ g) ≫ (makeCofRepl hC Z).p =
        (cofReplLift hC f ≫ cofReplLift hC g) ≫ (makeCofRepl hC Z).p := by
      rw [cofReplLift_fac, Category.assoc, cofReplLift_fac]
      have : cofReplLift hC f ≫ (makeCofRepl hC Y).p ≫ g = ((makeCofRepl hC X).p ≫ f) ≫ g := by
        rw [← Category.assoc, cofReplLift_fac]
      rw [this, Category.assoc]
    have h_eq := lift_uniq hC hD hfib adj hQ L₁ (cofReplLift hC (f ≫ g))
      (cofReplLift hC f ≫ cofReplLift hC g) h1
    rw [h_eq, L.map_comp, L₁.map_comp]

lemma functorF_inverts [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} [Category.{v₃} H₁]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD] :
    WC.IsInvertedBy (functorF hC hD hfib adj hQ L₁) := by
  intro X Y f hf
  have : WC.HasTwoOutOfThreeProperty := hC.twoOutOfThree
  have h_comp_W : WC ((makeCofRepl hC X).p ≫ f) :=
    WC.comp_mem _ _ (makeCofRepl hC X).hp_W hf
  have h_lift_comp : WC (cofReplLift hC f ≫ (makeCofRepl hC Y).p) := by
    rw [cofReplLift_fac]
    exact h_comp_W
  have h_lift_W : WC (cofReplLift hC f) :=
    WC.of_postcomp (cofReplLift hC f) (makeCofRepl hC Y).p (makeCofRepl hC Y).hp_W h_lift_comp
  have h_WD : WD (L.map (cofReplLift hC f)) :=
    L_map_trivFib_WD hC hD hfib adj hQ
      (cofRepl_isCof hC X) (cofRepl_isCof hC Y) _ h_lift_W
  exact Localization.inverts L₁ WD _ h_WD

lemma eps_prime_WD [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    (Y : D) :
    WD (L.map (makeCofRepl hC (R.obj Y)).p ≫ adj.counit.app Y) := by
  have h_fib_Y : IsFibrantFor fibD Y := hfib Y
  have h_cof_Q : IsCofibrantFor cofC (makeCofRepl hC (R.obj Y)).Q := cofRepl_isCof hC (R.obj Y)
  rw [hQ.weakEquivalence_iff _ h_cof_Q h_fib_Y]
  rw [adj.homEquiv_naturality_left]
  have h_counit : adj.homEquiv (R.obj Y) Y (adj.counit.app Y) = 𝟙 (R.obj Y) := by
    apply (adj.homEquiv (R.obj Y) Y).symm.injective
    rw [Equiv.symm_apply_apply, adj.homEquiv_counit, L.map_id, Category.id_comp]
  rw [h_counit, Category.comp_id]
  exact (makeCofRepl hC (R.obj Y)).hp_W

noncomputable def gamma [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} [Category.{v₃} H₁]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD] :
    R ⋙ functorF hC hD hfib adj hQ L₁ ≅ L₁ := by
  have h_iso (Y : D) : IsIso (L₁.map (L.map (makeCofRepl hC (R.obj Y)).p ≫ adj.counit.app Y)) :=
    Localization.inverts L₁ WD _ (eps_prime_WD hC hfib adj hQ Y)
  refine NatIso.ofComponents (fun Y ↦
    @asIso _ _ _ _ (L₁.map (L.map (makeCofRepl hC (R.obj Y)).p ≫ adj.counit.app Y)) (h_iso Y)) ?_
  intro Y Y' k
  dsimp [functorF]
  rw [← L₁.map_comp, ← L₁.map_comp]
  congr 1
  rw [← Category.assoc (L.map (cofReplLift hC (R.map k))) (L.map (makeCofRepl hC (R.obj Y')).p)]
  rw [← L.map_comp, cofReplLift_fac, L.map_comp, Category.assoc]
  have h_counit_nat : L.map (R.map k) ≫ adj.counit.app Y' = adj.counit.app Y ≫ k := by
    have := adj.counit.naturality k
    dsimp at this
    exact this
  rw [h_counit_nat, Category.assoc]

lemma unit_app_WC [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    (X : C) :
    WC (adj.unit.app (makeCofRepl hC X).Q) := by
  have h_fib : IsFibrantFor fibD (L.obj (makeCofRepl hC X).Q) := hfib _
  have h_id_WD : WD (𝟙 (L.obj (makeCofRepl hC X).Q)) := WD_id hD _
  have h_rw := (hQ.weakEquivalence_iff (𝟙 _) (cofRepl_isCof hC X) h_fib).mp h_id_WD
  rwa [adj.homEquiv_id] at h_rw

noncomputable def delta [HasInitial C]
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} [Category.{v₃} H₁]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD]
    {H₂ : Type u₄} [Category.{v₄} H₂]
    (L₂ : C ⥤ H₂) [L₂.IsLocalization WC]
    (Φ : H₁ ⥤ H₂) (hyp : L₁ ⋙ Φ ≅ R ⋙ L₂) :
    functorF hC hD hfib adj hQ L₁ ⋙ Φ ≅ L₂ := by
  have h_unit_iso (X : C) : IsIso (L₂.map (adj.unit.app (makeCofRepl hC X).Q)) :=
    Localization.inverts L₂ WC _ (unit_app_WC hC hD hfib adj hQ X)
  have h_p_iso (X : C) : IsIso (L₂.map (makeCofRepl hC X).p) :=
    Localization.inverts L₂ WC _ (makeCofRepl hC X).hp_W
  refine NatIso.ofComponents (fun X ↦
    hyp.app (L.obj (makeCofRepl hC X).Q) ≪≫
    (@asIso _ _ _ _ (L₂.map (adj.unit.app (makeCofRepl hC X).Q)) (h_unit_iso X)).symm ≪≫
    @asIso _ _ _ _ (L₂.map (makeCofRepl hC X).p) (h_p_iso X)) ?_
  intro X Y f
  have : IsIso (L₂.map (adj.unit.app (makeCofRepl hC X).Q)) := h_unit_iso X
  have : IsIso (L₂.map (adj.unit.app (makeCofRepl hC Y).Q)) := h_unit_iso Y
  dsimp [functorF]
  let g := cofReplLift hC f
  have h_nat_hyp := hyp.hom.naturality (L.map g)
  dsimp at h_nat_hyp
  rw [Category.assoc, Category.assoc]
  rw [← Category.assoc (Φ.map (L₁.map (L.map g))) (hyp.hom.app (L.obj (makeCofRepl hC Y).Q))]
  rw [h_nat_hyp]
  rw [Category.assoc]
  congr 1
  rw [← cancel_epi (L₂.map (adj.unit.app (makeCofRepl hC X).Q))]
  rw [IsIso.hom_inv_id_assoc]
  have h_unit_nat : adj.unit.app (makeCofRepl hC X).Q ≫ R.map (L.map g) = g ≫ adj.unit.app (makeCofRepl hC Y).Q := by
    have := (adj.unit.naturality g).symm
    dsimp at this
    exact this
  rw [← Category.assoc (L₂.map (adj.unit.app (makeCofRepl hC X).Q)), ← L₂.map_comp, h_unit_nat, L₂.map_comp, Category.assoc]
  rw [IsIso.hom_inv_id_assoc]
  rw [← L₂.map_comp, cofReplLift_fac, L₂.map_comp]

lemma equivalence_of_quillen_equivalence
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD)
    {H₁ : Type u₃} {H₂ : Type u₄} [Category.{v₃} H₁] [Category.{v₄} H₂]
    (L₁ : D ⥤ H₁) [L₁.IsLocalization WD]
    (L₂ : C ⥤ H₂) [L₂.IsLocalization WC]
    (Φ : H₁ ⥤ H₂) (hyp : L₁ ⋙ Φ ≅ R ⋙ L₂) :
    Φ.IsEquivalence := by
  have : HasFiniteColimits C := hC.hasFiniteColimits
  have : HasInitial C := inferInstance
  let F := functorF hC hD hfib adj hQ L₁
  have hF := functorF_inverts hC hD hfib adj hQ L₁
  let γ := gamma hC hD hfib adj hQ L₁
  let δ := delta hC hD hfib adj hQ L₁ L₂ Φ hyp
  have : Localization.Lifting L₁ WD (R ⋙ L₂) Φ := ⟨hyp⟩
  let α : (R ⋙ L₂) ⋙ Localization.lift F hF L₂ ≅ L₁ :=
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R (Localization.fac F hF L₂) ≪≫
    γ
  exact Localization.isEquivalence L₁ WD L₂ WC (R ⋙ L₂) Φ F (Localization.lift F hF L₂) α δ

theorem localization_of_isQuillenEquivalence_proof
    {cofC fibC WC : MorphismProperty C}
    {cofD fibD WD : MorphismProperty D}
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD) :
    WD ≤ WC.inverseImage R ∧
    ∀ {H₁ : Type u₃} {H₂ : Type u₄} [Category.{v₃} H₁] [Category.{v₄} H₂] (L₁ : D ⥤ H₁)
      [L₁.IsLocalization WD] (L₂ : C ⥤ H₂) [L₂.IsLocalization WC] (Φ : H₁ ⥤ H₂),
      (L₁ ⋙ Φ ≅ R ⋙ L₂) → Φ.IsEquivalence :=
  ⟨right_adjoint_preserves_weakEquivalences hC hD hfib adj hQ,
   fun L₁ _ L₂ _ Φ hyp ↦ equivalence_of_quillen_equivalence hC hD hfib adj hQ L₁ L₂ Φ hyp⟩

end HomotopyHypothesis.Localization.Quillen

#print axioms HomotopyHypothesis.Localization.Quillen.localization_of_isQuillenEquivalence_proof
