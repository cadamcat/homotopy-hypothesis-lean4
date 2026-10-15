import HomotopyHypothesis.Blueprint.Henry.SemiModel
open CategoryTheory Limits HomotopyHypothesis.Henry MorphismProperty

namespace HomotopyHypothesis.Localization.Quillen

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {cofC fibC WC : MorphismProperty C} {cofD fibD WD : MorphismProperty D}

lemma isCofibrantFor_of_initial (hC : IsSemiModelCategory C cofC fibC WC) [HasInitial C]
    {Z : C} (i : ⊥_ C ⟶ Z) (hi : cofC i) : IsCofibrantFor cofC Z := by
  have : cofC.IsStableUnderRetracts := hC.cof_retracts
  intro I' hI'
  have e := hI'.uniqueUpToIso initialIsInitial
  have h_eq : hI'.to Z = e.hom ≫ i := by
    apply hI'.hom_ext
  rw [h_eq]
  exact RespectsIso.precomp cofC e.hom i hi

theorem right_adjoint_preserves_weakEquivalences
    (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD)
    (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD) :
    WD ≤ WC.inverseImage R := by
  intro Y₁ Y₂ f hf
  have : HasFiniteColimits C := hC.hasFiniteColimits
  have : HasInitial C := inferInstance
  obtain ⟨X, i, p, hi, hp_fib, hp_W, -⟩ := hC.factor_cof_trivFib (initial.to (R.obj Y₁))
  have hX : IsCofibrantFor cofC X := isCofibrantFor_of_initial hC i hi
  let ε' : L.obj X ⟶ Y₁ := (adj.homEquiv X Y₁).symm p
  have h_adj_ε' : adj.homEquiv X Y₁ ε' = p := (adj.homEquiv X Y₁).apply_symm_apply p
  have hε'_W : WD ε' := by
    rw [hQ.weakEquivalence_iff ε' hX (hfib Y₁)]
    rw [h_adj_ε']
    exact hp_W
  have hcomp : WD (ε' ≫ f) := by
    have : WD.HasTwoOutOfThreeProperty := hD.twoOutOfThree
    exact WD.comp_mem _ _ hε'_W hf
  have h_adj_comp_W : WC (adj.homEquiv X Y₂ (ε' ≫ f)) := by
    rw [← hQ.weakEquivalence_iff (ε' ≫ f) hX (hfib Y₂)]
    exact hcomp
  have h_adj_eq : adj.homEquiv X Y₂ (ε' ≫ f) = p ≫ R.map f := by
    rw [Adjunction.homEquiv_naturality_right]
    rw [h_adj_ε']
  rw [h_adj_eq] at h_adj_comp_W
  have : WC.HasTwoOutOfThreeProperty := hC.twoOutOfThree
  exact WC.of_precomp p (R.map f) hp_W h_adj_comp_W

end HomotopyHypothesis.Localization.Quillen
