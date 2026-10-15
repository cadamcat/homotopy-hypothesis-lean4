import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelStructure.Filtered
import HomotopyHypothesis.Category.SemiModelStructure.Flat
import HomotopyHypothesis.Category.SemiModelStructure.PushoutColimit
import HomotopyHypothesis.Category.SemiModelStructure.YonedaFacts
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Attaching one cell to a flat object

Let `X` be a flat object of the completion, `c : C ⟶ D` a cofibration and `x : y C ⟶ X`. The
pushout `X ⊔_{y C} y D` is the filtered colimit of the representable objects `y (X_j ⊔_C D)`, where
`X = colim y X_j`; hence it is flat, and when `c` is a trivial cofibration the map
`X ⟶ X ⊔_{y C} y D` is a filtered colimit of the weak equivalences `y X_j ⟶ y (X_j ⊔_C D)`, hence a
weak equivalence (Henry, *Algebraic models of homotopy types*, Lemma 2.4.4 and Prop 2.4.13).
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C] [EssentiallySmall.{w} C]

attribute [local instance] Category.SemiModelConstruction.completion_hasColimits

theorem singleCell_stage {X : Completion.{w} C} {J : Type w} [SmallCategory J]
    (pres : ColimitPresentation J X)
    (hrep : ∀ j, IsRepresentableCompletion (pres.diag.obj j))
    {Cc Dd : C} (c : Cc ⟶ Dd) (hc : cofibrations C c) {j₀ : J}
    (x₀ : completionSmallYoneda.{w}.obj Cc ⟶ pres.diag.obj j₀) (s : Under j₀) :
    IsRepresentableCompletion
        ((underPushoutFunctor pres.diag (completionSmallYoneda.{w}.map c) x₀).obj s) ∧
      (weakEquivalences C c → Completion.weakEquivalences C
        ((underPushoutInl pres.diag (completionSmallYoneda.{w}.map c) x₀).app s)) := by
  obtain ⟨E, ⟨e⟩⟩ := hrep s.right
  let φ : Cc ⟶ E := completionSmallYoneda.{w}.preimage (x₀ ≫ pres.diag.map s.hom ≫ e.hom)
  have hφ : completionSmallYoneda.{w}.map φ = x₀ ≫ pres.diag.map s.hom ≫ e.hom :=
    completionSmallYoneda.{w}.map_preimage _
  have := IsCofibrationCategory.hasPushout c φ hc
  have hC : IsPushout c φ (pushout.inl c φ) (pushout.inr c φ) := IsPushout.of_hasPushout c φ
  have hY := (completionSmallYoneda_isPushout.{w} c φ _ _ hC hc).flip
  have hS : IsPushout (x₀ ≫ pres.diag.map s.hom) (completionSmallYoneda.{w}.map c)
      (pushout.inl _ _) (pushout.inr _ _) := IsPushout.of_hasPushout _ _
  have hS' : IsPushout (completionSmallYoneda.{w}.map φ) (completionSmallYoneda.{w}.map c)
      (e.inv ≫ pushout.inl (x₀ ≫ pres.diag.map s.hom) (completionSmallYoneda.{w}.map c))
      (pushout.inr _ _) := by
    refine IsPushout.of_iso hS (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [hφ]; simp
    · simp
    · simp
    · simp
  let iP := hS'.isoIsPushout _ _ hY
  refine ⟨⟨pushout c φ, ⟨iP⟩⟩, fun hW => ?_⟩
  have hinr : weakEquivalences C (pushout.inr c φ) :=
    IsCylinderCategory.trivialCofibration_cobaseChange c φ _ _ hC hc hW
  have hyW := completionSmallYoneda_weakEquivalence.{w} _ hinr
  have hsq : pushout.inl (x₀ ≫ pres.diag.map s.hom) (completionSmallYoneda.{w}.map c) ≫ iP.hom =
      e.hom ≫ completionSmallYoneda.{w}.map (pushout.inr c φ) := by
    have := hS'.inl_isoIsPushout_hom _ _ hY
    rw [← this]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, iP]
  have := Completion.weakEquivalences_respectsIso.{w} C
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk e iP hsq.symm)).mpr hyW

/-- Attaching one cell `y c` to a flat object gives a flat object, and the inclusion is a weak
equivalence when `c` is a trivial cofibration. -/
theorem singleCell {X : Completion.{w} C} (hX : IsFlat X) {Cc Dd : C} (c : Cc ⟶ Dd)
    (hc : cofibrations C c) (x : completionSmallYoneda.{w}.obj Cc ⟶ X) {X' : Completion.{w} C}
    (u : X ⟶ X') (d : completionSmallYoneda.{w}.obj Dd ⟶ X')
    (h : IsPushout x (completionSmallYoneda.{w}.map c) u d) :
    IsFlat X' ∧ (weakEquivalences C c → Completion.weakEquivalences C u) := by
  obtain ⟨J, _, _, pres, hrep⟩ := hX
  have := completionSmallYoneda_isFinitelyPresentable.{w} (C := C) Cc
  obtain ⟨j₀, x₀, hx₀⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit x
  have h' : IsPushout (x₀ ≫ (Cocone.mk _ pres.ι).ι.app j₀)
      (completionSmallYoneda.{w}.map c) u d := by
    rw [hx₀]; exact h
  have hcol := underPushoutIsColimit pres.isColimit (completionSmallYoneda.{w}.map c) x₀ u d h'
  have hstage := singleCell_stage pres hrep c hc x₀
  refine ⟨⟨Under j₀, inferInstance, inferInstance, ⟨_, _, hcol⟩, fun s => (hstage s).1⟩,
    fun hW => ?_⟩
  exact completion_weakEquivalence_of_isColimit _ (fun s => (hstage s).2 hW)
    (underIsColimit pres.isColimit) hcol u (fun s => (pushout.inl_desc _ _ _).symm)

end HomotopyHypothesis.Category.SemiModelStructure
