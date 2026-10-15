import HomotopyHypothesis.Bridge.Statement.Coherator
import HomotopyHypothesis.Bridge.Statement.Equivalence
import HomotopyHypothesis.Bridge.Statement.Theory
import HomotopyHypothesis.Bridge.Statement.Weak
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
/-!
# The statement from OpenAI's statement

For a coherator `C` of the statement, the transported theory is a coherator of OpenAI's library.
Its realizations give realizations of `C`; the realizations of `C` give realizations of the
transported theory with the same fundamental ∞-groupoid functor up to the restriction
equivalence of models, which preserves and reflects weak equivalences. The localization property
transports along the induced equivalence of localized categories.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory

universe u

theorem localization_modelToOAI {C : Grothendieck.GlobularTheory.{u}} (hC : C.IsCoherator)
    (hC' : (theoryToOAI C).IsCoherator) :
    (modelToOAI C ⋙ (HomotopyHypothesis.Blueprint.W hC').Q).IsLocalization
      (HomotopyHypothesis.modelWeakEquivalences hC) := by
  refine Functor.IsLocalization.of_equivalence_source (HomotopyHypothesis.Blueprint.W hC').Q
    (HomotopyHypothesis.Blueprint.W hC') (modelToOAI C ⋙ (HomotopyHypothesis.Blueprint.W hC').Q)
    (HomotopyHypothesis.modelWeakEquivalences hC) (modelToOAI C).asEquivalence.symm ?_ ?_
    ((Functor.associator (modelToOAI C).asEquivalence.inverse (modelToOAI C)
        (HomotopyHypothesis.Blueprint.W hC').Q).symm ≪≫
      Functor.isoWhiskerRight (modelToOAI C).asEquivalence.counitIso
        (HomotopyHypothesis.Blueprint.W hC').Q ≪≫ Functor.leftUnitor _)
  · intro X Y f hf
    refine MorphismProperty.le_isoClosure _ _ ?_
    change Grothendieck.GlobularTheory.Model.WeakEquivalence hC ((modelToOAI C).inv.map f)
    rw [← weakEquivalence_modelToOAI_iff hC hC']
    let ε := (modelToOAI C).asEquivalence.counitIso
    have h : (modelToOAI C).map ((modelToOAI C).inv.map f) =
        ε.hom.app X ≫ f ≫ ε.inv.app Y := (NatIso.naturality_2 ε f).symm
    rw [h]
    exact oai_weakEquivalence_comp hC' (oai_weakEquivalence_of_iso hC' (ε.app X))
      (oai_weakEquivalence_comp hC' hf (oai_weakEquivalence_of_iso hC' (ε.app Y).symm))
  · intro X Y f hf
    exact Localization.inverts (HomotopyHypothesis.Blueprint.W hC').Q
      (HomotopyHypothesis.Blueprint.W hC') _ ((weakEquivalence_modelToOAI_iff hC hC' f).2 hf)

/-- **Bridge.** The statement follows from the same statement on OpenAI's library
definitions. -/
theorem statement_of_oaiStatement_proof :
    HomotopyHypothesis.Blueprint.OAIStatement.{u} → HomotopyHypothesis.Statement.{u} := by
  intro hOAI C hC
  have hC' := isCoherator_theoryToOAI hC
  obtain ⟨⟨R'⟩, H⟩ := hOAI (theoryToOAI C) hC'
  refine ⟨⟨realizationOfOAI R'⟩, fun R => ?_⟩
  obtain ⟨h1, h2⟩ := H (realizationToOAI R)
  refine ⟨fun X Y f hf => (weakEquivalence_modelToOAI_iff hC hC'
    ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f)).1 (h1 f hf), ?_⟩
  have := localization_modelToOAI hC hC'
  have : ((HomotopyHypothesis.fundamentalGroupoidFunctor R ⋙ modelToOAI C) ⋙
      (HomotopyHypothesis.Blueprint.W hC').Q).IsLocalization
        HomotopyHypothesis.weakHomotopyEquivalences := h2
  let E := Localization.uniq (HomotopyHypothesis.modelWeakEquivalences hC).Q
    (modelToOAI C ⋙ (HomotopyHypothesis.Blueprint.W hC').Q)
    (HomotopyHypothesis.modelWeakEquivalences hC)
  have c : (HomotopyHypothesis.modelWeakEquivalences hC).Q ⋙ E.functor ≅
      modelToOAI C ⋙ (HomotopyHypothesis.Blueprint.W hC').Q :=
    Localization.compUniqFunctor _ _ _
  exact Functor.IsLocalization.of_equivalence_target
    ((HomotopyHypothesis.fundamentalGroupoidFunctor R ⋙ modelToOAI C) ⋙
      (HomotopyHypothesis.Blueprint.W hC').Q)
    HomotopyHypothesis.weakHomotopyEquivalences _ E.symm
    (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (HomotopyHypothesis.fundamentalGroupoidFunctor R) c.symm)
        E.inverse ≪≫
      Functor.isoWhiskerLeft (HomotopyHypothesis.fundamentalGroupoidFunctor R ⋙
        (HomotopyHypothesis.modelWeakEquivalences hC).Q) E.unitIso.symm ≪≫
      Functor.rightUnitor _)

end HomotopyHypothesis.Bridge.Statement

namespace HomotopyHypothesis.Blueprint.Packages

universe u

/-- **Bridge.** The statement follows from the same statement on OpenAI's library
definitions. -/
theorem statement_of_oaiStatement_proof : OAIStatement.{u} → Statement.{u} :=
  Bridge.Statement.statement_of_oaiStatement_proof

end HomotopyHypothesis.Blueprint.Packages
