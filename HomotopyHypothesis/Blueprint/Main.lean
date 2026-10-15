import HomotopyHypothesis.Blueprint.Bridge.StatementOfOaiStatement
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.AfinEssentiallySmall
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCoherator
import HomotopyHypothesis.Blueprint.Interfaces.CellularRealization
import HomotopyHypothesis.Blueprint.Interfaces.CompletionIsEquivalence
import HomotopyHypothesis.Blueprint.Interfaces.CompletionWeakEquivalencesIff
import HomotopyHypothesis.Blueprint.Interfaces.CompletionWeakEquivalencesRespectsIso
import HomotopyHypothesis.Blueprint.Interfaces.CompressionCriterion
import HomotopyHypothesis.Blueprint.Interfaces.ContractibleDisk0
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Blueprint.Interfaces.ExistsRealization
import HomotopyHypothesis.Blueprint.Interfaces.HenryComparison
import HomotopyHypothesis.Blueprint.Interfaces.PiComparison
import HomotopyHypothesis.Blueprint.Interfaces.PiIsRightAdjoint
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Blueprint.Interfaces.TopRestrictionIso
import HomotopyHypothesis.Challenge
/-!
# Assembly of the homotopy hypothesis from the packages

`HomotopyHypothesis.Blueprint.main : Statement` from the packages of `Blueprint/Interfaces.lean`.

For a coherator `C` and a realization `R`:
1. `Π_R` sends weak homotopy equivalences to weak equivalences (`pi_comparison`);
2. `A_fin` is a cylinder coherator (`afin_isCylinderCoherator`), the restriction of the
   realization `|−|_R` to `A_fin` is a cellular realization with `|D₀|` contractible, and Henry's
   `π_∞` for it is `Π_R` followed by the equivalence `C.Model ≌ Completion (A_fin)` that matches
   the weak equivalences;
3. Henry's comparison theorem then makes the functor induced by `Π_R` on localizations an
   equivalence, which is the localization property of `Π_R ⋙ Q`.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Henry

/-- The localization of `C.Model` at the weak equivalences, transported to the completion of
`A_fin` along the restriction equivalence. -/
theorem isLocalization_completion {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    [(Packages.restriction hC).IsEquivalence] :
    ((Packages.restriction hC).inv ⋙ (W hC).Q).IsLocalization
      (Completion.weakEquivalences (Afin C hC)) := by
  let E := (Packages.restriction hC).asEquivalence
  have := Packages.completion_weakEquivalences_respectsIso hC
  refine Functor.IsLocalization.of_equivalence_source (W hC).Q (W hC)
    (E.inverse ⋙ (W hC).Q) _ E ?_ ?_ ?_
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _
      ((Packages.completion_weakEquivalences_iff hC f).2 hf)
  · intro P P' g hg
    apply Localization.inverts (W hC).Q (W hC)
    rw [← Packages.completion_weakEquivalences_iff hC]
    exact ((Completion.weakEquivalences (Afin C hC)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso E.counitIso (Arrow.mk g))).2 hg
  · exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm _ ≪≫
      Functor.leftUnitor _

/-- The statement on OpenAI's definitions. -/
theorem oaiStatement : OAIStatement.{u} := by
  intro C hC
  refine ⟨Packages.exists_realization C hC, fun R => ?_⟩
  have h1 : weakHomotopyEquivalences ≤ (W hC).inverseImage R.Pi :=
    fun _ _ f hf => (Packages.pi_comparison hC R f).2 hf
  refine ⟨h1, ?_⟩
  obtain ⟨L, ⟨adj⟩⟩ := (Packages.pi_isRightAdjoint R).exists_leftAdjoint
  have hG := Packages.cellularRealization hC R L adj
  have ho := Packages.contractible_disk0 hC R L adj
  have := Packages.afin_essentiallySmall hC
  have := Packages.completion_isEquivalence hC
  have := isLocalization_completion hC
  obtain ⟨e⟩ := Packages.topRestriction_iso hC R L adj
  let E := (Packages.restriction hC).asEquivalence
  have hcomp := Packages.compression_criterion.{u}
  have hinv : (Henry.Top.weakEquivalences.{u}).IsInvertedBy (R.Pi ⋙ (W hC).Q) := by
    intro X Y f hf
    rw [hcomp] at hf
    exact Localization.inverts (W hC).Q (W hC) _ (h1 f hf)
  let Φ := Localization.lift (R.Pi ⋙ (W hC).Q) hinv (Henry.Top.weakEquivalences.{u}).Q
  have hfac : (Henry.Top.weakEquivalences.{u}).Q ⋙ Φ ≅ R.Pi ⋙ (W hC).Q :=
    Localization.fac _ _ _
  have isoQ : E.functor ⋙ (Packages.restriction hC).inv ⋙ (W hC).Q ≅ (W hC).Q :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm _ ≪≫
      Functor.leftUnitor _
  have iso3 : topRestriction hG ⋙ ((Packages.restriction hC).inv ⋙ (W hC).Q) ≅ R.Pi ⋙ (W hC).Q :=
    Functor.isoWhiskerRight e _ ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R.Pi isoQ
  have hΦ : Φ.IsEquivalence :=
    (Packages.henry_comparison (Packages.disk0 hC) (Packages.afin_isCylinderCoherator hC) _ hG
      ho).2 (Henry.Top.weakEquivalences.{u}).Q ((Packages.restriction hC).inv ⋙ (W hC).Q) Φ (hfac ≪≫ iso3.symm)
  have hloc : (R.Pi ⋙ (W hC).Q).IsLocalization Henry.Top.weakEquivalences.{u} :=
    Functor.IsLocalization.of_equivalence_target _ _ _ Φ.asEquivalence hfac
  exact hcomp ▸ hloc

/-- **The Grothendieck homotopy hypothesis for coherators**, from the packages. -/
theorem main : Statement.{u} :=
  Packages.statement_of_oaiStatement oaiStatement

end HomotopyHypothesis.Blueprint
