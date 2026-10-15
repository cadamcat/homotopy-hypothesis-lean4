import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# The relative homotopy for the collar vertex map

The geometric subdivision map and the collar vertex map have a common
original carrier on every derived simplex. A straight-line carrier homotopy
therefore joins them while fixing the retained realization.
-/

universe u v w

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Precompose a relative homotopy by a map carrying the new fixed set into the old one. -/
theorem homotopicRel_precomp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f g : C(Y, Z)} {A : Set Y} (h : f.HomotopicRel g A)
    (p : C(X, Y)) (B : Set X) (hp : Set.MapsTo p B A) :
    (f.comp p).HomotopicRel (g.comp p) B := by
  obtain ⟨H⟩ := h
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap p, prop' := ?_ }⟩
  intro t x hx
  exact H.eq_fst t (hp hx)

/-- A carrier homotopy joins the subdivision map to the collar map relative to L. -/
theorem relativeCollarMap_homotopicRel {K : SemiSSet.{u}}
    (hH : CarrierHomotopyStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (relativeRealizationMap hKs L).hom.HomotopicRel (relativeCollarMap hKs L).hom
      (Set.range (realization.map (relativeDerivedInclusion hKs L)).hom) := by
  apply hH hK hKs
  · rintro z ⟨a, rfl⟩
    exact (congrArg (fun e => e.hom a) (relativeRealizationMap_retained hKs L)).trans
      (congrArg (fun e => e.hom a) (relativeCollarMap_retained hKs L)).symm
  · intro n y
    let a := uliftYonedaEquiv y
    refine ⟨(leastRelativeCarrier hKs a).1,
      uliftYonedaEquiv.symm (leastRelativeCarrier hKs a).2,
      relativeLocalTopMap hKs a,
      relativeCollarTopMapInCarrier a (leastRelativeCarrier hKs a)
        (leastRelativeCarrier_spec hKs a).1, ?_, ?_⟩
    · simpa only [a, Equiv.symm_apply_apply] using relativeRealizationMap_simplex hKs a
    · simpa only [a, Equiv.symm_apply_apply, relativeCollarSimplexMap] using
        relativeCollarMap_simplex hKs a

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.homotopicRel_precomp
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_homotopicRel
