import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Zeeman

/-!
# `zeeman_relativeApproximation`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Zeeman's relative simplicial approximation theorem** (Zeeman 1964, main theorem, for finite
simplicial complexes; the subdivision is the iterated barycentric derived `K_r` of `K` modulo `L`,
the prism of `RelSubdivision` is its derived cylinder, Rourke–Sanderson Lemma 4.3). Let `K`, `M`
be finite semi-simplicial sets that are ordered simplicial complexes, `L ⊆ K`, and
`f : ‖K‖ ⟶ ‖M‖` simplicial on `‖L‖`. Then, after subdividing `K` away from `L`, there is a
simplicial map `g` agreeing with `f` on `L` and homotopic to `f` relative to `‖L‖`. Simplicial is
meant coherently (`IsSimplicial`): the global vertex map of the simplicial approximation gives the
map `K_r ⟶ M♯`, each simplex going to its image simplex with the induced vertex map. -/
theorem zeeman_relativeApproximation {K M : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (hM : M.IsFinite) (hMs : M.IsSimplicialComplex)
    (L : Subfunctor K) (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    ∃ (S : RelSubdivision K L) (g : realization.obj S.Y' ⟶ realization.obj M),
      IsSimplicial g ∧ realization.map S.j ≫ g = realization.map L.ι ≫ f ∧
        g.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) := by apply @_root_.HomotopyHypothesis.Henry.Packages.zeeman_relativeApproximation_proof <;> assumption
