import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsRelPrismSimplicialApproximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.KanExistsOfRelPrism
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.StdSimplexIsFinite
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial

/-!
# `HomotopyHypothesis.Blueprint.Henry.KanSimplices`, part 2

Lines 24–44 of `HomotopyHypothesis.Blueprint.Henry.KanSimplices`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits

namespace HomotopyHypothesis.Henry

/-- **Relative simplices in Kan semi-simplicial sets** (Rourke–Sanderson, *Δ-sets I*, Thm. 5.3,
finite cases 1–2, pp. 329–330). Let `X` be a semi-simplicial set satisfying the Kan condition and
`a : ∂Δ_n ⟶ X`. Every map `f : ‖Δ_n‖ ⟶ ‖X‖` extending `‖a‖` is homotopic relative to `‖∂Δ_n‖` to
the realization of an `n`-simplex `x` of `X` with boundary exactly `a`. This replaces the
Kan–Quillen comparison in H Lemma 5.2.7 (H:2914–2934). Proved from
`exists_relPrism_simplicialApproximation` (RS Thm. 5.1) and `kan_exists_of_relPrism`
(RS Thm. 5.3 for a given approximation). -/
theorem Packages.isKan_exists_simplex_homotopicRel (X : SemiSSet.{u}) (hX : X.IsKan) (n : ℕ)
    (a : (SemiSSet.boundary.{u} n).toFunctor ⟶ X)
    (f : SemiSSet.realization.obj (SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n)) ⟶
      SemiSSet.realization.obj X)
    (hf : SemiSSet.realization.map (SemiSSet.boundary n).ι ≫ f = SemiSSet.realization.map a) :
    ∃ x : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ X,
      (SemiSSet.boundary n).ι ≫ x = a ∧
        (SemiSSet.realization.map x).hom.HomotopicRel f.hom
          (Set.range (SemiSSet.realization.map (SemiSSet.boundary.{u} n).ι).hom) := by
  obtain ⟨S, f', hsimp, hjf', hf'⟩ := Packages.exists_relPrism_simplicialApproximation
    (Packages.stdSimplex_isFinite n) (SemiSSet.boundary n) a f hf
  obtain ⟨φ, hφ, hφh⟩ := Packages.kan_exists_of_relPrism hX (SemiSSet.boundary n) a S f' hsimp hjf'
  exact ⟨φ, hφ, hφh.trans hf'⟩
