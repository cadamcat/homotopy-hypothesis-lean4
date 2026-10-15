import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Dimension bounds for relative derived subdivision

Each entry of an admissible tuple contributes a new original vertex to
its least carrier. The tuple dimension is therefore at most its carrier
dimension, and relative derived subdivision preserves any dimension bound.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The dimension of a derived simplex is bounded by its least original carrier. -/
theorem relativeDerived_dim_le_carrier {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    n ≤ (leastRelativeCarrier hK a).1 := by
  classical
  let s := leastRelativeCarrier hK a
  have hv (i : Fin (n + 1)) : ∃ k : Fin (s.1 + 1),
      vertex s.2 k ∈ Set.range (vertex (a.val i).sourceSimplex.2) ∧
        ∀ j, j < i → vertex s.2 k ∉ Set.range (vertex (a.val j).sourceSimplex.2) := by
    obtain ⟨w, hw, hprev⟩ := relativeTuple_new_source_vertices hK a i
    obtain ⟨k, hk⟩ := source_vertex_range_subset_of_carried s.2 (a.val i)
      ((leastRelativeCarrier_spec hK a).1 i) hw
    exact ⟨k, hk ▸ hw, fun j hj => hk ▸ hprev j hj⟩
  choose k hk hprev using hv
  have hinj : Function.Injective k := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hw := hk i
      rw [hij] at hw
      exact hprev j i h hw
    · have hw := hk j
      rw [← hij] at hw
      exact hprev i j h hw
  have hc := Fintype.card_le_of_injective k hinj
  simp only [Fintype.card_fin] at hc
  exact Nat.le_of_succ_le_succ hc

/-- Relative derived subdivision preserves a fixed dimension bound. -/
theorem relativeDerived_dimensionBound {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n)))) :
    ∀ n, D < n → IsEmpty ((relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) := by
  intro n hn
  refine ⟨fun a => ?_⟩
  haveI := hD (leastRelativeCarrier hK a).1
    (lt_of_lt_of_le hn (relativeDerived_dim_le_carrier hK a))
  exact isEmptyElim (leastRelativeCarrier hK a).2

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerived_dim_le_carrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerived_dimensionBound
