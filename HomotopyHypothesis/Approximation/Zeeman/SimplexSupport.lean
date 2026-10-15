import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Simplex representatives with nonzero weights

Factoring a barycentric point through its ordered nonzero-weight support
gives a representative in which every vertex has nonzero weight.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A barycentric point factors through a face with nonzero weights everywhere. -/
theorem exists_nonzero_face {n : ℕ} (t : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
      (p : StdSimplex ℝ (Fin (m + 1))),
      StdSimplex.map θ.hom.toOrderHom p = t ∧ ∀ i, p.weights i ≠ 0 := by
  classical
  let s := t.weights.support
  have hpos : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
  have hcard : s.card = (s.card - 1) + 1 := by omega
  let e := s.orderEmbOfFin hcard
  have he : Set.range e = (s : Set (Fin (n + 1))) := Finset.range_orderEmbOfFin s hcard
  obtain ⟨p, hp⟩ := (StdSimplex.mem_range_map_iff e t).mpr (by
    intro i hi
    by_contra hne
    apply hi
    rw [he]
    exact Finsupp.mem_support_iff.mpr hne)
  let θ : Henry.SemiSimplexCategory.mk (s.card - 1) ⟶ Henry.SemiSimplexCategory.mk n :=
    ⟨SimplexCategory.Hom.mk e.toOrderHom, by
      change Mono (show SimplexCategory.mk (s.card - 1) ⟶ SimplexCategory.mk n from
        SimplexCategory.Hom.mk e.toOrderHom)
      rw [SimplexCategory.mono_iff_injective]
      exact e.injective⟩
  refine ⟨s.card - 1, θ, p, hp, ?_⟩
  intro i hi
  have hmem : e i ∈ s := s.orderEmbOfFin_mem hcard i
  have hne := Finsupp.mem_support_iff.mp hmem
  apply hne
  rw [← hp, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective e.injective, hi]

/-- Every realization point has a simplex representative with no zero weights. -/
theorem exists_simplexChar_nonzero_rep {K : SemiSSet.{u}} (z : realization.obj K) :
    ∃ (n : ℕ) (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
      (p : StdSimplex ℝ (Fin (n + 1))), (∀ i, p.weights i ≠ 0) ∧
      (simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p) = z := by
  obtain ⟨n, y, t, ht⟩ := exists_simplexChar_rep z
  obtain ⟨m, θ, p, hp, hnonzero⟩ :=
    exists_nonzero_face (show StdSimplex ℝ (Fin (n + 1)) from t.down)
  refine ⟨m, K.map θ.op (uliftYonedaEquiv y), p, hnonzero, ?_⟩
  rw [uliftYonedaEquiv_symm_map, Equiv.symm_apply_apply, simplexChar_naturality]
  change (simplexChar y).hom (ULift.up (StdSimplex.map θ.hom.toOrderHom p)) = z
  exact (congrArg (fun r : StdSimplex ℝ (Fin (n + 1)) =>
    (simplexChar y).hom (ULift.up r)) hp).trans ht

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_nonzero_face
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_simplexChar_nonzero_rep
