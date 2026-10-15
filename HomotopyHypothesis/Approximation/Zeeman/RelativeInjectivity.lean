import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ApexWeights
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativePrefixes
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RelativeSupports
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Uniqueness of relative derived representatives

Equal nonzero flag mixtures determine their common original carrier and
exterior apex. Removing that apex reduces the flag dimension. Induction
identifies the whole flag, and local affine injectivity identifies its
weights. Consequently the relative realization map is globally injective.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The affine original distribution of a fixed relative derived simplex is injective. -/
theorem relativeDistributionAffineMap_injective {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Function.Injective (relativeDistributionAffineMap a) := by
  apply affineMapMk_injective_of_triangular
  intro i
  obtain ⟨w, hw, hprev⟩ := relativeTuple_new_source_vertices hK a i
  refine ⟨w, (relativeVertexDistribution_weights_ne_zero_iff hK (a.val i) w).mpr hw, ?_⟩
  intro j hj
  by_contra hn
  exact hprev j hj ((relativeVertexDistribution_weights_ne_zero_iff hK (a.val j) w).mp hn)

/-- Equal original distributions of nonzero relative representatives identify their flags. -/
theorem relativeTuple_eq_of_distribution_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (t : StdSimplex ℝ (Fin (n + 1))) (p : StdSimplex ℝ (Fin (m + 1)))
    (ht : ∀ i, t.weights i ≠ 0) (hp : ∀ i, p.weights i ≠ 0)
    (h : relativeDistributionAffineMap a t = relativeDistributionAffineMap b p) :
    n = m ∧ HEq a b := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    have hcarrier := leastRelativeCarrier_eq_of_distribution_eq hK a b t p ht hp h
    cases ha : a.val (Fin.last n) with
    | inl v =>
      obtain ⟨x, hx⟩ := relativeTuple_retained_of_last hK a v ha
      have hca : leastRelativeCarrier hK a = ⟨n, x.val⟩ := by
        rw [hx, leastRelativeCarrier_retained]
      cases hb : b.val (Fin.last m) with
      | inl w =>
        obtain ⟨y, hy⟩ := relativeTuple_retained_of_last hK b w hb
        have hcb : leastRelativeCarrier hK b = ⟨m, y.val⟩ := by
          rw [hy, leastRelativeCarrier_retained]
        rw [hca, hcb] at hcarrier
        have hdim : n = m := congrArg Sigma.fst hcarrier
        subst m
        have hxy : x = y :=
          Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp hcarrier).2)
        subst y
        exact ⟨rfl, heq_of_eq (hx.trans hy.symm)⟩
      | inr s =>
        rw [hca, leastRelativeCarrier_eq_of_last_exterior hK b s hb] at hcarrier
        have hxL : (⟨n, x.val⟩ : Simplex K).2 ∈
            L.obj (op (Henry.SemiSimplexCategory.mk (⟨n, x.val⟩ : Simplex K).1)) := x.property
        exact (s.property (hcarrier ▸ hxL)).elim
    | inr s =>
      have hca := leastRelativeCarrier_eq_of_last_exterior hK a s ha
      cases hb : b.val (Fin.last m) with
      | inl w =>
        obtain ⟨y, hy⟩ := relativeTuple_retained_of_last hK b w hb
        have hcb : leastRelativeCarrier hK b = ⟨m, y.val⟩ := by
          rw [hy, leastRelativeCarrier_retained]
        rw [hca, hcb] at hcarrier
        have hyL : (⟨m, y.val⟩ : Simplex K).2 ∈
            L.obj (op (Henry.SemiSimplexCategory.mk (⟨m, y.val⟩ : Simplex K).1)) := y.property
        exact (s.property (hcarrier.symm ▸ hyL)).elim
      | inr z =>
        have hcb := leastRelativeCarrier_eq_of_last_exterior hK b z hb
        have hsz : s = z := Subtype.ext (hca.symm.trans (hcarrier.trans hcb))
        subst z
        have hweight := apex_weight_eq_of_distribution_eq hK a b t p s ha hb h
        cases n with
        | zero =>
          cases m with
          | zero =>
            refine ⟨rfl, heq_of_eq ?_⟩
            apply Subtype.ext
            funext i
            have hi : i = Fin.last 0 := by
              exact @Subsingleton.elim (Fin 1) inferInstance i (Fin.last 0)
            rw [hi, ha, hb]
          | succ m =>
            have ht1 : t.weights (Fin.last 0) = 1 := by
              simp
            have hlt := last_weight_lt_one_of_nonzero p hp
            rw [← hweight, ht1] at hlt
            exact (lt_irrefl (1 : ℝ) hlt).elim
        | succ n =>
          cases m with
          | zero =>
            have hp1 : p.weights (Fin.last 0) = 1 := by
              simp
            have hlt := last_weight_lt_one_of_nonzero t ht
            rw [hweight, hp1] at hlt
            exact (lt_irrefl (1 : ℝ) hlt).elim
          | succ m =>
            have hct := last_weight_lt_one_of_nonzero t ht
            have hcp := last_weight_lt_one_of_nonzero p hp
            have hprefix := relativePrefix_distribution_eq hK a b t p ht hp s ha hb h
            obtain ⟨hdim, hab⟩ := ih n (Nat.lt_succ_self n) (relativePrefix a) (relativePrefix b)
              (normalizedPrefix t hct) (normalizedPrefix p hcp)
              (normalizedPrefix_weights_ne_zero t hct ht)
              (normalizedPrefix_weights_ne_zero p hcp hp) hprefix
            subst m
            have hab' : relativePrefix a = relativePrefix b := eq_of_heq hab
            refine ⟨rfl, heq_of_eq ?_⟩
            apply Subtype.ext
            funext i
            induction i using Fin.lastCases with
            | last => exact ha.trans hb.symm
            | cast i =>
              exact congrArg (fun q => q.val i) hab'

/-- A nonzero relative derived point is uniquely determined, including its dimension and weights. -/
theorem relativeRepresentative_eq_of_distribution_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (t : StdSimplex ℝ (Fin (n + 1))) (p : StdSimplex ℝ (Fin (m + 1)))
    (ht : ∀ i, t.weights i ≠ 0) (hp : ∀ i, p.weights i ≠ 0)
    (h : relativeDistributionAffineMap a t = relativeDistributionAffineMap b p) :
    n = m ∧ HEq a b ∧ HEq t p := by
  obtain ⟨hdim, hab⟩ := relativeTuple_eq_of_distribution_eq hK a b t p ht hp h
  subst m
  have hab' : a = b := eq_of_heq hab
  subst b
  exact ⟨rfl, HEq.rfl, heq_of_eq (relativeDistributionAffineMap_injective hK a h)⟩

/-- The relative derived realization map of a simplicial complex is injective. -/
theorem relativeRealizationMap_injective {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : Function.Injective (relativeRealizationMap hK L).hom := by
  intro z w hzw
  obtain ⟨n, a, t, ht, rfl⟩ := exists_simplexChar_nonzero_rep z
  obtain ⟨m, b, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep w
  have he := congrArg (vertexDistributionMap K).hom hzw
  rw [relativeRealizationMap_distribution_simplex_apply,
    relativeRealizationMap_distribution_simplex_apply] at he
  obtain ⟨hdim, hab, htp⟩ := relativeRepresentative_eq_of_distribution_eq hK a b t p ht hp he
  subst m
  have hab' : a = b := eq_of_heq hab
  have htp' : t = p := eq_of_heq htp
  subst b
  subst p
  rfl

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRepresentative_eq_of_distribution_eq
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_injective
