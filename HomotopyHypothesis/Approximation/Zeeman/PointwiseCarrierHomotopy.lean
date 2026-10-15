import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Topology.CarrierHomotopy.CarrierHomotopy
import HomotopyHypothesis.Approximation.Zeeman.PointwiseCarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Relative homotopies from pointwise simplex carriers

Straight-line interpolation in vertex coordinates stays in the realization
whenever the two images of each point lie in a common simplex. The coordinate
embedding lifts this interpolation continuously, fixing every point where
the two maps agree.
-/

universe u

open CategoryTheory Opposite Convexity Topology

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet Topology.CarrierHomotopy

/-- Pointwise common simplex representatives keep coordinate interpolation in the realization. -/
theorem coordInterp_mem_range_of_pointwise {W K : SemiSSet.{u}}
    (f g : realization.obj W ⟶ realization.obj K)
    (hcarrier : ∀ z : realization.obj W,
      ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
        (p q : toTop.obj (Henry.SemiSimplexCategory.mk m)),
        f.hom z = (simplexChar x).hom p ∧ g.hom z = (simplexChar x).hom q)
    (a : unitInterval × realization.obj W) :
    coordInterp W K f g a ∈ Set.range (coordEmb K) := by
  let t := (a.1 : ℝ)
  have ht : 0 ≤ t := a.1.2.1
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr a.1.2.2
  obtain ⟨m, x, s₀, s₁, hf, hg⟩ := hcarrier a.2
  let p₀ : StdSimplex ℝ (Fin (m + 1)) := s₀.down
  let p₁ : StdSimplex ℝ (Fin (m + 1)) := s₁.down
  let st : StdSimplex ℝ (Fin (m + 1)) :=
    { weights := (1 - t) • p₀.weights + t • p₁.weights
      nonneg := fun j => by
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg h1t (p₀.nonneg j)) (mul_nonneg ht (p₁.nonneg j))
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [p₀.total_of_fintype, p₁.total_of_fintype, mul_one, mul_one, sub_add_cancel] }
  let z := (simplexChar x).hom (ULift.up st)
  have hx : simplexChar x ≫ vertexDistributionMap K =
      simplexVertexDistribution (uliftYonedaEquiv x) := by
    simpa only [Equiv.symm_apply_apply] using simplexChar_vertexDistributionMap (uliftYonedaEquiv x)
  have hz : (vertexDistributionMap K).hom z =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) st :=
    congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom (ULift.up st)) hx
  have hs₀ : (vertexDistributionMap K).hom (f.hom a.2) =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) p₀ := by
    rw [hf]
    exact congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom s₀) hx
  have hs₁ : (vertexDistributionMap K).hom (g.hom a.2) =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) p₁ := by
    rw [hg]
    exact congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom s₁) hx
  refine ⟨z, ?_⟩
  ext v
  change ((vertexDistributionMap K).hom z).weights v = coordInterp W K f g a v
  rw [hz, StdSimplex.weights_map]
  change (Finsupp.mapDomain (vertex (uliftYonedaEquiv x))
    ((1 - t) • p₀.weights + t • p₁.weights)) v = coordInterp W K f g a v
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.mapDomain_smul]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs₀_rep : coordEmb K (f.hom a.2) v =
      (Finsupp.mapDomain (vertex (uliftYonedaEquiv x)) p₀.weights) v := by
    dsimp [coordEmb]
    rw [hs₀, StdSimplex.weights_map]
  have hs₁_rep : coordEmb K (g.hom a.2) v =
      (Finsupp.mapDomain (vertex (uliftYonedaEquiv x)) p₁.weights) v := by
    dsimp [coordEmb]
    rw [hs₁, StdSimplex.weights_map]
  rw [← hs₀_rep, ← hs₁_rep]
  rfl

/-- Pointwise common simplex carriers give a relative straight-line homotopy. -/
theorem pointwiseCarrierHomotopyStatement_proof : PointwiseCarrierHomotopyStatement.{u} := by
  intro W K hK hKs f g A hA hcarrier
  let E := coordEmb K
  have hemb := isEmbedding_coordEmb hK hKs
  have hinj : Function.Injective E := hemb.injective
  let I := coordInterp W K f g
  have hI : Continuous I := continuous_coordInterp f g
  have hrange : ∀ p, I p ∈ Set.range E := coordInterp_mem_range_of_pointwise f g hcarrier
  let H : unitInterval × realization.obj W → realization.obj K := fun p => (hrange p).choose
  have hEH : E ∘ H = I := funext fun p => (hrange p).choose_spec
  have hH : Continuous H := hemb.continuous_iff.mpr (by rw [hEH]; exact hI)
  refine ⟨{ toFun := H
            continuous_toFun := hH
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro w
    apply hinj
    have h := congr_fun hEH (0, w)
    change E (H (0, w)) = I (0, w) at h
    rw [h]
    ext v
    change (1 - ((0 : unitInterval) : ℝ)) * coordEmb K (f.hom w) v +
      ((0 : unitInterval) : ℝ) * coordEmb K (g.hom w) v = coordEmb K (f.hom w) v
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0]
    ring
  · intro w
    apply hinj
    have h := congr_fun hEH (1, w)
    change E (H (1, w)) = I (1, w) at h
    rw [h]
    ext v
    change (1 - ((1 : unitInterval) : ℝ)) * coordEmb K (f.hom w) v +
      ((1 : unitInterval) : ℝ) * coordEmb K (g.hom w) v = coordEmb K (g.hom w) v
    have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [h1]
    ring
  · intro t w hw
    apply hinj
    have h := congr_fun hEH (t, w)
    change E (H (t, w)) = I (t, w) at h
    change E (H (t, w)) = E (f.hom w)
    rw [h]
    ext v
    change (1 - (t : ℝ)) * coordEmb K (f.hom w) v +
      (t : ℝ) * coordEmb K (g.hom w) v = coordEmb K (f.hom w) v
    have heq : coordEmb K (g.hom w) v = coordEmb K (f.hom w) v := by
      congr 1
      exact (hA w hw).symm
    rw [heq]
    ring

example : PointwiseCarrierHomotopyStatement.{u} := pointwiseCarrierHomotopyStatement_proof

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.coordInterp_mem_range_of_pointwise
#print axioms HomotopyHypothesis.Approximation.Zeeman.pointwiseCarrierHomotopyStatement_proof
