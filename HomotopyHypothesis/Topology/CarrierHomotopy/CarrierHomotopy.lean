import Mathlib.Topology.Homotopy.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.Maps.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.CarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Straight-line carrier homotopies in finite simplicial complexes

Two continuous maps from a semi-simplicial realization into a finite simplicial
complex that map each source simplex into a common target simplex are homotopic
relative to any subspace where they agree.
-/

universe u

open CategoryTheory Opposite Convexity Topology

namespace HomotopyHypothesis.Topology.CarrierHomotopy

open Henry Henry.SemiSSet HomotopyHypothesis.Approximation.Zeeman

/-- The coordinate embedding of the realization into vertex coordinates. -/
noncomputable def coordEmb (K : SemiSSet.{u}) :
    realization.obj K → (K.obj (op (Henry.SemiSimplexCategory.mk 0)) → ℝ) :=
  fun z => ((vertexDistributionMap K).hom z).weights

lemma isEmbedding_coordEmb {K : SemiSSet.{u}}
    (hKfin : K.IsFinite) (hKsc : K.IsSimplicialComplex) :
    IsEmbedding (coordEmb K) := by
  have : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hKfin.1 0
  have htop := HomotopyHypothesis.Realization.ComplexTopology.complexRealizationTopologyStatement_proof K hKfin hKsc
  have hemb1 : IsEmbedding (vertexDistributionMap K).hom := htop.2.toIsEmbedding
  have hemb2 : IsEmbedding (fun t : VertexDistributions K => (t.weights : K.obj (op (Henry.SemiSimplexCategory.mk 0)) → ℝ)) :=
    Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _
  exact hemb2.comp hemb1

/-- The interpolated coordinate map on the product `I × |W|`. -/
noncomputable def coordInterp (W K : SemiSSet.{u})
    (f g : realization.obj W ⟶ realization.obj K) :
    unitInterval × realization.obj W →
      (K.obj (op (Henry.SemiSimplexCategory.mk 0)) → ℝ) :=
  fun p v => (1 - (p.1 : ℝ)) * coordEmb K (f.hom p.2) v +
             (p.1 : ℝ) * coordEmb K (g.hom p.2) v

lemma continuous_coordInterp {W K : SemiSSet.{u}}
    (f g : realization.obj W ⟶ realization.obj K) :
    Continuous (coordInterp W K f g) := by
  rw [continuous_pi_iff]
  intro v
  have h1 : Continuous fun p : unitInterval × realization.obj W => 1 - (p.1 : ℝ) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous fun p : unitInterval × realization.obj W =>
      coordEmb K (f.hom p.2) v :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) v).comp
      ((vertexDistributionMap K).hom.continuous.comp (f.hom.continuous.comp continuous_snd))
  have h3 : Continuous fun p : unitInterval × realization.obj W => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h4 : Continuous fun p : unitInterval × realization.obj W =>
      coordEmb K (g.hom p.2) v :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) v).comp
      ((vertexDistributionMap K).hom.continuous.comp (g.hom.continuous.comp continuous_snd))
  exact (h1.mul h2).add (h3.mul h4)

lemma coordInterp_mem_range {W K : SemiSSet.{u}}
    (f g : realization.obj W ⟶ realization.obj K)
    (h_carrier : ∀ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ W),
      ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
        (e₀ e₁ : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
          toTop.obj (Henry.SemiSimplexCategory.mk m)),
        simplexChar y ≫ f = e₀ ≫ simplexChar x ∧
          simplexChar y ≫ g = e₁ ≫ simplexChar x)
    (p : unitInterval × realization.obj W) :
    coordInterp W K f g p ∈ Set.range (coordEmb K) := by
  let t := (p.1 : ℝ)
  let w := p.2
  have ht_nonneg : 0 ≤ t := p.1.2.1
  have ht_le_one : t ≤ 1 := p.1.2.2
  have h1t_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
  obtain ⟨n, y, s, hs⟩ := exists_simplexChar_rep w
  obtain ⟨m, x, e₀, e₁, hf, hg⟩ := h_carrier n y
  have hfw : f.hom w = (simplexChar x).hom (e₀.hom s) := by
    rw [← hs]
    exact congrArg (fun h => h.hom s) hf
  have hgw : g.hom w = (simplexChar x).hom (e₁.hom s) := by
    rw [← hs]
    exact congrArg (fun h => h.hom s) hg
  let p₀ : StdSimplex ℝ (Fin (m + 1)) := (e₀.hom s).down
  let p₁ : StdSimplex ℝ (Fin (m + 1)) := (e₁.hom s).down
  let st : StdSimplex ℝ (Fin (m + 1)) := {
    weights := (1 - t) • p₀.weights + t • p₁.weights
    nonneg := fun j => by
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg h1t_nonneg (p₀.nonneg j)) (mul_nonneg ht_nonneg (p₁.nonneg j))
    total := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [p₀.total_of_fintype, p₁.total_of_fintype, mul_one, mul_one, sub_add_cancel]
  }
  let z := (simplexChar x).hom (ULift.up st)
  refine ⟨z, ?_⟩
  have hx : simplexChar x ≫ vertexDistributionMap K =
      simplexVertexDistribution (uliftYonedaEquiv x) := by
    simpa using simplexChar_vertexDistributionMap (uliftYonedaEquiv x)
  have hz : (vertexDistributionMap K).hom z =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) st :=
    congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom (ULift.up st)) hx
  have hs₀ : (vertexDistributionMap K).hom (f.hom w) =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) p₀ := by
    rw [hfw]
    exact congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom (e₀.hom s)) hx
  have hs₁ : (vertexDistributionMap K).hom (g.hom w) =
      StdSimplex.map (vertex (uliftYonedaEquiv x)) p₁ := by
    rw [hgw]
    exact congrArg (fun F : toTop.obj (Henry.SemiSimplexCategory.mk m) ⟶
      TopCat.of (VertexDistributions K) => F.hom (e₁.hom s)) hx
  ext v
  change ((vertexDistributionMap K).hom z).weights v = coordInterp W K f g p v
  rw [hz, StdSimplex.weights_map]
  change (Finsupp.mapDomain (vertex (uliftYonedaEquiv x))
    ((1 - t) • p₀.weights + t • p₁.weights)) v = coordInterp W K f g p v
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.mapDomain_smul]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs₀_rep : (coordEmb K (f.hom w)) v =
      (Finsupp.mapDomain (vertex (uliftYonedaEquiv x)) p₀.weights) v := by
    dsimp [coordEmb]
    rw [hs₀, StdSimplex.weights_map]
  have hs₁_rep : (coordEmb K (g.hom w)) v =
      (Finsupp.mapDomain (vertex (uliftYonedaEquiv x)) p₁.weights) v := by
    dsimp [coordEmb]
    rw [hs₁, StdSimplex.weights_map]
  rw [← hs₀_rep, ← hs₁_rep]
  rfl

/-- The relative straight-line carrier homotopy. -/
theorem carrierHomotopyStatement_proof : CarrierHomotopyStatement := by
  intro W K hKfin hKsc f g A hA h_carrier
  let E := coordEmb K
  have hemb := isEmbedding_coordEmb hKfin hKsc
  have hinj : Function.Injective E := hemb.injective
  let I := coordInterp W K f g
  have hI_cont : Continuous I := continuous_coordInterp f g
  have h_range : ∀ p, I p ∈ Set.range E := coordInterp_mem_range f g h_carrier
  let H : unitInterval × realization.obj W → realization.obj K :=
    fun p => (h_range p).choose
  have hEH : E ∘ H = I := funext fun p => (h_range p).choose_spec
  have hH_cont : Continuous H := hemb.continuous_iff.mpr (by rw [hEH]; exact hI_cont)
  refine ⟨{
    toFun := H
    continuous_toFun := hH_cont
    map_zero_left := by
      intro w
      apply hinj
      have h := congr_fun hEH (0, w)
      change E (H (0, w)) = I (0, w) at h
      rw [h]
      ext v
      change (1 - ((0 : unitInterval) : ℝ)) * coordEmb K (f.hom w) v +
             ((0 : unitInterval) : ℝ) * coordEmb K (g.hom w) v = coordEmb K (f.hom w) v
      have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
      rw [h0]
      ring_nf
    map_one_left := by
      intro w
      apply hinj
      have h := congr_fun hEH (1, w)
      change E (H (1, w)) = I (1, w) at h
      rw [h]
      ext v
      change (1 - ((1 : unitInterval) : ℝ)) * coordEmb K (f.hom w) v +
             ((1 : unitInterval) : ℝ) * coordEmb K (g.hom w) v = coordEmb K (g.hom w) v
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [h1]
      ring_nf
    prop' := by
      intro t w hw
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
      ring_nf
  }⟩

example : CarrierHomotopyStatement :=
  carrierHomotopyStatement_proof

#print axioms carrierHomotopyStatement_proof

end HomotopyHypothesis.Topology.CarrierHomotopy
