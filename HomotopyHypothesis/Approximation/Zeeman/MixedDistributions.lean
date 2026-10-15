import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Vertex distributions of the mixed relative prism

Original vertices represent point distributions and exterior faces represent
their uniform barycentric distributions. Every mixed flag has an original
carrier, so each affine mixture lies in the original realization's image
under vertex distributions. The mixtures agree on faces and descend to a
continuous distribution map.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The original face represented by a mixed vertex. -/
def MixedVertex.sourceSimplex {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : MixedVertex K L) : Simplex K :=
  match v with
  | .inl w => ⟨0, w⟩
  | .inr s => s.val

/-- A mixed vertex's source face is a face of an original carrier. -/
def MixedVertex.CarriedBy {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (v : MixedVertex K L) (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) : Prop :=
  ∃ θ : Henry.SemiSimplexCategory.mk v.sourceSimplex.1 ⟶
    Henry.SemiSimplexCategory.mk m, K.map θ.op y = v.sourceSimplex.2

/-- All vertices of a mixed flag lie in a common original carrier. -/
theorem exists_mixedCarrier {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ s : Simplex K, ∀ i, MixedVertex.CarriedBy (a.val i) s.2 := by
  cases hlast : a.val (Fin.last n) with
  | inl v =>
    let w : Fin (n + 1) → K.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
      fun i => match a.val i with | .inl z => z | .inr _ => v
    have hw (i : Fin (n + 1)) : a.val i = .inl (w i) := by
      by_cases hi : i = Fin.last n
      · subst i
        simp only [w, hlast]
      · have hb := a.property.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
        cases he : a.val i with
        | inl z => simp only [w, he]
        | inr s => simp only [he, hlast, MixedVertex.Precedes] at hb
    obtain ⟨x, hx⟩ := a.property.2.2 n (𝟙 _) w hw
    refine ⟨⟨n, x⟩, ?_⟩
    intro i
    rw [hw i]
    exact ⟨vertexInclusion i, hx i⟩
  | inr s =>
    refine ⟨s.val, ?_⟩
    intro i
    by_cases hi : i = Fin.last n
    · subst i
      rw [hlast]
      change ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶
        Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = s.val.2
      exact ⟨𝟙 _, by simp⟩
    · have hb := a.property.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
      rw [hlast] at hb
      cases he : a.val i with
      | inl v =>
        change ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶
          Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = v
        simpa only [he, MixedVertex.Precedes] using hb
      | inr t =>
        simp only [he, MixedVertex.Precedes] at hb
        exact hb.2

/-- The original distribution represented by a mixed vertex. -/
noncomputable def mixedVertexDistribution {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : MixedVertex K L) : VertexDistributions K :=
  StdSimplex.map (vertex v.sourceSimplex.2)
    (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))

/-- An original mixed vertex represents its original point distribution. -/
theorem mixedVertexDistribution_original {K : SemiSSet.{u}} {L : Subfunctor K}
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    mixedVertexDistribution (Sum.inl w : MixedVertex K L) = StdSimplex.single w := by
  change StdSimplex.map (vertex w) (StdSimplex.barycenter (K := ℝ) (M := Fin 1)) = _
  rw [StdSimplex.barycenter_fin_one, StdSimplex.map_single, vertex_zero]

/-- Passing from derived to mixed vertices preserves their original distributions. -/
theorem mixedVertexDistribution_derived {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : RelativeVertex K L) :
    mixedVertexDistribution (relativeToMixedVertex v) = relativeVertexDistribution v := by
  cases v <;> rfl

/-- A vertex distribution can be computed inside any original carrier. -/
theorem mixedVertexDistribution_mem_range {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : MixedVertex K L)
    (hv : MixedVertex.CarriedBy v y) :
    mixedVertexDistribution v ∈ Set.range (StdSimplex.map (R := ℝ) (vertex y)) := by
  obtain ⟨θ, hθ⟩ := hv
  let b := StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1))
  refine ⟨StdSimplex.map θ.hom.toOrderHom b, ?_⟩
  refine (StdSimplex.map_comp b θ.hom.toOrderHom (vertex y)).symm.trans
    (congrArg (fun f => StdSimplex.map f b) ?_)
  funext i
  exact (vertex_map θ y i).symm.trans (congrArg (fun z => vertex z i) hθ)

/-- Extend a mixed tuple's original distributions affinely. -/
noncomputable def mixedDistributionAffineMap {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (VertexDistributions K) :=
  StdSimplex.affineMapMk (R := ℝ) (fun i => mixedVertexDistribution (a.val i))

/-- An affine mixed distribution lies in the distribution image of an original simplex. -/
theorem mixedDistributionAffineMap_mem_range {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    mixedDistributionAffineMap a t ∈ Set.range (vertexDistributionMap K).hom := by
  obtain ⟨s, hs⟩ := exists_mixedCarrier a
  have hm : mixedDistributionAffineMap a t ∈
      Set.range (StdSimplex.map (R := ℝ) (vertex s.2)) := by
    apply (StdSimplex.mem_range_map_iff _ _).mpr
    intro w hw
    rw [mixedDistributionAffineMap, affineMapMk_weights_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [(StdSimplex.mem_range_map_iff _ _).mp
      (mixedVertexDistribution_mem_range s.2 (a.val i) (hs i)) w hw, mul_zero]
  obtain ⟨p, hp⟩ := hm
  refine ⟨(simplexChar (uliftYonedaEquiv.symm s.2)).hom (ULift.up p), ?_⟩
  exact (vertexDistributionMap_simplex_apply s.2 p).trans hp

/-- Finite original vertex sets make affine mixed distributions continuous. -/
theorem mixedDistributionAffineMap_continuous {K : SemiSSet.{u}} (hK : K.IsFinite)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Continuous (mixedDistributionAffineMap a) := by
  have : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hK.1 0
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (K.obj (op (Henry.SemiSimplexCategory.mk 0)))).continuous_iff.mpr
  apply continuous_pi
  intro w
  apply StdSimplex.continuous_of_isAffineMap
  exact (IsAffineMap.linearMap (Finsupp.lapply w :
    (K.obj (op (Henry.SemiSimplexCategory.mk 0)) →₀ ℝ) →ₗ[ℝ] ℝ)).comp
      ((StdSimplex.isAffineMap_weights ℝ _).comp (mixedDistributionAffineMap a).isAffineMap)

/-- Affine mixed distributions agree under face restriction. -/
theorem mixedDistributionAffineMap_face {K : SemiSSet.{u}} {L : Subfunctor K} {n m : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    (mixedDistributionAffineMap a).comp (StdSimplex.affineMap θ.hom.toOrderHom) =
      mixedDistributionAffineMap ((mixedFlags K L).map θ.op a) := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [ConvexSpace.AffineMap.comp_apply, Function.comp_apply, StdSimplex.coe_affineMap,
    StdSimplex.map_single, mixedDistributionAffineMap, StdSimplex.affineMapMk_single]
  rfl

/-- Bundle a simplex's mixed distribution map continuously. -/
noncomputable def mixedSimplexDistribution {K : SemiSSet.{u}} (hK : K.IsFinite)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶ TopCat.of (VertexDistributions K) :=
  TopCat.ofHom ⟨fun t => mixedDistributionAffineMap a t.down,
    (mixedDistributionAffineMap_continuous hK a).comp continuous_uliftDown⟩

/-- The topological mixed distribution maps agree on faces. -/
theorem mixedSimplexDistribution_face {K : SemiSSet.{u}} (hK : K.IsFinite)
    {L : Subfunctor K} {n m : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    toTop.map θ ≫ mixedSimplexDistribution hK a =
      mixedSimplexDistribution hK ((mixedFlags K L).map θ.op a) := by
  apply ConcreteCategory.hom_ext
  intro t
  exact DFunLike.congr_fun (mixedDistributionAffineMap_face a θ) t.down

/-- The compatible family of mixed distribution maps. -/
noncomputable def mixedDistributionFamily {K : SemiSSet.{u}} (hK : K.IsFinite)
    (L : Subfunctor K) :
    mixedFlags K L ⟶ (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj
      (TopCat.of (VertexDistributions K)) where
  app _ := ↾fun a => ULift.up (mixedSimplexDistribution hK a)
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    exact (mixedSimplexDistribution_face hK a θ.unop).symm

/-- The continuous distribution map of the mixed prism. -/
noncomputable def mixedDistributionMap {K : SemiSSet.{u}} (hK : K.IsFinite)
    (L : Subfunctor K) :
    realization.obj (mixedFlags K L) ⟶ TopCat.of (VertexDistributions K) :=
  realizationDesc (mixedDistributionFamily hK L)

/-- Evaluate the descended mixed distribution map on a simplex. -/
theorem mixedDistributionMap_simplex_apply {K : SemiSSet.{u}} (hK : K.IsFinite)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    (mixedDistributionMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up t)) =
        mixedDistributionAffineMap a t :=
  congrArg (fun f => f.hom (ULift.up t)) (simplexChar_realizationDesc
    (mixedDistributionFamily hK L) a)

/-- Every mixed realization point has an original vertex distribution. -/
theorem mixedDistributionMap_mem_range {K : SemiSSet.{u}} (hK : K.IsFinite)
    (L : Subfunctor K) (z : realization.obj (mixedFlags K L)) :
    (mixedDistributionMap hK L).hom z ∈ Set.range (vertexDistributionMap K).hom := by
  obtain ⟨n, y, t, rfl⟩ := exists_simplexChar_rep z
  have h := mixedDistributionMap_simplex_apply hK (uliftYonedaEquiv y) t.down
  simp only [Equiv.symm_apply_apply] at h
  erw [h]
  exact mixedDistributionAffineMap_mem_range _ _

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_mixedCarrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedDistributionMap_mem_range
