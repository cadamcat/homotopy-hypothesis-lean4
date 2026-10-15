import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.VertexMaps.SimplicialVertexMap
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.GlobalStars
import HomotopyHypothesis.Approximation.Zeeman.PointwiseCarrierHomotopyStatement
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.TargetStars
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.VertexStarApproximationStatement
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Simplicial approximation from global vertex stars

Map each point's vertex distribution through the chosen vertex map. The
star condition places each resulting distribution in a target simplex.
The target distribution embedding lifts this map continuously, and its
local affine formulas give a coherent simplicial approximation. Simplicial
restrictions are preserved, with a relative pointwise carrier homotopy.
-/

universe u

open CategoryTheory Opposite Convexity Topology

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The star condition places all image vertices of a source simplex in one target simplex. -/
theorem exists_vertexStarMap_simplex {W M : SemiSSet.{u}}
    (F : realization.obj W ⟶ realization.obj M)
    (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hq : IsVertexStarMap F q) {n : ℕ} (x : W.obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ (m : ℕ) (y : M.obj (op (Henry.SemiSimplexCategory.mk m))) (v : Fin (n + 1) → Fin (m + 1)),
      ∀ i, vertex y (v i) = q (vertex x i) := by
  let b := StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))
  have hb (i : Fin (n + 1)) : b.weights i ≠ 0 := by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  have hs (i : Fin (n + 1)) :
      F.hom ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up b)) ∈
        vertexOpenStar M (q (vertex x i)) :=
    hq _ ((mem_vertexOpenStar_simplex_iff x b (vertex x i)).mpr ⟨i, rfl, hb i⟩)
  obtain ⟨m, y, _, v, hv, _, _⟩ := exists_simplex_of_vertexOpenStar_intersection
    (fun i => q (vertex x i))
    (F.hom ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up b))) hs
  exact ⟨m, y, v, hv⟩

/-- A prescribed distribution formula determines every compatible affine simplex formula. -/
theorem simplexChar_eq_of_vertexDistribution {W M : SemiSSet.{u}}
    (hM : M.IsSimplicialComplex) (G : realization.obj W ⟶ realization.obj M)
    (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hG : ∀ z, (vertexDistributionMap M).hom (G.hom z) =
      StdSimplex.map q ((vertexDistributionMap W).hom z))
    {n m : ℕ} (x : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (y : M.obj (op (Henry.SemiSimplexCategory.mk m))) (v : Fin (n + 1) → Fin (m + 1))
    (hv : ∀ i, vertex y (v i) = q (vertex x i)) :
    simplexChar (uliftYonedaEquiv.symm x) ≫ G = vertexMap v ≫ simplexChar (uliftYonedaEquiv.symm y) := by
  apply ConcreteCategory.hom_ext
  intro t
  apply vertexDistributionMap_injective hM
  change (vertexDistributionMap M).hom (G.hom
      ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up t.down))) =
    (vertexDistributionMap M).hom ((simplexChar (uliftYonedaEquiv.symm y)).hom
      (ULift.up (StdSimplex.map v t.down)))
  calc
    _ = StdSimplex.map q ((vertexDistributionMap W).hom
        ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up t.down))) := hG _
    _ = StdSimplex.map q (StdSimplex.map (vertex x) t.down) :=
      congrArg (StdSimplex.map q) (vertexDistributionMap_simplex_apply x t.down)
    _ = StdSimplex.map (q ∘ vertex x) t.down := (StdSimplex.map_comp t.down (vertex x) q).symm
    _ = StdSimplex.map (vertex y ∘ v) t.down :=
      congrArg (fun f => StdSimplex.map f t.down) (funext hv).symm
    _ = StdSimplex.map (vertex y) (StdSimplex.map v t.down) := StdSimplex.map_comp t.down v (vertex y)
    _ = _ := (vertexDistributionMap_simplex_apply y (StdSimplex.map v t.down)).symm

/-- The global image distribution lifts to a coherent simplicial map. -/
theorem exists_simplicialMap_of_vertexStarMap {W M : SemiSSet.{u}}
    (hM : M.IsFinite) (hMs : M.IsSimplicialComplex) (F : realization.obj W ⟶ realization.obj M)
    (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hq : IsVertexStarMap F q) :
    ∃ g : realization.obj W ⟶ realization.obj M,
      (∀ z, (vertexDistributionMap M).hom (g.hom z) =
        StdSimplex.map q ((vertexDistributionMap W).hom z)) ∧ IsSimplicial g := by
  classical
  let D : realization.obj W → VertexDistributions M := fun z =>
    StdSimplex.map q ((vertexDistributionMap W).hom z)
  have hrange (z : realization.obj W) : D z ∈ Set.range (vertexDistributionMap M).hom := by
    obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep z
    obtain ⟨m, y, v, hv⟩ := exists_vertexStarMap_simplex F q hq x
    refine ⟨(simplexChar (uliftYonedaEquiv.symm y)).hom (ULift.up (StdSimplex.map v p)), ?_⟩
    calc
      _ = StdSimplex.map (vertex y) (StdSimplex.map v p) :=
        vertexDistributionMap_simplex_apply y (StdSimplex.map v p)
      _ = StdSimplex.map (vertex y ∘ v) p := (StdSimplex.map_comp p v (vertex y)).symm
      _ = StdSimplex.map (q ∘ vertex x) p := congrArg (fun a => StdSimplex.map a p) (funext hv)
      _ = StdSimplex.map q (StdSimplex.map (vertex x) p) := StdSimplex.map_comp p (vertex x) q
      _ = _ := congrArg (StdSimplex.map q) (vertexDistributionMap_simplex_apply x p).symm
  let G : realization.obj W → realization.obj M := fun z => (hrange z).choose
  have hG : ∀ z, (vertexDistributionMap M).hom (G z) = D z := fun z => (hrange z).choose_spec
  have hemb := (Realization.ComplexTopology.complexRealizationTopologyStatement_proof M hM hMs).2.toIsEmbedding
  have hc : Continuous G := hemb.continuous_iff.mpr (by
    have he : (vertexDistributionMap M).hom ∘ G = D := funext hG
    rw [he]
    exact (StdSimplex.continuous_map ℝ q).comp (vertexDistributionMap W).hom.continuous)
  let g : realization.obj W ⟶ realization.obj M := TopCat.ofHom ⟨G, hc⟩
  refine ⟨g, hG, ?_⟩
  apply Simplicial.VertexMaps.simplicialVertexMapStatement_proof hMs g q
  intro n a
  obtain ⟨m, y, v, hv⟩ := exists_vertexStarMap_simplex F q hq (uliftYonedaEquiv a)
  refine ⟨m, uliftYonedaEquiv.symm y, v, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hv
  · simpa only [Equiv.symm_apply_apply] using
      simplexChar_eq_of_vertexDistribution hMs g q hG (uliftYonedaEquiv a) y v hv

/-- The star condition forces the vertex images in every already affine simplex formula. -/
theorem vertexStarMap_vertex_eq {W M : SemiSSet.{u}}
    (F : realization.obj W ⟶ realization.obj M)
    (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hq : IsVertexStarMap F q) {n m : ℕ}
    (x : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (y : M.obj (op (Henry.SemiSimplexCategory.mk m))) (v : Fin (n + 1) → Fin (m + 1))
    (he : simplexChar (uliftYonedaEquiv.symm x) ≫ F =
      vertexMap v ≫ simplexChar (uliftYonedaEquiv.symm y)) (i : Fin (n + 1)) :
    vertex y (v i) = q (vertex x i) := by
  have hmem := hq (vertex x i) ((mem_vertexOpenStar_vertex_iff (vertex x i) (vertex x i)).mpr rfl)
  have hp := congrArg (fun e => e.hom (simplexVertex i)) he
  have hvp : (vertexMap v).hom (simplexVertex i) = simplexVertex (v i) :=
    congrArg ULift.up (StdSimplex.map_single (R := ℝ) i v)
  have hpoint : F.hom ((simplexChar (uliftYonedaEquiv.symm (vertex x i))).hom
      (simplexVertex (n := 0) 0)) =
      (simplexChar (uliftYonedaEquiv.symm (vertex y (v i)))).hom (simplexVertex (n := 0) 0) :=
    (congrArg F.hom (simplexChar_vertex x i)).trans
      ((hp.trans (congrArg (simplexChar (uliftYonedaEquiv.symm y)).hom hvp)).trans
        (simplexChar_vertex y (v i)).symm)
  exact (mem_vertexOpenStar_vertex_iff (vertex y (v i)) (q (vertex x i))).mp (hpoint ▸ hmem)

/-- The star condition gives coherent simplicial approximation and a relative carrier homotopy. -/
theorem vertexStarApproximationStatement_proof : VertexStarApproximationStatement.{u} := by
  intro hPH W M hM hMs F q hq J hJ
  obtain ⟨g, hdist, hgs⟩ := exists_simplicialMap_of_vertexStarMap hM hMs F q hq
  have hgj : realization.map J.ι ≫ g = realization.map J.ι ≫ F := by
    obtain ⟨φ, hφ⟩ := hJ
    apply realization_hom_ext
    intro n x
    obtain ⟨m, y, v, _, he⟩ := hφ n (uliftYonedaEquiv.symm x)
    have hinc := simplexChar_postcomp x J.ι
    change simplexChar (uliftYonedaEquiv.symm x) ≫ realization.map J.ι =
      simplexChar (uliftYonedaEquiv.symm x.val) at hinc
    have he' : simplexChar (uliftYonedaEquiv.symm x.val) ≫ F = vertexMap v ≫ simplexChar y := by
      simpa only [← Category.assoc, hinc] using he
    have he'' : simplexChar (uliftYonedaEquiv.symm x.val) ≫ F =
        vertexMap v ≫ simplexChar (uliftYonedaEquiv.symm (uliftYonedaEquiv y)) := by
      simpa only [Equiv.symm_apply_apply] using he'
    have hv := vertexStarMap_vertex_eq F q hq x.val (uliftYonedaEquiv y) v he''
    have hlocal := (simplexChar_eq_of_vertexDistribution hMs g q hdist
      x.val (uliftYonedaEquiv y) v hv).trans he''.symm
    simpa only [← Category.assoc, hinc] using hlocal
  refine ⟨g, hgs, hgj, ?_⟩
  apply hPH hM hMs
  · rintro z ⟨a, rfl⟩
    exact congrArg (fun e => e.hom a) hgj
  · intro z
    obtain ⟨n, x, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
    have hs (i : Fin (n + 1)) :
        F.hom ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p)) ∈
          vertexOpenStar M (q (vertex x i)) :=
      hq _ ((mem_vertexOpenStar_simplex_iff x p (vertex x i)).mpr ⟨i, rfl, hp i⟩)
    obtain ⟨m, y, pF, v, hv, _, hF⟩ := exists_simplex_of_vertexOpenStar_intersection
      (fun i => q (vertex x i))
      (F.hom ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p))) hs
    have hg := congrArg (fun e => e.hom (ULift.up p))
      (simplexChar_eq_of_vertexDistribution hMs g q hdist x y v hv)
    exact ⟨m, uliftYonedaEquiv.symm y, ULift.up (StdSimplex.map v p), ULift.up pF, hg, hF.symm⟩

example : VertexStarApproximationStatement.{u} := vertexStarApproximationStatement_proof

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_simplicialMap_of_vertexStarMap
#print axioms HomotopyHypothesis.Approximation.Zeeman.vertexStarApproximationStatement_proof
