import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Vertex distributions on realization

The barycentric weights of a simplex give a distribution on its raw vertices.
These distributions agree on faces and descend to a continuous map on
realization.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The space of finitely supported probability distributions on the vertices. -/
abbrev VertexDistributions (K : SemiSSet.{u}) :=
  StdSimplex ℝ (K.obj (op (Henry.SemiSimplexCategory.mk 0)))

/-- Distribute a simplex's barycentric weights over its raw vertices. -/
noncomputable def simplexVertexDistribution {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶ TopCat.of (VertexDistributions K) :=
  TopCat.ofHom ⟨fun t => StdSimplex.map (vertex x) t.down,
    (StdSimplex.continuous_map ℝ (vertex x)).comp continuous_uliftDown⟩

/-- Vertex distributions commute with face inclusions. -/
theorem simplexVertexDistribution_face {K : SemiSSet.{u}} {n m : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    toTop.map θ ≫ simplexVertexDistribution x =
      simplexVertexDistribution (K.map θ.op x) := by
  apply ConcreteCategory.hom_ext
  intro t
  change StdSimplex.map (vertex x) (StdSimplex.map θ.hom.toOrderHom t.down) =
    StdSimplex.map (vertex (K.map θ.op x)) t.down
  exact (StdSimplex.map_comp t.down θ.hom.toOrderHom (vertex x)).symm.trans
    (congrArg (fun v => StdSimplex.map v t.down)
      (funext fun i => (vertex_map θ x i).symm))

/-- The compatible vertex distributions as a restricted Yoneda family. -/
noncomputable def vertexDistributionFamily (K : SemiSSet.{u}) :
    K ⟶ (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj
      (TopCat.of (VertexDistributions K)) where
  app X := ↾fun x => ULift.up (simplexVertexDistribution x)
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact (simplexVertexDistribution_face x θ.unop).symm

/-- The continuous vertex-distribution map on realization. -/
noncomputable def vertexDistributionMap (K : SemiSSet.{u}) :
    realization.obj K ⟶ TopCat.of (VertexDistributions K) :=
  realizationDesc (vertexDistributionFamily K)

/-- The global distribution map restricts to the distribution map of each simplex. -/
theorem simplexChar_vertexDistributionMap {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    simplexChar (uliftYonedaEquiv.symm x) ≫ vertexDistributionMap K =
      simplexVertexDistribution x :=
  simplexChar_realizationDesc (vertexDistributionFamily K) x

/-- Evaluate the distribution map at a simplex representative. -/
theorem vertexDistributionMap_simplex_apply {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) (t : StdSimplex ℝ (Fin (n + 1))) :
    (vertexDistributionMap K).hom
      ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up t)) =
        StdSimplex.map (vertex x) t :=
  congrArg (fun f => f.hom (ULift.up t)) (simplexChar_vertexDistributionMap x)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap_simplex_apply
