import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Vertices and the retained subcomplex

Combinatorial vertices agree with the vertices of characteristic maps.
For a simplicial complex they distinguish the simplices, allowing the fixed
subcomplex to be included in the relative derived complex.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Characteristic maps are natural with respect to the faces of a simplex. -/
theorem simplexChar_naturality {K : SemiSSet.{u}} {m n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K) :
    simplexChar (Henry.SemiSSet.stdSimplex.map θ ≫ x) = toTop.map θ ≫ simplexChar x := by
  unfold simplexChar realization
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  simpa only [Functor.comp_map] using congrArg
    (fun t => t ≫ (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u}).map x)
    ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).naturality θ).symm

/-- The realization of a combinatorial vertex is the corresponding vertex
of the characteristic map. -/
theorem simplexChar_vertex {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
    (simplexChar (uliftYonedaEquiv.symm (vertex x i))).hom (simplexVertex (n := 0) 0) =
      (simplexChar (uliftYonedaEquiv.symm x)).hom (simplexVertex i) := by
  rw [vertex, uliftYonedaEquiv_symm_map, simplexChar_naturality]
  change (simplexChar (uliftYonedaEquiv.symm x)).hom
    ((toTop.map (vertexInclusion i)).hom (simplexVertex (n := 0) 0)) = _
  congr 1
  change ULift.up (StdSimplex.map (fun _ : Fin 1 => i) (StdSimplex.single 0)) =
    ULift.up (StdSimplex.single i)
  rw [StdSimplex.map_single]

/-- Restricting a simplex restricts its ordered vertex tuple. -/
theorem vertex_map {K : SemiSSet.{u}} {m n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (m + 1)) :
    vertex (K.map θ.op x) i = vertex x (θ.hom.toOrderHom i) := by
  have hc : vertexInclusion i ≫ θ = vertexInclusion (θ.hom.toOrderHom i) := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext
    ext j
    rfl
  unfold vertex
  rw [← K.map_comp_apply, ← op_comp, hc]

/-- The ordered vertices of a simplex in a simplicial complex are distinct. -/
theorem vertex_injective {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) : Function.Injective (vertex x) := by
  intro i j hij
  apply hK.1 n (uliftYonedaEquiv.symm x)
  simpa only [simplexChar_vertex] using congrArg
    (fun t => (simplexChar (uliftYonedaEquiv.symm t)).hom (simplexVertex (n := 0) 0)) hij

/-- A simplex of a simplicial complex is determined by its ordered vertices. -/
theorem simplex_eq_of_vertex_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) {n : ℕ}
    {x y : K.obj (op (Henry.SemiSimplexCategory.mk n))} (h : vertex x = vertex y) : x = y := by
  apply uliftYonedaEquiv.symm.injective
  apply hK.2 n
  have hv : (fun i => (simplexChar (uliftYonedaEquiv.symm x)).hom (simplexVertex i)) =
      fun i => (simplexChar (uliftYonedaEquiv.symm y)).hom (simplexVertex i) := by
    funext i
    simpa only [simplexChar_vertex] using congrArg
      (fun t => (simplexChar (uliftYonedaEquiv.symm t)).hom (simplexVertex (n := 0) 0))
      (congrFun h i)
  exact congrArg Set.range hv

private theorem retained_admissible {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ} (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    RelativeAdmissible (fun i => Sum.inl (vertex x i) : Fin (n + 1) → RelativeVertex K L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    apply vertex_injective hK x.val
    exact congrArg Subtype.val (Sum.inl.inj h)
  · intro i j hij
    trivial
  · intro m θ w hw
    refine ⟨L.toFunctor.map θ.op x, ?_⟩
    intro i
    rw [vertex_map]
    exact Sum.inl.inj (hw i)

/-- The copy of the fixed subcomplex in its relative derived subdivision. -/
def relativeDerivedInclusion {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : L.toFunctor ⟶ relativeDerived K L where
  app X := ↾fun x => ⟨fun i => Sum.inl (vertex x i), retained_admissible hK L x⟩
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext i
    exact congrArg Sum.inl (vertex_map θ.unop x i)

instance relativeDerivedInclusion_mono {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : Mono (relativeDerivedInclusion hK L) := by
  rw [NatTrans.mono_iff_mono_app]
  intro X
  rw [mono_iff_injective]
  intro x y h
  apply Subtype.ext
  apply simplex_eq_of_vertex_eq hK
  funext i
  have hi := congrArg (fun a => a.val i) h
  exact congrArg Subtype.val (Sum.inl.inj hi)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerivedInclusion
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerivedInclusion_mono
