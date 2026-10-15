import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.DerivedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionPrismCompositionStatement
/-!
# Composition and iteration of relative subdivisions

Linear simplex embeddings and the retained-subcomplex equations compose.
Together with a composite pinched prism, they give successive relative
derived subdivisions while preserving finiteness and the complex predicate.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The identity map of a standard simplex is a linear embedding. -/
theorem isLinearEmbedding_id (n : ℕ) :
    IsLinearEmbedding (𝟙 (toTop.{u}.obj (Henry.SemiSimplexCategory.mk n))) := by
  constructor
  · change IsAffineMap ℝ (id : StdSimplex ℝ (Fin (n + 1)) → _)
    exact IsAffineMap.id
  · exact Function.injective_id

/-- Composing linear embeddings of standard simplices gives a linear embedding. -/
theorem isLinearEmbedding_comp {n m k : ℕ}
    {e : toTop.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      toTop.obj (Henry.SemiSimplexCategory.mk m)}
    {f : toTop.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶
      toTop.obj (Henry.SemiSimplexCategory.mk k)}
    (he : IsLinearEmbedding e) (hf : IsLinearEmbedding f) :
    IsLinearEmbedding (e ≫ f) := by
  constructor
  · change IsAffineMap ℝ
      ((fun y : StdSimplex ℝ (Fin (m + 1)) =>
        (ULift.down (f.hom (ULift.up y)) : StdSimplex ℝ (Fin (k + 1)))) ∘
        (fun x : StdSimplex ℝ (Fin (n + 1)) =>
          (ULift.down (e.hom (ULift.up x)) : StdSimplex ℝ (Fin (m + 1)))))
    exact hf.1.comp he.1
  · exact hf.2.comp he.2

/-- The retained map through two successive relative subdivisions. -/
def compositeSubdivisionRetainedMap {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (S₁ : RelSubdivision Y J) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    J.toFunctor ⟶ S₂.Y' := Subfunctor.toRange S₁.j ≫ S₂.j

/-- The composite retained map is a monomorphism. -/
theorem compositeSubdivisionRetainedMap_mono {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (S₁ : RelSubdivision Y J) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    Mono (compositeSubdivisionRetainedMap S₁ S₂) := by
  haveI : Mono S₁.j := S₁.mono_j
  haveI : Mono S₂.j := S₂.mono_j
  unfold compositeSubdivisionRetainedMap
  infer_instance

/-- The composite realization identification fixes the retained subcomplex. -/
theorem compositeSubdivision_retained {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (S₁ : RelSubdivision Y J) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    realization.map (compositeSubdivisionRetainedMap S₁ S₂) ≫ (S₂.h ≪≫ S₁.h).hom =
      realization.map J.ι := by
  unfold compositeSubdivisionRetainedMap
  calc
    realization.map (Subfunctor.toRange S₁.j ≫ S₂.j) ≫ (S₂.h ≪≫ S₁.h).hom =
        realization.map (Subfunctor.toRange S₁.j) ≫
          ((realization.map S₂.j ≫ S₂.h.hom) ≫ S₁.h.hom) := by
      rw [Functor.map_comp]
      simp only [Iso.trans_hom, Category.assoc]
    _ = realization.map (Subfunctor.toRange S₁.j) ≫
        (realization.map (Subfunctor.range S₁.j).ι ≫ S₁.h.hom) := by rw [S₂.hj]
    _ = (realization.map (Subfunctor.toRange S₁.j) ≫
        realization.map (Subfunctor.range S₁.j).ι) ≫ S₁.h.hom :=
      (Category.assoc _ _ _).symm
    _ = realization.map S₁.j ≫ S₁.h.hom := by
      rw [← Functor.map_comp, Subfunctor.toRange_ι]
    _ = realization.map J.ι := S₁.hj

/-- Linear characteristic-map factorizations compose through the intermediate complex. -/
theorem compositeSubdivision_linear {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (S₁ : RelSubdivision Y J) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j))
    (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ S₂.Y') :
    ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ Y)
      (e : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶ toTop.obj (Henry.SemiSimplexCategory.mk m)),
      IsLinearEmbedding e ∧ simplexChar y ≫ (S₂.h ≪≫ S₁.h).hom = e ≫ simplexChar x := by
  obtain ⟨m, z, e₂, he₂, h₂⟩ := S₂.linear n y
  obtain ⟨k, x, e₁, he₁, h₁⟩ := S₁.linear m z
  refine ⟨k, x, e₂ ≫ e₁, isLinearEmbedding_comp he₂ he₁, ?_⟩
  calc
    simplexChar y ≫ (S₂.h ≪≫ S₁.h).hom = (simplexChar y ≫ S₂.h.hom) ≫ S₁.h.hom := by
      rw [Iso.trans_hom, Category.assoc]
    _ = (e₂ ≫ simplexChar z) ≫ S₁.h.hom := by rw [h₂]
    _ = e₂ ≫ (simplexChar z ≫ S₁.h.hom) := Category.assoc _ _ _
    _ = e₂ ≫ (e₁ ≫ simplexChar x) := by rw [h₁]
    _ = (e₂ ≫ e₁) ≫ simplexChar x := (Category.assoc _ _ _).symm

/-- Compose two relative subdivisions using their composite pinched prism. -/
noncomputable def composeRelSubdivision {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (hP : SubdivisionPrismCompositionStatement.{u}) (S₁ : RelSubdivision Y J)
    (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) : RelSubdivision Y J := by
  classical
  choose C a b ρ hc ha h₀ h₁ using hP J S₁ S₂
  exact
    { Y' := S₂.Y'
      finite := S₂.finite
      h := S₂.h ≪≫ S₁.h
      linear := compositeSubdivision_linear S₁ S₂
      j := compositeSubdivisionRetainedMap S₁ S₂
      mono_j := compositeSubdivisionRetainedMap_mono S₁ S₂
      hj := compositeSubdivision_retained S₁ S₂
      C := C
      c₀ := a
      c₁ := b
      hc := hc
      anodyne_c₀ := ha
      ρ := ρ
      hρ₀ := h₀
      hρ₁ := h₁ }

/-- The zero-fold subdivision with the identity prism. -/
noncomputable def identityRelSubdivision {Y : SemiSSet.{u}} (hY : Y.IsFinite)
    (J : Subfunctor Y) : RelSubdivision Y J where
  Y' := Y
  finite := hY
  h := Iso.refl _
  linear n y := ⟨n, y, 𝟙 _, isLinearEmbedding_id n,
    (Category.comp_id (simplexChar y)).trans (Category.id_comp (simplexChar y)).symm⟩
  j := J.ι
  mono_j := inferInstance
  hj := by simp
  C := Y
  c₀ := 𝟙 _
  c₁ := 𝟙 _
  hc := by simp
  anodyne_c₀ := by unfold anodyne; exact .id _
  ρ := 𝟙 _
  hρ₀ := by simp
  hρ₁ := by simp

/-- Iterated relative derived subdivisions, preserving the ordered complex predicate. -/
noncomputable def iteratedDerivedSubdivision {K : SemiSSet.{u}}
    (hP : SubdivisionPrismCompositionStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    ℕ → {S : RelSubdivision K L // S.Y'.IsSimplicialComplex}
  | 0 => ⟨identityRelSubdivision hK L, hKs⟩
  | r + 1 =>
    let prev := iteratedDerivedSubdivision hP hK hKs L r
    let next := derivedSubdivision prev.val.finite prev.property (Subfunctor.range prev.val.j)
    ⟨composeRelSubdivision hP prev.val next,
      derivedSubdivision_isSimplicialComplex prev.val.finite prev.property
        (Subfunctor.range prev.val.j)⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.isLinearEmbedding_comp
#print axioms HomotopyHypothesis.Approximation.Zeeman.compositeSubdivision_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.composeRelSubdivision
#print axioms HomotopyHypothesis.Approximation.Zeeman.iteratedDerivedSubdivision
