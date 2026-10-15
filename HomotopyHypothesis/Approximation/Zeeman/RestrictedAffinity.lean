import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ExteriorIteration
import HomotopyHypothesis.Approximation.Zeeman.InducedCover
import HomotopyHypothesis.Approximation.Zeeman.InducedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.ScalarContraction
import HomotopyHypothesis.Approximation.Zeeman.ScalarMesh
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.TargetStars
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Affine coordinates on induced subcomplexes

Scalar affinity on a subcomplex persists on its induced subdivisions.
A nonnegative affine coordinate that is positive at a vertex stays positive
on that vertex's open star. Applied to a cover by collar and exterior, this
gives target star choices for vertices outside the exterior.
-/

universe u

open CategoryTheory Opposite Convexity
open scoped BigOperators

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A scalar function is affine on each simplex of a specified subcomplex. -/
def IsSimplexwiseScalarAffineOn {K : SemiSSet.{u}} (A : Subfunctor K)
    (F : realization.obj K → ℝ) : Prop :=
  ∀ (n : ℕ) (x : K.obj (op (Henry.SemiSimplexCategory.mk n))),
    x ∈ A.obj (op (Henry.SemiSimplexCategory.mk n)) → IsAffineMap ℝ (simplexScalarFunction F x)

/-- Scalar affinity on a subcomplex persists on its induced relative subdivision. -/
theorem isSimplexwiseScalarAffineOn_relativeRealizationMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) (F : realization.obj K → ℝ)
    (hF : IsSimplexwiseScalarAffineOn A F) :
    IsSimplexwiseScalarAffineOn (inducedRelativeSubdivision hK L A)
      (F ∘ (relativeRealizationMap hK L).hom) := by
  intro n x hx
  rw [simplexScalarFunction_relativeRealizationMap]
  exact (hF _ (leastRelativeCarrier hK x).2 hx).comp (relativeLocalAffineMap hK x).isAffineMap

/-- Restricted scalar affinity persists throughout the relative subdivision tower. -/
theorem isSimplexwiseScalarAffineOn_iteratedSubdivision {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (F : realization.obj K → ℝ) (hF : IsSimplexwiseScalarAffineOn A F) (r : ℕ) :
    IsSimplexwiseScalarAffineOn (iteratedInducedSubdivision hK hKs L A r)
      (F ∘ (derivedSubdivisionIterate hK hKs L r).h.hom.hom) := by
  induction r with
  | zero =>
    change IsSimplexwiseScalarAffineOn A (F ∘ id)
    simpa only [Function.comp_id] using hF
  | succ r ih =>
    exact isSimplexwiseScalarAffineOn_relativeRealizationMap
      (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)
      (iteratedInducedSubdivision hK hKs L A r)
      (F ∘ (derivedSubdivisionIterate hK hKs L r).h.hom.hom) ih

/-- A positive vertex value contributes positively wherever its barycentric weight is positive. -/
theorem scalarAffineMap_pos_of_vertex {n : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (hF : ∀ j, 0 ≤ F (StdSimplex.single j)) (i : Fin (n + 1))
    (hi : 0 < F (StdSimplex.single i)) (p : StdSimplex ℝ (Fin (n + 1)))
    (hp : 0 < p.weights i) : 0 < F p := by
  rw [scalarAffineMap_apply]
  exact (mul_pos hp hi).trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (p.nonneg j) (hF j)) (Finset.mem_univ i))

/-- An affine target coordinate at a nonexterior vertex determines a target star for its star. -/
theorem mapsTo_vertexOpenStar_of_scalarAffineOn {W M : SemiSSet.{u}}
    (A B : Subfunctor W) (hAB : A ⊔ B = ⊤)
    (F : realization.obj W ⟶ realization.obj M)
    (w : W.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hwB : w ∉ B.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (a : M.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hF : IsSimplexwiseScalarAffineOn A (vertexCoordinate M a ∘ F.hom))
    (hw : F.hom ((simplexChar (uliftYonedaEquiv.symm w)).hom
      (simplexVertex (n := 0) 0)) ∈ vertexOpenStar M a) :
    Set.MapsTo F.hom (vertexOpenStar W w) (vertexOpenStar M a) := by
  intro z hz
  obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep z
  obtain ⟨i, hi, hp⟩ := (mem_vertexOpenStar_simplex_iff x p w).mp hz
  have hx := simplex_mem_of_vertex_not_mem_of_cover A B hAB x i
    (by simpa only [hi] using hwB)
  let G : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ :=
    ⟨simplexScalarFunction (vertexCoordinate M a ∘ F.hom) x, hF n x hx⟩
  have hG (j : Fin (n + 1)) : 0 ≤ G (StdSimplex.single j) :=
    ((vertexDistributionMap M).hom
      (F.hom ((simplexChar (uliftYonedaEquiv.symm x)).hom (simplexVertex j)))).nonneg a
  have hGi : G (StdSimplex.single i) ≠ 0 := by
    have he := (simplexChar_vertex x i).symm
    rw [hi] at he
    change vertexCoordinate M a (F.hom
      ((simplexChar (uliftYonedaEquiv.symm x)).hom (simplexVertex i))) ≠ 0
    rw [he]
    exact hw
  have hpos := scalarAffineMap_pos_of_vertex G hG i
    (lt_of_le_of_ne (hG i) hGi.symm) p (lt_of_le_of_ne (p.nonneg i) hp.symm)
  exact ne_of_gt hpos

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplexwiseScalarAffineOn_iteratedSubdivision
#print axioms HomotopyHypothesis.Approximation.Zeeman.mapsTo_vertexOpenStar_of_scalarAffineOn
