import Mathlib.Data.Finset.Max
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.FiniteAverageContractionStatement
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Scalar contraction on exterior derived simplices

Scalar affine functions evaluate at face barycentres as averages of their
vertex values. On a derived simplex without retained vertices, its nested
source faces therefore give the barycentric contraction bound in any carrier.
-/

universe u

open CategoryTheory Opposite Convexity
open scoped BigOperators

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A scalar affine function is the weighted sum of its vertex values. -/
theorem scalarAffineMap_apply {n : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    F t = ∑ i, t.weights i * F (StdSimplex.single i) := by
  have he : StdSimplex.affineMapMk (R := ℝ) (fun i => F (StdSimplex.single i)) = F := by
    apply StdSimplex.affineMap_ext
    intro i
    exact StdSimplex.affineMapMk_single _ i
  rw [← he, StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  simp only [smul_eq_mul, StdSimplex.affineMapMk_single]

/-- Evaluation at the barycentre is the average of the vertex values. -/
theorem scalarAffineMap_barycenter {n : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ) :
    F (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) =
      (∑ i, F (StdSimplex.single i)) / ((n : ℝ) + 1) := by
  rw [scalarAffineMap_apply]
  simp only [StdSimplex.weights_barycenter_apply, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv]
  rw [← Finset.mul_sum, mul_comm]

/-- Evaluation at a face barycentre averages the corresponding original vertices. -/
theorem scalarAffineMap_face_barycenter {n m : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    F (StdSimplex.map θ.hom.toOrderHom
      (StdSimplex.barycenter (K := ℝ) (M := Fin (m + 1)))) =
      (∑ i, F (StdSimplex.single (θ.hom.toOrderHom i))) / ((m : ℝ) + 1) := by
  simpa only [ConvexSpace.AffineMap.comp_apply, Function.comp_apply,
    StdSimplex.coe_affineMap, StdSimplex.map_single] using
      scalarAffineMap_barycenter (F.comp (StdSimplex.affineMap θ.hom.toOrderHom))

/-- Vertex interval bounds hold throughout the standard simplex. -/
theorem scalarAffineMap_mem_interval {n : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (a b : ℝ) (hF : ∀ i, a ≤ F (StdSimplex.single i) ∧ F (StdSimplex.single i) ≤ b)
    (t : StdSimplex ℝ (Fin (n + 1))) : a ≤ F t ∧ F t ≤ b := by
  rw [scalarAffineMap_apply]
  have hc (c : ℝ) : (∑ i, t.weights i * c) = c := by
    rw [← Finset.sum_mul, t.total_of_fintype, one_mul]
  constructor
  · rw [← hc a]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF i).1 (t.nonneg i)
  · rw [← hc b]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF i).2 (t.nonneg i)

/-- A bound on pairwise vertex differences holds for arbitrary simplex points. -/
theorem scalarAffineMap_diameter_of_vertices {n : ℕ}
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ) (c : ℝ)
    (hF : ∀ i j, |F (StdSimplex.single i) - F (StdSimplex.single j)| ≤ c)
    (x y : StdSimplex ℝ (Fin (n + 1))) : |F x - F y| ≤ c := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (n + 1) => F (StdSimplex.single i)) ⟨0, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin (n + 1) => F (StdSimplex.single i)) ⟨0, Finset.mem_univ _⟩
  have hv (k : Fin (n + 1)) : F (StdSimplex.single i) ≤ F (StdSimplex.single k) ∧
      F (StdSimplex.single k) ≤ F (StdSimplex.single j) :=
    ⟨hi k (Finset.mem_univ _), hj k (Finset.mem_univ _)⟩
  have hx := scalarAffineMap_mem_interval F _ _ hv x
  have hy := scalarAffineMap_mem_interval F _ _ hv y
  have hc : F (StdSimplex.single j) - F (StdSimplex.single i) ≤ c :=
    (le_abs_self _).trans (hF j i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The dimension contraction factor increases with the dimension. -/
theorem dimensionContraction_mono {m n : ℕ} (hmn : m ≤ n) :
    (m : ℝ) / ((m : ℝ) + 1) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Any chosen source inclusion computes the same barycentric position. -/
theorem relativeVertexPosition_of_faceMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (s : K.obj (op (Henry.SemiSimplexCategory.mk n))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v s)
    (θ : Henry.SemiSimplexCategory.mk v.sourceSimplex.1 ⟶ Henry.SemiSimplexCategory.mk n)
    (hθ : K.map θ.op s = v.sourceSimplex.2) :
    relativeVertexPosition s v hv = StdSimplex.map θ.hom.toOrderHom
      (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1))) := by
  unfold relativeVertexPosition
  rw [faceMap_unique hK (carriedFaceMap s v hv) θ (carriedFaceMap_spec s v hv) hθ]

/-- Nested source faces satisfy the scalar contraction bound in any carrier. -/
theorem relativeVertexPosition_scalar_contraction
    (havg : FiniteAverageContractionStatement) {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (s : K.obj (op (Henry.SemiSimplexCategory.mk n))) (v w : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v s) (hw : RelativeVertex.CarriedBy w s)
    (θ : Henry.SemiSimplexCategory.mk v.sourceSimplex.1 ⟶
      Henry.SemiSimplexCategory.mk w.sourceSimplex.1)
    (hθ : K.map θ.op w.sourceSimplex.2 = v.sourceSimplex.2)
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (a b : ℝ) (hF : ∀ i, a ≤ F (StdSimplex.single i) ∧ F (StdSimplex.single i) ≤ b) :
    |F (relativeVertexPosition s v hv) - F (relativeVertexPosition s w hw)| ≤
      (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
  let η := carriedFaceMap s w hw
  let G := F.comp (StdSimplex.affineMap η.hom.toOrderHom)
  have hη : K.map η.op s = w.sourceSimplex.2 := carriedFaceMap_spec s w hw
  have hcomp : K.map (θ ≫ η).op s = v.sourceSimplex.2 := by
    rw [op_comp, K.map_comp_apply, hη, hθ]
  have hvpos := relativeVertexPosition_of_faceMap hK s v hv (θ ≫ η) hcomp
  have hwpos := relativeVertexPosition_of_faceMap hK s w hw η hη
  have he : F (relativeVertexPosition s v hv) = G (StdSimplex.map θ.hom.toOrderHom
      (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))) := by
    rw [hvpos]
    change F (StdSimplex.map (θ ≫ η).hom.toOrderHom _) = F (StdSimplex.map
      η.hom.toOrderHom (StdSimplex.map θ.hom.toOrderHom _))
    congr 1
    simpa only [WideSubcategory.comp_def, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe] using StdSimplex.map_comp
        (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))
        θ.hom.toOrderHom η.hom.toOrderHom
  have hwval : F (relativeVertexPosition s w hw) =
      G (StdSimplex.barycenter (K := ℝ) (M := Fin (w.sourceSimplex.1 + 1))) := by
    rw [hwpos]
    rfl
  have hG (i : Fin (w.sourceSimplex.1 + 1)) :
      a ≤ G (StdSimplex.single i) ∧ G (StdSimplex.single i) ≤ b := by
    simpa only [G, ConvexSpace.AffineMap.comp_apply, Function.comp_apply,
      StdSimplex.coe_affineMap, StdSimplex.map_single] using hF (η.hom.toOrderHom i)
  have hh := havg w.sourceSimplex.1 v.sourceSimplex.1
    ⟨θ.hom.toOrderHom, SimplexCategory.mono_iff_injective.mp θ.property⟩
    (fun i => G (StdSimplex.single i)) a b hG
  rw [he, hwval, scalarAffineMap_face_barycenter, scalarAffineMap_barycenter]
  refine hh.trans (mul_le_mul_of_nonneg_right (dimensionContraction_mono ?_) ?_)
  · have : Mono η.hom := η.property
    exact SimplexCategory.len_le_of_mono η.hom
  · exact sub_nonneg.mpr (le_trans (hF 0).1 (hF 0).2)

/-- Every pair of vertices of an exterior derived simplex obeys the contraction bound. -/
theorem relativeTuple_scalar_contraction
    (havg : FiniteAverageContractionStatement) {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {m n : ℕ}
    (q : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (hq : ∀ i, ¬ ∃ v, q.val i = Sum.inl v)
    (s : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hs : ∀ i, RelativeVertex.CarriedBy (q.val i) s)
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (a b : ℝ) (hF : ∀ i, a ≤ F (StdSimplex.single i) ∧ F (StdSimplex.single i) ≤ b)
    (i j : Fin (m + 1)) :
    |F (relativeVertexPosition s (q.val i) (hs i)) -
      F (relativeVertexPosition s (q.val j) (hs j))| ≤
        (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
  have hab : 0 ≤ b - a := sub_nonneg.mpr (le_trans (hF 0).1 (hF 0).2)
  have hordered (i j : Fin (m + 1)) (hij : i < j) :
      |F (relativeVertexPosition s (q.val i) (hs i)) -
        F (relativeVertexPosition s (q.val j) (hs j))| ≤
          (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
    have hp := q.property.2.1 i j hij
    obtain ⟨v, hv⟩ : ∃ v, q.val i = Sum.inr v := by
      cases hi : q.val i with
      | inl v => exact False.elim (hq i ⟨v, hi⟩)
      | inr v => exact ⟨v, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, q.val j = Sum.inr w := by
      cases hj : q.val j with
      | inl w => exact False.elim (hq j ⟨w, hj⟩)
      | inr w => exact ⟨w, rfl⟩
    rw [hv, hw] at hp
    obtain ⟨θ, hθ⟩ := hp.2
    simpa only [hv, hw, RelativeVertex.sourceSimplex] using
      relativeVertexPosition_scalar_contraction havg hK s (Sum.inr v) (Sum.inr w)
        (hv ▸ hs i) (hw ▸ hs j) θ hθ F a b hF
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hordered i j hij
  · subst j
    simp only [sub_self, abs_zero]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) (by positivity)) hab
  · rw [abs_sub_comm]
    exact hordered j i hij

/-- The scalar diameter contracts on the whole exterior derived simplex. -/
theorem relativeAffineMapInCarrier_scalar_contraction
    (havg : FiniteAverageContractionStatement) {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {m n : ℕ}
    (q : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (hq : ∀ i, ¬ ∃ v, q.val i = Sum.inl v)
    (s : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hs : ∀ i, RelativeVertex.CarriedBy (q.val i) s)
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ)
    (a b : ℝ) (hF : ∀ i, a ≤ F (StdSimplex.single i) ∧ F (StdSimplex.single i) ≤ b)
    (x y : StdSimplex ℝ (Fin (m + 1))) :
    |F (relativeAffineMapInCarrier q ⟨n, s⟩ hs x) -
      F (relativeAffineMapInCarrier q ⟨n, s⟩ hs y)| ≤
        (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
  apply scalarAffineMap_diameter_of_vertices
    (F.comp (relativeAffineMapInCarrier q ⟨n, s⟩ hs))
  intro i j
  simpa only [ConvexSpace.AffineMap.comp_apply, Function.comp_apply,
    relativeAffineMapInCarrier, StdSimplex.affineMapMk_single] using
      relativeTuple_scalar_contraction havg hK q hq s hs F a b hF i j

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.scalarAffineMap_barycenter
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeTuple_scalar_contraction
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeAffineMapInCarrier_scalar_contraction
