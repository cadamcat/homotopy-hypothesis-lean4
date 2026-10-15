import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeCones
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Original supports of relative derived points

A mixture with nonzero coefficients has support equal to the union of its
source supports. For an admissible relative derived tuple, that union is
the vertex set of its least original carrier. Equal mixtures therefore
determine the same original carrier.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Nonzero coefficients preserve the union of supports in an affine mixture. -/
theorem affineMapMk_weights_ne_zero_iff {n : ℕ} {M : Type v}
    (q : Fin (n + 1) → StdSimplex ℝ M) (t : StdSimplex ℝ (Fin (n + 1)))
    (ht : ∀ i, t.weights i ≠ 0) (w : M) :
    (StdSimplex.affineMapMk (R := ℝ) q t).weights w ≠ 0 ↔
      ∃ i, (q i).weights w ≠ 0 := by
  classical
  rw [affineMapMk_weights_apply]
  constructor
  · intro h
    by_contra hn
    apply h
    apply Finset.sum_eq_zero
    intro i _
    have hi : (q i).weights w = 0 := by
      by_contra hi
      exact hn ⟨i, hi⟩
    rw [hi, mul_zero]
  · rintro ⟨i, hi⟩
    have hpos : 0 < t.weights i * (q i).weights w :=
      mul_pos (lt_of_le_of_ne (t.weights_nonneg i) (Ne.symm (ht i)))
        (lt_of_le_of_ne ((q i).weights_nonneg w) (Ne.symm hi))
    have hle : t.weights i * (q i).weights w ≤
        ∑ j, t.weights j * (q j).weights w :=
      Finset.single_le_sum (fun j _ =>
        mul_nonneg (t.weights_nonneg j) ((q j).weights_nonneg w)) (Finset.mem_univ i)
    exact ne_of_gt (lt_of_lt_of_le hpos hle)

/-- A tuple ending in a retained vertex is the retained image of a simplex of the subcomplex. -/
theorem relativeTuple_retained_of_last {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hlast : a.val (Fin.last n) = .inl v) :
    ∃ x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n)),
      a = (relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x := by
  let w : Fin (n + 1) → L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
    fun i => match a.val i with | .inl z => z | .inr _ => v
  have hw (i : Fin (n + 1)) : a.val i = .inl (w i) := by
    by_cases hi : i = Fin.last n
    · subst i
      simp only [w, hlast]
    · have hp := a.property.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
      cases he : a.val i with
      | inl z => simp only [w, he]
      | inr s => simp only [he, hlast, RelativeVertex.Precedes] at hp
  obtain ⟨x, hx⟩ := a.property.2.2 n (𝟙 _) w hw
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  exact (hw i).trans (congrArg Sum.inl (hx i).symm)

/-- A tuple ending in an exterior face is carried by that face. -/
theorem relativeTuple_carried_of_last_exterior {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hlast : a.val (Fin.last n) = .inr s) :
    ∀ i, RelativeVertex.CarriedBy (a.val i) s.val.2 := by
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    rw [hlast]
    exact ⟨𝟙 _, by simp⟩
  · have hp := a.property.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
    rw [hlast] at hp
    cases he : a.val i with
    | inl v =>
      simpa only [he, RelativeVertex.Precedes, RelativeVertex.CarriedBy] using hp
    | inr t =>
      simp only [he, RelativeVertex.Precedes] at hp
      exact hp.2

/-- The union of an admissible tuple's source supports is its least carrier's vertex support. -/
theorem relativeTuple_source_support_iff_carrier {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    (∃ i, w ∈ Set.range (vertex (a.val i).sourceSimplex.2)) ↔
      w ∈ Set.range (vertex (leastRelativeCarrier hK a).2) := by
  constructor
  · rintro ⟨i, hi⟩
    exact source_vertex_range_subset_of_carried (leastRelativeCarrier hK a).2
      (a.val i) ((leastRelativeCarrier_spec hK a).1 i) hi
  · intro hw
    cases hlast : a.val (Fin.last n) with
    | inr s =>
      have hs := relativeTuple_carried_of_last_exterior a s hlast
      have hsub := (vertex_range_subset_iff_existsUnique_faceMap hK
        (leastRelativeCarrier hK a).2 s.val.2).mpr
          ((leastRelativeCarrier_spec hK a).2 s.val hs)
      refine ⟨Fin.last n, ?_⟩
      rw [hlast]
      exact hsub hw
    | inl v =>
      obtain ⟨x, hx⟩ := relativeTuple_retained_of_last hK a v hlast
      subst a
      let b := (relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x
      have hsub := (vertex_range_subset_iff_existsUnique_faceMap hK
        (leastRelativeCarrier hK b).2 x.val).mpr
          ((leastRelativeCarrier_spec hK b).2 ⟨n, x.val⟩ (retainedTuple_carried hK L x))
      obtain ⟨i, hi⟩ := hsub hw
      refine ⟨i, 0, ?_⟩
      change vertex (vertex x i).val 0 = w
      exact (vertex_zero (vertex x i).val).trans hi

/-- A nonzero derived representative has support exactly the vertices of its least carrier. -/
theorem relativeDistribution_weights_ne_zero_iff_carrier {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) (ht : ∀ i, t.weights i ≠ 0)
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    (relativeDistributionAffineMap a t).weights w ≠ 0 ↔
      w ∈ Set.range (vertex (leastRelativeCarrier hK a).2) := by
  change (StdSimplex.affineMapMk (R := ℝ)
    (fun i => relativeVertexDistribution (a.val i)) t).weights w ≠ 0 ↔ _
  rw [affineMapMk_weights_ne_zero_iff _ t ht]
  simp_rw [relativeVertexDistribution_weights_ne_zero_iff hK]
  exact relativeTuple_source_support_iff_carrier hK a w

/-- Equal original vertex supports identify simplices together with their dimensions. -/
theorem simplex_eq_of_vertex_range_eq_sigma {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (s t : Simplex K) (h : Set.range (vertex s.2) = Set.range (vertex t.2)) : s = t := by
  obtain ⟨n, x⟩ := s
  obtain ⟨m, y⟩ := t
  obtain ⟨θ, _⟩ := exists_faceMap_of_vertex_range_subset hK x y h.subset
  obtain ⟨η, _⟩ := exists_faceMap_of_vertex_range_subset hK y x h.symm.subset
  have hnm := Fintype.card_le_of_injective θ.hom.toOrderHom
    (SimplexCategory.mono_iff_injective.mp θ.property)
  have hmn := Fintype.card_le_of_injective η.hom.toOrderHom
    (SimplexCategory.mono_iff_injective.mp η.property)
  simp only [Fintype.card_fin] at hnm hmn
  have hdim : n = m := by omega
  subst m
  exact congrArg (fun z => (⟨n, z⟩ : Simplex K)) (simplex_eq_of_vertex_range_eq hK h)

/-- Equal distributions of nonzero relative representatives determine the same least carrier. -/
theorem leastRelativeCarrier_eq_of_distribution_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (t : StdSimplex ℝ (Fin (n + 1))) (p : StdSimplex ℝ (Fin (m + 1)))
    (ht : ∀ i, t.weights i ≠ 0) (hp : ∀ i, p.weights i ≠ 0)
    (h : relativeDistributionAffineMap a t = relativeDistributionAffineMap b p) :
    leastRelativeCarrier hK a = leastRelativeCarrier hK b := by
  apply simplex_eq_of_vertex_range_eq_sigma hK
  ext w
  rw [← relativeDistribution_weights_ne_zero_iff_carrier hK a t ht,
    ← relativeDistribution_weights_ne_zero_iff_carrier hK b p hp, h]

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDistribution_weights_ne_zero_iff_carrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.leastRelativeCarrier_eq_of_distribution_eq
