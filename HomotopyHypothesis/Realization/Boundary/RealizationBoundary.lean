import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
import HomotopyHypothesis.Realization.Boundary.SimplexDisk
import HomotopyHypothesis.Simplicial.CycleRealization.BoundaryMono
/-!
# The realized boundary of a semi-simplicial simplex

The boundary presheaf is realized as a compact subspace of the standard topological simplex.
-/

universe u

open CategoryTheory Limits
open Convexity
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Boundary

/-- Barycentric coordinates in the universe of the topological realization. -/
abbrev LiftedClosedCoordSimplex (n : ℕ) := ULift.{u} (ClosedCoordSimplex n)

/-- The closed coordinate simplex as a subset of its ambient vector space. -/
def closedCoordSimplexSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The sum of coordinates is a continuous linear map. -/
noncomputable def closedCoordSumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

@[simp]
theorem closedCoordSumCLM_apply (n : ℕ) (x : Fin n → ℝ) :
    closedCoordSumCLM n x = ∑ i, x i := by
  simp [closedCoordSumCLM]

/-- The coordinate simplex is a closed convex bounded subset of its ambient vector space. -/
theorem closedCoordSimplexSet_closed (n : ℕ) : IsClosed (closedCoordSimplexSet n) := by
  have hset : closedCoordSimplexSet n =
      (⋂ i : Fin n, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) ⁻¹' Set.Ici 0) ∩
        (closedCoordSumCLM n) ⁻¹' Set.Iic 1 := by
    ext x
    simp [closedCoordSimplexSet, closedCoordSumCLM_apply]
  rw [hset]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_Ici.preimage (ContinuousLinearMap.continuous _)
  · exact isClosed_Iic.preimage (closedCoordSumCLM n).continuous

theorem closedCoordSimplexSet_convex (n : ℕ) : Convex ℝ (closedCoordSimplexSet n) := by
  apply (convex_iff_add_mem).2
  intro x hx y hy a b ha hb hab
  simp only [closedCoordSimplexSet, Set.mem_setOf_eq] at hx hy ⊢
  constructor
  · intro i
    simp only [Pi.add_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · have hsum : (∑ i : Fin n, (a • x + b • y) i) =
        a * (∑ i : Fin n, x i) + b * (∑ i : Fin n, y i) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, Pi.add_apply, smul_eq_mul]
    rw [hsum]
    nlinarith

theorem closedCoordSimplexSet_isBounded (n : ℕ) : Bornology.IsBounded (closedCoordSimplexSet n) := by
  apply (Bornology.IsBounded.pi fun _ : Fin n => Metric.isBounded_Icc (0 : ℝ) 1).subset
  intro x hx
  change (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 at hx
  simp only [Set.mem_pi]
  intro i _
  refine ⟨hx.1 i, ?_⟩
  have hi_le_sum : x i ≤ ∑ j : Fin n, x j :=
    Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  linarith [hx.2]

/-- Recover all barycentric weights from the coordinates with the last one omitted. -/
noncomputable def closedCoordBarycentricWeights (n : ℕ) (x : ClosedCoordSimplex n) :
    Fin (n + 1) → ℝ :=
  fun i => (stdSimplexCoordsEquiv n).symm x |>.weights i

/-- Interior points of a nonzero-dimensional coordinate simplex are exactly the points with all
coordinates and the omitted coordinate strictly positive. -/
theorem interior_closedCoordSimplexSet {n : ℕ} (hn : 0 < n) :
    interior (closedCoordSimplexSet n) =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  have hset : closedCoordSimplexSet n =
      (⋂ i : Fin n, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) ⁻¹' Set.Ici 0) ∩
        (closedCoordSumCLM n) ⁻¹' Set.Iic 1 := by
    ext x
    simp [closedCoordSimplexSet, closedCoordSumCLM_apply]
  rw [hset, interior_inter, interior_iInter_of_finite]
  have hprojOpen (i : Fin n) :
      IsOpenMap (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
    apply (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).isOpenMap_of_finiteDimensional
    intro y
    refine ⟨Pi.single i y, ?_⟩
    simp
  have hsumOpen : IsOpenMap (closedCoordSumCLM n) := by
    apply (closedCoordSumCLM n).isOpenMap_of_finiteDimensional
    intro y
    refine ⟨Pi.single ⟨0, hn⟩ y, ?_⟩
    simp [closedCoordSumCLM_apply]
  simp only [← (hprojOpen _).preimage_interior_eq_interior_preimage (by fun_prop),
    ← hsumOpen.preimage_interior_eq_interior_preimage (by fun_prop), interior_Ici,
    interior_Iic]
  ext x
  simp [closedCoordSumCLM_apply]

/-- A positive-dimensional coordinate simplex is carried to the standard Euclidean ball by an
ambient homeomorphism, and its frontier is carried to the unit sphere. -/
theorem exists_closedCoord_disk_homeomorph {n : ℕ} (hn : 0 < n) :
    ∃ g : (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n),
      g '' closedCoordSimplexSet n = Metric.closedBall 0 1 ∧
        g '' frontier (closedCoordSimplexSet n) = Metric.sphere 0 1 := by
  let e : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  let eHomeo : (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n) := e.toHomeomorph
  let sE : Set (EuclideanSpace ℝ (Fin n)) := e '' closedCoordSimplexSet n
  have hconv : Convex ℝ sE := by
    dsimp [sE]
    exact (closedCoordSimplexSet_convex n).linear_image e.toLinearEquiv.toLinearMap
  have hbound : Bornology.IsBounded sE := by
    dsimp [sE]
    exact (closedCoordSimplexSet_isBounded n).image e.toContinuousLinearMap
  have hne : (interior sE).Nonempty := by
    have hcoord : (interior (closedCoordSimplexSet n)).Nonempty := by
      refine ⟨fun _ => (1 : ℝ) / (n + 1), ?_⟩
      rw [interior_closedCoordSimplexSet hn]
      constructor
      · intro i
        positivity
      · have hsum : (∑ _i : Fin n, (1 : ℝ) / (n + 1)) = (n : ℝ) / (n + 1) := by
          simp [div_eq_mul_inv]
        rw [hsum]
        apply (div_lt_one (by positivity)).2
        exact_mod_cast Nat.lt_succ_self n
    obtain ⟨x, hx⟩ := hcoord
    change (interior (eHomeo '' closedCoordSimplexSet n)).Nonempty
    rw [← eHomeo.image_interior (closedCoordSimplexSet n)]
    exact ⟨e x, ⟨x, hx, rfl⟩⟩
  obtain ⟨h, _, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbound
  let g := eHomeo.trans h
  have hclosedCoord : IsClosed (closedCoordSimplexSet n) := closedCoordSimplexSet_closed n
  have hclosedE : closure sE = sE := by
    change closure (eHomeo '' closedCoordSimplexSet n) = eHomeo '' closedCoordSimplexSet n
    rw [← eHomeo.image_closure (closedCoordSimplexSet n), hclosedCoord.closure_eq]
  have htransImage (t : Set (Fin n → ℝ)) :
      (eHomeo.trans h) '' t = h '' (eHomeo '' t) := by
    ext z
    simp
  refine ⟨g, ?_, ?_⟩
  · calc
      g '' closedCoordSimplexSet n = h '' sE := by
        rw [show g = eHomeo.trans h from rfl, htransImage]
        rfl
      _ = h '' closure sE := by rw [hclosedE]
      _ = Metric.closedBall 0 1 := hclosure
  · calc
      g '' frontier (closedCoordSimplexSet n) = h '' frontier sE := by
        rw [show g = eHomeo.trans h from rfl, htransImage, eHomeo.image_frontier]
        rfl
      _ = Metric.sphere 0 1 := hfrontier

/-- Restrict the coordinate rescaling to the frontier of the simplex. -/
noncomputable def closedCoordFrontierToSphereHomeomorph_pos {n : ℕ} (hn : 0 < n) :
    {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)} ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ∈ Metric.sphere 0 1} := by
  classical
  let hg := exists_closedCoord_disk_homeomorph hn
  let g := Classical.choose hg
  have hprops := Classical.choose_spec hg
  have hfrontier : g '' frontier (closedCoordSimplexSet n) = Metric.sphere 0 1 := hprops.2
  refine g.subtype ?_
  intro x
  constructor
  · intro hx
    rw [← hfrontier]
    exact ⟨x, hx, rfl⟩
  · intro hy
    have hx : g x ∈ g '' frontier (closedCoordSimplexSet n) := by
      rw [hfrontier]
      exact hy
    rcases hx with ⟨y, hy, hxy⟩
    have : y = x := g.injective hxy
    simpa [this] using hy

/-- Restrict the coordinate rescaling to the closed simplex. -/
noncomputable def closedCoordToDiskHomeomorph_pos {n : ℕ} (hn : 0 < n) :
    ClosedCoordSimplex n ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ∈ Metric.closedBall 0 1} := by
  classical
  let hg := exists_closedCoord_disk_homeomorph hn
  let g := Classical.choose hg
  have hprops := Classical.choose_spec hg
  have hball : g '' closedCoordSimplexSet n = Metric.closedBall 0 1 := hprops.1
  refine g.subtype ?_
  intro x
  change x ∈ closedCoordSimplexSet n ↔ g x ∈ Metric.closedBall 0 1
  constructor
  · intro hx
    rw [← hball]
    exact ⟨x, hx, rfl⟩
  · intro hy
    have hx : g x ∈ g '' closedCoordSimplexSet n := by
      rw [hball]
      exact hy
    rcases hx with ⟨y, hy, hxy⟩
    have : y = x := g.injective hxy
    simpa [this] using hy

theorem closedCoordFrontier_isEmpty_zero :
    IsEmpty {x : Fin 0 → ℝ // x ∈ frontier (closedCoordSimplexSet 0)} := by
  refine ⟨fun x => ?_⟩
  have hset : closedCoordSimplexSet 0 = Set.univ := by
    ext z
    simp [closedCoordSimplexSet]
  have hfront : frontier (closedCoordSimplexSet 0) = ∅ := by
    rw [hset]
    simp
  have hx : x.1 ∈ (∅ : Set (Fin 0 → ℝ)) := by simpa [hfront] using x.2
  exact hx

theorem euclideanUnitSphere_isEmpty_zero :
    IsEmpty {x : EuclideanSpace ℝ (Fin 0) // x ∈ Metric.sphere 0 1} := by
  refine ⟨fun x => ?_⟩
  have hx : x.1 = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  have hmem : (0 : EuclideanSpace ℝ (Fin 0)) ∈ Metric.sphere 0 1 := by
    simpa [hx] using x.2
  norm_num [Metric.sphere] at hmem

/-- The frontier of the zero-dimensional coordinate simplex is the empty zero-sphere. -/
noncomputable def closedCoordFrontierToSphereHomeomorph (n : ℕ) :
    {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)} ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ∈ Metric.sphere 0 1} := by
  cases n with
  | zero =>
    letI : IsEmpty {x : Fin 0 → ℝ // x ∈ frontier (closedCoordSimplexSet 0)} :=
      closedCoordFrontier_isEmpty_zero
    letI : IsEmpty {x : EuclideanSpace ℝ (Fin 0) // x ∈ Metric.sphere 0 1} :=
      euclideanUnitSphere_isEmpty_zero
    exact {
      toEquiv := Equiv.equivOfIsEmpty _ _
      continuous_toFun := continuous_empty_function _
      continuous_invFun := continuous_empty_function _ }
  | succ n => exact closedCoordFrontierToSphereHomeomorph_pos (Nat.succ_pos n)

/-- The zero-dimensional coordinate simplex is a point, hence a zero-disk. -/
noncomputable def closedCoordToDiskHomeomorph (n : ℕ) :
    ClosedCoordSimplex n ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ∈ Metric.closedBall 0 1} := by
  cases n with
  | zero =>
    letI : Unique (ClosedCoordSimplex 0) := {
      default := ⟨fun i => Fin.elim0 i, by simp⟩
      uniq := fun x => Subtype.ext (funext fun i => Fin.elim0 i) }
    letI : Unique {x : EuclideanSpace ℝ (Fin 0) // x ∈ Metric.closedBall 0 1} := {
      default := ⟨0, by simp [Metric.mem_closedBall]⟩
      uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
    exact Homeomorph.homeomorphOfUnique _ _
  | succ n => exact closedCoordToDiskHomeomorph_pos (Nat.succ_pos n)

/-- Flatten the frontier subtype of the coordinate simplex to the ambient frontier subtype. -/
noncomputable def closedCoordFrontierSubtypeHomeomorph (n : ℕ) :
    {x : ClosedCoordSimplex n // x.1 ∈ frontier (closedCoordSimplexSet n)} ≃ₜ
      {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)} := by
  have hfrontier_subset : ∀ {x}, x ∈ frontier (closedCoordSimplexSet n) →
      x ∈ closedCoordSimplexSet n := by
    intro x hx
    have hxcl : x ∈ closure (closedCoordSimplexSet n) := frontier_subset_closure hx
    rw [(closedCoordSimplexSet_closed n).closure_eq] at hxcl
    exact hxcl
  let e :
      {x : ClosedCoordSimplex n // x.1 ∈ frontier (closedCoordSimplexSet n)} ≃
        {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)} :=
    Equiv.subtypeSubtypeEquivSubtype
      (α := Fin n → ℝ)
      (p := fun x => x ∈ closedCoordSimplexSet n)
      (q := fun x => x ∈ frontier (closedCoordSimplexSet n)) hfrontier_subset
  refine { toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous (fun z :
      {x : ClosedCoordSimplex n // x.1 ∈ frontier (closedCoordSimplexSet n)} =>
        (⟨z.1.1, z.2⟩ : {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)}))
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  · change Continuous (fun z :
      {x : Fin n → ℝ // x ∈ frontier (closedCoordSimplexSet n)} =>
        (⟨⟨z.1, hfrontier_subset z.2⟩, z.2⟩ :
          {x : ClosedCoordSimplex n // x.1 ∈ frontier (closedCoordSimplexSet n)}))
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val _) (fun z => z.2)

/-- The realization's ULifted coordinate simplex is homeomorphic to the disk object. -/
noncomputable def liftedClosedCoordToDiskHomeomorph (n : ℕ) :
    LiftedClosedCoordSimplex n ≃ₜ TopCat.disk.{u} n := by
  exact (Homeomorph.ulift.trans (closedCoordToDiskHomeomorph n)).trans Homeomorph.ulift.symm

/-- The ULifted coordinate frontier is homeomorphic to the disk boundary object. -/
noncomputable def liftedClosedCoordFrontierToDiskBoundaryHomeomorph (n : ℕ) :
    {z : LiftedClosedCoordSimplex n // z.down.1 ∈ frontier (closedCoordSimplexSet n)} ≃ₜ
      TopCat.diskBoundary.{u} n := by
  let hULift : ULift.{u} (ClosedCoordSimplex n) ≃ₜ ClosedCoordSimplex n := Homeomorph.ulift
  let hfront :
      {z : LiftedClosedCoordSimplex n // z.down.1 ∈ frontier (closedCoordSimplexSet n)} ≃ₜ
        {x : ClosedCoordSimplex n // x.1 ∈ frontier (closedCoordSimplexSet n)} :=
    hULift.subtype
      (p := fun z => z.down.1 ∈ frontier (closedCoordSimplexSet n))
      (q := fun x : ClosedCoordSimplex n => x.1 ∈ frontier (closedCoordSimplexSet n))
      (by intro z; rfl)
  exact ((hfront.trans (closedCoordFrontierSubtypeHomeomorph n)).trans
    (closedCoordFrontierToSphereHomeomorph n)).trans Homeomorph.ulift.symm

@[simp]
theorem closedCoordBarycentricWeights_castSucc (n : ℕ) (x : ClosedCoordSimplex n)
    (i : Fin n) : closedCoordBarycentricWeights n x i.castSucc = x.1 i := by
  simp [closedCoordBarycentricWeights, stdSimplexCoordsEquiv]

@[simp]
theorem closedCoordBarycentricWeights_last (n : ℕ) (x : ClosedCoordSimplex n) :
    closedCoordBarycentricWeights n x (Fin.last n) = 1 - ∑ i, x.1 i := by
  simp [closedCoordBarycentricWeights, stdSimplexCoordsEquiv]

/-- A point of positive dimension lies outside the interior of the coordinate simplex exactly
when one of its barycentric weights vanishes. -/
theorem closedCoordBarycentricWeights_exists_zero_iff_not_mem_interior {n : ℕ} (hn : 0 < n)
    (x : ClosedCoordSimplex n) :
    (∃ i, closedCoordBarycentricWeights n x i = 0) ↔
      (x.1 ∉ interior (closedCoordSimplexSet n)) := by
  rw [interior_closedCoordSimplexSet hn]
  constructor
  · rintro ⟨i, hi⟩ hstrict
    cases i using Fin.lastCases with
    | last =>
        rw [closedCoordBarycentricWeights_last] at hi
        linarith [hstrict.2]
    | cast j =>
        rw [closedCoordBarycentricWeights_castSucc] at hi
        linarith [hstrict.1 j]
  · intro hnot
    by_cases hpos : ∀ i, 0 < x.1 i
    · have hsum : (∑ i, x.1 i) = 1 := by
        by_contra hne
        have hlt : (∑ i, x.1 i) < 1 := lt_of_le_of_ne x.2.2 hne
        exact hnot ⟨hpos, hlt⟩
      refine ⟨Fin.last n, ?_⟩
      rw [closedCoordBarycentricWeights_last]
      linarith
    · push_neg at hpos
      obtain ⟨i, hi⟩ := hpos
      have hi0 : x.1 i = 0 := by linarith [x.2.1 i]
      exact ⟨i.castSucc, by simpa using hi0⟩

/-- The zero-weight locus is the frontier of the closed coordinate simplex. -/
theorem closedCoordBarycentricWeights_exists_zero_iff_mem_frontier_pos {n : ℕ} (hn : 0 < n)
    (x : ClosedCoordSimplex n) :
    (∃ i, closedCoordBarycentricWeights n x i = 0) ↔
      x.1 ∈ frontier (closedCoordSimplexSet n) := by
  have hset : closedCoordSimplexSet n =
      (⋂ i : Fin n, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) ⁻¹' Set.Ici 0) ∩
        (closedCoordSumCLM n) ⁻¹' Set.Iic 1 := by
    ext z
    simp [closedCoordSimplexSet, closedCoordSumCLM_apply]
  have hclosed : IsClosed (closedCoordSimplexSet n) := by
    rw [hset]
    apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_Ici.preimage (ContinuousLinearMap.continuous _)
    · exact isClosed_Iic.preimage (closedCoordSumCLM n).continuous
  rw [frontier, hclosed.closure_eq]
  simp only [Set.mem_sdiff]
  constructor
  · intro hz
    exact ⟨x.2, (closedCoordBarycentricWeights_exists_zero_iff_not_mem_interior hn x).mp hz⟩
  · rintro ⟨hx, hnot⟩
    exact (closedCoordBarycentricWeights_exists_zero_iff_not_mem_interior hn x).mpr hnot

/-- The zero-weight locus is the frontier of the closed coordinate simplex in every dimension. -/
theorem closedCoordBarycentricWeights_exists_zero_iff_mem_frontier (n : ℕ)
    (x : ClosedCoordSimplex n) :
    (∃ i, closedCoordBarycentricWeights n x i = 0) ↔
      x.1 ∈ frontier (closedCoordSimplexSet n) := by
  cases n with
  | zero =>
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      let t : StdSimplex ℝ (Fin 1) := (stdSimplexCoordsEquiv 0).symm x
      have ht : t.weights 0 = 0 := by
        simpa [t, closedCoordBarycentricWeights] using hi
      have htotal : t.weights 0 = 1 := by simpa using t.total_of_fintype
      rw [ht] at htotal
      norm_num at htotal
    · intro hx
      have hset : closedCoordSimplexSet 0 = Set.univ := by
        ext z
        simp [closedCoordSimplexSet]
      simpa [hset] using hx
  | succ n =>
    exact closedCoordBarycentricWeights_exists_zero_iff_mem_frontier_pos (by omega) x

/-- A missing vertex in a simplex map has zero barycentric weight in its image. -/
theorem stdSimplexMap_weight_eq_zero_of_not_mem_range
    {c : HomotopyHypothesis.Henry.SemiSimplexCategory} {n : ℕ}
    (f : c ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
    (s : StdSimplex ℝ (Fin (c.obj.len + 1)))
    (i : Fin (n + 1))
    (hi : i ∉ Set.range
      ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom)) :
    closedCoordBarycentricWeights n
      (stdSimplexCoordsEquiv n (StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s)) i = 0 := by
  rw [closedCoordBarycentricWeights, Equiv.symm_apply_apply]
  change Finsupp.mapDomain
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s.weights i = 0
  exact Finsupp.mapDomain_of_notMem_range s.weights i hi

/-- A simplex point with a zero coordinate is in the image of the opposite face map. -/
theorem exists_stdSimplex_preimage_face {n : ℕ} (i : Fin (n + 2))
    (t : StdSimplex ℝ (Fin (n + 2))) (ht : t.weights i = 0) :
    ∃ s : StdSimplex ℝ (Fin (n + 1)),
      StdSimplex.map (Fin.succAboveOrderEmb i) s = t := by
  classical
  let g : Fin (n + 1) → Fin (n + 2) := Fin.succAboveOrderEmb i
  have hg : Function.Injective g := (Fin.succAboveOrderEmb i).injective
  have hsupport : (t.weights.support : Set (Fin (n + 2))) ⊆ Set.range g := by
    intro k hk
    by_cases hki : k = i
    · subst k
      exact False.elim ((Finsupp.mem_support_iff.mp hk) ht)
    · change k ∈ Set.range (Fin.succAboveOrderEmb i)
      rw [Fin.range_succAboveOrderEmb]
      simp [hki]
  let w : Fin (n + 1) →₀ ℝ := Finsupp.comapDomain g t.weights hg.injOn
  have hmap : Finsupp.mapDomain g w = t.weights :=
    Finsupp.mapDomain_comapDomain g hg t.weights hsupport
  refine ⟨⟨w, ?_, ?_⟩, ?_⟩
  · intro j
    change 0 ≤ t.weights (g j)
    exact t.weights_nonneg (g j)
  · have hsum : (Finsupp.mapDomain g w).sum (fun _ r => r) = w.sum (fun _ r => r) := by
      simp [Finsupp.sum_mapDomain_index]
    rw [hmap] at hsum
    simpa [t.total] using hsum.symm
  · apply StdSimplex.ext
    ext k
    change (Finsupp.mapDomain g w) k = t.weights k
    exact congrArg (fun v : Fin (n + 2) →₀ ℝ => v k) hmap

/-- A density-cocone leg for a representable simplex is the map induced by its element. -/
theorem stdSimplexCoconeLeg_eq_map (n : ℕ)
    (e : (SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).Elements) :
    ((Presheaf.coconeOfRepresentable (SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))).ι.app (Opposite.op e)) =
        SemiSSet.stdSimplex.map e.val.down := by
  ext d x
  apply ULift.ext
  dsimp [Presheaf.coconeOfRepresentable, Presheaf.functorToRepresentables,
    SemiSSet.stdSimplex, uliftYonedaEquiv, uliftYoneda]
  rfl

/-- Composing the density-cocone leg of a boundary simplex with the boundary inclusion gives
the representable map named by that simplex. -/
theorem boundaryRepresentableMap_eq_stdSimplexMap (n : ℕ)
    (e : (SemiSSet.boundary.{u} n).toFunctor.Elements) :
    (Presheaf.coconeOfRepresentable (SemiSSet.boundary.{u} n).toFunctor).ι.app (Opposite.op e) ≫
      (SemiSSet.boundary n).ι =
        SemiSSet.stdSimplex.map e.val.val.down := by
  let P := (SemiSSet.boundary.{u} n).toFunctor
  let Q := SemiSSet.stdSimplex.{u}.obj
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  let e' : Q.Elements := (SemiSSet.boundary n).ι.mapElements.obj e
  have hNat := Presheaf.coconeOfRepresentable_naturality (SemiSSet.boundary n).ι (Opposite.op e)
  have hval : e'.val.down = e.val.val.down := by
    dsimp [e', NatTrans.mapElements]
    rfl
  have h1 : (Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e) ≫
      (SemiSSet.boundary n).ι =
        (Presheaf.coconeOfRepresentable Q).ι.app (Opposite.op e') := by
    simpa [P, Q, e'] using hNat
  have h2 := stdSimplexCoconeLeg_eq_map n e'
  rw [hval] at h2
  exact h1.trans h2

/-- The realization of the representable simplex is homeomorphic to its barycentric-coordinate
model with the last coordinate omitted. -/
noncomputable def toTopSimplexCoordsIso
    (c : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    SemiSSet.toTop.{u}.obj c ≅ TopCat.of (LiftedClosedCoordSimplex c.obj.len) :=
  TopCat.isoOfHomeo
    ((Homeomorph.ulift.trans (stdSimplexCoordsHomeomorph c.obj.len)).trans Homeomorph.ulift.symm)

noncomputable def realizationRepresentableCoordsIso
    (c : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c) ≅
      TopCat.of (LiftedClosedCoordSimplex c.obj.len) :=
  realization_representable_iso c ≪≫ toTopSimplexCoordsIso c

noncomputable def realizationSimplexCoordsIso (n : ℕ) :
    SemiSSet.realization.{u}.obj
      (SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ≅
      TopCat.of (LiftedClosedCoordSimplex n) :=
  realizationRepresentableCoordsIso (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)

/-- The coordinate homeomorphism sends a face map to its affine barycentric map. -/
theorem toTopSimplexCoordsIso_map
    {c d : HomotopyHypothesis.Henry.SemiSimplexCategory} (f : c ⟶ d)
    (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    (toTopSimplexCoordsIso d).hom.hom
        ((SemiSSet.toTop.{u}.map f).hom (ULift.up s)) =
      ULift.up (stdSimplexCoordsEquiv d.obj.len (StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s)) := by
  rfl

/-- Realizing a representable map and then taking coordinates is the corresponding topological
map followed by the target coordinates. -/
theorem realizationRepresentableCoordsIso_map
    {c d : HomotopyHypothesis.Henry.SemiSimplexCategory} (f : c ⟶ d) :
    SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationRepresentableCoordsIso d).hom =
      (realization_representable_iso c).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso d).hom := by
  have hNat : SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realization_representable_iso d).hom =
      (realization_representable_iso c).hom ≫ SemiSSet.toTop.{u}.map f := by
    simpa [realization_representable_iso, SemiSSet.realization] using
      (Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1}
        (SemiSSet.toTop.{u})).hom.naturality f
  calc
    SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationRepresentableCoordsIso d).hom =
      (SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realization_representable_iso d).hom) ≫ (toTopSimplexCoordsIso d).hom := by
          rfl
    _ = (realization_representable_iso c).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso d).hom := by
          rw [← Category.assoc, hNat]

/-- The canonical map from the realized boundary to barycentric coordinates on the simplex. -/
noncomputable def boundaryRealizationToCoords (n : ℕ) :
    SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor ⟶
      TopCat.of (LiftedClosedCoordSimplex n) :=
  SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι ≫
    (realizationSimplexCoordsIso n).hom

/-- Every point in the realized boundary has a zero barycentric coordinate. -/
theorem boundaryRealizationToCoords_hasZeroWeight (n : ℕ)
    (x : SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) :
    ∃ i : Fin (n + 1),
      closedCoordBarycentricWeights n
        (ULift.down ((boundaryRealizationToCoords n).hom x)) i = 0 := by
  classical
  let P := (SemiSSet.boundary.{u} n).toFunctor
  let D := Presheaf.functorToRepresentables P ⋙ SemiSSet.realization.{u}
  let c := SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable P)
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1} SemiSSet.realization := by
    change PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1}
      (SemiSSet.stdSimplex.{u}.leftKanExtension SemiSSet.toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      (A := SemiSSet.toTop.{u})
  have hc : IsColimit c :=
    isColimitOfPreserves SemiSSet.realization.{u} (Presheaf.colimitOfRepresentable P)
  have hcol : IsColimit ((forget TopCat).mapCocone c) := isColimitOfPreserves (forget TopCat) hc
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol x
  let e : P.Elements := j.unop
  let c₀ : HomotopyHypothesis.Henry.SemiSimplexCategory :=
    ((Functor.Elements.π P).obj e).unop
  change SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c₀) at y
  let f : c₀ ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n := e.val.val.down
  obtain ⟨i, hi⟩ := e.val.property
  have hmissing : i ∉ Set.range
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom := by
    rintro ⟨a, ha⟩
    exact hi ⟨a, ha⟩
  have hC : c.ι.app j = SemiSSet.realization.{u}.map
      ((Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e)) := rfl
  have hfactor : c.ι.app j ≫ SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι =
      SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) := by
    rw [hC]
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg (SemiSSet.realization.{u}.map)
        (boundaryRepresentableMap_eq_stdSimplexMap n e))
  have htoCoords : c.ι.app j ≫ boundaryRealizationToCoords n =
      SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom := by
    change c.ι.app j ≫
      (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι ≫
        (realizationSimplexCoordsIso n).hom) = _
    rw [← Category.assoc, hfactor]
    rfl
  have hy' : (c.ι.app j).hom y = x := by
    simpa using hy
  let s : StdSimplex ℝ (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c₀).len + 1)) :=
    ULift.down ((realization_representable_iso c₀).hom.hom y)
  refine ⟨i, ?_⟩
  have hEval := congrArg
    (fun g : D.obj j ⟶ TopCat.of (LiftedClosedCoordSimplex n) => g.hom y) htoCoords
  have hEval' : (boundaryRealizationToCoords n).hom x =
      ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom).hom y) := by
    have hEval2 : (boundaryRealizationToCoords n).hom ((c.ι.app j).hom y) =
        (realizationSimplexCoordsIso n).hom.hom
          ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f)).hom y) := by
      change (c.ι.app j ≫ boundaryRealizationToCoords n).hom y =
        (SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
          (realizationSimplexCoordsIso n).hom).hom y
      exact hEval
    rw [hy'] at hEval2
    exact hEval2
  have hIsoEval :
      ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom).hom y) =
      (((realization_representable_iso c₀).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom).hom y) := by
    exact congrArg
      (fun g : SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c₀) ⟶
        TopCat.of (LiftedClosedCoordSimplex n) => g.hom y)
      (realizationRepresentableCoordsIso_map f)
  have hs : (realization_representable_iso c₀).hom.hom y = ULift.up s := by
    apply ULift.ext
    rfl
  have htopEval :
      (toTopSimplexCoordsIso
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)) =
        ULift.up (stdSimplexCoordsEquiv n (StdSimplex.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s)) := by
    calc
      (toTopSimplexCoordsIso
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
            ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)) =
          (toTopSimplexCoordsIso
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
              ((SemiSSet.toTop.{u}.map f).hom (ULift.up s)) := by
                exact congrArg
                  (fun z => (toTopSimplexCoordsIso
                    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
                    ((SemiSSet.toTop.{u}.map f).hom z)) hs
      _ = _ := toTopSimplexCoordsIso_map f s
  rw [hEval', hIsoEval]
  change closedCoordBarycentricWeights n
      (ULift.down ((toTopSimplexCoordsIso
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
        ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)))) i = 0
  rw [htopEval]
  exact stdSimplexMap_weight_eq_zero_of_not_mem_range f s i hmissing

/-- The realized boundary contains the image of each codimension-one face. -/
theorem boundaryRealizationToCoords_face {m : ℕ} (i : Fin (m + 2))
    (s : StdSimplex ℝ (Fin (m + 1))) :
    ∃ x : SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} (m + 1)).toFunctor,
      (boundaryRealizationToCoords (m + 1)).hom x =
        ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s)) := by
  classical
  let c := HomotopyHypothesis.Henry.SemiSimplexCategory.mk m
  let d := HomotopyHypothesis.Henry.SemiSimplexCategory.mk (m + 1)
  let face : SimplexCategory.mk m ⟶ SimplexCategory.mk (m + 1) :=
    SimplexCategory.Hom.mk (Fin.succAboveOrderEmb i).toOrderHom
  have hfaceMono : Mono face := by
    change Mono (SimplexCategory.δ i)
    infer_instance
  let f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk (m + 1) :=
    ⟨face, hfaceMono⟩
  have hmissing : i ∉ Set.range (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom := by
    change i ∉ Set.range face.toOrderHom
    simp [face, SimplexCategory.Hom.toOrderHom_mk, Fin.range_succAboveOrderEmb]
  let P := (SemiSSet.boundary.{u} (m + 1)).toFunctor
  have hval : (ULift.up f : (SemiSSet.stdSimplex.{u}.obj d).obj (Opposite.op c)) ∈
      (SemiSSet.boundary.{u} (m + 1)).obj (Opposite.op c) := ⟨i, hmissing⟩
  let e : P.Elements := Functor.elementsMk P (Opposite.op c) ⟨ULift.up f, hval⟩
  let leg := (Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e)
  let s' : StdSimplex ℝ
      (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c).len + 1)) := by
    simpa [c, HomotopyHypothesis.Henry.SemiSimplexCategory.incl] using s
  have hs' : s' = s := by
    apply StdSimplex.ext
    ext j
    simp [s', c, HomotopyHypothesis.Henry.SemiSimplexCategory.incl]
  let y := (realization_representable_iso c).inv.hom (ULift.up s')
  refine ⟨(SemiSSet.realization.{u}.map leg).hom y, ?_⟩
  have hfactor : SemiSSet.realization.{u}.map leg ≫
      SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} (m + 1)).ι =
        SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) := by
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg (SemiSSet.realization.{u}.map)
        (boundaryRepresentableMap_eq_stdSimplexMap (m + 1) e))
  have hcoords : SemiSSet.realization.{u}.map leg ≫
      boundaryRealizationToCoords (m + 1) =
        SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
          (realizationSimplexCoordsIso (m + 1)).hom := by
    change SemiSSet.realization.{u}.map leg ≫
      (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} (m + 1)).ι ≫
        (realizationSimplexCoordsIso (m + 1)).hom) = _
    rw [← Category.assoc, hfactor]
    rfl
  have hEval := congrArg (fun g => g.hom y) hcoords
  have hIsoEval := congrArg (fun g => g.hom y)
    (realizationRepresentableCoordsIso_map f)
  have hs : (realization_representable_iso c).hom.hom y = ULift.up s' := by
    simpa [y] using Iso.inv_hom_id_apply (realization_representable_iso c) (ULift.up s')
  have htopEval :
      (toTopSimplexCoordsIso d).hom.hom
        ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c).hom.hom y)) =
      ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s')) := by
    calc
      (toTopSimplexCoordsIso d).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c).hom.hom y)) =
        (toTopSimplexCoordsIso d).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom (ULift.up s')) :=
            congrArg (fun z => (toTopSimplexCoordsIso d).hom.hom
              ((SemiSSet.toTop.{u}.map f).hom z)) hs
      _ = _ := by
        simpa [d] using toTopSimplexCoordsIso_map f s'
  have hMapFace : StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s' =
      StdSimplex.map (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s := by
    rw [hs']
    change StdSimplex.map face.toOrderHom s =
      StdSimplex.map (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s
    simp [face, SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk]
  calc
    (boundaryRealizationToCoords (m + 1)).hom ((SemiSSet.realization.{u}.map leg).hom y) =
        ((SemiSSet.realization.{u}.map leg ≫ boundaryRealizationToCoords (m + 1)).hom y) := rfl
    _ = ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso (m + 1)).hom).hom y) := hEval
    _ = (((realization_representable_iso c).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso d).hom).hom y) := hIsoEval
    _ = ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
        (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s)) :=
      htopEval.trans (congrArg ULift.up
        (congrArg (stdSimplexCoordsEquiv (m + 1)) hMapFace))

/-- Every point with a zero barycentric coordinate is covered by a realized boundary face. -/
theorem boundaryRealizationToCoords_surjective_zeroWeight (n : ℕ)
    (x : ClosedCoordSimplex n) (hx : ∃ i, closedCoordBarycentricWeights n x i = 0) :
    ∃ y : SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor,
      (boundaryRealizationToCoords n).hom y = ULift.up x := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := hx
    fin_cases i
    let t : StdSimplex ℝ (Fin 1) := (stdSimplexCoordsEquiv 0).symm x
    have ht : t.weights 0 = 0 := by
      simpa [t, closedCoordBarycentricWeights] using hi
    have htotal : t.weights 0 = 1 := by
      simpa using t.total_of_fintype
    rw [ht] at htotal
    norm_num at htotal
  | succ n =>
    obtain ⟨i, hi⟩ := hx
    let t := (stdSimplexCoordsEquiv (n + 1)).symm x
    have ht : t.weights i = 0 := by
      simpa [t, closedCoordBarycentricWeights] using hi
    obtain ⟨s, hmap⟩ := exists_stdSimplex_preimage_face i t ht
    obtain ⟨y, hy⟩ := boundaryRealizationToCoords_face (m := n) i s
    have hcoords : stdSimplexCoordsEquiv (n + 1)
        (StdSimplex.map (Fin.succAboveOrderEmb i) s) = x := by
      rw [hmap]
      exact Equiv.apply_symm_apply (stdSimplexCoordsEquiv (n + 1)) x
    exact ⟨y, hy.trans (congrArg ULift.up hcoords)⟩

/-- The image of the realized boundary is exactly the frontier of the coordinate simplex. -/
theorem boundaryRealizationToCoords_range_eq_frontier (n : ℕ) :
    Set.range (boundaryRealizationToCoords n).hom =
      {z : LiftedClosedCoordSimplex n | z.down.1 ∈ frontier (closedCoordSimplexSet n)} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, hi⟩ := boundaryRealizationToCoords_hasZeroWeight n y
    exact (closedCoordBarycentricWeights_exists_zero_iff_mem_frontier n
      (ULift.down ((boundaryRealizationToCoords n).hom y))).mp ⟨i, hi⟩
  · intro hz
    have hzero := (closedCoordBarycentricWeights_exists_zero_iff_mem_frontier n z.down).mpr hz
    obtain ⟨y, hy⟩ := boundaryRealizationToCoords_surjective_zeroWeight n z.down hzero
    refine ⟨y, ?_⟩
    exact hy.trans (by apply ULift.ext; rfl)

/-- Realizing the boundary inclusion gives an injective map. -/
theorem boundaryRealizationToCoords_injective (n : ℕ) :
    Function.Injective (boundaryRealizationToCoords n).hom := by
  exact (TopCat.homeoOfIso (realizationSimplexCoordsIso n)).injective.comp
    (HomotopyHypothesis.Simplicial.CycleRealization.realization_boundary_injective n)

/-- The realized boundary maps homeomorphically onto the frontier of the coordinate simplex. -/
noncomputable def boundaryRealizationToFrontierHomeomorph (n : ℕ) :
    SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor ≃ₜ
      {z : LiftedClosedCoordSimplex n // z.down.1 ∈ frontier (closedCoordSimplexSet n)} := by
  classical
  let f := (boundaryRealizationToCoords n).hom
  have hf : ∀ x, f x ∈ {z : LiftedClosedCoordSimplex n |
      z.down.1 ∈ frontier (closedCoordSimplexSet n)} := by
    intro x
    rw [← boundaryRealizationToCoords_range_eq_frontier n]
    exact ⟨x, rfl⟩
  let F : SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor →
      {z : LiftedClosedCoordSimplex n // z.down.1 ∈ frontier (closedCoordSimplexSet n)} :=
    fun x => ⟨f x, hf x⟩
  have hBij : Function.Bijective F := by
    constructor
    · intro x y hxy
      apply boundaryRealizationToCoords_injective n
      exact congrArg Subtype.val hxy
    · intro z
      have hz : z.1 ∈ Set.range (boundaryRealizationToCoords n).hom := by
        rw [boundaryRealizationToCoords_range_eq_frontier n]
        exact z.2
      rcases hz with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let e : SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor ≃ _ :=
    Equiv.ofBijective F hBij
  letI : CompactSpace (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) :=
    compactSpace_realization_boundary n
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (by
    exact (boundaryRealizationToCoords n).hom.continuous.subtype_mk hf)

/-- The realized simplex is homeomorphic to the corresponding disk. -/
noncomputable def realizationSimplexToDiskIso (n : ℕ) :
    SemiSSet.realization.{u}.obj
      (SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ≅
      TopCat.disk.{u} n :=
  realizationSimplexCoordsIso n ≪≫
    TopCat.isoOfHomeo (liftedClosedCoordToDiskHomeomorph n)

/-- The realized boundary is homeomorphic to the corresponding disk boundary. -/
noncomputable def realizationBoundaryToDiskBoundaryHomeomorph (n : ℕ) :
    SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor ≃ₜ
      TopCat.diskBoundary.{u} n :=
  (boundaryRealizationToFrontierHomeomorph n).trans
    (liftedClosedCoordFrontierToDiskBoundaryHomeomorph n)

/-- The boundary realization square commutes under the simplex and sphere identifications. -/
theorem realizationBoundaryToDiskBoundary_square (n : ℕ) :
    SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι ≫
        (realizationSimplexToDiskIso n).hom =
      (TopCat.isoOfHomeo (realizationBoundaryToDiskBoundaryHomeomorph n)).hom ≫
        TopCat.diskBoundaryInclusion.{u} n := by
  cases n with
  | zero =>
    ext x
    have hset : closedCoordSimplexSet 0 = Set.univ := by
      ext z
      simp [closedCoordSimplexSet]
    have hxrange : (boundaryRealizationToCoords 0).hom x ∈
        Set.range (boundaryRealizationToCoords 0).hom := ⟨x, rfl⟩
    rw [boundaryRealizationToCoords_range_eq_frontier 0] at hxrange
    have hxnot : ((boundaryRealizationToCoords 0).hom x).down.1 ∉
        (Set.univ : Set (Fin 0 → ℝ)) := by simpa [hset] using hxrange.2
    exact False.elim (hxnot (Set.mem_univ _))
  | succ n =>
    ext x
    simp [realizationSimplexToDiskIso, realizationBoundaryToDiskBoundaryHomeomorph,
      boundaryRealizationToCoords, liftedClosedCoordToDiskHomeomorph,
      liftedClosedCoordFrontierToDiskBoundaryHomeomorph,
      closedCoordFrontierToSphereHomeomorph, closedCoordToDiskHomeomorph,
      closedCoordFrontierToSphereHomeomorph_pos, closedCoordToDiskHomeomorph_pos,
      boundaryRealizationToFrontierHomeomorph, closedCoordFrontierSubtypeHomeomorph,
      Continuous.homeoOfEquivCompactToT2]
    apply ULift.ext
    apply Subtype.ext
    rfl

end HomotopyHypothesis.Realization.Boundary
