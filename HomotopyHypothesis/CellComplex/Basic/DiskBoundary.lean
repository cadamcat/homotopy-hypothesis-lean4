import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CellComplex.Basic.Proofs
universe u

open CategoryTheory Limits TopologicalSpace Topology TopCat

namespace HomotopyHypothesis.CellComplex.Basic

private def euclideanSnoc (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc x y)

private theorem euclideanSnoc_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    ‖euclideanSnoc n x y‖ ^ 2 = ‖x‖ ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [euclideanSnoc, EuclideanSpace.real_norm_sq_eq]

private def diskValue (n : ℕ) (x : disk.{u} n) : EuclideanSpace ℝ (Fin n) :=
  (ULift.down x).val

private theorem diskValue_continuous (n : ℕ) :
    Continuous (diskValue n) := by
  exact continuous_subtype_val.comp continuous_uliftDown

private theorem diskValue_norm_le_one (n : ℕ) (x : disk.{u} n) :
    ‖diskValue n x‖ ≤ 1 := by
  change ‖(ULift.down x).val‖ ≤ 1
  rw [← dist_zero_right]
  exact (ULift.down x).property

private noncomputable def radiusCoordinate {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (max 0 (1 - ‖x‖ ^ 2))

private theorem radiusCoordinate_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) : radiusCoordinate x ^ 2 = 1 - ‖x‖ ^ 2 := by
  have hnonneg : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  simp [radiusCoordinate, max_eq_right hnonneg, Real.sq_sqrt hnonneg]

private noncomputable def upperHemisphereVec (n : ℕ) (x : disk.{u} n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  euclideanSnoc n (diskValue n x) (radiusCoordinate (diskValue n x))

private noncomputable def lowerHemisphereVec (n : ℕ) (x : disk.{u} n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  euclideanSnoc n (diskValue n x) (-radiusCoordinate (diskValue n x))

private theorem upperHemisphereVec_norm (n : ℕ) (x : disk.{u} n) :
    ‖upperHemisphereVec n x‖ = 1 := by
  have h := euclideanSnoc_norm_sq n (diskValue n x) (radiusCoordinate (diskValue n x))
  rw [radiusCoordinate_sq (diskValue n x) (diskValue_norm_le_one n x)] at h
  have hnorm : ‖upperHemisphereVec n x‖ ^ 2 = 1 := by simpa [upperHemisphereVec] using h
  nlinarith [norm_nonneg (upperHemisphereVec n x)]

private theorem lowerHemisphereVec_norm (n : ℕ) (x : disk.{u} n) :
    ‖lowerHemisphereVec n x‖ = 1 := by
  have h := euclideanSnoc_norm_sq n (diskValue n x) (-radiusCoordinate (diskValue n x))
  rw [show (-radiusCoordinate (diskValue n x)) ^ 2 =
      radiusCoordinate (diskValue n x) ^ 2 by ring,
    radiusCoordinate_sq (diskValue n x) (diskValue_norm_le_one n x)] at h
  have hnorm : ‖lowerHemisphereVec n x‖ ^ 2 = 1 := by
    simpa [lowerHemisphereVec] using h
  nlinarith [norm_nonneg (lowerHemisphereVec n x)]

private theorem upperHemisphereVec_continuous (n : ℕ) :
    Continuous (fun x : disk.{u} n => upperHemisphereVec n x) := by
  have hv := diskValue_continuous n
  have hr : Continuous (fun x : disk.{u} n => radiusCoordinate (diskValue n x)) := by
    change Continuous (fun x : disk.{u} n => Real.sqrt (max 0 (1 - ‖diskValue n x‖ ^ 2)))
    fun_prop
  have hcoords : Continuous (fun x : disk.{u} n =>
      Fin.snoc (n := n) (α := fun _ : Fin (n + 1) => ℝ)
        (diskValue n x) (radiusCoordinate (diskValue n x))) := by
    refine continuous_pi ?_
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hr
    · simpa [Fin.snoc_castSucc, Function.comp_def] using
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) j).comp hv
  exact (PiLp.continuous_toLp 2 _).comp hcoords

private theorem lowerHemisphereVec_continuous (n : ℕ) :
    Continuous (fun x : disk.{u} n => lowerHemisphereVec n x) := by
  have hv := diskValue_continuous n
  have hr : Continuous (fun x : disk.{u} n => -radiusCoordinate (diskValue n x)) := by
    change Continuous (fun x : disk.{u} n => -Real.sqrt (max 0 (1 - ‖diskValue n x‖ ^ 2)))
    fun_prop
  have hcoords : Continuous (fun x : disk.{u} n =>
      Fin.snoc (n := n) (α := fun _ : Fin (n + 1) => ℝ)
        (diskValue n x) (-radiusCoordinate (diskValue n x))) := by
    refine continuous_pi ?_
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hr
    · simpa [Fin.snoc_castSucc, Function.comp_def] using
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) j).comp hv
  exact (PiLp.continuous_toLp 2 _).comp hcoords

private noncomputable def upperHemisphereMap (n : ℕ) : disk.{u} n ⟶ diskBoundary.{u} (n + 1) :=
  TopCat.ofHom ⟨fun x => ULift.up ⟨upperHemisphereVec n x, by
      simpa [Metric.mem_sphere, dist_eq_norm] using upperHemisphereVec_norm n x⟩,
    continuous_uliftUp.comp ((upperHemisphereVec_continuous n).subtype_mk
      (fun x => by simpa [Metric.mem_sphere, dist_eq_norm] using upperHemisphereVec_norm n x))⟩

private noncomputable def lowerHemisphereMap (n : ℕ) : disk.{u} n ⟶ diskBoundary.{u} (n + 1) :=
  TopCat.ofHom ⟨fun x => ULift.up ⟨lowerHemisphereVec n x, by
      simpa [Metric.mem_sphere, dist_eq_norm] using lowerHemisphereVec_norm n x⟩,
    continuous_uliftUp.comp ((lowerHemisphereVec_continuous n).subtype_mk
      (fun x => by simpa [Metric.mem_sphere, dist_eq_norm] using lowerHemisphereVec_norm n x))⟩

private theorem upperHemisphereMap_injective (n : ℕ) :
    Function.Injective (upperHemisphereMap.{u} n) := by
  intro x y h
  have hvec : upperHemisphereVec.{u} n x = upperHemisphereVec.{u} n y := by
    have h' := congrArg (fun z : diskBoundary.{u} (n + 1) => (ULift.down z).val) h
    exact h'
  have hval : diskValue n x = diskValue n y := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.castSucc) hvec
    simpa [upperHemisphereVec, euclideanSnoc, Fin.snoc_castSucc] using hi
  apply ULift.ext
  apply Subtype.ext
  exact hval

private theorem lowerHemisphereMap_injective (n : ℕ) :
    Function.Injective (lowerHemisphereMap.{u} n) := by
  intro x y h
  have hvec : lowerHemisphereVec.{u} n x = lowerHemisphereVec.{u} n y := by
    have h' := congrArg (fun z : diskBoundary.{u} (n + 1) => (ULift.down z).val) h
    exact h'
  have hval : diskValue n x = diskValue n y := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.castSucc) hvec
    simpa [lowerHemisphereVec, euclideanSnoc, Fin.snoc_castSucc] using hi
  apply ULift.ext
  apply Subtype.ext
  exact hval

private theorem hemisphereVec_eq_on_boundary (n : ℕ) (x : diskBoundary.{u} n) :
    upperHemisphereVec n (diskBoundaryInclusion n x) =
      lowerHemisphereVec n (diskBoundaryInclusion n x) := by
  have hval : diskValue n (diskBoundaryInclusion n x) = (ULift.down x).val := rfl
  have hnorm : ‖diskValue n (diskBoundaryInclusion n x)‖ = 1 := by
    rw [hval]
    simpa [dist_zero_right] using (ULift.down x).property
  have hrad : radiusCoordinate (diskValue n (diskBoundaryInclusion n x)) = 0 := by
    simp [radiusCoordinate, hnorm]
  unfold upperHemisphereVec lowerHemisphereVec
  rw [hrad, neg_zero]

private theorem upper_lower_compatibility (n : ℕ) :
    diskBoundaryInclusion.{u} n ≫ upperHemisphereMap.{u} n =
      diskBoundaryInclusion.{u} n ≫ lowerHemisphereMap.{u} n := by
  ext x
  apply ULift.ext
  apply Subtype.ext
  exact hemisphereVec_eq_on_boundary.{u} n x

private def euclideanInit (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Fin.init (WithLp.ofLp z))

private def euclideanLast (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  z (Fin.last n)

private theorem euclideanSnoc_init (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanSnoc n (euclideanInit n z) (euclideanLast n z) = z := by
  apply PiLp.ext
  intro i
  simp [euclideanSnoc, euclideanInit, euclideanLast, Fin.snoc_init_self]

private theorem euclideanInit_norm_sq (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖z‖ ^ 2 = ‖euclideanInit n z‖ ^ 2 + (euclideanLast n z) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq]
  simp [euclideanInit, euclideanLast, Fin.init]

private noncomputable def diskPoint (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) : disk.{u} n :=
  ULift.up ⟨x, by
    change dist x 0 ≤ 1
    rw [dist_zero_right]
    exact hx⟩

private theorem diskValue_diskPoint (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) : diskValue n (diskPoint n x hx) = x := rfl

private theorem hemispheres_cover (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1)))
    (hz : ‖z‖ = 1) :
    ∃ x : disk.{u} n,
      upperHemisphereMap.{u} n x = ULift.up ⟨z, by
        simpa [Metric.mem_sphere, dist_zero_right] using hz⟩ ∨
      lowerHemisphereMap.{u} n x = ULift.up ⟨z, by
        simpa [Metric.mem_sphere, dist_zero_right] using hz⟩ := by
  let x₀ := euclideanInit n z
  let y := euclideanLast n z
  have hsplit := euclideanInit_norm_sq n z
  have hbase : 1 - ‖x₀‖ ^ 2 = y ^ 2 := by
    dsimp [x₀, y] at hsplit ⊢
    rw [hz] at hsplit
    nlinarith
  have hx : ‖x₀‖ ≤ 1 := by
    have hnonneg : 0 ≤ ‖x₀‖ := norm_nonneg _
    nlinarith [sq_nonneg y]
  have hbase_nonneg : 0 ≤ 1 - ‖x₀‖ ^ 2 := by nlinarith [sq_nonneg y]
  let x := diskPoint n x₀ hx
  have hxval : diskValue n x = x₀ := by simp [x, diskValue_diskPoint]
  by_cases hy : 0 ≤ y
  · have hrad : radiusCoordinate x₀ = y := by
      rw [radiusCoordinate, max_eq_right hbase_nonneg]
      exact (Real.sqrt_eq_iff_eq_sq hbase_nonneg hy).2 hbase
    have hvec : upperHemisphereVec.{u} n x = z := by
      rw [upperHemisphereVec, hxval, hrad]
      exact euclideanSnoc_init n z
    refine ⟨x, Or.inl ?_⟩
    apply ULift.ext
    apply Subtype.ext
    exact hvec
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hrad : radiusCoordinate x₀ = -y := by
      rw [radiusCoordinate, max_eq_right hbase_nonneg]
      apply (Real.sqrt_eq_iff_eq_sq hbase_nonneg (neg_nonneg.mpr hy')).2
      nlinarith [hbase]
    have hvec : lowerHemisphereVec.{u} n x = z := by
      rw [lowerHemisphereVec, hxval, hrad, neg_neg]
      exact euclideanSnoc_init n z
    refine ⟨x, Or.inr ?_⟩
    apply ULift.ext
    apply Subtype.ext
    exact hvec

private theorem pushout_exists_rep (n : ℕ)
    (p : (pushout (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n) : TopCat.{u})) :
    (∃ x : disk.{u} n,
      (pushout.inl (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n)).hom x = p) ∨
      ∃ x : disk.{u} n,
        (pushout.inr (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n)).hom x = p := by
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let F : WalkingSpan ⥤ TopCat.{u} := span i i
  obtain ⟨j, z, hz⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep F p
  rcases j with (⟨⟩ | ⟨⟨⟩⟩)
  · left
    refine ⟨i z, ?_⟩
    have hw := ConcreteCategory.congr_hom (colimit.w F WalkingSpan.Hom.fst) z
    exact hw.trans hz
  · left
    exact ⟨z, by simpa [F, i, pushout.inl] using hz⟩
  · right
    exact ⟨z, by simpa [F, i, pushout.inr] using hz⟩

private theorem doubleDiskPushout_compact (n : ℕ) :
    CompactSpace (pushout (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n) : TopCat.{u}) := by
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let F : WalkingSpan ⥤ TopCat.{u} := span i i
  change CompactSpace (CategoryTheory.Limits.colimit F : TopCat.{u})
  exact compactSpace_colimit_of_finite_shape (J := WalkingSpan) F (by
      intro j
      cases j with
      | none => simpa [F] using
          (inferInstance : CompactSpace (diskBoundary.{u} n))
      | some j => cases j with
        | left => simpa [F] using (inferInstance : CompactSpace (disk.{u} n))
        | right => simpa [F] using (inferInstance : CompactSpace (disk.{u} n)))

private noncomputable def doubleHemisphereMap (n : ℕ) :
    (pushout (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n) : TopCat.{u}) ⟶
      diskBoundary.{u} (n + 1) :=
  pushout.desc (upperHemisphereMap.{u} n) (lowerHemisphereMap.{u} n)
    (upper_lower_compatibility.{u} n)

private theorem doubleHemisphereMap_surjective (n : ℕ) :
    Function.Surjective (doubleHemisphereMap.{u} n).hom := by
  intro z
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let P : TopCat.{u} := pushout i i
  let z₀ := (ULift.down z).val
  have hz : ‖z₀‖ = 1 := by
    simpa [z₀, dist_zero_right] using (ULift.down z).property
  obtain ⟨x, hx | hx⟩ := hemispheres_cover n z₀ hz
  · refine ⟨(pushout.inl (diskBoundaryInclusion.{u} n)
      (diskBoundaryInclusion.{u} n)).hom x, ?_⟩
    have hfac : (doubleHemisphereMap.{u} n).hom
        ((pushout.inl (diskBoundaryInclusion.{u} n)
          (diskBoundaryInclusion.{u} n)).hom x) = (upperHemisphereMap.{u} n).hom x := by
      simpa [doubleHemisphereMap, i, P] using
        ConcreteCategory.congr_hom (pushout.inl_desc (upperHemisphereMap.{u} n)
          (lowerHemisphereMap.{u} n) (upper_lower_compatibility.{u} n)) x
    exact hfac.trans hx
  · refine ⟨(pushout.inr (diskBoundaryInclusion.{u} n)
      (diskBoundaryInclusion.{u} n)).hom x, ?_⟩
    have hfac : (doubleHemisphereMap.{u} n).hom
        ((pushout.inr (diskBoundaryInclusion.{u} n)
          (diskBoundaryInclusion.{u} n)).hom x) = (lowerHemisphereMap.{u} n).hom x := by
      simpa [doubleHemisphereMap, i, P] using
        ConcreteCategory.congr_hom (pushout.inr_desc (upperHemisphereMap.{u} n)
          (lowerHemisphereMap.{u} n) (upper_lower_compatibility.{u} n)) x
    exact hfac.trans hx

private theorem diskValue_eq_radius_zero_of_upper_lower (n : ℕ)
    {x y : disk.{u} n}
    (h : (upperHemisphereMap.{u} n).hom x = (lowerHemisphereMap.{u} n).hom y) :
    diskValue n x = diskValue n y ∧
      radiusCoordinate (diskValue n x) = 0 ∧ radiusCoordinate (diskValue n y) = 0 := by
  have hvec : upperHemisphereVec.{u} n x = lowerHemisphereVec.{u} n y := by
    have h' := congrArg (fun z : diskBoundary.{u} (n + 1) => (ULift.down z).val) h
    exact h'
  have hval : diskValue n x = diskValue n y := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.castSucc) hvec
    simpa [upperHemisphereVec, lowerHemisphereVec, euclideanSnoc, Fin.snoc_castSucc,
      Function.comp_def] using hi
  have hlast : radiusCoordinate (diskValue n x) = -radiusCoordinate (diskValue n y) := by
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hvec
    simpa [upperHemisphereVec, lowerHemisphereVec, euclideanSnoc, Fin.snoc_last] using hi
  have hrx : 0 ≤ radiusCoordinate (diskValue n x) := Real.sqrt_nonneg _
  have hry : 0 ≤ radiusCoordinate (diskValue n y) := Real.sqrt_nonneg _
  refine ⟨hval, ?_, ?_⟩ <;> nlinarith [hlast, hrx, hry]

private theorem doubleHemisphereMap_injective (n : ℕ) :
    Function.Injective (doubleHemisphereMap.{u} n).hom := by
  intro p q h
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  have hupper (x : disk.{u} n) :
      (doubleHemisphereMap.{u} n).hom ((pushout.inl i i).hom x) =
        (upperHemisphereMap.{u} n).hom x := by
    simpa [doubleHemisphereMap] using
      ConcreteCategory.congr_hom (pushout.inl_desc (upperHemisphereMap.{u} n)
        (lowerHemisphereMap.{u} n) (upper_lower_compatibility.{u} n)) x
  have hlower (x : disk.{u} n) :
      (doubleHemisphereMap.{u} n).hom ((pushout.inr i i).hom x) =
        (lowerHemisphereMap.{u} n).hom x := by
    simpa [doubleHemisphereMap] using
      ConcreteCategory.congr_hom (pushout.inr_desc (upperHemisphereMap.{u} n)
        (lowerHemisphereMap.{u} n) (upper_lower_compatibility.{u} n)) x
  rcases pushout_exists_rep n p with ⟨x, hp⟩ | ⟨x, hp⟩
  · rcases pushout_exists_rep n q with ⟨y, hq⟩ | ⟨y, hq⟩
    · have hxy : (upperHemisphereMap.{u} n).hom x = (upperHemisphereMap.{u} n).hom y := by
        calc
          (upperHemisphereMap.{u} n).hom x =
              (doubleHemisphereMap.{u} n).hom ((pushout.inl i i).hom x) := (hupper x).symm
          _ = (doubleHemisphereMap.{u} n).hom ((pushout.inl i i).hom y) := by rw [hp, h, hq]
          _ = (upperHemisphereMap.{u} n).hom y := hupper y
      have : x = y := upperHemisphereMap_injective n hxy
      subst y
      exact hp.symm.trans hq
    · have hxy : (upperHemisphereMap.{u} n).hom x = (lowerHemisphereMap.{u} n).hom y := by
        calc
          (upperHemisphereMap.{u} n).hom x =
              (doubleHemisphereMap.{u} n).hom ((pushout.inl i i).hom x) := (hupper x).symm
          _ = (doubleHemisphereMap.{u} n).hom ((pushout.inr i i).hom y) := by rw [hp, h, hq]
          _ = (lowerHemisphereMap.{u} n).hom y := hlower y
      obtain ⟨hval, hrx, hry⟩ := diskValue_eq_radius_zero_of_upper_lower n hxy
      have hnorm : ‖diskValue n x‖ = 1 := by
        have hs := radiusCoordinate_sq (diskValue n x) (diskValue_norm_le_one n x)
        rw [hrx] at hs
        nlinarith [norm_nonneg (diskValue n x)]
      let a : diskBoundary.{u} n := ULift.up ⟨diskValue n x, by
        simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩
      have hia : (diskBoundaryInclusion.{u} n).hom a = x := by
        apply ULift.ext
        apply Subtype.ext
        rfl
      have hja : (diskBoundaryInclusion.{u} n).hom a = y := by
        apply ULift.ext
        apply Subtype.ext
        exact hval
      have hglue : (pushout.inl i i).hom ((diskBoundaryInclusion.{u} n).hom a) =
          (pushout.inr i i).hom ((diskBoundaryInclusion.{u} n).hom a) := by
        simpa using ConcreteCategory.congr_hom (pushout.condition (f := i) (g := i)) a
      calc
        p = (pushout.inl i i).hom x := hp.symm
        _ = (pushout.inl i i).hom ((diskBoundaryInclusion.{u} n).hom a) :=
          congrArg (pushout.inl i i).hom hia.symm
        _ = (pushout.inr i i).hom ((diskBoundaryInclusion.{u} n).hom a) := hglue
        _ = (pushout.inr i i).hom y := congrArg (pushout.inr i i).hom hja
        _ = q := hq
  · rcases pushout_exists_rep n q with ⟨y, hq⟩ | ⟨y, hq⟩
    · have hxy : (lowerHemisphereMap.{u} n).hom x = (upperHemisphereMap.{u} n).hom y := by
        calc
          (lowerHemisphereMap.{u} n).hom x =
              (doubleHemisphereMap.{u} n).hom ((pushout.inr i i).hom x) := (hlower x).symm
          _ = (doubleHemisphereMap.{u} n).hom ((pushout.inl i i).hom y) := by rw [hp, h, hq]
          _ = (upperHemisphereMap.{u} n).hom y := hupper y
      have hxy' : (upperHemisphereMap.{u} n).hom y = (lowerHemisphereMap.{u} n).hom x := hxy.symm
      obtain ⟨hval, hrx, hry⟩ := diskValue_eq_radius_zero_of_upper_lower n hxy'
      have hnorm : ‖diskValue n y‖ = 1 := by
        have hs := radiusCoordinate_sq (diskValue n y) (diskValue_norm_le_one n y)
        rw [hrx] at hs
        nlinarith [norm_nonneg (diskValue n y)]
      let a : diskBoundary.{u} n := ULift.up ⟨diskValue n y, by
        simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩
      have hia : (diskBoundaryInclusion.{u} n).hom a = y := by
        apply ULift.ext
        apply Subtype.ext
        rfl
      have hja : (diskBoundaryInclusion.{u} n).hom a = x := by
        apply ULift.ext
        apply Subtype.ext
        exact hval
      have hglue : (pushout.inl i i).hom ((diskBoundaryInclusion.{u} n).hom a) =
          (pushout.inr i i).hom ((diskBoundaryInclusion.{u} n).hom a) := by
        simpa using ConcreteCategory.congr_hom (pushout.condition (f := i) (g := i)) a
      calc
        p = (pushout.inr i i).hom x := hp.symm
        _ = (pushout.inr i i).hom ((diskBoundaryInclusion.{u} n).hom a) :=
          congrArg (pushout.inr i i).hom hja.symm
        _ = (pushout.inl i i).hom ((diskBoundaryInclusion.{u} n).hom a) := hglue.symm
        _ = (pushout.inl i i).hom y := congrArg (pushout.inl i i).hom hia
        _ = q := hq
    · have hxy : (lowerHemisphereMap.{u} n).hom x = (lowerHemisphereMap.{u} n).hom y := by
        calc
          (lowerHemisphereMap.{u} n).hom x =
              (doubleHemisphereMap.{u} n).hom ((pushout.inr i i).hom x) := (hlower x).symm
          _ = (doubleHemisphereMap.{u} n).hom ((pushout.inr i i).hom y) := by rw [hp, h, hq]
          _ = (lowerHemisphereMap.{u} n).hom y := hlower y
      have : x = y := lowerHemisphereMap_injective n hxy
      subst y
      exact hp.symm.trans hq

private theorem doubleHemisphereMap_isIso (n : ℕ) :
    IsIso (doubleHemisphereMap.{u} n) := by
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let P : TopCat.{u} := pushout i i
  letI : CompactSpace P := doubleDiskPushout_compact n
  haveI : T2Space (diskBoundary.{u} (n + 1) : Type u) := by
    change T2Space (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    haveI : T2Space (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := inferInstance
    exact Homeomorph.ulift.symm.t2Space
  have hbij : Function.Bijective (doubleHemisphereMap.{u} n).hom :=
    ⟨doubleHemisphereMap_injective n, doubleHemisphereMap_surjective n⟩
  have hhomeo : IsHomeomorph (doubleHemisphereMap.{u} n).hom :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨(doubleHemisphereMap.{u} n).hom.continuous, hbij⟩
  exact (TopCat.isIso_iff_isHomeomorph (doubleHemisphereMap.{u} n)).2 hhomeo

private theorem finiteCell_disk_of_boundary (n : ℕ)
    (hB : HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (diskBoundary.{u} n)) :
    HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (disk.{u} n) := by
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let G : MorphismProperty TopCat.{u} :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}
  have hi : HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts i :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.le_pushouts i
      (MorphismProperty.ofHoms.mk n)
  have hiG : G i := Or.inl hi
  have hcomp : G.multiplicativeClosure (initial.to (diskBoundary.{u} n) ≫ i) :=
    MorphismProperty.multiplicativeClosure.comp_of _ _ hB hiG
  have hEq : initial.to (diskBoundary.{u} n) ≫ i = initial.to (disk.{u} n) := by
    apply initial.hom_ext
  change HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes (initial.to (disk.{u} n))
  rw [← hEq]
  exact hcomp

private theorem finiteCell_doubleDiskPushout (n : ℕ)
    (hD : HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (disk.{u} n)) :
    HomotopyHypothesis.Henry.Top.IsFiniteCellComplex
      (pushout (diskBoundaryInclusion.{u} n) (diskBoundaryInclusion.{u} n) : TopCat.{u}) := by
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let P : TopCat.{u} := pushout i i
  let G : MorphismProperty TopCat.{u} :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}
  have hAttach : HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts (pushout.inl i i) :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts_mk
      (IsPushout.of_hasPushout i i) (MorphismProperty.ofHoms.mk n)
  have hAttachG : G (pushout.inl i i) := Or.inl hAttach
  have hcomp : G.multiplicativeClosure (initial.to (disk.{u} n) ≫ pushout.inl i i) :=
    MorphismProperty.multiplicativeClosure.comp_of _ _ hD hAttachG
  have hEq : initial.to (disk.{u} n) ≫ pushout.inl i i = initial.to P := by
    apply initial.hom_ext
  change HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes (initial.to P)
  rw [← hEq]
  exact hcomp

private theorem diskBoundary_succ_finiteCell_of_disk (n : ℕ)
    (hD : HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (disk.{u} n)) :
    HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (diskBoundary.{u} (n + 1)) := by
  have hP := finiteCell_doubleDiskPushout n hD
  have hIso : IsIso (doubleHemisphereMap.{u} n) := doubleHemisphereMap_isIso n
  let i : diskBoundary.{u} n ⟶ disk.{u} n := diskBoundaryInclusion n
  let P : TopCat.{u} := pushout i i
  let e : P ≅ diskBoundary.{u} (n + 1) := asIso (doubleHemisphereMap.{u} n)
  let G : MorphismProperty TopCat.{u} :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}
  have he : G e.hom := Or.inr (show IsIso e.hom from inferInstance)
  have hcomp : G.multiplicativeClosure (initial.to P ≫ e.hom) :=
    MorphismProperty.multiplicativeClosure.comp_of _ _ hP he
  have hEq : initial.to P ≫ e.hom =
      initial.to (diskBoundary.{u} (n + 1)) := by
    apply initial.hom_ext
  change HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes
    (initial.to (diskBoundary.{u} (n + 1)))
  rw [← hEq]
  exact hcomp

private theorem diskBoundary_zero_isEmpty : IsEmpty (diskBoundary.{u} 0) := by
  refine ⟨fun x => ?_⟩
  have hx : ‖((ULift.down x).val : EuclideanSpace ℝ (Fin 0))‖ = 1 := by
    simpa [dist_zero_right] using (ULift.down x).property
  have hz : (ULift.down x).val = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  rw [hz] at hx
  norm_num at hx

private theorem diskBoundary_zero_finiteCell :
    HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (diskBoundary.{u} 0) := by
  let f := initial.to (diskBoundary.{u} 0)
  haveI : IsEmpty (diskBoundary.{u} 0) := diskBoundary_zero_isEmpty
  haveI : IsEmpty (⊥_ TopCat.{u} : Type u) := by
    refine ⟨fun x => ?_⟩
    exact PEmpty.elim ((TopCat.initialIsoPEmpty.{u}).hom x)
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact isEmptyElim x
    · intro y
      exact isEmptyElim y
  have hopen : IsOpenMap f := by
    intro s hs
    have hs0 : s = ∅ := by
      ext x
      exact isEmptyElim x
    simp [hs0]
  haveI : IsIso f := TopCat.isIso_of_bijective_of_isOpenMap f hbij hopen
  let G : MorphismProperty TopCat.{u} :=
    HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}
  change HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes f
  exact MorphismProperty.le_multiplicativeClosure G f (Or.inr (show IsIso f from inferInstance))

theorem diskBoundary_isFiniteCellComplex_proof (n : ℕ) :
    HomotopyHypothesis.Henry.Top.IsFiniteCellComplex (diskBoundary.{u} n) := by
  induction n with
  | zero => exact diskBoundary_zero_finiteCell
  | succ n ih =>
      exact diskBoundary_succ_finiteCell_of_disk n (finiteCell_disk_of_boundary n ih)

#print axioms diskBoundary_isFiniteCellComplex_proof

end HomotopyHypothesis.CellComplex.Basic
