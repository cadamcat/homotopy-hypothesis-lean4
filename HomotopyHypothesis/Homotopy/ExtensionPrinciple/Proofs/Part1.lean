import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology

/-!
# `HomotopyHypothesis.Homotopy.ExtensionPrinciple.Proofs`, part 1

Lines 9–1619 of `HomotopyHypothesis.Homotopy.ExtensionPrinciple.Proofs`, split so that the modules of the development form an acyclic import graph.
-/

open CategoryTheory Limits HomotopicalAlgebra TopCat Set Topology

universe u v

namespace HomotopyHypothesis.Homotopy.ExtensionPrinciple

/-- Evaluation at the initial point of the unit interval. -/
def pathEval (Z : TopCat.{u}) : TopCat.of C(unitInterval, Z) ⟶ Z :=
  TopCat.ofHom ⟨fun γ : C(unitInterval, Z) => γ 0, continuous_eval_const 0⟩

/-- The family of path evaluation maps. -/
def pathEvaluations : MorphismProperty TopCat.{u} :=
  MorphismProperty.ofHoms (fun Z : TopCat.{u} => pathEval Z)

private def diskPoint (n : ℕ) (x : TopCat.disk.{u} n) : EuclideanSpace ℝ (Fin n) :=
  x.down.1

private def boundaryPoint (n : ℕ) (x : TopCat.diskBoundary.{u} n) :
    EuclideanSpace ℝ (Fin n) := x.down.1

private lemma norm_diskPoint_le (n : ℕ) (x : TopCat.disk.{u} n) :
    ‖diskPoint n x‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp x.down.property
  simpa [diskPoint, dist_eq_norm] using h

private lemma norm_boundaryPoint (n : ℕ) (x : TopCat.diskBoundary.{u} n) :
    ‖boundaryPoint n x‖ = 1 := by
  simp [boundaryPoint]

private noncomputable def prismScale {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (t : unitInterval) : ℝ :=
  min (2 / (2 - (t : ℝ))) (1 / max ‖x‖ (1 / 2))

private lemma prismScale_bounds {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) (t : unitInterval) :
    1 ≤ prismScale x t ∧
      prismScale x t ≤ 2 / (2 - (t : ℝ)) ∧
      prismScale x t ≤ 1 / max ‖x‖ (1 / 2) := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hden : 0 < 2 - (t : ℝ) := by linarith
  have hq : 1 ≤ 2 / (2 - (t : ℝ)) := (le_div_iff₀ hden).2 (by linarith)
  have hmpos : 0 < max ‖x‖ (1 / 2) := by positivity
  have hmle : max ‖x‖ (1 / 2) ≤ 1 := max_le hx (by norm_num)
  have hr : 1 ≤ 1 / max ‖x‖ (1 / 2) := (le_div_iff₀ hmpos).2 (by nlinarith)
  exact ⟨le_min hq hr, min_le_left _ _, min_le_right _ _⟩

private lemma prismScale_mul_norm_le_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) (t : unitInterval) : prismScale x t * ‖x‖ ≤ 1 := by
  obtain ⟨hscale, _, hscale'⟩ := prismScale_bounds x hx t
  have hmpos : 0 < max ‖x‖ (1 / 2) := by positivity
  have hquot : ‖x‖ / max ‖x‖ (1 / 2) ≤ 1 :=
    (div_le_iff₀ hmpos).2 (by nlinarith [le_max_left ‖x‖ (1 / 2)])
  calc
    prismScale x t * ‖x‖ ≤ (1 / max ‖x‖ (1 / 2)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hscale' (norm_nonneg _)
    _ = ‖x‖ / max ‖x‖ (1 / 2) := by ring
    _ ≤ 1 := hquot

private noncomputable def prismVector (n : ℕ) (x : TopCat.disk.{u} n) (t : unitInterval) :
    EuclideanSpace ℝ (Fin n) := prismScale (diskPoint n x) t • diskPoint n x

private noncomputable def prismTime (n : ℕ) (x : TopCat.disk.{u} n) (t : unitInterval) : ℝ :=
  2 - prismScale (diskPoint n x) t * (2 - (t : ℝ))

private lemma norm_prismVector_le (n : ℕ) (x : TopCat.disk.{u} n) (t : unitInterval) :
    ‖prismVector n x t‖ ≤ 1 := by
  have hx := norm_diskPoint_le n x
  have hs := (prismScale_bounds (diskPoint n x) hx t).1
  have hs0 : 0 ≤ prismScale (diskPoint n x) t := le_trans (by norm_num) hs
  calc
    ‖prismVector n x t‖ =
        |prismScale (diskPoint n x) t| * ‖diskPoint n x‖ := by
      simp [prismVector, norm_smul]
    _ = prismScale (diskPoint n x) t * ‖diskPoint n x‖ := by rw [abs_of_nonneg hs0]
    _ ≤ 1 := prismScale_mul_norm_le_one (diskPoint n x) hx t

private lemma prismTime_mem (n : ℕ) (x : TopCat.disk.{u} n) (t : unitInterval) :
    prismTime n x t ∈ Set.Icc (0 : ℝ) 1 := by
  have hx := norm_diskPoint_le n x
  obtain ⟨hs, hsq, _⟩ := prismScale_bounds (diskPoint n x) hx t
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hd0 : 0 ≤ 2 - (t : ℝ) := by linarith
  have hd1 : 1 ≤ 2 - (t : ℝ) := by linarith
  have hprod_hi : prismScale (diskPoint n x) t * (2 - (t : ℝ)) ≤ 2 := by
    calc
      prismScale (diskPoint n x) t * (2 - (t : ℝ)) ≤
          (2 / (2 - (t : ℝ))) * (2 - (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq hd0
      _ = 2 := by field_simp [ne_of_gt (show 0 < 2 - (t : ℝ) by linarith)]
  have hprod_lo : 2 - (t : ℝ) ≤ prismScale (diskPoint n x) t * (2 - (t : ℝ)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hd0
  constructor
  · dsimp [prismTime]
    linarith
  · dsimp [prismTime]
    linarith

private lemma continuous_prismScale (n : ℕ) :
    Continuous fun p : TopCat.disk.{u} n × unitInterval =>
      prismScale (diskPoint n p.1) p.2 := by
  have hp : Continuous (fun p : TopCat.disk.{u} n × unitInterval => diskPoint n p.1) := by
    exact continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)
  have ht : Continuous (fun p : TopCat.disk.{u} n × unitInterval => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hden : Continuous (fun p : TopCat.disk.{u} n × unitInterval => 2 - (p.2 : ℝ)) := by
    fun_prop
  have hden0 : ∀ p : TopCat.disk.{u} n × unitInterval, 2 - (p.2 : ℝ) ≠ 0 := by
    intro p
    have hp' := p.2.2.2
    norm_num
    linarith
  have hfirst : Continuous (fun p : TopCat.disk.{u} n × unitInterval => 2 / (2 - (p.2 : ℝ))) :=
    Continuous.div continuous_const hden hden0
  have hmax : Continuous (fun p : TopCat.disk.{u} n × unitInterval =>
      max ‖diskPoint n p.1‖ (1 / 2)) := by
    exact (hp.norm).max continuous_const
  have hmax0 : ∀ p : TopCat.disk.{u} n × unitInterval,
      max ‖diskPoint n p.1‖ (1 / 2) ≠ 0 := by
    intro p
    exact ne_of_gt (by positivity)
  have hsecond : Continuous (fun p : TopCat.disk.{u} n × unitInterval =>
      1 / max ‖diskPoint n p.1‖ (1 / 2)) :=
    Continuous.div continuous_const hmax hmax0
  exact hfirst.min hsecond

private lemma continuous_prismVector (n : ℕ) :
    Continuous fun p : TopCat.disk.{u} n × unitInterval => prismVector n p.1 p.2 := by
  have hp : Continuous (fun p : TopCat.disk.{u} n × unitInterval => diskPoint n p.1) := by
    exact continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)
  have hs := continuous_prismScale n
  change Continuous fun p : TopCat.disk.{u} n × unitInterval =>
    prismScale (diskPoint n p.1) p.2 • diskPoint n p.1
  exact hs.smul hp

private lemma continuous_prismTime (n : ℕ) :
    Continuous fun p : TopCat.disk.{u} n × unitInterval => prismTime n p.1 p.2 := by
  have hs := continuous_prismScale n
  have ht : Continuous (fun p : TopCat.disk.{u} n × unitInterval => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have htwo : Continuous (fun p : TopCat.disk.{u} n × unitInterval => 2 - (p.2 : ℝ)) := by
    fun_prop
  change Continuous fun p : TopCat.disk.{u} n × unitInterval =>
    2 - prismScale (diskPoint n p.1) p.2 * (2 - (p.2 : ℝ))
  exact continuous_const.sub (hs.mul htwo)

private noncomputable def prismRetraction (n : ℕ) :
    C(TopCat.disk.{u} n × unitInterval, TopCat.disk.{u} n × unitInterval) where
  toFun p :=
    ( ULift.up (⟨prismVector n p.1 p.2, by
        apply Metric.mem_closedBall.mpr
        simpa [dist_eq_norm] using norm_prismVector_le n p.1 p.2⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    , ⟨prismTime n p.1 p.2, prismTime_mem n p.1 p.2⟩ )
  continuous_toFun := by
    have hv := continuous_prismVector n
    have ht := continuous_prismTime n
    have hdisk : Continuous (fun p : TopCat.disk.{u} n × unitInterval =>
        ULift.up (⟨prismVector n p.1 p.2, by
          apply Metric.mem_closedBall.mpr
          simpa [dist_eq_norm] using norm_prismVector_le n p.1 p.2⟩ :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      apply continuous_uliftUp.comp
      exact hv.subtype_mk (fun p => by
        apply Metric.mem_closedBall.mpr
        simpa [dist_eq_norm] using norm_prismVector_le n p.1 p.2)
    have htime : Continuous (fun p : TopCat.disk.{u} n × unitInterval =>
        (⟨prismTime n p.1 p.2, prismTime_mem n p.1 p.2⟩ : unitInterval)) :=
      ht.subtype_mk (fun p => prismTime_mem n p.1 p.2)
    exact hdisk.prodMk htime

private lemma prismScale_at_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    prismScale x 0 = 1 := by
  obtain ⟨hge, hq, _⟩ := prismScale_bounds x hx 0
  have hq' : (2 : ℝ) / (2 - ((0 : unitInterval) : ℝ)) = 1 := by norm_num
  exact le_antisymm (hq.trans_eq hq') hge

private lemma prismScale_on_boundary {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (t : unitInterval) : prismScale x t = 1 := by
  obtain ⟨hge, _, hr⟩ := prismScale_bounds x (le_of_eq hx) t
  have hmax : max ‖x‖ (1 / 2) = 1 := by
    rw [hx]
    exact max_eq_left (by norm_num)
  have hr' : 1 / max ‖x‖ (1 / 2) = 1 := by rw [hmax]; norm_num
  exact le_antisymm (hr.trans_eq hr') hge

private lemma prismRetraction_mem_base (n : ℕ) (x : TopCat.disk.{u} n)
    (t : unitInterval) :
    prismTime n x t = 0 ∨ ‖prismVector n x t‖ = 1 := by
  let v := diskPoint n x
  let q : ℝ := 2 / (2 - (t : ℝ))
  let r : ℝ := 1 / max ‖v‖ (1 / 2)
  let s : ℝ := prismScale v t
  have hx := norm_diskPoint_le n x
  have hsq : s ≤ q := by
    exact (prismScale_bounds v hx t).2.1
  have hsr : s ≤ r := by
    exact (prismScale_bounds v hx t).2.2
  have hge : 1 ≤ s := (prismScale_bounds v hx t).1
  by_cases hqr : q ≤ r
  · left
    have hs : s = q := by
      change min q r = q
      exact min_eq_left hqr
    have hd : 2 - (t : ℝ) ≠ 0 := by linarith [t.2.1, t.2.2]
    change 2 - s * (2 - (t : ℝ)) = 0
    rw [hs]
    dsimp [q]
    field_simp [hd]
    ring
  · have hrq : r ≤ q := le_of_lt (lt_of_not_ge hqr)
    by_cases hn : 1 / 2 ≤ ‖v‖
    · right
      have hs : s = r := by
        change min q r = r
        exact min_eq_right hrq
      have hnormpos : 0 < ‖v‖ := by linarith
      have hmax : max ‖v‖ (1 / 2) = ‖v‖ := max_eq_left hn
      have hs0 : 0 ≤ s := le_trans (by norm_num) hge
      change ‖s • v‖ = 1
      calc
        ‖s • v‖ = |s| * ‖v‖ := by simp [norm_smul, Real.norm_eq_abs]
        _ = s * ‖v‖ := by rw [abs_of_nonneg hs0]
        _ = 1 := by
          rw [hs]
          dsimp [r]
          rw [hmax]
          field_simp [ne_of_gt hnormpos]
    · have hn' : ‖v‖ < 1 / 2 := lt_of_not_ge hn
      have hr' : r = 2 := by
        dsimp [r]
        rw [max_eq_right (le_of_lt hn')]
        norm_num
      have hq2 : q ≤ 2 := by
        have hd : 0 < 2 - (t : ℝ) := by linarith [t.2.1, t.2.2]
        apply (div_le_iff₀ hd).2
        have ht : 1 ≤ 2 - (t : ℝ) := by linarith [t.2.2]
        nlinarith
      have hq' : q = 2 := by rw [hr'] at hrq; linarith
      have ht' : (t : ℝ) = 1 := by
        dsimp [q] at hq'
        have hd : 2 - (t : ℝ) ≠ 0 := by linarith [t.2.1, t.2.2]
        field_simp at hq'
        linarith
      left
      have hs : s = 2 := by
        change min q r = 2
        rw [hr', hq']
        norm_num
      change 2 - s * (2 - (t : ℝ)) = 0
      rw [ht', hs]
      norm_num

private lemma prismRetraction_bottom (n : ℕ) (x : TopCat.disk.{u} n) :
    prismRetraction n (x, 0) = (x, 0) := by
  have hs := prismScale_at_zero (diskPoint n x) (norm_diskPoint_le n x)
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change prismScale (diskPoint n x) 0 • diskPoint n x = diskPoint n x
    rw [hs]
    simp
  · apply Subtype.ext
    simp [prismRetraction, prismTime, hs]

private lemma prismRetraction_side (n : ℕ) (x : TopCat.diskBoundary.{u} n)
    (t : unitInterval) :
    prismRetraction n (diskBoundaryInclusion n x, t) =
      (diskBoundaryInclusion n x, t) := by
  have hv : diskPoint n (diskBoundaryInclusion n x) = boundaryPoint n x := rfl
  have hx : ‖diskPoint n (diskBoundaryInclusion n x)‖ = 1 := by
    rw [hv]
    exact norm_boundaryPoint n x
  have hs := prismScale_on_boundary (diskPoint n (diskBoundaryInclusion n x)) hx t
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change prismScale (diskPoint n (diskBoundaryInclusion n x)) t •
      diskPoint n (diskBoundaryInclusion n x) = diskPoint n (diskBoundaryInclusion n x)
    rw [hs]
    simp
  · apply Subtype.ext
    simp [prismRetraction, prismTime, hs]

private noncomputable def boundaryAt (n : ℕ) (x : TopCat.disk.{u} n)
    (hx : ‖diskPoint n x‖ = 1) : TopCat.diskBoundary.{u} n :=
  ULift.up ⟨diskPoint n x, by
    apply Metric.mem_sphere.mpr
    simpa [dist_eq_norm] using hx⟩

private lemma diskBoundaryInclusion_boundaryAt (n : ℕ) (x : TopCat.disk.{u} n)
    (hx : ‖diskPoint n x‖ = 1) : diskBoundaryInclusion n (boundaryAt n x hx) = x := by
  apply ULift.ext
  apply Subtype.ext
  rfl

private def prismBottom (n : ℕ) : Set (TopCat.disk.{u} n × unitInterval) :=
  {p | (p.2 : ℝ) = 0}

private def prismSide (n : ℕ) : Set (TopCat.disk.{u} n × unitInterval) :=
  {p | ‖diskPoint n p.1‖ = 1}

private def prismBase (n : ℕ) : Set (TopCat.disk.{u} n × unitInterval) :=
  prismBottom n ∪ prismSide n

private lemma continuous_diskPoint (n : ℕ) :
    Continuous fun p : TopCat.disk.{u} n × unitInterval => diskPoint n p.1 := by
  exact continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)

private lemma isClosed_prismBottom (n : ℕ) : IsClosed (prismBottom n) := by
  unfold prismBottom
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_snd)

private lemma isClosed_prismSide (n : ℕ) : IsClosed (prismSide n) := by
  unfold prismSide
  exact isClosed_singleton.preimage (continuous_diskPoint n).norm

private noncomputable def prismPaste {Z : TopCat.{u}} (n : ℕ) (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z)) :
    TopCat.disk.{u} n × unitInterval → Z := by
  classical
  exact fun p => if h : ‖diskPoint n p.1‖ = 1 then a (boundaryAt n p.1 h) p.2 else f p.1

private noncomputable def boundaryOnSide (n : ℕ) (p : prismSide n) : TopCat.diskBoundary.{u} n :=
  boundaryAt n p.1.1 (by simpa [prismSide] using p.2)

private lemma continuous_boundaryOnSide (n : ℕ) : Continuous (boundaryOnSide n) := by
  have hv : Continuous (fun p : prismSide n => diskPoint n p.1.1) :=
    (continuous_diskPoint n).comp continuous_subtype_val
  exact continuous_uliftUp.comp (hv.subtype_mk fun p => by
    apply Metric.mem_sphere.mpr
    have hp : ‖diskPoint n p.1.1‖ = 1 := by simpa [prismSide] using p.2
    simpa [dist_eq_norm] using hp)

private noncomputable def prismSideFunction {Z : TopCat.{u}} (n : ℕ)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z)) (p : prismSide n) : Z :=
  a (boundaryOnSide n p) p.1.2

private lemma continuous_prismSideFunction {Z : TopCat.{u}} (n : ℕ)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z)) :
    Continuous (prismSideFunction n a) := by
  have hp : Continuous (fun p : prismSide n => a (boundaryOnSide n p)) :=
    a.hom.continuous.comp (continuous_boundaryOnSide n)
  have ht : Continuous (fun p : prismSide n => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have heval : Continuous fun q : C(unitInterval, Z) × unitInterval => q.1 q.2 :=
    ContinuousEval.continuous_eval
  exact heval.comp (hp.prodMk ht)

private lemma prismRetraction_mapsTo_base (n : ℕ)
    (p : TopCat.disk.{u} n × unitInterval) : prismRetraction n p ∈ prismBase n := by
  change prismTime n p.1 p.2 = 0 ∨ ‖prismVector n p.1 p.2‖ = 1
  exact prismRetraction_mem_base n p.1 p.2

private lemma prismPaste_eq_bottom {Z : TopCat.{u}} (n : ℕ)
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z))
    (hsq : a ≫ pathEval Z = diskBoundaryInclusion n ≫ f) :
    Set.EqOn (prismPaste n f a) (fun p => f p.1) (prismBottom n) := by
  have hzero : ∀ y : TopCat.diskBoundary.{u} n,
      a y 0 = f (diskBoundaryInclusion n y) := by
    intro y
    have hy := congrArg (fun k : TopCat.diskBoundary.{u} n ⟶ Z => k y) hsq
    simpa [pathEval] using hy
  intro p hp
  have ht : p.2 = 0 := by
    apply Subtype.ext
    exact hp
  by_cases hx : ‖diskPoint n p.1‖ = 1
  · simp [prismPaste, hx, ht, hzero, diskBoundaryInclusion_boundaryAt]
  · simp [prismPaste, hx]

private lemma prismPaste_domRestrict_side {Z : TopCat.{u}} (n : ℕ)
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z)) :
    (prismSide n).domRestrict (prismPaste n f a) = prismSideFunction n a := by
  funext p
  have hp : ‖diskPoint n p.1.1‖ = 1 := by simpa [prismSide] using p.2
  change prismPaste n f a p.1 = prismSideFunction n a p
  simp [prismPaste, prismSideFunction, boundaryOnSide, prismSide, hp]

private lemma continuousOn_prismPaste {Z : TopCat.{u}} (n : ℕ)
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z))
    (hsq : a ≫ pathEval Z = diskBoundaryInclusion n ≫ f) :
    ContinuousOn (prismPaste n f a) (prismBase n) := by
  have hbottom : ContinuousOn (fun p : TopCat.disk.{u} n × unitInterval => f p.1)
      (prismBottom n ∪ prismSide n) := by fun_prop
  have hside : ContinuousOn (prismPaste n f a) (prismSide n) := by
    rw [continuousOn_iff_continuous_domRestrict, prismPaste_domRestrict_side]
    exact continuous_prismSideFunction n a
  have hbottom' : ContinuousOn (prismPaste n f a) (prismBottom n) :=
    hbottom.mono (Set.subset_union_left) |>.congr (prismPaste_eq_bottom n f a hsq)
  change ContinuousOn (prismPaste n f a) (prismBottom n ∪ prismSide n)
  exact hbottom'.union_of_isClosed hside (isClosed_prismBottom n) (isClosed_prismSide n)

private lemma boundaryAt_inclusion (n : ℕ) (y : TopCat.diskBoundary.{u} n)
    (hy : ‖diskPoint n (diskBoundaryInclusion n y)‖ = 1) :
    boundaryAt n (diskBoundaryInclusion n y) hy = y := by
  apply ULift.ext
  apply Subtype.ext
  rfl

private lemma norm_diskBoundaryInclusion (n : ℕ) (y : TopCat.diskBoundary.{u} n) :
    ‖diskPoint n (diskBoundaryInclusion n y)‖ = 1 := by
  have h : diskPoint n (diskBoundaryInclusion n y) = boundaryPoint n y := rfl
  rw [h]
  exact norm_boundaryPoint n y

private lemma prismPaste_side {Z : TopCat.{u}} (n : ℕ)
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z))
    (y : TopCat.diskBoundary.{u} n) (t : unitInterval) :
    prismPaste n f a (diskBoundaryInclusion n y, t) = a y t := by
  have hy := norm_diskBoundaryInclusion n y
  have hboundary := boundaryAt_inclusion n y hy
  simp [prismPaste, hy, hboundary]

private lemma prismPaste_bottom {Z : TopCat.{u}} (n : ℕ)
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z))
    (hsq : a ≫ pathEval Z = diskBoundaryInclusion n ≫ f)
    (x : TopCat.disk.{u} n) : prismPaste n f a (x, 0) = f x := by
  have hx : (x, 0) ∈ prismBottom n := by simp [prismBottom]
  exact prismPaste_eq_bottom n f a hsq hx

private lemma boundaryLift (n : ℕ) {Z : TopCat.{u}}
    (f : TopCat.disk.{u} n ⟶ Z)
    (a : TopCat.diskBoundary.{u} n ⟶ TopCat.of C(unitInterval, Z))
    (hsq : a ≫ pathEval Z = diskBoundaryInclusion n ≫ f) :
    ∃ l : TopCat.disk.{u} n ⟶ TopCat.of C(unitInterval, Z),
      diskBoundaryInclusion n ≫ l = a ∧ l ≫ pathEval Z = f := by
  let G : C(TopCat.disk.{u} n × unitInterval, Z) :=
    ⟨fun p => prismPaste n f a (prismRetraction n p), by
      exact (continuousOn_prismPaste n f a hsq).comp_continuous
        (prismRetraction n).continuous (prismRetraction_mapsTo_base n)⟩
  let l : TopCat.disk.{u} n ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom G.curry
  refine ⟨l, ?_, ?_⟩
  · ext y t
    change G.curry (diskBoundaryInclusion n y) t = a y t
    rw [ContinuousMap.curry_apply]
    change prismPaste n f a (prismRetraction n (diskBoundaryInclusion n y, t)) = a y t
    rw [prismRetraction_side]
    exact prismPaste_side n f a y t
  · ext x
    change G.curry x 0 = f x
    rw [ContinuousMap.curry_apply]
    change prismPaste n f a (prismRetraction n (x, 0)) = f x
    rw [prismRetraction_bottom]
    exact prismPaste_bottom n f a hsq x

private lemma diskBoundaryInclusion_hasPathLift (n : ℕ) (Z : TopCat.{u}) :
    HasLiftingProperty (diskBoundaryInclusion.{u} n) (pathEval Z) := by
  constructor
  intro f g sq
  obtain ⟨l, hl₁, hl₂⟩ := boundaryLift n g f sq.w
  exact ⟨⟨l, hl₁, hl₂⟩⟩

private def pathEvaluationFamily (Z : TopCat.{u}) : MorphismProperty TopCat.{u} :=
  MorphismProperty.ofHoms (fun _ : Unit => pathEval Z)

private lemma diskBoundaryInclusion_pathEvaluationLLP (n : ℕ) (Z : TopCat.{u}) :
    (pathEvaluationFamily Z).llp (diskBoundaryInclusion.{u} n) := by
  intro X Y p hp
  rcases (MorphismProperty.ofHoms_iff (fun _ : Unit => pathEval Z) p).mp hp with ⟨_, hp⟩
  let e : Arrow.mk p ≅ Arrow.mk (pathEval Z) := eqToIso hp
  exact (HasLiftingProperty.iff_of_arrow_iso_right (diskBoundaryInclusion n) e).mpr
    (diskBoundaryInclusion_hasPathLift n Z)

private lemma relativeFiniteCellComplex_pathEvaluationLLP {A B : TopCat.{u}}
    (i : A ⟶ B) (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (Z : TopCat.{u}) : (pathEvaluationFamily Z).llp i := by
  let Q := (pathEvaluationFamily Z).llp
  have hcell : HomotopyHypothesis.Henry.Top.cellBoundaries ≤ Q := by
    intro X Y f hf
    rcases (MorphismProperty.ofHoms_iff
      (fun n : ℕ => diskBoundaryInclusion.{u} n) f).mp hf with ⟨n, hf⟩
    let eL : Arrow.mk (diskBoundaryInclusion n) ≅ Arrow.mk f := eqToIso hf.symm
    have hBoundary : HasLiftingProperty (diskBoundaryInclusion n) (pathEval Z) :=
      diskBoundaryInclusion_hasPathLift n Z
    have hLeft : HasLiftingProperty f (pathEval Z) :=
      (HasLiftingProperty.iff_of_arrow_iso_left eL (pathEval Z)).mp hBoundary
    change ∀ ⦃X' Y' : TopCat.{u}⦄ (p : X' ⟶ Y'),
      pathEvaluationFamily Z p → HasLiftingProperty f p
    intro X' Y' p hp
    rcases (MorphismProperty.ofHoms_iff (fun _ : Unit => pathEval Z) p).mp hp with ⟨_, hp⟩
    let eR : Arrow.mk p ≅ Arrow.mk (pathEval Z) := eqToIso hp
    exact (HasLiftingProperty.iff_of_arrow_iso_right f eR).mpr hLeft
  have hpush : HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ≤ Q :=
    (MorphismProperty.pushouts_le_iff).2 hcell
  have hIso : MorphismProperty.isomorphisms TopCat.{u} ≤ Q := by
    intro X Y f hf
    have hIso : IsIso f := (MorphismProperty.isomorphisms.iff f).1 hf
    letI := hIso
    exact MorphismProperty.llp_of_isIso (pathEvaluationFamily Z) f
  have hbase :
      HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u} ≤ Q := sup_le hpush hIso
  have hclosure :
      (HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure ≤ Q :=
    (MorphismProperty.multiplicativeClosure_le_iff _ _).2 hbase
  exact hclosure i hi

private lemma relativeFiniteCellComplex_hasPathLift {A B : TopCat.{u}}
    (i : A ⟶ B) (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (Z : TopCat.{u}) : HasLiftingProperty i (pathEval Z) := by
  have h := relativeFiniteCellComplex_pathEvaluationLLP i hi Z
  exact h (pathEval Z) ⟨Unit.unit⟩

private def swapContinuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] :
    C(X × Y, Y × X) := ⟨Prod.swap, by fun_prop⟩

private def homotopyPathMap {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
    {f g : C(X, Z)} (H : f.Homotopy g) : C(X, C(unitInterval, Z)) :=
  ContinuousMap.curry
    (H.toContinuousMap.comp (swapContinuous : C(X × unitInterval, unitInterval × X)))

private def pathEval1 (Z : TopCat.{u}) : TopCat.of C(unitInterval, Z) ⟶ Z :=
  TopCat.ofHom ⟨fun γ : C(unitInterval, Z) => γ 1, continuous_eval_const 1⟩

theorem relativeFiniteCellComplex_homotopyExtension_proof
    {A B Z : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (f : C(B, Z)) (g : C(A, Z)) (H : (f.comp i.hom).Homotopy g) :
    ∃ (g' : C(B, Z)) (H' : f.Homotopy g'),
      ∀ (t : unitInterval) (a : A), H' (t, i.hom a) = H (t, a) := by
  let a : A ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap H)
  have hsq : a ≫ pathEval Z = i ≫ TopCat.ofHom f := by
    ext x
    change a.hom x 0 = f (i.hom x)
    simp [a, homotopyPathMap, ContinuousMap.curry_apply, swapContinuous]
  have hLift := relativeFiniteCellComplex_hasPathLift i hi Z
  let sq : CommSq a i (pathEval Z) (TopCat.ofHom f) := ⟨hsq⟩
  obtain ⟨l, hl₁, hl₂⟩ := hLift.sq_hasLift sq
  let g' : C(B, Z) := (l ≫ pathEval1 Z).hom
  let H' : f.Homotopy g' := {
    toContinuousMap := (ContinuousMap.uncurry l.hom).comp
      (swapContinuous : C(unitInterval × B, B × unitInterval))
    map_zero_left := by
      intro x
      have hx := congrArg (fun m : B ⟶ Z => m x) hl₂
      simpa [pathEval, ContinuousMap.uncurry, swapContinuous] using hx
    map_one_left := by
      intro x
      simp [pathEval1, ContinuousMap.uncurry, swapContinuous, g']
  }
  refine ⟨g', H', ?_⟩
  intro t x
  change l (i.hom x) t = H (t, x)
  have hx := congrArg (fun m : A ⟶ TopCat.of C(unitInterval, Z) => m x t) hl₁
  simpa [a, homotopyPathMap, ContinuousMap.curry_apply, swapContinuous] using hx

noncomputable def homotopy_of_isPushout {A B C P Z : TopCat.{u}} (i : A ⟶ B)
    (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P) (h : IsPushout i f k j)
    {g₀ g₁ : C(P, Z)}
    (Hk : (g₀.comp k.hom).Homotopy (g₁.comp k.hom))
    (Hj : (g₀.comp j.hom).Homotopy (g₁.comp j.hom))
    (hc : ∀ (t : unitInterval) (a : A), Hk (t, i.hom a) =
      Hj (t, f.hom a)) : g₀.Homotopy g₁ := by
  let pB : B ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hk)
  let pC : C ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hj)
  have hp : i ≫ pB = f ≫ pC := by
    ext a t
    change Hk (t, i.hom a) = Hj (t, f.hom a)
    exact hc t a
  let d : P ⟶ TopCat.of C(unitInterval, Z) := h.desc pB pC hp
  have hdB : k ≫ d = pB := by simp [d]
  have hdC : j ≫ d = pC := by simp [d]
  have hzB : k ≫ d ≫ pathEval Z = k ≫ TopCat.ofHom g₀ := by
    change (k ≫ d) ≫ pathEval Z = k ≫ TopCat.ofHom g₀
    rw [hdB]
    ext b
    change (homotopyPathMap Hk) b 0 = g₀ (k.hom b)
    simp [homotopyPathMap, swapContinuous]
  have hzC : j ≫ d ≫ pathEval Z = j ≫ TopCat.ofHom g₀ := by
    change (j ≫ d) ≫ pathEval Z = j ≫ TopCat.ofHom g₀
    rw [hdC]
    ext c
    change (homotopyPathMap Hj) c 0 = g₀ (j.hom c)
    simp [homotopyPathMap, swapContinuous]
  have hoB : k ≫ d ≫ pathEval1 Z = k ≫ TopCat.ofHom g₁ := by
    change (k ≫ d) ≫ pathEval1 Z = k ≫ TopCat.ofHom g₁
    rw [hdB]
    ext b
    change (homotopyPathMap Hk) b 1 = g₁ (k.hom b)
    simp [homotopyPathMap, swapContinuous]
  have hoC : j ≫ d ≫ pathEval1 Z = j ≫ TopCat.ofHom g₁ := by
    change (j ≫ d) ≫ pathEval1 Z = j ≫ TopCat.ofHom g₁
    rw [hdC]
    ext c
    change (homotopyPathMap Hj) c 1 = g₁ (j.hom c)
    simp [homotopyPathMap, swapContinuous]
  have hz : d ≫ pathEval Z = TopCat.ofHom g₀ := h.hom_ext hzB hzC
  have ho : d ≫ pathEval1 Z = TopCat.ofHom g₁ := h.hom_ext hoB hoC
  refine {
    toContinuousMap := (ContinuousMap.uncurry d.hom).comp
      (swapContinuous : C(unitInterval × P, P × unitInterval))
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro x
    change d.hom x 0 = g₀ x
    have hx := congrArg (fun m : P ⟶ Z => m.hom x) hz
    simpa [pathEval, ContinuousMap.comp_apply] using hx
  · intro x
    change d.hom x 1 = g₁ x
    have hx := congrArg (fun m : P ⟶ Z => m.hom x) ho
    simpa [pathEval1, ContinuousMap.comp_apply] using hx

private noncomputable def homotopy_of_isPushoutLeftData {A B C P Z : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P) (h : IsPushout i f k j)
    {g₀ g₁ : C(P, Z)} (Hk : (g₀.comp k.hom).Homotopy (g₁.comp k.hom))
    (Hj : (g₀.comp j.hom).Homotopy (g₁.comp j.hom))
    (hc : ∀ (t : unitInterval) (a : A), Hk (t, i.hom a) = Hj (t, f.hom a)) :
    {H : g₀.Homotopy g₁ // ∀ (t : unitInterval) (b : B), H (t, k.hom b) = Hk (t, b)} := by
  let pB : B ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hk)
  let pC : C ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hj)
  have hp : i ≫ pB = f ≫ pC := by
    ext a t
    exact hc t a
  let d : P ⟶ TopCat.of C(unitInterval, Z) := h.desc pB pC hp
  have hdB : k ≫ d = pB := by simp [d]
  have hdC : j ≫ d = pC := by simp [d]
  have hzB : k ≫ d ≫ pathEval Z = k ≫ TopCat.ofHom g₀ := by
    change (k ≫ d) ≫ pathEval Z = k ≫ TopCat.ofHom g₀
    rw [hdB]
    ext b
    change (homotopyPathMap Hk) b 0 = g₀ (k.hom b)
    simp [homotopyPathMap, swapContinuous]
  have hzC : j ≫ d ≫ pathEval Z = j ≫ TopCat.ofHom g₀ := by
    change (j ≫ d) ≫ pathEval Z = j ≫ TopCat.ofHom g₀
    rw [hdC]
    ext c
    change (homotopyPathMap Hj) c 0 = g₀ (j.hom c)
    simp [homotopyPathMap, swapContinuous]
  have hoB : k ≫ d ≫ pathEval1 Z = k ≫ TopCat.ofHom g₁ := by
    change (k ≫ d) ≫ pathEval1 Z = k ≫ TopCat.ofHom g₁
    rw [hdB]
    ext b
    change (homotopyPathMap Hk) b 1 = g₁ (k.hom b)
    simp [homotopyPathMap, swapContinuous]
  have hoC : j ≫ d ≫ pathEval1 Z = j ≫ TopCat.ofHom g₁ := by
    change (j ≫ d) ≫ pathEval1 Z = j ≫ TopCat.ofHom g₁
    rw [hdC]
    ext c
    change (homotopyPathMap Hj) c 1 = g₁ (j.hom c)
    simp [homotopyPathMap, swapContinuous]
  have hz : d ≫ pathEval Z = TopCat.ofHom g₀ := h.hom_ext hzB hzC
  have ho : d ≫ pathEval1 Z = TopCat.ofHom g₁ := h.hom_ext hoB hoC
  let H : g₀.Homotopy g₁ := {
    toContinuousMap := (ContinuousMap.uncurry d.hom).comp
      (swapContinuous : C(unitInterval × P, P × unitInterval))
    map_zero_left := by
      intro x
      change d.hom x 0 = g₀ x
      have hx := congrArg (fun m : P ⟶ Z => m.hom x) hz
      simpa [pathEval, ContinuousMap.comp_apply] using hx
    map_one_left := by
      intro x
      change d.hom x 1 = g₁ x
      have hx := congrArg (fun m : P ⟶ Z => m.hom x) ho
      simpa [pathEval1, ContinuousMap.comp_apply] using hx
  }
  refine ⟨H, ?_⟩
  intro t b
  change d.hom (k.hom b) t = Hk (t, b)
  have hb := congrArg (fun g : B ⟶ TopCat.of C(unitInterval, Z) => g.hom b t) hdB
  simpa [pB, homotopyPathMap, swapContinuous] using hb

private theorem homotopy_of_isPushout_left {A B C P Z : TopCat.{u}} (i : A ⟶ B)
    (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P) (h : IsPushout i f k j)
    {g₀ g₁ : C(P, Z)} (Hk : (g₀.comp k.hom).Homotopy (g₁.comp k.hom))
    (Hj : (g₀.comp j.hom).Homotopy (g₁.comp j.hom))
    (hc : ∀ (t : unitInterval) (a : A), Hk (t, i.hom a) = Hj (t, f.hom a)) :
    ∀ (t : unitInterval) (b : B),
      homotopy_of_isPushout i f k j h Hk Hj hc (t, k.hom b) = Hk (t, b) := by
  let pB : B ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hk)
  let pC : C ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom (homotopyPathMap Hj)
  have hp : i ≫ pB = f ≫ pC := by
    ext a t
    exact hc t a
  let d : P ⟶ TopCat.of C(unitInterval, Z) := h.desc pB pC hp
  have hdB : k ≫ d = pB := by simp [d]
  intro t b
  change d.hom (k.hom b) t = Hk (t, b)
  have hb := congrArg (fun g : B ⟶ TopCat.of C(unitInterval, Z) => g.hom b t) hdB
  simpa [pB, homotopyPathMap, swapContinuous] using hb

private def cylinderBottom (A : TopCat.{u}) : A ⟶ TopCat.of (A × unitInterval) :=
  TopCat.ofHom ⟨fun a => (a, 0), by fun_prop⟩

def cylinderTop (A : TopCat.{u}) : A ⟶ TopCat.of (A × unitInterval) :=
  TopCat.ofHom ⟨fun a => (a, 1), by fun_prop⟩

noncomputable def mappingCylinder {A C : TopCat.{u}} (f : A ⟶ C) : TopCat.{u} :=
  pushout (cylinderBottom A) f

noncomputable def mappingCylinderCylinder {A C : TopCat.{u}} (f : A ⟶ C) :
    TopCat.of (A × unitInterval) ⟶ mappingCylinder f :=
  pushout.inl (cylinderBottom A) f

noncomputable def mappingCylinderBase {A C : TopCat.{u}} (f : A ⟶ C) :
    C ⟶ mappingCylinder f :=
  pushout.inr (cylinderBottom A) f

noncomputable def mappingCylinderTop {A C : TopCat.{u}} (f : A ⟶ C) :
    A ⟶ mappingCylinder f :=
  cylinderTop A ≫ mappingCylinderCylinder f

private noncomputable def cylinderExtensionParameter (r t : unitInterval) : ℝ :=
  (r : ℝ) + min (r : ℝ) t

private lemma cylinderExtensionParameter_bounds (r t : unitInterval) :
    0 ≤ cylinderExtensionParameter r t ∧ cylinderExtensionParameter r t ≤ 2 := by
  have hr0 : 0 ≤ (r : ℝ) := r.2.1
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have hr1 : (r : ℝ) ≤ 1 := r.2.2
  have hmin0 : 0 ≤ min (r : ℝ) t := le_min hr0 ht0
  have hmin1 : min (r : ℝ) t ≤ 1 := (min_le_left _ _).trans hr1
  constructor <;> dsimp [cylinderExtensionParameter] <;> linarith

private noncomputable def cylinderExtensionSquare (r t : unitInterval) :
    unitInterval × unitInterval :=
  let s := cylinderExtensionParameter r t
  (⟨min s 1, ⟨le_min (cylinderExtensionParameter_bounds r t).1 (by norm_num),
      min_le_right _ _⟩⟩,
    ⟨max (s - 1) 0, ⟨le_max_right _ _, max_le (by
      have hs := (cylinderExtensionParameter_bounds r t).2
      linarith) (by norm_num)⟩⟩)

private lemma continuous_cylinderExtensionParameter :
    Continuous fun p : unitInterval × unitInterval =>
      cylinderExtensionParameter p.1 p.2 := by
  change Continuous fun p : unitInterval × unitInterval =>
    (p.1 : ℝ) + min (p.1 : ℝ) p.2
  fun_prop

private lemma continuous_cylinderExtensionSquare :
    Continuous fun p : unitInterval × unitInterval =>
      cylinderExtensionSquare p.1 p.2 := by
  have hs := continuous_cylinderExtensionParameter
  have hx : Continuous fun p : unitInterval × unitInterval =>
      (⟨min (cylinderExtensionParameter p.1 p.2) 1,
        ⟨le_min (cylinderExtensionParameter_bounds p.1 p.2).1 (by norm_num),
          min_le_right _ _⟩⟩ : unitInterval) := by
    exact (hs.min continuous_const).subtype_mk fun p =>
      ⟨le_min (cylinderExtensionParameter_bounds p.1 p.2).1 (by norm_num), min_le_right _ _⟩
  have hy : Continuous fun p : unitInterval × unitInterval =>
      (⟨max (cylinderExtensionParameter p.1 p.2 - 1) 0,
        ⟨le_max_right _ _, max_le (by
          have hs' := (cylinderExtensionParameter_bounds p.1 p.2).2
          change cylinderExtensionParameter p.1 p.2 - 1 ≤ 1
          linarith) (by norm_num)⟩⟩ : unitInterval) := by
    exact ((hs.sub continuous_const).max continuous_const).subtype_mk fun p =>
      ⟨le_max_right _ _, max_le (by
        have hs' := (cylinderExtensionParameter_bounds p.1 p.2).2
        change cylinderExtensionParameter p.1 p.2 - 1 ≤ 1
        linarith) (by norm_num)⟩
  change Continuous fun p : unitInterval × unitInterval =>
    ((⟨min (cylinderExtensionParameter p.1 p.2) 1, _⟩ : unitInterval),
      (⟨max (cylinderExtensionParameter p.1 p.2 - 1) 0, _⟩ : unitInterval))
  exact hx.prodMk hy

private lemma cylinderExtensionSquare_bottom (r : unitInterval) :
    cylinderExtensionSquare r 0 = (r, 0) := by
  ext <;>
    simp [cylinderExtensionSquare, cylinderExtensionParameter,
      min_eq_right (show (0 : ℝ) ≤ (r : ℝ) by exact r.2.1),
      max_eq_right (show (r : ℝ) - 1 ≤ 0 by linarith [r.2.2])] <;>
    linarith [r.2.1, r.2.2]

private lemma cylinderExtensionSquare_left (t : unitInterval) :
    cylinderExtensionSquare 0 t = (0, 0) := by
  ext <;>
    simp [cylinderExtensionSquare, cylinderExtensionParameter,
      min_eq_left (show (0 : ℝ) ≤ (t : ℝ) by exact t.2.1)] <;>
    linarith [t.2.1, t.2.2]

private lemma cylinderExtensionSquare_right (t : unitInterval) :
    (cylinderExtensionSquare 1 t).1 = 1 ∧
      (cylinderExtensionSquare 1 t).2 = t := by
  constructor <;> apply Subtype.ext <;>
    simp [cylinderExtensionSquare, cylinderExtensionParameter,
      min_eq_right (show (t : ℝ) ≤ 1 by exact t.2.2),
      max_eq_left (show (0 : ℝ) ≤ (t : ℝ) by exact t.2.1)] <;>
    linarith [t.2.1, t.2.2]

private noncomputable def cylinderExtensionHomotopyMap {A C Z : TopCat.{u}}
    (f : A ⟶ C) (F : C(mappingCylinder f, Z)) {g : C(A, Z)}
    (K : (F.comp (mappingCylinderTop f).hom).Homotopy g) :
    C(unitInterval × (A × unitInterval), Z) where
  toFun p :=
    if cylinderExtensionParameter p.2.2 p.1 ≤ 1 then
      F ((mappingCylinderCylinder f).hom
        (p.2.1, (cylinderExtensionSquare p.2.2 p.1).1))
    else K ((cylinderExtensionSquare p.2.2 p.1).2, p.2.1)
  continuous_toFun := by
    have hcoords : Continuous fun p : unitInterval × (A × unitInterval) =>
        (p.2.2, p.1) :=
      (continuous_snd.comp continuous_snd).prodMk continuous_fst
    have hsquare : Continuous fun p : unitInterval × (A × unitInterval) =>
        cylinderExtensionSquare p.2.2 p.1 :=
      continuous_cylinderExtensionSquare.comp hcoords
    have ha : Continuous fun p : unitInterval × (A × unitInterval) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hleft : Continuous fun p : unitInterval × (A × unitInterval) =>
        F ((mappingCylinderCylinder f).hom
          (p.2.1, (cylinderExtensionSquare p.2.2 p.1).1)) := by
      exact F.continuous.comp ((mappingCylinderCylinder f).hom.continuous.comp
        (ha.prodMk (continuous_fst.comp hsquare)))
    have hright : Continuous fun p : unitInterval × (A × unitInterval) =>
        K ((cylinderExtensionSquare p.2.2 p.1).2, p.2.1) := by
      exact K.toContinuousMap.continuous.comp
        ((continuous_snd.comp hsquare).prodMk ha)
    have hparam : Continuous fun p : unitInterval × (A × unitInterval) =>
        cylinderExtensionParameter p.2.2 p.1 :=
      continuous_cylinderExtensionParameter.comp hcoords
    have hclosed : IsClosed {p : unitInterval × (A × unitInterval) |
        cylinderExtensionParameter p.2.2 p.1 ≤ 1} :=
      isClosed_Iic.preimage hparam
    have hfront : ∀ p ∈ frontier {p : unitInterval × (A × unitInterval) |
        cylinderExtensionParameter p.2.2 p.1 ≤ 1},
        F ((mappingCylinderCylinder f).hom
          (p.2.1, (cylinderExtensionSquare p.2.2 p.1).1)) =
          K ((cylinderExtensionSquare p.2.2 p.1).2, p.2.1) := by
      intro p hp
      have hpS : p ∈ {q : unitInterval × (A × unitInterval) |
          cylinderExtensionParameter q.2.2 q.1 ≤ 1} :=
        hclosed.closure_subset (frontier_subset_closure hp)
      have hle : cylinderExtensionParameter p.2.2 p.1 ≤ 1 := hpS
      have hpnotint : p ∉ interior {q : unitInterval × (A × unitInterval) |
          cylinderExtensionParameter q.2.2 q.1 ≤ 1} :=
        (mem_frontier_iff_notMem_interior hpS).mp hp
      have hge : 1 ≤ cylinderExtensionParameter p.2.2 p.1 := by
        by_contra hn
        have hlt : cylinderExtensionParameter p.2.2 p.1 < 1 := lt_of_not_ge hn
        have hopen : IsOpen {q : unitInterval × (A × unitInterval) |
            cylinderExtensionParameter q.2.2 q.1 < 1} :=
          isOpen_Iio.preimage hparam
        have hnbh : {q : unitInterval × (A × unitInterval) |
            cylinderExtensionParameter q.2.2 q.1 < 1} ∈ 𝓝 p :=
          hopen.mem_nhds hlt
        have hsub : {q : unitInterval × (A × unitInterval) |
            cylinderExtensionParameter q.2.2 q.1 < 1} ⊆
              {q | cylinderExtensionParameter q.2.2 q.1 ≤ 1} := by
          intro q hq
          change cylinderExtensionParameter q.2.2 q.1 < 1 at hq
          exact le_of_lt hq
        have hinter : p ∈ interior {q : unitInterval × (A × unitInterval) |
            cylinderExtensionParameter q.2.2 q.1 ≤ 1} :=
          (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hnbh hsub)
        exact hpnotint hinter
      have heq : cylinderExtensionParameter p.2.2 p.1 = 1 := le_antisymm hle hge
      have hsq : cylinderExtensionSquare p.2.2 p.1 = (1, 0) := by
        ext <;>
          simp [cylinderExtensionSquare, heq]
      rw [hsq]
      simpa [mappingCylinderTop, cylinderTop, ContinuousMap.comp_apply] using
        (K.apply_zero p.2.1).symm
    exact hleft.if hfront hright

private theorem mappingCylinderIsPushout {A C : TopCat.{u}} (f : A ⟶ C) :
    IsPushout (cylinderBottom A) f (mappingCylinderCylinder f) (mappingCylinderBase f) :=
  IsPushout.of_hasPushout _ _

private theorem cylinderExtensionHomotopyMap_top {A C Z : TopCat.{u}}
    (f : A ⟶ C) (F : C(mappingCylinder f, Z)) {g : C(A, Z)}
    (K : (F.comp (mappingCylinderTop f).hom).Homotopy g)
    (t : unitInterval) (a : A) :
    cylinderExtensionHomotopyMap f F K (t, (a, 1)) = K (t, a) := by
  by_cases ht0 : (t : ℝ) = 0
  · have ht : t = 0 := Subtype.ext ht0
    subst t
    obtain ⟨hsq₁, hsq₂⟩ := cylinderExtensionSquare_right (0 : unitInterval)
    change (cylinderExtensionHomotopyMap f F K).toFun (0, (a, 1)) = K (0, a)
    dsimp [cylinderExtensionHomotopyMap]
    rw [if_pos (by simp [cylinderExtensionParameter])]
    rw [hsq₁]
    change F ((mappingCylinderTop f).hom a) = K (0, a)
    exact (K.apply_zero a).symm
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
    have hparam : cylinderExtensionParameter (1 : unitInterval) t = 1 + (t : ℝ) := by
      simp [cylinderExtensionParameter, min_eq_right t.2.2]
    have hgt : ¬ cylinderExtensionParameter (1 : unitInterval) t ≤ 1 := by
      rw [hparam]
      linarith
    change (cylinderExtensionHomotopyMap f F K).toFun (t, (a, 1)) = K (t, a)
    dsimp [cylinderExtensionHomotopyMap]
    obtain ⟨hsq₁, hsq₂⟩ := cylinderExtensionSquare_right t
    rw [if_neg hgt, hsq₂]

private theorem mappingCylinderTop_homotopyExtension {A C Z : TopCat.{u}}
    (f : A ⟶ C) (F : C(mappingCylinder f, Z)) {g : C(A, Z)}
    (K : (F.comp (mappingCylinderTop f).hom).Homotopy g) :
    ∃ (g' : C(mappingCylinder f, Z)) (H : F.Homotopy g'),
      ∀ (t : unitInterval) (a : A),
        H (t, (mappingCylinderTop f).hom a) = K (t, a) := by
  let m := mappingCylinderCylinder f
  let c := mappingCylinderBase f
  let E := cylinderExtensionHomotopyMap f F K
  let gB : C(TopCat.of (A × unitInterval), Z) := {
    toFun := fun p => E (1, p)
    continuous_toFun := E.continuous.comp (continuous_const.prodMk continuous_id)
  }
  let baseMap : C(C, Z) := F.comp c.hom
  let Hm : (F.comp m.hom).Homotopy gB := {
    toContinuousMap := E
    map_zero_left := by
      intro p
      rcases p with ⟨a, r⟩
      change (cylinderExtensionHomotopyMap f F K).toFun (0, (a, r)) = F (m.hom (a, r))
      have hparam : cylinderExtensionParameter r 0 ≤ 1 := by
        have hr : cylinderExtensionParameter r 0 = (r : ℝ) := by
          simp [cylinderExtensionParameter, min_eq_right r.2.1]
        rw [hr]
        exact r.2.2
      dsimp [cylinderExtensionHomotopyMap]
      rw [if_pos hparam, cylinderExtensionSquare_bottom]
    map_one_left := by
      intro p
      rfl
  }
  let hP := mappingCylinderIsPushout f
  have hEnd : cylinderBottom A ≫ TopCat.ofHom gB = f ≫ TopCat.ofHom baseMap := by
    ext a
    change gB (a, 0) = baseMap (f.hom a)
    have hbottom : m.hom (a, 0) = c.hom (f.hom a) := by
      have hh := congrArg (fun q : A ⟶ mappingCylinder f => q.hom a) hP.w
      simpa [cylinderBottom] using hh
    change (cylinderExtensionHomotopyMap f F K).toFun (1, (a, 0)) =
      F (c.hom (f.hom a))
    dsimp [cylinderExtensionHomotopyMap]
    rw [if_pos (by simp [cylinderExtensionParameter]), cylinderExtensionSquare_left]
    change F (m.hom (a, 0)) = F (c.hom (f.hom a))
    rw [hbottom]
  let gMap : mappingCylinder f ⟶ Z := hP.desc (TopCat.ofHom gB)
    (TopCat.ofHom baseMap) hEnd
  have hdescB : m ≫ gMap = TopCat.ofHom gB := hP.inl_desc _ _ hEnd
  have hdescC : c ≫ gMap = TopCat.ofHom baseMap := hP.inr_desc _ _ hEnd
  have hBend : (m ≫ gMap).hom = gB := by
    simpa [TopCat.comp_app] using congrArg TopCat.Hom.hom hdescB
  have hCend : (c ≫ gMap).hom = baseMap := by
    simpa [TopCat.comp_app] using congrArg TopCat.Hom.hom hdescC
  let Hm' := Hm.cast rfl hBend.symm
  let Hc' := (ContinuousMap.Homotopy.refl baseMap).cast rfl hCend.symm
  have hbottom (a : A) : m.hom (a, 0) = c.hom (f.hom a) := by
    have hh := congrArg (fun q : A ⟶ mappingCylinder f => q.hom a) hP.w
    simpa [cylinderBottom] using hh
  have hcompat : ∀ (t : unitInterval) (a : A),
      Hm' (t, cylinderBottom A a) = Hc' (t, f.hom a) := by
    intro t a
    change (cylinderExtensionHomotopyMap f F K).toFun (t, (a, 0)) =
      baseMap (f.hom a)
    have h := hbottom a
    dsimp [cylinderExtensionHomotopyMap]
    rw [if_pos (by simp [cylinderExtensionParameter]), cylinderExtensionSquare_left]
    change F (m.hom (a, 0)) = baseMap (f.hom a)
    rw [h]
    change F (c.hom (f.hom a)) = F (c.hom (f.hom a))
    rfl
  let Hdata := homotopy_of_isPushoutLeftData (g₀ := F) (g₁ := gMap.hom)
    (cylinderBottom A) f m c hP Hm' Hc' hcompat
  refine ⟨gMap.hom, Hdata.val, ?_⟩
  intro t a
  have hleft := Hdata.property t (a, 1)
  simpa [mappingCylinderTop, cylinderTop] using
    hleft.trans (cylinderExtensionHomotopyMap_top f F K t a)

private def cylinderShrink {A : TopCat.{u}} :
    C(unitInterval × (A × unitInterval), A × unitInterval) where
  toFun p := (p.2.1, p.2.2 * p.1)
  continuous_toFun := by fun_prop

private def mappingCylinderCylinderCollapseMap {A C : TopCat.{u}} (f : A ⟶ C) :
    TopCat.of (A × unitInterval) ⟶ C :=
  TopCat.ofHom ⟨fun p => f.hom p.1, f.hom.continuous.comp continuous_fst⟩

noncomputable def mappingCylinderCollapse {A C : TopCat.{u}} (f : A ⟶ C) :
    mappingCylinder f ⟶ C := by
  have hq : cylinderBottom A ≫ mappingCylinderCylinderCollapseMap f = f ≫ (𝟙 C) := by
    ext a
    rfl
  exact (mappingCylinderIsPushout f).desc (mappingCylinderCylinderCollapseMap f) (𝟙 C) hq

theorem mappingCylinderCollapse_cylinder {A C : TopCat.{u}} (f : A ⟶ C) :
    mappingCylinderCylinder f ≫ mappingCylinderCollapse f =
      mappingCylinderCylinderCollapseMap f := by
  simp [mappingCylinderCollapse]

theorem mappingCylinderCollapse_base {A C : TopCat.{u}} (f : A ⟶ C) :
    mappingCylinderBase f ≫ mappingCylinderCollapse f = 𝟙 C := by
  simp [mappingCylinderCollapse]

theorem mappingCylinderTop_collapse {A C : TopCat.{u}} (f : A ⟶ C) :
    mappingCylinderTop f ≫ mappingCylinderCollapse f = f := by
  ext a
  have h := congrArg (fun g : TopCat.of (A × unitInterval) ⟶ C => g.hom (a, 1))
    (mappingCylinderCollapse_cylinder f)
  simpa [mappingCylinderTop, cylinderTop, mappingCylinderCylinderCollapseMap,
    ContinuousMap.comp_apply] using h

private noncomputable def mappingCylinderSection {A C : TopCat.{u}} (f : A ⟶ C) :
    C ⟶ mappingCylinder f := mappingCylinderBase f

set_option maxHeartbeats 500000 in
private noncomputable def mappingCylinderCollapse_sourceData {A C : TopCat.{u}} (f : A ⟶ C) :
    {H : (mappingCylinderCollapse f ≫ mappingCylinderBase f).hom.Homotopy
          (ContinuousMap.id (mappingCylinder f)) //
      ∀ (t : unitInterval) (a : A) (r : unitInterval),
        H (t, (mappingCylinderCylinder f).hom (a, r)) =
          (mappingCylinderCylinder f).hom (a, r * t)} := by
  let c := mappingCylinderBase f
  let q := mappingCylinderCollapse f
  let s := c
  have hbot : cylinderBottom A ≫ mappingCylinderCylinder f = f ≫ c :=
    (mappingCylinderIsPushout f).w
  let Hm : (mappingCylinderCylinder f ≫ q ≫ s).hom.Homotopy
      (mappingCylinderCylinder f).hom := {
    toContinuousMap := (mappingCylinderCylinder f).hom.comp cylinderShrink
    map_zero_left := by
      intro p
      rcases p with ⟨a, t⟩
      change (mappingCylinderCylinder f).hom (a, t * 0) =
        (mappingCylinderCylinder f ≫ q ≫ s).hom (a, t)
      simp only [mul_zero]
      have hbottom := congrArg (fun g : A ⟶ mappingCylinder f => g.hom a) hbot
      have hcollapse := congrArg
        (fun g : TopCat.of (A × unitInterval) ⟶ C => g.hom (a, t))
        (mappingCylinderCollapse_cylinder f)
      change (mappingCylinderCylinder f).hom (a, 0) =
        s.hom (q.hom ((mappingCylinderCylinder f).hom (a, t)))
      calc
        (mappingCylinderCylinder f).hom (a, 0) = c.hom (f.hom a) := by
          simpa [cylinderBottom] using hbottom
        _ = s.hom (q.hom ((mappingCylinderCylinder f).hom (a, t))) := by
          have hcollapse' : q.hom ((mappingCylinderCylinder f).hom (a, t)) = f.hom a := by
            simpa [q, mappingCylinderCylinderCollapseMap,
              ContinuousMap.comp_apply] using hcollapse
          rw [hcollapse']
    map_one_left := by
      intro p
      rcases p with ⟨a, t⟩
      simp [cylinderShrink, ContinuousMap.comp_apply]
  }
  have hcq : c ≫ q = 𝟙 C := by simp [c, q, mappingCylinderCollapse]
  have hcs : c ≫ q ≫ s = s := by
    calc
      c ≫ q ≫ s = (c ≫ q) ≫ s := (Category.assoc _ _ _).symm
      _ = (𝟙 C) ≫ s := by rw [hcq]
      _ = s := Category.id_comp _
  have hcs' : c ≫ q ≫ s = c := by simpa [s] using hcs
  let Hc : (c ≫ q ≫ s).hom.Homotopy c.hom :=
    (ContinuousMap.Homotopy.refl c.hom).cast
      (congrArg TopCat.Hom.hom hcs'.symm) rfl
  have hcompat : ∀ (t : unitInterval) (a : A), Hm (t, cylinderBottom A a) =
      Hc (t, f.hom a) := by
    intro t a
    dsimp [Hm, Hc, cylinderBottom, cylinderShrink,
      ContinuousMap.Homotopy.cast, ContinuousMap.Homotopy.refl]
    change (mappingCylinderCylinder f).hom (a, (0 : unitInterval) * t) =
      c.hom (f.hom a)
    have h := congrArg (fun g : A ⟶ mappingCylinder f => g.hom a) hbot
    simpa [cylinderBottom] using h
  let Hdata := homotopy_of_isPushoutLeftData (g₀ := (q ≫ s).hom)
    (g₁ := ContinuousMap.id (mappingCylinder f)) (cylinderBottom A) f
    (mappingCylinderCylinder f) (mappingCylinderBase f)
    (mappingCylinderIsPushout f) Hm Hc hcompat
  refine ⟨Hdata.val, ?_⟩
  intro t a r
  have hright : Hm (t, (a, r)) = (mappingCylinderCylinder f).hom (a, r * t) := rfl
  exact (Hdata.property t (a, r)).trans hright

private noncomputable def mappingCylinderCollapse_sourceHomotopy {A C : TopCat.{u}}
    (f : A ⟶ C) : (mappingCylinderCollapse f ≫ mappingCylinderBase f).hom.Homotopy
      (ContinuousMap.id (mappingCylinder f)) := (mappingCylinderCollapse_sourceData f).val

private theorem mappingCylinderCollapse_sourceHomotopy_top {A C : TopCat.{u}}
    (f : A ⟶ C) (t : unitInterval) (a : A) :
    mappingCylinderCollapse_sourceHomotopy f (t, mappingCylinderTop f a) =
      (mappingCylinderCylinder f).hom (a, t) := by
  simpa [mappingCylinderCollapse_sourceHomotopy, mappingCylinderTop, cylinderTop] using
    (mappingCylinderCollapse_sourceData f).property t a 1

theorem mappingCylinderCollapse_homotopyEquivalence {A C : TopCat.{u}}
    (f : A ⟶ C) :
    HomotopyHypothesis.Henry.Top.homotopyEquivalences (mappingCylinderCollapse f) := by
  refine ⟨mappingCylinderBase f, ⟨mappingCylinderCollapse_sourceHomotopy f⟩, ?_⟩
  have hsec : mappingCylinderBase f ≫ mappingCylinderCollapse f = 𝟙 C := by
    simp [mappingCylinderCollapse]
  simpa [hsec] using (ContinuousMap.Homotopic.refl (ContinuousMap.id C))

theorem homotopyEquivalences_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HomotopyHypothesis.Henry.Top.homotopyEquivalences f)
    (hg : HomotopyHypothesis.Henry.Top.homotopyEquivalences g) :
    HomotopyHypothesis.Henry.Top.homotopyEquivalences (f ≫ g) := by
  obtain ⟨fInv, hfl, hfr⟩ := hf
  obtain ⟨gInv, hgl, hgr⟩ := hg
  refine ⟨gInv ≫ fInv, ?_, ?_⟩
  · have h₁ : ((g ≫ gInv).hom.comp f.hom).Homotopic f.hom :=
      ⟨hgl.some.compContinuousMap f.hom⟩
    have h₂ := ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl fInv.hom) h₁
    exact h₂.trans hfl
  · have h₁ : ((fInv ≫ f).hom.comp gInv.hom).Homotopic gInv.hom :=
      ⟨hfr.some.compContinuousMap gInv.hom⟩
    have h₂ := ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl g.hom) h₁
    exact h₂.trans hgr

noncomputable def mappingCylinderMap {A C A' C' : TopCat.{u}}
    (f : A ⟶ C) (f' : A' ⟶ C') (vA : A ⟶ A') (vC : C ⟶ C')
    (hc : f ≫ vC = vA ≫ f') : mappingCylinder f ⟶ mappingCylinder f' := by
  let cylMap : TopCat.of (A × unitInterval) ⟶ mappingCylinder f' :=
    TopCat.ofHom (vA.hom.prodMap (ContinuousMap.id unitInterval)) ≫
      mappingCylinderCylinder f'
  let baseMap : C ⟶ mappingCylinder f' := vC ≫ mappingCylinderBase f'
  have hprod : cylinderBottom A ≫
      TopCat.ofHom (vA.hom.prodMap (ContinuousMap.id unitInterval)) =
        vA ≫ cylinderBottom A' := by
    ext a
    · rfl
    · simp [cylinderBottom, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply]
  have hbot : cylinderBottom A' ≫ mappingCylinderCylinder f' =
      f' ≫ mappingCylinderBase f' := (mappingCylinderIsPushout f').w
  have hsq : cylinderBottom A ≫ cylMap = f ≫ baseMap := by
    calc
      cylinderBottom A ≫ cylMap =
          (cylinderBottom A ≫ TopCat.ofHom
            (vA.hom.prodMap (ContinuousMap.id unitInterval))) ≫
              mappingCylinderCylinder f' := by simp [cylMap, Category.assoc]
      _ = (vA ≫ cylinderBottom A') ≫ mappingCylinderCylinder f' := by rw [hprod]
      _ = vA ≫ (cylinderBottom A' ≫ mappingCylinderCylinder f') := Category.assoc _ _ _
      _ = vA ≫ (f' ≫ mappingCylinderBase f') := by rw [hbot]
      _ = (vA ≫ f') ≫ mappingCylinderBase f' := (Category.assoc _ _ _).symm
      _ = (f ≫ vC) ≫ mappingCylinderBase f' := by rw [← hc]
      _ = f ≫ baseMap := by rfl
  exact (mappingCylinderIsPushout f).desc cylMap baseMap hsq

theorem mappingCylinderMap_homotopyEquivalence {A C A' C' : TopCat.{u}}
    (f : A ⟶ C) (f' : A' ⟶ C') (vA : A ⟶ A') (vC : C ⟶ C')
    (hc : f ≫ vC = vA ≫ f')
    (hC : HomotopyHypothesis.Henry.Top.homotopyEquivalences vC) :
    HomotopyHypothesis.Henry.Top.homotopyEquivalences (mappingCylinderMap f f' vA vC hc) := by
  let m := mappingCylinderMap f f' vA vC hc
  let q := mappingCylinderCollapse f
  let q' := mappingCylinderCollapse f'
  let s := mappingCylinderBase f
  let s' := mappingCylinderBase f'
  obtain ⟨uC, hCu, hCv⟩ := hC
  have hqL := mappingCylinderCollapse_sourceHomotopy f
  have hq'L := mappingCylinderCollapse_sourceHomotopy f'
  have hqR : (s ≫ q).hom.Homotopic (ContinuousMap.id C) := by
    have hs : s ≫ q = 𝟙 C := by simp [s, q, mappingCylinderCollapse]
    simpa [hs] using (ContinuousMap.Homotopic.refl (ContinuousMap.id C))
  have hq'R : (s' ≫ q').hom.Homotopic (ContinuousMap.id C') := by
    have hs : s' ≫ q' = 𝟙 C' := by simp [s', q', mappingCylinderCollapse]
    simpa [hs] using (ContinuousMap.Homotopic.refl (ContinuousMap.id C'))
  have hmq : m ≫ q' = q ≫ vC := by
    apply (mappingCylinderIsPushout f).hom_ext
    · ext p
      rcases p with ⟨a, t⟩
      simpa [m, mappingCylinderMap, q', q, mappingCylinderCollapse,
        mappingCylinderCylinderCollapseMap, ContinuousMap.comp_apply] using
          (congrArg (fun g : A ⟶ C' => g.hom a) hc).symm
    · simp [m, mappingCylinderMap, q', q, mappingCylinderCollapse,
        mappingCylinderCylinderCollapseMap, Category.assoc]
  have hsectionMap : s ≫ m = vC ≫ s' := by
    simp [s, s', m, mappingCylinderMap]
  let r : mappingCylinder f' ⟶ mappingCylinder f := q' ≫ uC ≫ s
  have heq₁ : m ≫ r = q ≫ vC ≫ uC ≫ s := by
    calc
      m ≫ r = m ≫ (q' ≫ uC ≫ s) := rfl
      _ = (m ≫ q') ≫ uC ≫ s := by simp only [← Category.assoc]
      _ = (q ≫ vC) ≫ uC ≫ s := by rw [hmq]
      _ = q ≫ vC ≫ uC ≫ s := by simp only [Category.assoc]
  have heq₂ : r ≫ m = q' ≫ uC ≫ vC ≫ s' := by
    calc
      r ≫ m = (q' ≫ uC ≫ s) ≫ m := rfl
      _ = q' ≫ uC ≫ (s ≫ m) := by simp only [Category.assoc]
      _ = q' ≫ uC ≫ (vC ≫ s') := by rw [hsectionMap]
      _ = q' ≫ uC ≫ vC ≫ s' := by simp only [Category.assoc]
  have hmInv₁ : (m ≫ r).hom.Homotopic (q ≫ s).hom := by
    have h := hCu.some.compContinuousMap q.hom
    have hh := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl s.hom) ⟨h⟩
    rw [heq₁]
    exact hh
  have hmInv₂ : (r ≫ m).hom.Homotopic (q' ≫ s').hom := by
    have h := hCv.some.compContinuousMap q'.hom
    have hh := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl s'.hom) ⟨h⟩
    rw [heq₂]
    exact hh
  have hmLeft := hmInv₁.trans ⟨hqL⟩
  have hmRight := hmInv₂.trans ⟨hq'L⟩
  exact ⟨r, hmLeft, hmRight⟩

theorem mappingCylinderMap_top {A C A' C' : TopCat.{u}}
    (f : A ⟶ C) (f' : A' ⟶ C') (vA : A ⟶ A') (vC : C ⟶ C')
    (hc : f ≫ vC = vA ≫ f') :
    mappingCylinderTop f ≫ mappingCylinderMap f f' vA vC hc =
      vA ≫ mappingCylinderTop f' := by
  ext a
  simp [mappingCylinderTop, mappingCylinderMap, cylinderTop, TopCat.comp_app,
    ContinuousMap.comp_apply, ContinuousMap.prodMap_apply]

theorem mappingCylinderMap_collapse {A C A' C' : TopCat.{u}}
    (f : A ⟶ C) (f' : A' ⟶ C') (vA : A ⟶ A') (vC : C ⟶ C')
    (hc : f ≫ vC = vA ≫ f') :
    mappingCylinderMap f f' vA vC hc ≫ mappingCylinderCollapse f' =
      mappingCylinderCollapse f ≫ vC := by
  let m := mappingCylinderMap f f' vA vC hc
  let q := mappingCylinderCollapse f
  let q' := mappingCylinderCollapse f'
  apply (mappingCylinderIsPushout f).hom_ext
  · ext p
    rcases p with ⟨a, t⟩
    simpa [m, mappingCylinderMap, q', q, mappingCylinderCollapse,
      mappingCylinderCylinderCollapseMap, ContinuousMap.comp_apply] using
        (congrArg (fun g : A ⟶ C' => g.hom a) hc).symm
  · simp [m, mappingCylinderMap, q', q, mappingCylinderCollapse,
      mappingCylinderCylinderCollapseMap, Category.assoc]

theorem mappingCylinderMap_inverse_preserves_top {A C A' C' : TopCat.{u}}
    (f : A ⟶ C) (f' : A' ⟶ C') (vA : A ⟶ A') (vC : C ⟶ C')
    (hc : f ≫ vC = vA ≫ f')
    (hA : HomotopyHypothesis.Henry.Top.homotopyEquivalences vA)
    (hC : HomotopyHypothesis.Henry.Top.homotopyEquivalences vC) :
    ∃ (uA : A' ⟶ A) (w : C(mappingCylinder f', mappingCylinder f)),
      (uA ≫ vA).hom.Homotopic (ContinuousMap.id A') ∧
      (vA ≫ uA).hom.Homotopic (ContinuousMap.id A) ∧
      mappingCylinderTop f' ≫ TopCat.ofHom w = uA ≫ mappingCylinderTop f ∧
      HomotopyHypothesis.Henry.Top.homotopyEquivalences (TopCat.ofHom w) := by
  obtain ⟨uA, hAleft, hAright⟩ := hA
  let m := mappingCylinderMap f f' vA vC hc
  obtain ⟨w₀, hmLeft, hmRight⟩ := mappingCylinderMap_homotopyEquivalence
    f f' vA vC hc hC
  let top := mappingCylinderTop f
  let top' := mappingCylinderTop f'
  let F : C(A', mappingCylinder f) := w₀.hom.comp top'.hom
  let G : C(A', mappingCylinder f) := top.hom.comp uA.hom
  have hFv : (F.comp vA.hom).Homotopic top.hom := by
    have htop := congrArg TopCat.Hom.hom (mappingCylinderMap_top f f' vA vC hc)
    have hEq : F.comp vA.hom = (m ≫ TopCat.ofHom w₀.hom).hom.comp top.hom := by
      ext a
      change w₀ (top'.hom (vA.hom a)) = w₀ (m.hom (top.hom a))
      have hx := congrArg (fun q : C(A, mappingCylinder f') => q a) htop
      change m.hom (top.hom a) = top'.hom (vA.hom a) at hx
      exact congrArg w₀.hom hx.symm
    rw [hEq]
    exact ⟨hmLeft.some.compContinuousMap top.hom⟩
  have hGv : (G.comp vA.hom).Homotopic top.hom := by
    have h := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl top.hom)
      ⟨hAleft.some⟩
    simpa [G, ContinuousMap.comp_apply, Category.assoc] using h
  have hK : (F.comp vA.hom).Homotopic (G.comp vA.hom) := hFv.trans hGv.symm
  have hFcancel : ((F.comp vA.hom).comp uA.hom).Homotopic F := by
    have h := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl F) ⟨hAright.some⟩
    simpa [ContinuousMap.comp_apply, Category.assoc] using h
  have hGcancel : ((G.comp vA.hom).comp uA.hom).Homotopic G := by
    have h := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl G) ⟨hAright.some⟩
    simpa [ContinuousMap.comp_apply, Category.assoc] using h
  have hKpre : ((F.comp vA.hom).comp uA.hom).Homotopic
      ((G.comp vA.hom).comp uA.hom) := ⟨hK.some.compContinuousMap uA.hom⟩
  have hJ : F.Homotopic G := hFcancel.symm.trans (hKpre.trans hGcancel)
  obtain ⟨w, L, hL⟩ := mappingCylinderTop_homotopyExtension f' w₀.hom hJ.some
  have hstrict : top' ≫ TopCat.ofHom w = uA ≫ top := by
    ext a
    have hx := hL 1 a
    rw [L.apply_one] at hx
    rw [hJ.some.apply_one] at hx
    exact hx
  have hpre : ((m ≫ TopCat.ofHom w₀.hom).hom).Homotopic
      ((m ≫ TopCat.ofHom w).hom) := by
    simpa [TopCat.comp_app] using
      (show ((m ≫ TopCat.ofHom w₀.hom).hom).Homotopic
          ((m ≫ TopCat.ofHom w).hom) from ⟨L.compContinuousMap m.hom⟩)
  have hpost : ((TopCat.ofHom w₀.hom ≫ m).hom).Homotopic
      ((TopCat.ofHom w ≫ m).hom) := by
    exact ⟨ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl m.hom) L⟩
  refine ⟨uA, w, hAright, hAleft, hstrict, ?_⟩
  exact ⟨m, hpost.symm.trans hmRight, hpre.symm.trans hmLeft⟩

private def cylinderReverse {A : TopCat.{u}} :
    C(unitInterval × A, A × unitInterval) where
  toFun p := (p.2, unitInterval.symm p.1)
  continuous_toFun := by fun_prop

private noncomputable def mappingCylinderTopBottomHomotopy {A C : TopCat.{u}} (f : A ⟶ C) :
    (mappingCylinderTop f).hom.Homotopy
      (f ≫ mappingCylinderBase f).hom where
  toContinuousMap := (mappingCylinderCylinder f).hom.comp cylinderReverse
  map_zero_left := by
    intro a
    simpa [cylinderReverse, cylinderTop, mappingCylinderTop, ContinuousMap.comp_apply]
  map_one_left := by
    intro a
    have h := congrArg (fun g : A ⟶ mappingCylinder f => g.hom a)
      (mappingCylinderIsPushout f).w
    simpa [cylinderBottom, cylinderReverse, mappingCylinderTop,
      ContinuousMap.comp_apply] using h

private theorem mappingCylinderTopBottomCollapse {A C : TopCat.{u}} (f : A ⟶ C)
    (t : unitInterval) (a : A) :
    (mappingCylinderCollapse f).hom
        (mappingCylinderTopBottomHomotopy f (t, a)) = f.hom a := by
  change (mappingCylinderCylinder f ≫ mappingCylinderCollapse f).hom
    (cylinderReverse (t, a)) = f.hom a
  have h := congrArg
    (fun g : TopCat.of (A × unitInterval) ⟶ C => g.hom (cylinderReverse (t, a)))
    (mappingCylinderCollapse_cylinder f)
  simpa [mappingCylinderCylinderCollapseMap, cylinderReverse,
    ContinuousMap.comp_apply] using h

noncomputable abbrev mappingCylinderReplacement {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) : TopCat.{u} :=
  pushout i (mappingCylinderTop f)

theorem mappingCylinderReplacementIsPushout {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) :
    IsPushout i (mappingCylinderTop f) (pushout.inl i (mappingCylinderTop f))
      (pushout.inr i (mappingCylinderTop f)) :=
  IsPushout.of_hasPushout _ _

theorem mappingCylinderReplacementCollapseSquare {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) :
    mappingCylinderTop f ≫ (mappingCylinderCollapse f ≫ pushout.inr i f) =
      i ≫ pushout.inl i f := by
  let b : B ⟶ pushout i f := pushout.inl i f
  let m : mappingCylinder f ⟶ pushout i f :=
    mappingCylinderCollapse f ≫ pushout.inr i f
  have hP : i ≫ b = f ≫ (pushout.inr i f) :=
    (IsPushout.of_hasPushout i f).w
  have htop : mappingCylinderTop f ≫ m = i ≫ b := by
    calc
      mappingCylinderTop f ≫ m =
          mappingCylinderTop f ≫ mappingCylinderCollapse f ≫ pushout.inr i f := rfl
      _ = f ≫ pushout.inr i f := by
        rw [← Category.assoc, mappingCylinderTop_collapse]
      _ = i ≫ b := hP.symm
  simpa [m, b] using htop

noncomputable def mappingCylinderReplacementCollapse {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) :
    mappingCylinderReplacement i f ⟶ pushout i f :=
  (mappingCylinderReplacementIsPushout i f).desc (pushout.inl i f)
    (mappingCylinderCollapse f ≫ pushout.inr i f)
    (mappingCylinderReplacementCollapseSquare i f).symm

theorem mappingCylinderReplacementCollapse_inl {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) :
    pushout.inl i (mappingCylinderTop f) ≫ mappingCylinderReplacementCollapse i f =
      pushout.inl i f := by
  simp [mappingCylinderReplacementCollapse]

theorem mappingCylinderReplacementCollapse_inr {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) :
    pushout.inr i (mappingCylinderTop f) ≫ mappingCylinderReplacementCollapse i f =
      mappingCylinderCollapse f ≫ pushout.inr i f := by
  simp [mappingCylinderReplacementCollapse]

noncomputable def mappingCylinderReplacementMap
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    mappingCylinderReplacement i f ⟶ mappingCylinderReplacement i' f' := by
  let b' := pushout.inl i' (mappingCylinderTop f')
  let m' := pushout.inr i' (mappingCylinderTop f')
  let m := mappingCylinderMap f f' vA vC c₂
  let hQ' : IsPushout i' (mappingCylinderTop f') b' m' :=
    mappingCylinderReplacementIsPushout i' f'
  have hs : i ≫ (vB ≫ b') = mappingCylinderTop f ≫ (m ≫ m') := by
    calc
      i ≫ (vB ≫ b') = (i ≫ vB) ≫ b' := by simp only [Category.assoc]
      _ = (vA ≫ i') ≫ b' := by rw [c₁]
      _ = vA ≫ (i' ≫ b') := Category.assoc _ _ _
      _ = vA ≫ (mappingCylinderTop f' ≫ m') := by rw [hQ'.w]
      _ = (vA ≫ mappingCylinderTop f') ≫ m' := (Category.assoc _ _ _).symm
      _ = (mappingCylinderTop f ≫ m) ≫ m' := by rw [mappingCylinderMap_top]
      _ = mappingCylinderTop f ≫ (m ≫ m') := Category.assoc _ _ _
  exact (mappingCylinderReplacementIsPushout i f).desc (vB ≫ b') (m ≫ m') hs

theorem mappingCylinderReplacementMap_inl
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    pushout.inl i (mappingCylinderTop f) ≫
      mappingCylinderReplacementMap i f i' f' vA vB vC c₁ c₂ =
        vB ≫ pushout.inl i' (mappingCylinderTop f') := by
  unfold mappingCylinderReplacementMap
  exact (mappingCylinderReplacementIsPushout i f).inl_desc _ _ _

theorem mappingCylinderReplacementMap_inr
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    pushout.inr i (mappingCylinderTop f) ≫
      mappingCylinderReplacementMap i f i' f' vA vB vC c₁ c₂ =
        mappingCylinderMap f f' vA vC c₂ ≫ pushout.inr i' (mappingCylinderTop f') := by
  unfold mappingCylinderReplacementMap
  exact (mappingCylinderReplacementIsPushout i f).inr_desc _ _ _

noncomputable def pushoutComparisonMap
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    pushout i f ⟶ pushout i' f' := by
  let b' := pushout.inl i' f'
  let c' := pushout.inr i' f'
  let hp' : IsPushout i' f' b' c' := IsPushout.of_hasPushout i' f'
  have hs : i ≫ (vB ≫ b') = f ≫ (vC ≫ c') := by
    rw [← Category.assoc, c₁, Category.assoc, hp'.w, ← Category.assoc,
      ← c₂, Category.assoc]
  exact (IsPushout.of_hasPushout i f).desc (vB ≫ b') (vC ≫ c') hs

theorem pushoutComparisonMap_inl
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    pushout.inl i f ≫ pushoutComparisonMap i f i' f' vA vB vC c₁ c₂ =
      vB ≫ pushout.inl i' f' := by
  unfold pushoutComparisonMap
  exact (IsPushout.of_hasPushout i f).inl_desc _ _ _

theorem pushoutComparisonMap_inr
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    pushout.inr i f ≫ pushoutComparisonMap i f i' f' vA vB vC c₁ c₂ =
      vC ≫ pushout.inr i' f' := by
  unfold pushoutComparisonMap
  exact (IsPushout.of_hasPushout i f).inr_desc _ _ _

theorem mappingCylinderReplacementMap_collapse
    {A B C A' B' C' : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ C)
    (i' : A' ⟶ B') (f' : A' ⟶ C') (vA : A ⟶ A') (vB : B ⟶ B')
    (vC : C ⟶ C') (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') :
    mappingCylinderReplacementMap i f i' f' vA vB vC c₁ c₂ ≫
        mappingCylinderReplacementCollapse i' f' =
      mappingCylinderReplacementCollapse i f ≫
        pushoutComparisonMap i f i' f' vA vB vC c₁ c₂ := by
  let bQ := pushout.inl i (mappingCylinderTop f)
  let mQ := pushout.inr i (mappingCylinderTop f)
  let bQ' := pushout.inl i' (mappingCylinderTop f')
  let mQ' := pushout.inr i' (mappingCylinderTop f')
  let p := mappingCylinderReplacementCollapse i f
  let p' := mappingCylinderReplacementCollapse i' f'
  let r := mappingCylinderReplacementMap i f i' f' vA vB vC c₁ c₂
  let φ := pushoutComparisonMap i f i' f' vA vB vC c₁ c₂
  have hQ : IsPushout i (mappingCylinderTop f) bQ mQ :=
    mappingCylinderReplacementIsPushout i f
  have hB : (bQ ≫ r) ≫ p' = (bQ ≫ p) ≫ φ := by
    calc
      (bQ ≫ r) ≫ p' = (vB ≫ bQ') ≫ p' := by
        rw [mappingCylinderReplacementMap_inl]
      _ = vB ≫ (bQ' ≫ p') := Category.assoc _ _ _
      _ = vB ≫ pushout.inl i' f' := by rw [mappingCylinderReplacementCollapse_inl]
      _ = (pushout.inl i f ≫ φ) := (pushoutComparisonMap_inl i f i' f' vA vB vC c₁ c₂).symm
      _ = (bQ ≫ p) ≫ φ := by rw [mappingCylinderReplacementCollapse_inl]
  have hM : (mQ ≫ r) ≫ p' = (mQ ≫ p) ≫ φ := by
    calc
      (mQ ≫ r) ≫ p' = (mappingCylinderMap f f' vA vC c₂ ≫ mQ') ≫ p' := by
        rw [mappingCylinderReplacementMap_inr]
      _ = mappingCylinderMap f f' vA vC c₂ ≫ (mQ' ≫ p') := Category.assoc _ _ _
      _ = mappingCylinderMap f f' vA vC c₂ ≫
            (mappingCylinderCollapse f' ≫ pushout.inr i' f') := by
              rw [mappingCylinderReplacementCollapse_inr]
      _ = (mappingCylinderCollapse f ≫ vC) ≫ pushout.inr i' f' := by
        rw [← Category.assoc, mappingCylinderMap_collapse]
      _ = mappingCylinderCollapse f ≫ (vC ≫ pushout.inr i' f') :=
        Category.assoc _ _ _
      _ = mappingCylinderCollapse f ≫ (pushout.inr i f ≫ φ) := by
        rw [(pushoutComparisonMap_inr i f i' f' vA vB vC c₁ c₂).symm]
      _ = (mappingCylinderCollapse f ≫ pushout.inr i f) ≫ φ :=
        (Category.assoc _ _ _).symm
      _ = (mQ ≫ p) ≫ φ := by rw [← mappingCylinderReplacementCollapse_inr]
  apply hQ.hom_ext
  · exact hB
  · exact hM

theorem mappingCylinderReplacementCollapse_homotopyEquivalence {A B C : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i) :
    HomotopyHypothesis.Henry.Top.homotopyEquivalences
      (mappingCylinderReplacementCollapse i f) := by
  let bQ : B ⟶ mappingCylinderReplacement i f :=
    pushout.inl i (mappingCylinderTop f)
  let mQ : mappingCylinder f ⟶ mappingCylinderReplacement i f :=
    pushout.inr i (mappingCylinderTop f)
  let cQ : C ⟶ mappingCylinderReplacement i f := mappingCylinderBase f ≫ mQ
  let bP : B ⟶ pushout i f := pushout.inl i f
  let cP : C ⟶ pushout i f := pushout.inr i f
  let p := mappingCylinderReplacementCollapse i f
  let hP : IsPushout i f bP cP := IsPushout.of_hasPushout i f
  let hQ : IsPushout i (mappingCylinderTop f) bQ mQ :=
    mappingCylinderReplacementIsPushout i f
  have hInc : i ≫ bQ = mappingCylinderTop f ≫ mQ := hQ.w
  have hpB : bQ ≫ p = bP := mappingCylinderReplacementCollapse_inl i f
  have hpM : mQ ≫ p = mappingCylinderCollapse f ≫ cP :=
    mappingCylinderReplacementCollapse_inr i f
  have hpC : cQ ≫ p = cP := by
    dsimp [cQ]
    rw [Category.assoc, hpM]
    rw [← Category.assoc, mappingCylinderCollapse_base]
    rfl
  let gA : A ⟶ mappingCylinderReplacement i f := f ≫ cQ
  let HBraw := ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl mQ.hom)
    (mappingCylinderTopBottomHomotopy f)
  have hs : (mappingCylinderTop f ≫ mQ).hom = bQ.hom.comp i.hom := by
    simpa [TopCat.comp_app] using congrArg TopCat.Hom.hom hInc.symm
  have ht : (f ≫ mappingCylinderBase f ≫ mQ).hom = gA.hom := rfl
  let HB : (bQ.hom.comp i.hom).Homotopy gA.hom := HBraw.cast hs ht
  obtain ⟨b₁, G, hG⟩ :=
    relativeFiniteCellComplex_homotopyExtension_proof i hi bQ.hom gA.hom HB
  have hcompatB : i ≫ TopCat.ofHom b₁ = gA := by
    ext a
    have hx := hG 1 a
    rw [G.apply_one] at hx
    rw [HB.apply_one] at hx
    exact hx
  let s : pushout i f ⟶ mappingCylinderReplacement i f := hP.desc
    (TopCat.ofHom b₁) cQ hcompatB
  have hsB : bP ≫ s = TopCat.ofHom b₁ := hP.inl_desc _ _ hcompatB
  have hsC : cP ≫ s = cQ := hP.inr_desc _ _ hcompatB
  have hB0 : (bQ ≫ p).hom = bP.hom := congrArg TopCat.Hom.hom hpB
  have hB1 : (TopCat.ofHom b₁ ≫ p).hom = (bP ≫ s ≫ p).hom :=
    congrArg (fun g : B ⟶ mappingCylinderReplacement i f => (g ≫ p).hom) hsB.symm
  let HBtarget : bP.hom.Homotopy (bP ≫ s ≫ p).hom :=
    ((ContinuousMap.Homotopy.refl p.hom).comp G).cast hB0 hB1
  have hCcomp : cP ≫ s ≫ p = cP := by
    calc
      cP ≫ s ≫ p = (cP ≫ s) ≫ p := (Category.assoc _ _ _).symm
      _ = cQ ≫ p := by rw [hsC]
      _ = cP := hpC
  have hCeq : (cP ≫ s ≫ p).hom = cP.hom := congrArg TopCat.Hom.hom hCcomp
  let hCtarget : cP.hom.Homotopy ((cP ≫ s ≫ p).hom) :=
    (ContinuousMap.Homotopy.refl cP.hom).cast rfl hCeq.symm
  have hcompatTarget : ∀ (t : unitInterval) (a : A),
      HBtarget (t, i.hom a) = hCtarget (t, f.hom a) := by
    intro t a
    have hx := hG t a
    calc
      HBtarget (t, i.hom a) = p.hom (G (t, i.hom a)) := rfl
      _ = p.hom (HB (t, a)) := congrArg p.hom hx
      _ = cP.hom (f.hom a) := by
        change (mQ ≫ p).hom (mappingCylinderTopBottomHomotopy f (t, a)) = _
        rw [hpM]
        exact congrArg cP.hom (mappingCylinderTopBottomCollapse f t a)
      _ = hCtarget (t, f.hom a) := by
        change cP.hom (f.hom a) = cP.hom (f.hom a)
        rfl
  have hBP0 : (ContinuousMap.id (pushout i f : TopCat.{u})).comp bP.hom = bP.hom := by
    ext b
    rfl
  have hBP1 : (s ≫ p).hom.comp bP.hom = (bP ≫ s ≫ p).hom := by
    ext b
    rfl
  have hCP0 : (ContinuousMap.id (pushout i f : TopCat.{u})).comp cP.hom = cP.hom := by
    ext c
    rfl
  have hCP1 : (s ≫ p).hom.comp cP.hom = (cP ≫ s ≫ p).hom := by
    ext c
    rfl
  let Hk : ((ContinuousMap.id (pushout i f : TopCat.{u})).comp bP.hom).Homotopy
      ((s ≫ p).hom.comp bP.hom) := HBtarget.cast hBP0 hBP1
  let Hj : ((ContinuousMap.id (pushout i f : TopCat.{u})).comp cP.hom).Homotopy
      ((s ≫ p).hom.comp cP.hom) := hCtarget.cast hCP0 hCP1
  have hcompatTarget' : ∀ (t : unitInterval) (a : A), Hk (t, i.hom a) =
      Hj (t, f.hom a) := by
    intro t a
    change HBtarget (t, i.hom a) = hCtarget (t, f.hom a)
    exact hcompatTarget t a
  let Htarget := homotopy_of_isPushout (Z := (pushout i f : TopCat.{u}))
    (g₀ := ContinuousMap.id (pushout i f : TopCat.{u})) (g₁ := (s ≫ p).hom) i f bP cP hP
    Hk Hj hcompatTarget'
  have hSbase : bQ ≫ p ≫ s = TopCat.ofHom b₁ := by
    calc
      bQ ≫ p ≫ s = (bQ ≫ p) ≫ s := (Category.assoc _ _ _).symm
      _ = bP ≫ s := by rw [hpB]
      _ = TopCat.ofHom b₁ := hsB
  let HsourceB : ((p ≫ s).hom.comp bQ.hom).Homotopy bQ.hom :=
    G.symm.cast (congrArg TopCat.Hom.hom hSbase).symm rfl
  have hSmapM : mQ ≫ p ≫ s =
      (mappingCylinderCollapse f ≫ mappingCylinderBase f) ≫ mQ := by
    calc
      mQ ≫ p ≫ s = (mQ ≫ p) ≫ s := (Category.assoc _ _ _).symm
      _ = (mappingCylinderCollapse f ≫ cP) ≫ s := by rw [hpM]
      _ = mappingCylinderCollapse f ≫ (cP ≫ s) := Category.assoc _ _ _
      _ = mappingCylinderCollapse f ≫ cQ := by rw [hsC]
      _ = (mappingCylinderCollapse f ≫ mappingCylinderBase f) ≫ mQ := by rfl
  let HsourceM : ((p ≫ s).hom.comp mQ.hom).Homotopy mQ.hom :=
    ((ContinuousMap.Homotopy.refl mQ.hom).comp
      (mappingCylinderCollapse_sourceHomotopy f)).cast
        (congrArg TopCat.Hom.hom hSmapM.symm) rfl
  have hcompatSource : ∀ (t : unitInterval) (a : A),
      HsourceB (t, i.hom a) = HsourceM (t, mappingCylinderTop f a) := by
    intro t a
    have hx := hG (unitInterval.symm t) a
    change G (unitInterval.symm t, i.hom a) = HB (unitInterval.symm t, a) at hx
    have hleft : HsourceB (t, i.hom a) = mQ.hom ((mappingCylinderCylinder f).hom (a, t)) := by
      calc
        HsourceB (t, i.hom a) = G (unitInterval.symm t, i.hom a) := rfl
        _ = HB (unitInterval.symm t, a) := hx
        _ = mQ.hom ((mappingCylinderCylinder f).hom (a, t)) := by
          change mQ.hom ((mappingCylinderCylinder f).hom
            (a, unitInterval.symm (unitInterval.symm t))) = _
          rw [unitInterval.symm_symm]
    have hright : HsourceM (t, mappingCylinderTop f a) =
        mQ.hom ((mappingCylinderCylinder f).hom (a, t)) := by
      change mQ.hom (mappingCylinderCollapse_sourceHomotopy f
        (t, mappingCylinderTop f a)) = _
      rw [mappingCylinderCollapse_sourceHomotopy_top]
    exact hleft.trans hright.symm
  let Hsource := homotopy_of_isPushout (Z := mappingCylinderReplacement i f)
    (g₀ := (p ≫ s).hom) (g₁ := ContinuousMap.id (mappingCylinderReplacement i f))
    i (mappingCylinderTop f) bQ mQ hQ HsourceB HsourceM hcompatSource
  exact ⟨s, ⟨Hsource⟩, ⟨Htarget.symm⟩⟩
