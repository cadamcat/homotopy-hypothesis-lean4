import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Comparison.FundamentalGroupoid.Cells
import HomotopyHypothesis.Comparison.FundamentalGroupoid.Geom
import HomotopyHypothesis.Completion.Compression.DiskOne
import HomotopyHypothesis.Completion.Compression.ExtTransport
import HomotopyHypothesis.Completion.Compression.PiZero
import HomotopyHypothesis.Completion.Compression.Transport
import HomotopyHypothesis.Realization.Cellular.SpherePushout
/-
# The compression criterion: from homotopy groups to relative lifts

Let `f : X → Y` be bijective on path components and on all homotopy groups. For a boundary map
`a : ∂𝔻ᵐ → X` and an extension `b : 𝔻ᵐ → Y` of `f ∘ a`, we find an extension `l` of `a` with
`f ∘ l` homotopic to `b` relative to the boundary.

The argument works with extension classes (extensions of `a` modulo homotopy relative to the
boundary), which are transported bijectively along homotopies of `a`, naturally in postcomposition.

* If `a` has some extension `l₀`, contracting the disk deforms `a` to a constant map, and for a
  constant boundary the statement is surjectivity on `πₘ`.
* An extension of `a` exists: for `m = 1` by injectivity on path components. For `m = n + 2`,
  deform `a` (homotopy extension along a hemisphere) so that it is constant on one hemisphere;
  the other hemisphere is then an element of `π_{n+1}(X)` whose image is trivial (the disk `b`
  fills it), hence is trivial by injectivity, and a null-homotopy is a filler of the sphere.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory Limits TopCat

/-- Henry's lifting condition at a single boundary map `a : ∂𝔻ᵐ ⟶ X`. -/
def LiftsAt {X Y : TopCat.{u}} (f : X ⟶ Y) (m : ℕ) (a : diskBoundary.{u} m ⟶ X) : Prop :=
  ∀ b : disk.{u} m ⟶ Y, a ≫ f = diskBoundaryInclusion m ≫ b →
    ∃ l : disk.{u} m ⟶ X, diskBoundaryInclusion m ≫ l = a ∧
      (l ≫ f).hom.HomotopicRel b.hom (Set.range (diskBoundaryInclusion.{u} m))

/-- The boundary inclusion `∂𝔻ᵐ ⟶ 𝔻ᵐ` is a relative finite cell complex. -/
lemma diskBoundaryInclusion_mem (m : ℕ) :
    Henry.Top.relativeFiniteCellComplexes (diskBoundaryInclusion.{u} m) :=
  MorphismProperty.multiplicativeClosure.of _
    (Or.inl (MorphismProperty.le_pushouts _ _ (MorphismProperty.ofHoms.mk m)))

lemma liftsAt_of_surjective {X Y : TopCat.{u}} (f : X ⟶ Y) (m : ℕ) (a : diskBoundary.{u} m ⟶ X)
    (h : Function.Surjective
      (postcomposeExtensionClass (diskBoundaryInclusion.{u} m) a.hom f.hom)) :
    LiftsAt f m a := by
  intro b hb
  let eb : Extension (diskBoundaryInclusion.{u} m) (f.hom.comp a.hom) :=
    ⟨b.hom, (congrArg Hom.hom hb).symm⟩
  obtain ⟨x, hx⟩ := h (Quotient.mk _ eb)
  obtain ⟨l, rfl⟩ := Quotient.exists_rep x
  refine ⟨ofHom l.val, ?_, ?_⟩
  · apply TopCat.hom_ext
    exact l.property
  · exact Quotient.exact hx

lemma surjective_of_liftsAt {X Y : TopCat.{u}} (f : X ⟶ Y) (m : ℕ) (a : diskBoundary.{u} m ⟶ X)
    (h : LiftsAt f m a) :
    Function.Surjective
      (postcomposeExtensionClass (diskBoundaryInclusion.{u} m) a.hom f.hom) := by
  intro y
  obtain ⟨e, rfl⟩ := Quotient.exists_rep y
  obtain ⟨l, hl, hrel⟩ := h (ofHom e.val) (by
    apply TopCat.hom_ext
    exact e.property.symm)
  refine ⟨Quotient.mk _ ⟨l.hom, congrArg Hom.hom hl⟩, ?_⟩
  exact Quotient.sound hrel

/-- Constant boundary: lifting from surjectivity on `π_{n+1}`. -/
lemma liftsAt_const {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) (x : X)
    (hsurj : Function.Surjective (homotopyGroupMap (Fin (n + 1)) f x)) :
    LiftsAt f (n + 1) (diskBoundaryConstMap X x (n + 1)) := by
  intro b hb
  have hbC : ∀ c ∈ Cube.boundary (Fin (n + 1)),
      (b.hom.comp (cubeToDiskULiftCMap (n + 1))) c = f x := by
    intro c hc
    obtain ⟨p, hp⟩ := bwdU_mem_range (n + 1) c hc
    have h1 := congrArg (fun g => g p) (congrArg Hom.hom hb)
    simp only [hom_comp, ContinuousMap.comp_apply] at h1
    rw [ContinuousMap.comp_apply, ← hp]
    exact h1.symm
  let bC : GenLoop (Fin (n + 1)) Y (f x) := ⟨_, hbC⟩
  obtain ⟨q, hq⟩ := hsurj ⟦bC⟧
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep q
  have hγ : ∀ p : diskBoundary.{u} (n + 1),
      γ.1 (diskToCubeULiftCMap (n + 1) (diskBoundaryInclusion (n + 1) p)) = x :=
    fun p => γ.2 _ (fwdU_mem_cubeBoundary (n + 1) p)
  refine ⟨ofHom (γ.1.comp (diskToCubeULiftCMap (n + 1))), ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    exact hγ p
  · have hmap : homotopyGroupMap (Fin (n + 1)) f x ⟦γ⟧ =
        ⟦⟨f.hom.comp γ.1, fun y hy => by simp [γ.2 y hy]⟩⟧ :=
      Quotient.map_mk _ _ _
    rw [hmap] at hq
    have hhom : (f.hom.comp γ.1).HomotopicRel bC.1 (Cube.boundary (Fin (n + 1))) :=
      Quotient.exact hq
    have hpre := HomotopicRel_precomp hhom (diskToCubeULiftCMap (n + 1))
      (T := Set.range (diskBoundaryInclusion.{u} (n + 1)))
      (by
        rintro c ⟨p, rfl⟩
        exact fwdU_mem_cubeBoundary (n + 1) p)
    have hb' : (bC.1.comp (diskToCubeULiftCMap (n + 1))) = b.hom := by
      apply ContinuousMap.ext
      intro d
      show b.hom (cubeToDiskULiftCMap (n + 1) (diskToCubeULiftCMap (n + 1) d)) = b.hom d
      rw [bwdFwdCubeULift_apply]
    rw [hb', ContinuousMap.comp_assoc] at hpre
    exact hpre

/-- Radial scaling of the disk, `(t, y) ↦ (1 - t) y`. -/
def diskScale (m : ℕ) : C(unitInterval × disk.{u} m, disk.{u} m) where
  toFun p := ULift.up ⟨(1 - (p.1 : ℝ)) • (p.2.down.1 : EuclideanSpace ℝ (Fin m)), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [p.1.2.2] : (0 : ℝ) ≤ 1 - (p.1 : ℝ))]
    have h1 : ‖(p.2.down.1 : EuclideanSpace ℝ (Fin m))‖ ≤ 1 :=
      mem_closedBall_zero_iff.mp p.2.down.2
    have h2 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
    nlinarith [norm_nonneg (p.2.down.1 : EuclideanSpace ℝ (Fin m))]⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
      (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))

/-- The center of the disk. -/
def diskCenter (m : ℕ) : disk.{u} m := ULift.up ⟨0, by simp⟩

lemma diskScale_zero (m : ℕ) (y : disk.{u} m) : diskScale m (0, y) = y := by
  apply ULift.ext
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) • (y.down.1 : EuclideanSpace ℝ (Fin m)) = y.down.1
  simp

lemma diskScale_one (m : ℕ) (y : disk.{u} m) : diskScale m (1, y) = diskCenter m := by
  apply ULift.ext
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) • (y.down.1 : EuclideanSpace ℝ (Fin m)) = 0
  simp

/-- Contracting an extension `l` deforms its boundary values to a constant map. -/
def contractHomotopy {X : TopCat.{u}} {m : ℕ} {A : TopCat.{u}} (j : A ⟶ disk.{u} m)
    (l : disk.{u} m ⟶ X) :
    (l.hom.comp j.hom).Homotopy (ContinuousMap.const A (l (diskCenter m))) where
  toFun p := l (diskScale m (p.1, j p.2))
  continuous_toFun := by
    apply l.hom.continuous.comp
    exact (diskScale m).continuous.comp
      (continuous_fst.prodMk (j.hom.continuous.comp continuous_snd))
  map_zero_left y := by
    simp only [diskScale_zero]
    rfl
  map_one_left y := by
    simp only [diskScale_one]
    rfl

/-- If `a` has some extension, lifting at `a` follows from surjectivity on `πₘ`. -/
lemma liftsAt_of_extension {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : diskBoundary.{u} (n + 1) ⟶ X) (l₀ : disk.{u} (n + 1) ⟶ X)
    (hl₀ : diskBoundaryInclusion (n + 1) ≫ l₀ = a)
    (hsurj : ∀ x : X, Function.Surjective (homotopyGroupMap (Fin (n + 1)) f x)) :
    LiftsAt f (n + 1) a := by
  subst hl₀
  apply liftsAt_of_surjective
  let x₀ := l₀ (diskCenter (n + 1))
  have hc := surjective_of_liftsAt f (n + 1) _ (liftsAt_const f n x₀ (hsurj x₀))
  exact postcomposeExtensionClass_surjective_of_homotopy _ (diskBoundaryInclusion_mem (n + 1))
    (contractHomotopy (diskBoundaryInclusion (n + 1)) l₀) f.hom hc

/-! ### Existence of an extension in dimension one -/

/-- Every 1-sphere map is a pair map for its endpoint values. -/
lemma boundaryOne_eq_pair (X : TopCat.{u}) (a : TopCat.diskBoundary.{u} 1 ⟶ X) :
    a = boundaryOneMap X (a boundaryMinusOnePt.{u}) (a boundaryPlusOnePt.{u}) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  have hcoord : (p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
      (p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    have hmem : (p.down.val : EuclideanSpace ℝ (Fin 1)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := p.down.property
    exact (mem_sphere_fin1 _).mp hmem
  rcases hcoord with h | h
  · have hp : p = boundaryPlusOnePt.{u} := by
      apply ULift.ext
      apply Subtype.ext
      have hsingle : (p.down.val : EuclideanSpace ℝ (Fin 1)) =
          EuclideanSpace.single 0 (1 : ℝ) := by
        have hsc : EuclideanSpace.single 0 ((p.down.val : EuclideanSpace ℝ (Fin 1)) 0) =
            p.down.val := single_coord_id _
        rw [h] at hsc
        exact hsc.symm
      have hplus : (boundaryPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
          EuclideanSpace.single 0 (1 : ℝ) := boundaryPlusOne_vec.{u}
      rw [hsingle, hplus]
    rw [hp]
    exact (boundaryPlusOne_val X _ _).symm
  · have hp : p = boundaryMinusOnePt.{u} := by
      apply ULift.ext
      apply Subtype.ext
      have hsingle : (p.down.val : EuclideanSpace ℝ (Fin 1)) =
          EuclideanSpace.single 0 (-1 : ℝ) := by
        have hsc : EuclideanSpace.single 0 ((p.down.val : EuclideanSpace ℝ (Fin 1)) 0) =
            p.down.val := single_coord_id _
        rw [h] at hsc
        exact hsc.symm
      have hminus : (boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
          EuclideanSpace.single 0 (-1 : ℝ) := boundaryMinusOne_vec.{u}
      rw [hsingle, hminus]
    rw [hp]
    have hne : ¬ ((boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0 = 1) := by
      rw [boundaryMinusOne_coord]
      norm_num
    simp [boundaryOneMap_apply, hne]

/-- In dimension one, an extension exists by injectivity on path components. -/
lemma exists_extension_one {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hinj : Function.Injective (zerothHomotopyMap f))
    (a : diskBoundary.{u} 1 ⟶ X) (b : disk.{u} 1 ⟶ Y)
    (hb : a ≫ f = diskBoundaryInclusion 1 ≫ b) :
    ∃ l₀ : disk.{u} 1 ⟶ X, diskBoundaryInclusion 1 ≫ l₀ = a := by
  have hbpt : ∀ p, f (a p) = b (diskBoundaryInclusion 1 p) := fun p =>
    congrArg (fun g => g p) (congrArg Hom.hom hb)
  let δ : C(unitInterval, Y) :=
    b.hom.comp ((uliftUpContinuousMap
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).comp backwardContinuousMap)
  have h0 : δ 0 = f (a boundaryMinusOnePt.{u}) := by
    show b.hom (((uliftUpContinuousMap _).comp backwardContinuousMap) 0) = _
    rw [hpt0, hbpt, incl_minus]
  have h1 : δ 1 = f (a boundaryPlusOnePt.{u}) := by
    show b.hom (((uliftUpContinuousMap _).comp backwardContinuousMap) 1) = _
    rw [hpt1, hbpt, incl_plus]
  have hY : Joined (f (a boundaryMinusOnePt.{u})) (f (a boundaryPlusOnePt.{u})) :=
    ⟨⟨δ, h0, h1⟩⟩
  have hX : Joined (a boundaryMinusOnePt.{u}) (a boundaryPlusOnePt.{u}) := by
    have hq : zerothHomotopyMap f (ZerothHomotopy.mk (a boundaryMinusOnePt.{u})) =
        zerothHomotopyMap f (ZerothHomotopy.mk (a boundaryPlusOnePt.{u})) :=
      Quotient.sound hY
    exact Quotient.exact (hinj hq)
  obtain ⟨γ⟩ := hX
  refine ⟨diskOneMapOfPath γ, ?_⟩
  have hc := comm_one (𝟙 X) rfl rfl γ
  rw [Category.comp_id] at hc
  exact hc.symm.trans (boundaryOne_eq_pair X a).symm

/-! ### Existence of an extension in dimension at least two -/

open Comparison.FundamentalGroupoid.Geom in
/-- The boundary inclusion on a hemisphere is the geometric hemisphere map. -/
lemma incl_sphereFace_up (N : ℕ) (s : Bool) (z : ClosedBall N) :
    diskBoundaryInclusion.{u} (N + 1) (Realization.Cellular.sphereFace.{u} N s (ULift.up z)) =
      ULift.up (hemi N s z) := by
  have h1 := congrArg (fun g => g (Comparison.FundamentalGroupoid.Cells.diskUp.{u} N z))
    (Realization.Cellular.sphereFace_inclusion.{u} N s)
  exact h1.trans (Comparison.FundamentalGroupoid.Cells.face_diskUp N s z)

open Comparison.FundamentalGroupoid.Geom in
/-- The two hemispheres agree on the equator. -/
lemma sphereFace_equator (N : ℕ) (z : ClosedBall N) (hz : z ∈ sphereSet N) :
    Realization.Cellular.sphereFace.{u} N true (ULift.up z) =
      Realization.Cellular.sphereFace.{u} N false (ULift.up z) := by
  let p : diskBoundary.{u} N := ULift.up ⟨z.1, mem_sphere_zero_iff_norm.mpr hz⟩
  have hp : diskBoundaryInclusion N p = ULift.up z := rfl
  have h := congrArg (fun g => g p) (Realization.Cellular.sphereFace_condition.{u} N)
  simp only [TopCat.comp_app, hp] at h
  exact h.symm

open Comparison.FundamentalGroupoid.Geom in
/-- In dimension `n + 2`, an extension exists by injectivity on `π_{n+1}`. -/
lemma exists_extension_succ_succ {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (hinj : ∀ x : X, Function.Injective (homotopyGroupMap (Fin (n + 1)) f x))
    (a : diskBoundary.{u} (n + 2) ⟶ X) (b : disk.{u} (n + 2) ⟶ Y)
    (hb : a ≫ f = diskBoundaryInclusion (n + 2) ≫ b) :
    ∃ l₀ : disk.{u} (n + 2) ⟶ X, diskBoundaryInclusion (n + 2) ≫ l₀ = a := by
  let F : Bool → (disk.{u} (n + 1) ⟶ diskBoundary.{u} (n + 2)) :=
    Realization.Cellular.sphereFace.{u} (n + 1)
  have hF : Henry.Top.relativeFiniteCellComplexes (F false) :=
    MorphismProperty.multiplicativeClosure.of _ (Or.inl
      (MorphismProperty.pushouts_mk _ (Realization.Cellular.sphere_isPushout.{u} (n + 1))
        (MorphismProperty.ofHoms.mk (n + 1))))
  -- deform `a` to be constant on the hemisphere `F false`
  let x₀ : X := a (F false (diskCenter (n + 1)))
  let c := contractHomotopy (𝟙 (disk.{u} (n + 1))) (F false ≫ a)
  obtain ⟨a', H', hH'⟩ :=
    Henry.Packages.relativeFiniteCellComplex_homotopyExtension (F false) hF a.hom
      (ContinuousMap.const _ x₀) c
  have ha'F : ∀ z, a' (F false z) = x₀ := by
    intro z
    rw [← H'.apply_one, hH' 1 z]
    exact c.apply_one z
  -- transport `b` to an extension of `f ∘ a'`
  obtain ⟨yb, -⟩ := exists_track (diskBoundaryInclusion.{u} (n + 2))
    (diskBoundaryInclusion_mem (n + 2)) ((ContinuousMap.Homotopy.refl f.hom).comp H')
    (⟨b.hom, (congrArg Hom.hom hb).symm⟩ :
      Extension (diskBoundaryInclusion.{u} (n + 2)) (f.hom.comp a.hom))
  have hyb : ∀ p, yb.val (diskBoundaryInclusion (n + 2) p) = f (a' p) := fun p =>
    congrArg (fun g => g p) yb.property
  -- the other hemisphere is an element of `π_{n+1}(X, x₀)`
  let g : BallPair (n + 1) x₀ :=
    ⟨a'.comp ((F true).hom.comp (uliftUpCMap _)), fun z hz => by
      show a' (F true (ULift.up z)) = x₀
      rw [sphereFace_equator (n + 1) z hz]
      exact ha'F _⟩
  let cX : BallPair (n + 1) x₀ := ⟨ContinuousMap.const _ x₀, fun _ _ => rfl⟩
  let fg : BallPair (n + 1) (f x₀) :=
    ⟨f.hom.comp g.1, fun z hz => by simp [g.2 z hz]⟩
  let cY : BallPair (n + 1) (f x₀) := ⟨ContinuousMap.const _ (f x₀), fun _ _ => rfl⟩
  have hglobeY : globeRel cY fg := by
    refine ⟨yb.val.comp (uliftUpCMap _), ?_, ?_⟩
    · apply ContinuousMap.ext
      intro z
      show yb.val (ULift.up (hemi (n + 1) false z)) = f x₀
      rw [← incl_sphereFace_up, hyb]
      exact congrArg f (ha'F _)
    · apply ContinuousMap.ext
      intro z
      show yb.val (ULift.up (hemi (n + 1) true z)) = f (a' (F true (ULift.up z)))
      rw [← incl_sphereFace_up, hyb]
  have hY := (ballPair_homotopic_iff_genLoop cY fg).mp (homotopic_of_globeRel hglobeY)
  have hmapc : homotopyGroupMap (Fin (n + 1)) f x₀ ⟦ballPairEquivGenLoop x₀ cX⟧ =
      ⟦ballPairEquivGenLoop (f x₀) cY⟧ := by
    refine (Quotient.map_mk _ _ _).trans (congrArg _ ?_)
    apply Subtype.ext
    rfl
  have hmapg : homotopyGroupMap (Fin (n + 1)) f x₀ ⟦ballPairEquivGenLoop x₀ g⟧ =
      ⟦ballPairEquivGenLoop (f x₀) fg⟧ := by
    refine (Quotient.map_mk _ _ _).trans (congrArg _ ?_)
    apply Subtype.ext
    rfl
  have heq : (⟦ballPairEquivGenLoop x₀ cX⟧ : HomotopyGroup (Fin (n + 1)) X x₀) =
      ⟦ballPairEquivGenLoop x₀ g⟧ := by
    apply hinj x₀
    rw [hmapc, hmapg]
    exact Quotient.sound hY
  obtain ⟨Fx, hFx0, hFx1⟩ := globeRel_of_homotopic
    ((ballPair_homotopic_iff_genLoop cX g).mpr (Quotient.exact heq))
  -- the filler is an extension of `a'`
  let l' : C(disk.{u} (n + 2), X) := Fx.comp (uliftDownCMap _)
  have hl' : l'.comp (diskBoundaryInclusion.{u} (n + 2)).hom = a' := by
    apply ContinuousMap.ext
    intro p
    rcases Realization.Cellular.sphereFace_cover (n + 1) p with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · show Fx (diskBoundaryInclusion (n + 2) (F false (ULift.up z.down))).down = _
      rw [incl_sphereFace_up]
      have h := congrArg (fun k => k z.down) hFx0
      exact h.trans (ha'F _).symm
    · show Fx (diskBoundaryInclusion (n + 2) (F true (ULift.up z.down))).down = _
      rw [incl_sphereFace_up]
      have h := congrArg (fun k => k z.down) hFx1
      exact h
  -- transport back along the deformation
  obtain ⟨e, -⟩ := exists_track (diskBoundaryInclusion.{u} (n + 2))
    (diskBoundaryInclusion_mem (n + 2)) H'.symm
    (⟨l', hl'⟩ : Extension (diskBoundaryInclusion.{u} (n + 2)) a')
  exact ⟨ofHom e.val, TopCat.hom_ext e.property⟩

end HomotopyHypothesis.Completion.Compression
