import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Completion.Compression.DiskCube
import HomotopyHypothesis.Completion.Compression.PiZero
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat Topology

/-- Direct ULift down/up continuous maps (application is definitionally transparent). -/
def uliftDownCMap (α : Type*) [TopologicalSpace α] : C(ULift α, α) :=
  ⟨ULift.down, continuous_uliftDown⟩

def uliftUpCMap (α : Type*) [TopologicalSpace α] : C(α, ULift α) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-! ### TopCat-level transport maps -/

/-- Forward cube map at TopCat level (domain is ULift-wrapped). -/
def diskToCubeULiftCMap (n : ℕ) :
    C(TopCat.disk.{u} n, Fin n → unitInterval) :=
  (⟨diskToCubeFun n, continuous_diskToCubeFun n⟩ :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, _)).comp
    (uliftDownCMap _)

/-- Backward cube map at TopCat level. -/
def cubeToDiskULiftCMap (n : ℕ) :
    C(Fin n → unitInterval, TopCat.disk.{u} n) :=
  (uliftUpCMap _).comp
    (⟨cubeToDiskFun n, continuous_cubeToDiskFun n⟩ :
      C(_, Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))

/-- The ULift inclusion preserves the underlying vector (all `n`, by `rfl`). -/
lemma inclusion_preserves_vector_all (n : ℕ) (p : TopCat.diskBoundary.{u} n) :
    (((TopCat.diskBoundaryInclusion n p).down.val : EuclideanSpace ℝ (Fin n))) =
      ((p.down.val : EuclideanSpace ℝ (Fin n))) := by
  rfl

/-- Function-level forward roundtrip (no ULift, no wrappers). -/
lemma fwdBwdCube_apply (n : ℕ) (t : Fin n → unitInterval) :
    diskToCubeFun n (cubeToDiskFun n t) = t := by
  have h1 : radialFSub n (radialGSub n (cubeToLinfFun n t)) = cubeToLinfFun n t :=
    (radialHomeomorph n).right_inv _
  have h2 : linfToCubeFun n (cubeToLinfFun n t) = t :=
    (linfCubeHomeomorph n).right_inv t
  show linfToCubeFun n (radialFSub n (radialGSub n (cubeToLinfFun n t))) = t
  rw [h1]
  exact h2

lemma fwdBwdCubeULift_apply (n : ℕ) (t : Fin n → unitInterval) :
    diskToCubeULiftCMap n (cubeToDiskULiftCMap n t) = t := by
  have e : diskToCubeULiftCMap n (cubeToDiskULiftCMap n t) =
      diskToCubeFun n (cubeToDiskFun n t) := rfl
  rw [e]
  exact fwdBwdCube_apply n t

/-- Function-level backward roundtrip (no ULift). -/
lemma bwdFwdCube_apply (n : ℕ) (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    cubeToDiskFun n (diskToCubeFun n x) = x := by
  have h1 : cubeToLinfFun n (linfToCubeFun n (radialFSub n x)) = radialFSub n x :=
    (linfCubeHomeomorph n).left_inv _
  have h2 : radialGSub n (radialFSub n x) = x :=
    (radialHomeomorph n).left_inv x
  show radialGSub n (cubeToLinfFun n (linfToCubeFun n (radialFSub n x))) = x
  rw [h1]
  exact h2

lemma bwdFwdCubeULift_apply (n : ℕ) (d : TopCat.disk.{u} n) :
    cubeToDiskULiftCMap n (diskToCubeULiftCMap n d) = d := by
  have e : cubeToDiskULiftCMap n (diskToCubeULiftCMap n d) =
      ULift.up (cubeToDiskFun n (diskToCubeFun n (ULift.down d))) := rfl
  rw [e, bwdFwdCube_apply]
  exact ULift.up_down d

/-- Constant boundary map. -/
def diskBoundaryConstMap (X : TopCat.{u}) (x : X) (n : ℕ) :
    TopCat.diskBoundary.{u} n ⟶ X :=
  TopCat.ofHom ⟨fun _ => x, continuous_const⟩

lemma diskBoundaryConstMap_apply (X : TopCat.{u}) (x : X) (n : ℕ)
    (p : TopCat.diskBoundary.{u} n) : (diskBoundaryConstMap X x n) p = x := by
  rfl

/-- Forward image of a sphere point lies in the cube boundary (ULift version). -/
lemma fwdU_mem_cubeBoundary (n : ℕ) (p : TopCat.diskBoundary.{u} n) :
    diskToCubeULiftCMap n (TopCat.diskBoundaryInclusion n p) ∈
      Cube.boundary (Fin n) := by
  have hnorm : ‖((TopCat.diskBoundaryInclusion n p).down.val :
      EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hmem : (p.down.val : EuclideanSpace ℝ (Fin n)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := p.down.property
    rw [Metric.mem_sphere, dist_zero_right] at hmem
    rw [inclusion_preserves_vector_all]
    exact hmem
  have e : diskToCubeULiftCMap n (TopCat.diskBoundaryInclusion n p) =
      diskToCubeFun n (ULift.down (TopCat.diskBoundaryInclusion n p)) := rfl
  rw [e]
  exact diskToCube_mem_boundary n _ hnorm

/-- Backward image of a cube-boundary point lies in the range of the inclusion. -/
lemma bwdU_mem_range (n : ℕ) (c : Fin n → unitInterval)
    (hc : c ∈ Cube.boundary (Fin n)) :
    cubeToDiskULiftCMap n c ∈ Set.range (TopCat.diskBoundaryInclusion n) := by
  have hdist := cubeToDisk_mem_sphere n c hc
  refine ⟨ULift.up ⟨(cubeToDiskFun n c).val, ?_⟩, ?_⟩
  · rw [Metric.mem_sphere]
    exact hdist
  · apply ULift.ext
    apply Subtype.ext
    rfl

lemma diskBoundaryConstMap_hom_apply (X : TopCat.{u}) (x : X) (n : ℕ)
    (p : TopCat.diskBoundary.{u} n) : (diskBoundaryConstMap X x n).hom p = x := rfl

/-- The constant-boundary square commutes. -/
lemma const_comm_cube (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (bmap : C(Fin (n + 1) → unitInterval, Y))
    (hb : ∀ y ∈ Cube.boundary (Fin (n + 1)), bmap y = f x) :
    diskBoundaryConstMap X x (n + 1) ≫ f =
      TopCat.diskBoundaryInclusion (n + 1) ≫
        TopCat.ofHom (bmap.comp (diskToCubeULiftCMap (n + 1))) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [diskBoundaryConstMap_hom_apply]
  have hmem : diskToCubeULiftCMap (n + 1)
      ((TopCat.diskBoundaryInclusion (n + 1)).hom p) ∈
      Cube.boundary (Fin (n + 1)) :=
    fwdU_mem_cubeBoundary (n + 1) p
  exact (hb _ hmem).symm

/-- Cube-side roundtrip as a ContinuousMap identity. -/
lemma fwdBwdCubeULift_comp (n : ℕ) :
    (diskToCubeULiftCMap.{u} n).comp (cubeToDiskULiftCMap.{u} n) =
      ContinuousMap.id (Fin n → unitInterval) := by
  apply ContinuousMap.ext
  intro t
  show diskToCubeULiftCMap.{u} n (cubeToDiskULiftCMap.{u} n t) = t
  have e : diskToCubeULiftCMap.{u} n (cubeToDiskULiftCMap.{u} n t) =
      diskToCubeFun n (cubeToDiskFun n t) := rfl
  rw [e]
  exact fwdBwdCube_apply n t

/-- Precomposing a homotopy relative to `S` with `φ` gives a homotopy relative
to any `T` that `φ` sends into `S`. -/
lemma HomotopicRel_precomp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {g₀ g₁ : C(X, Y)} {S : Set X} (h : g₀.HomotopicRel g₁ S)
    (φ : C(Z, X)) {T : Set Z} (hT : ∀ c ∈ T, φ c ∈ S) :
    (g₀.comp φ).HomotopicRel (g₁.comp φ) T := by
  obtain ⟨H⟩ := h
  obtain ⟨⟨Hcm, Hz, Ho⟩, Hprop⟩ := H
  let ψ : C(unitInterval × Z, unitInterval × X) :=
    (ContinuousMap.id _).prodMap φ
  refine ⟨⟨⟨Hcm.comp ψ, ?_, ?_⟩, ?_⟩⟩
  · intro c
    show Hcm (ψ (0, c)) = (g₀.comp φ) c
    rw [show ψ (0, c) = ((0 : unitInterval), φ c) from rfl,
      ContinuousMap.comp_apply]
    exact Hz _
  · intro c
    show Hcm (ψ (1, c)) = (g₁.comp φ) c
    rw [show ψ (1, c) = ((1 : unitInterval), φ c) from rfl,
      ContinuousMap.comp_apply]
    exact Ho _
  · intro t c hc
    show Hcm (ψ (t, c)) = g₀ (φ c)
    rw [show ψ (t, c) = (t, φ c) from rfl]
    exact Hprop t (φ c) (hT c hc)

/-- Surjectivity on higher homotopy groups from the compression property. -/
theorem henry_imp_surjective_pi {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) (n : ℕ) (x : X) :
    Function.Surjective (homotopyGroupMap (Fin (n + 1)) f x) := by
  intro QB
  obtain ⟨b, rfl⟩ := Quotient.exists_rep QB
  let bD : TopCat.disk.{u} (n + 1) ⟶ Y :=
    TopCat.ofHom (b.1.comp (diskToCubeULiftCMap (n + 1)))
  let aD := diskBoundaryConstMap X x (n + 1)
  have hcomm : aD ≫ f = TopCat.diskBoundaryInclusion (n + 1) ≫ bD :=
    const_comm_cube n f x b.1 b.2
  obtain ⟨l, hl, hrel⟩ := H (n + 1) aD bD hcomm
  -- return loop, transported back to the cube
  have hCbound : ∀ c ∈ Cube.boundary (Fin (n + 1)),
      (l.hom.comp (cubeToDiskULiftCMap (n + 1))) c = x := by
    intro c hc
    obtain ⟨p, hp⟩ := bwdU_mem_range (n + 1) c hc
    have h1 : (TopCat.diskBoundaryInclusion (n + 1) ≫ l) p = aD p := by
      rw [hl]
    rw [TopCat.comp_app] at h1
    rw [ContinuousMap.comp_apply]
    have h2 : (cubeToDiskULiftCMap (n + 1)) c =
        (TopCat.diskBoundaryInclusion (n + 1)) p := hp.symm
    rw [h2]
    have h3 : l ((TopCat.diskBoundaryInclusion (n + 1)) p) = x := by
      rw [h1]
      exact diskBoundaryConstMap_apply X x (n + 1) p
    exact h3
  let lC : GenLoop (Fin (n + 1)) X x := ⟨_, hCbound⟩
  refine ⟨⟦lC⟧, ?_⟩
  have hmap : homotopyGroupMap (Fin (n + 1)) f x ⟦lC⟧ =
      ⟦⟨f.hom.comp lC.1, fun y hy => congrArg f.hom (hCbound y hy)⟩⟧ :=
    Quotient.map_mk _ _ _
  rw [hmap]
  apply Quotient.sound
  show GenLoop.Homotopic _ _
  -- transport Henry's rel-homotopy back to the cube
  have hpre := HomotopicRel_precomp hrel (cubeToDiskULiftCMap (n + 1))
    (fun c hc => bwdU_mem_range (n + 1) c hc)
  have hbD : bD.hom = b.1.comp (diskToCubeULiftCMap (n + 1)) := rfl
  rw [TopCat.hom_comp, hbD, ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    fwdBwdCubeULift_comp, ContinuousMap.comp_id] at hpre
  exact hpre

end HomotopyHypothesis.Completion.Compression
