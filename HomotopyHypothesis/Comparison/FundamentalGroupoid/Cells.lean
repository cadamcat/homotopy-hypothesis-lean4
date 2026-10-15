import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Comparison.FundamentalGroupoid.Geom
/-!
# Cells of `Π_R X` as disk maps

An `n`-cell of the fundamental ∞-groupoid is a map out of the realized `n`-globe. Transport along
the realization's identification with the Euclidean disk turns it into a map `𝔻 n → X`. Base cells
factor through the point `𝔻⁰`, so they are constant. Loops are then maps of pairs
`(𝔻^{n+1}, S^n) → (X, x)`, and joining them is a homotopy relative to the sphere.
-/

noncomputable section

namespace HomotopyHypothesis.Comparison.FundamentalGroupoid.Cells

open CategoryTheory Opposite
open OAI.Grothendieck
open OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Comparison.FundamentalGroupoid.Geom
open HomotopyHypothesis
open ContinuousMap

universe u

variable {C : GlobularTheory.{u}} (R : OAIRealization C)

/-- An `n`-cell of `Π_R X`. -/
abbrev Cell (X : TopCat.{u}) (n : ℕ) := (R.Pi.obj X).underlying.Cell n

/-- The realized `n`-globe, identified with the Euclidean disk. -/
def globeIso (n : ℕ) :
    R.functor.obj (C.globes.obj ⟨n⟩) ≅ TopCat.disk n :=
  R.onGlobes.app ⟨n⟩

/-- Send a cell to the corresponding map out of the disk. -/
def toDisk {X : TopCat.{u}} {n : ℕ} (φ : Cell R X n) : TopCat.disk n ⟶ X :=
  (globeIso R n).inv ≫ φ

/-- Send a map out of the disk back to a cell. -/
def ofDisk {X : TopCat.{u}} {n : ℕ} (f : TopCat.disk n ⟶ X) : Cell R X n :=
  (globeIso R n).hom ≫ f

lemma toDisk_ofDisk {X : TopCat.{u}} {n : ℕ} (f : TopCat.disk n ⟶ X) :
    toDisk R (ofDisk R f) = f := by
  simp only [toDisk, ofDisk]
  exact Iso.inv_hom_id_assoc (globeIso R n) f

lemma ofDisk_toDisk {X : TopCat.{u}} {n : ℕ} (φ : Cell R X n) :
    ofDisk R (toDisk R φ) = φ := by
  simp only [toDisk, ofDisk]
  exact Iso.hom_inv_id_assoc (globeIso R n) φ

/-- The homeomorphism `𝔻 n →` the carrier of `TopCat.disk n`, upwards. -/
def diskUp (n : ℕ) : C(ClosedBall n, TopCat.disk.{u} n) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- The homeomorphism the other way. -/
def diskDown (n : ℕ) : C(TopCat.disk.{u} n, ClosedBall n) :=
  ⟨ULift.down, continuous_uliftDown⟩

@[simp] lemma diskDown_up (n : ℕ) (y : ClosedBall n) : diskDown n (diskUp n y) = y := rfl

@[simp] lemma diskUp_down (n : ℕ) (y : TopCat.disk.{u} n) : diskUp n (diskDown n y) = y := by
  cases y
  rfl

/-- A cell, as a map out of the closed disk. -/
def toMap {X : TopCat.{u}} {n : ℕ} (φ : Cell R X n) : C(ClosedBall n, X) :=
  (toDisk R φ).hom.comp (diskUp n)

/-- A disk map, as a cell. -/
def ofMap {X : TopCat.{u}} {n : ℕ} (f : C(ClosedBall n, X)) : Cell R X n :=
  ofDisk R (TopCat.ofHom (f.comp (diskDown n)))

lemma toMap_ofMap {X : TopCat.{u}} {n : ℕ} (f : C(ClosedBall n, X)) :
    toMap R (ofMap R f) = f := by
  ext y
  have hdisk := toDisk_ofDisk R (TopCat.ofHom (f.comp (diskDown n)))
  have h := congrArg (fun g : TopCat.disk n ⟶ X => g.hom (diskUp n y)) hdisk
  have hcoe : (TopCat.ofHom (f.comp (diskDown n))).hom (diskUp n y) = f y := by
    simp only [TopCat.hom_ofHom, ContinuousMap.comp_apply, diskDown_up]
  simpa [toMap, ofMap] using h.trans hcoe

lemma ofMap_toMap {X : TopCat.{u}} {n : ℕ} (φ : Cell R X n) :
    ofMap R (toMap R φ) = φ := by
  simp only [ofMap, toMap]
  exact ofDisk_toDisk R φ

lemma toMap_injective {X : TopCat.{u}} {n : ℕ} : Function.Injective (toMap R (X := X) (n := n)) := by
  intro φ ψ h
  apply_fun ofMap R at h
  simpa [ofMap_toMap] using h

lemma source_precomp {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    (R.Pi.obj X).underlying.source n φ =
      R.functor.map (C.globes.map (Globe.source n)) ≫ φ := rfl

lemma target_precomp {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    (R.Pi.obj X).underlying.target n φ =
      R.functor.map (C.globes.map (Globe.target n)) ≫ φ := rfl

lemma postcomp_cell {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (φ : Cell R X n) :
    (underlyingMap (R.Pi.map f)).app n φ = φ ≫ f := rfl

lemma unitCell_precomp {X : TopCat.{u}} (hC : C.IsCoherator) {n : ℕ} (φ : Cell R X n) :
    (R.Pi.obj X).unitCell hC n φ = R.functor.map (C.unit hC n) ≫ φ := rfl

/-- A globe face, as a map of Euclidean disks. -/
def faceDisk (n : ℕ) (side : Bool) : TopCat.disk.{u} n ⟶ TopCat.disk.{u} (n + 1) :=
  oaiTopGlobes.map (Globe.face (Nat.lt_succ_self n) side)

lemma faceDisk_source (n : ℕ) :
    (globeIso R n).inv ≫ R.functor.map (C.globes.map (Globe.source n)) =
      faceDisk n false ≫ (globeIso R (n + 1)).inv := by
  have hnat := (R.onGlobes.inv.naturality (Globe.source n)).symm
  simp only [Functor.comp_map] at hnat
  simp only [globeIso, faceDisk, Globe.source]
  exact hnat

lemma faceDisk_target (n : ℕ) :
    (globeIso R n).inv ≫ R.functor.map (C.globes.map (Globe.target n)) =
      faceDisk n true ≫ (globeIso R (n + 1)).inv := by
  have hnat := (R.onGlobes.inv.naturality (Globe.target n)).symm
  simp only [Functor.comp_map] at hnat
  simp only [globeIso, faceDisk, Globe.target]
  exact hnat

lemma toDisk_source {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    toDisk R ((R.Pi.obj X).underlying.source n φ) =
      faceDisk n false ≫ toDisk R φ := by
  have hL : toDisk R ((R.Pi.obj X).underlying.source n φ) =
      ((globeIso R n).inv ≫ R.functor.map (C.globes.map (Globe.source n))) ≫ φ :=
    (Category.assoc (globeIso R n).inv (R.functor.map (C.globes.map (Globe.source n))) φ).symm
  exact (hL.trans (congrArg (fun g => g ≫ φ) (faceDisk_source R n))).trans
    (Category.assoc (faceDisk n false) (globeIso R (n + 1)).inv φ)

lemma toDisk_target {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    toDisk R ((R.Pi.obj X).underlying.target n φ) =
      faceDisk n true ≫ toDisk R φ := by
  have hL : toDisk R ((R.Pi.obj X).underlying.target n φ) =
      ((globeIso R n).inv ≫ R.functor.map (C.globes.map (Globe.target n))) ≫ φ :=
    (Category.assoc (globeIso R n).inv (R.functor.map (C.globes.map (Globe.target n))) φ).symm
  exact (hL.trans (congrArg (fun g => g ≫ φ) (faceDisk_target R n))).trans
    (Category.assoc (faceDisk n true) (globeIso R (n + 1)).inv φ)

/-- `snocVec` is the coordinate formula of a globe face into the next disk. -/
lemma snocVec_eq_faceVec (n : ℕ) (side : Bool) (v : E n) :
    snocVec v ((if side then -1 else 1) * Real.sqrt (1 - ‖v‖ ^ 2)) =
      faceVec n (n + 1) side v := by
  ext i
  simp only [snocVec, faceVec, PiLp.toLp_apply]
  by_cases hi : (i : ℕ) < n
  · rw [dite_eq_left hi, dite_eq_left hi]
  · have hin : (i : ℕ) = n := by
      have hlt : (i : ℕ) < n + 1 := i.isLt
      omega
    simp [hin]

/-- The geometric hemisphere agrees with the globe-category face. -/
lemma hemi_eq_ballFace (n : ℕ) (side : Bool) :
    hemi n side = ballFace (Nat.lt_succ_self n) side := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  simpa [hemi, ballFace] using snocVec_eq_faceVec n side y.1

lemma face_diskUp (n : ℕ) (side : Bool) (y : ClosedBall n) :
    (oaiTopGlobes.map (Globe.face (Nat.lt_succ_self n) side)) (diskUp n y) =
      diskUp (n + 1) (hemi n side y) := by
  rw [hemi_eq_ballFace]
  rfl

lemma faceDisk_diskUp (n : ℕ) (side : Bool) (y : ClosedBall n) :
    (faceDisk n side).hom (diskUp n y) = diskUp (n + 1) (hemi n side y) := by
  simp only [faceDisk]
  exact face_diskUp n side y

lemma toMap_source {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    toMap R ((R.Pi.obj X).underlying.source n φ) = (toMap R φ).comp (hemi n false) := by
  ext y
  have h := congrArg (fun g : TopCat.disk n ⟶ X => g.hom (diskUp n y)) (toDisk_source R φ)
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h
  rw [faceDisk_diskUp] at h
  simpa [toMap] using h

lemma toMap_target {X : TopCat.{u}} {n : ℕ} (φ : Cell R X (n + 1)) :
    toMap R ((R.Pi.obj X).underlying.target n φ) = (toMap R φ).comp (hemi n true) := by
  ext y
  have h := congrArg (fun g : TopCat.disk n ⟶ X => g.hom (diskUp n y)) (toDisk_target R φ)
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h
  rw [faceDisk_diskUp] at h
  simpa [toMap] using h

lemma toMap_postcomp {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (φ : Cell R X n) :
    toMap R (φ ≫ f) = f.hom.comp (toMap R φ) := by
  ext y
  have hassoc : (globeIso R n).inv ≫ φ ≫ f = ((globeIso R n).inv ≫ φ) ≫ f :=
    (Category.assoc (globeIso R n).inv φ f).symm
  have h := congrArg (fun g : TopCat.disk n ⟶ Y => g.hom (diskUp n y)) hassoc
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h
  simpa [toMap, toDisk] using h

/-! ### Points and path components -/

lemma closedBall_zero_eq (a b : ClosedBall 0) : a = b := by
  apply Subtype.ext
  ext i
  exact Fin.elim0 i

/-- The point of `X` named by a `0`-cell. -/
def pointOfCell {X : TopCat.{u}} (φ : Cell R X 0) : X :=
  toMap R φ (originBall 0)

/-- The `0`-cell which is the constant map at a point, through the point-disk. -/
def cellOfPoint {X : TopCat.{u}} (x : X) : Cell R X 0 :=
  ofMap R (ContinuousMap.const _ x)

lemma toMap_eq_const {X : TopCat.{u}} (φ : Cell R X 0) :
    toMap R φ = ContinuousMap.const _ (pointOfCell R φ) := by
  ext y
  rw [closedBall_zero_eq y (originBall 0)]
  rfl

lemma toMap_cellOfPoint {X : TopCat.{u}} (x : X) :
    toMap R (cellOfPoint R x) = ContinuousMap.const _ x := by
  simp [cellOfPoint, toMap_ofMap]

lemma pointOfCell_cellOfPoint {X : TopCat.{u}} (x : X) :
    pointOfCell R (cellOfPoint R x) = x := by
  simp [pointOfCell, toMap_cellOfPoint, ContinuousMap.const_apply]

lemma cellOfPoint_pointOfCell {X : TopCat.{u}} (φ : Cell R X 0) :
    cellOfPoint R (pointOfCell R φ) = φ := by
  rw [cellOfPoint, ← toMap_eq_const, ofMap_toMap]

/-- `0`-cells of `Π_R X` are the points of `X`. -/
def cellPointEquiv {X : TopCat.{u}} : Cell R X 0 ≃ X where
  toFun := pointOfCell R
  invFun := cellOfPoint R
  left_inv := cellOfPoint_pointOfCell R
  right_inv := pointOfCell_cellOfPoint R

lemma pointOfCell_postcomp {X Y : TopCat.{u}} (f : X ⟶ Y) (φ : Cell R X 0) :
    pointOfCell R (φ ≫ f) = f (pointOfCell R φ) := by
  simp [pointOfCell, toMap_postcomp, ContinuousMap.comp_apply]

lemma toMap_endpoint_source {X : TopCat.{u}} (φ : Cell R X 1) :
    toMap R φ endpointSource = pointOfCell R ((R.Pi.obj X).underlying.source 0 φ) := by
  have h := congrFun (congrArg DFunLike.coe (toMap_source R φ)) (originBall 0)
  simpa [pointOfCell, endpointSource_eq_hemi] using h.symm

lemma toMap_endpoint_target {X : TopCat.{u}} (φ : Cell R X 1) :
    toMap R φ endpointTarget = pointOfCell R ((R.Pi.obj X).underlying.target 0 φ) := by
  have h := congrFun (congrArg DFunLike.coe (toMap_target R φ)) (originBall 0)
  simpa [pointOfCell, endpointTarget_eq_hemi] using h.symm

lemma mapOfPath_hemi_source {X : Type*} [TopologicalSpace X] {a b : X} (p : Path a b) :
    (mapOfPath p).comp (hemi 0 false) = ContinuousMap.const _ a := by
  ext y
  rw [closedBall_zero_eq y (originBall 0)]
  simp [ContinuousMap.comp_apply, endpointSource_eq_hemi.symm, mapOfPath_source,
    ContinuousMap.const_apply]

lemma mapOfPath_hemi_target {X : Type*} [TopologicalSpace X] {a b : X} (p : Path a b) :
    (mapOfPath p).comp (hemi 0 true) = ContinuousMap.const _ b := by
  ext y
  rw [closedBall_zero_eq y (originBall 0)]
  simp [ContinuousMap.comp_apply, endpointTarget_eq_hemi.symm, mapOfPath_target,
    ContinuousMap.const_apply]

/-- A `1`-cell joins two `0`-cells if and only if the corresponding points are path-joined. -/
lemma cell_joined_iff {X : TopCat.{u}} (a b : Cell R X 0) :
    (R.Pi.obj X).underlying.Joined 0 a b ↔ Joined (pointOfCell R a) (pointOfCell R b) := by
  constructor
  · rintro ⟨h, hs, ht⟩
    refine ⟨{
      toContinuousMap := (toMap R h).comp intervalToBall1
      source' := by simp [intervalToBall1_zero, toMap_endpoint_source, hs]
      target' := by simp [intervalToBall1_one, toMap_endpoint_target, ht]
    }⟩
  · rintro ⟨p⟩
    refine ⟨ofMap R (mapOfPath p), ?_, ?_⟩
    · apply toMap_injective R
      simp only [toMap_source, toMap_ofMap]
      exact (mapOfPath_hemi_source p).trans (toMap_eq_const R a).symm
    · apply toMap_injective R
      simp only [toMap_target, toMap_ofMap]
      exact (mapOfPath_hemi_target p).trans (toMap_eq_const R b).symm

/-- Path components of `Π_R X` are the path components of `X`. -/
def componentsEquiv {X : TopCat.{u}} :
    (R.Pi.obj X).Components ≃ ZerothHomotopy X :=
  Quot.congr (cellPointEquiv R (X := X)) (cell_joined_iff R)

lemma componentsMap_comm {X Y : TopCat.{u}} (f : X ⟶ Y) :
    componentsEquiv R (X := Y) ∘ componentsMap (R.Pi.map f) =
      zerothHomotopyMap f ∘ componentsEquiv R (X := X) := by
  funext q
  refine Quot.inductionOn q ?_
  intro a
  have hmk : componentsMap (R.Pi.map f) (Quot.mk _ a) =
      Quot.mk _ ((underlyingMap (R.Pi.map f)).app 0 a) := rfl
  have hLY : componentsEquiv R (X := Y)
      (Quot.mk _ ((underlyingMap (R.Pi.map f)).app 0 a)) =
      Quot.mk _ (pointOfCell R ((underlyingMap (R.Pi.map f)).app 0 a)) := rfl
  have hLX : componentsEquiv R (X := X) (Quot.mk _ a) =
      Quot.mk _ (pointOfCell R a) := rfl
  have hZ : zerothHomotopyMap f (Quot.mk _ (pointOfCell R a)) =
      Quot.mk _ (f.hom (pointOfCell R a)) := rfl
  have hpoint : pointOfCell R ((underlyingMap (R.Pi.map f)).app 0 a) =
      f.hom (pointOfCell R a) := by
    rw [postcomp_cell, pointOfCell_postcomp]
  refine (congrArg (componentsEquiv R (X := Y)) hmk).trans ?_
  refine hLY.trans ?_
  refine (congrArg (Quot.mk _) hpoint).trans ?_
  exact hZ.symm.trans (congrArg (zerothHomotopyMap f) hLX).symm

/-! ### Base cells are constant, and loops are maps of pairs -/

/-- Precomposing a constant cell with a map of realized globes keeps the constant map. -/
lemma toMap_whisker_const {X : TopCat.{u}} {m n : ℕ}
    (g : R.functor.obj (C.globes.obj ⟨m⟩) ⟶ R.functor.obj (C.globes.obj ⟨n⟩))
    {φ : Cell R X n} {p : X} (hφ : toMap R φ = ContinuousMap.const _ p) :
    toMap R (g ≫ φ) = ContinuousMap.const _ p := by
  ext y
  have hφdisk : φ = (globeIso R n).hom ≫ toDisk R φ := by
    simpa only [ofDisk] using (ofDisk_toDisk R φ).symm
  have hsub := congrArg (fun ψ : Cell R X n => (globeIso R m).inv ≫ g ≫ ψ) hφdisk
  have hassoc :
      (globeIso R m).inv ≫ g ≫ ((globeIso R n).hom ≫ toDisk R φ) =
        ((globeIso R m).inv ≫ g ≫ (globeIso R n).hom) ≫ toDisk R φ := by
    calc
      (globeIso R m).inv ≫ g ≫ ((globeIso R n).hom ≫ toDisk R φ) =
          ((globeIso R m).inv ≫ g) ≫ ((globeIso R n).hom ≫ toDisk R φ) :=
        (Category.assoc _ _ _).symm
      _ = (((globeIso R m).inv ≫ g) ≫ (globeIso R n).hom) ≫ toDisk R φ :=
        (Category.assoc _ _ _).symm
      _ = ((globeIso R m).inv ≫ g ≫ (globeIso R n).hom) ≫ toDisk R φ :=
        Category.assoc _ _ _
  have hk := hsub.trans hassoc
  have hpt := congrArg (fun t : TopCat.disk m ⟶ X => t.hom (diskUp m y)) hk
  have hL : toMap R (g ≫ φ) y = ((globeIso R m).inv ≫ g ≫ φ).hom (diskUp m y) := rfl
  set w : TopCat.disk n :=
    ((globeIso R m).inv ≫ g ≫ (globeIso R n).hom).hom (diskUp m y)
  have hR : (((globeIso R m).inv ≫ g ≫ (globeIso R n).hom) ≫ toDisk R φ).hom (diskUp m y) =
      toMap R φ (diskDown n w) := by
    simp only [w, toMap, TopCat.hom_comp, ContinuousMap.comp_apply, diskUp_down]
  have happ : toMap R φ (diskDown n w) = p :=
    (congrFun (congrArg DFunLike.coe hφ) (diskDown n w)).trans (ContinuousMap.const_apply _ _)
  exact hL.trans (hpt.trans (hR.trans (happ.trans (ContinuousMap.const_apply _ _).symm)))

lemma toMap_baseCell {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) :
    ∀ n, toMap R ((R.Pi.obj X).baseCell hC x n) =
      ContinuousMap.const (ClosedBall n) (pointOfCell R x) := by
  intro n
  induction n with
  | zero =>
    exact toMap_eq_const R x
  | succ n ih =>
    have hcell : (R.Pi.obj X).baseCell hC x (n + 1) =
        R.functor.map (C.unit hC n) ≫ (R.Pi.obj X).baseCell hC x n := by
      rw [baseCell, unitCell_precomp]
    exact hcell.symm ▸ toMap_whisker_const R (R.functor.map (C.unit hC n)) ih

/-- A loop, read as a map of pairs `(𝔻^{n+1}, S^n)`. -/
def toBallPair {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ)
    (z : (R.Pi.obj X).Loops hC x n) : BallPair (n + 1) (pointOfCell R x) :=
  ⟨toMap R z.1, by
    refine (const_on_sphere_iff_hemi (toMap R z.1)).mpr ⟨?_, ?_⟩
    · rw [← toMap_source, z.2.1, toMap_baseCell]
    · rw [← toMap_target, z.2.2, toMap_baseCell]⟩

/-- A map of pairs, read as a loop. -/
def ofBallPair {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ)
    (f : BallPair (n + 1) (pointOfCell R x)) : (R.Pi.obj X).Loops hC x n :=
  ⟨ofMap R f.1, by
    constructor
    · apply toMap_injective R
      have hconst := (const_on_sphere_iff_hemi f.1).mp f.2
      simp [toMap_source, toMap_ofMap, hconst.1, toMap_baseCell]
    · apply toMap_injective R
      have hconst := (const_on_sphere_iff_hemi f.1).mp f.2
      simp [toMap_target, toMap_ofMap, hconst.2, toMap_baseCell]⟩

/-- Loops in `Π_R X` are maps of pairs. -/
def loopsBallEquiv {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ) :
    (R.Pi.obj X).Loops hC x n ≃ BallPair (n + 1) (pointOfCell R x) where
  toFun := toBallPair R hC x n
  invFun := ofBallPair R hC x n
  left_inv z := by
    apply Subtype.ext
    simp [toBallPair, ofBallPair, ofMap_toMap]
  right_inv f := by
    apply Subtype.ext
    simp [toBallPair, ofBallPair, toMap_ofMap]

lemma toBallPair_postcomp {X Y : TopCat.{u}} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : Cell R X 0) (n : ℕ) (z : (R.Pi.obj X).Loops hC x n) :
    (toBallPair R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
        (loopsMap (R.Pi.map f) hC x n z)).1 =
      f.hom.comp (toBallPair R hC x n z).1 := by
  have hcoe : (loopsMap (R.Pi.map f) hC x n z).1 =
      (underlyingMap (R.Pi.map f)).app (n + 1) z.1 := rfl
  simp [toBallPair, hcoe, postcomp_cell, toMap_postcomp]

/-- Joining two loops by an `(n+2)`-cell is a globe filler of the corresponding disk maps. -/
lemma joined_iff_globeRel {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ)
    (a b : (R.Pi.obj X).Loops hC x n) :
    (R.Pi.obj X).underlying.Joined (n + 1) a.1 b.1 ↔
      globeRel (toBallPair R hC x n a) (toBallPair R hC x n b) := by
  constructor
  · rintro ⟨H, hs, ht⟩
    refine ⟨toMap R H, ?_, ?_⟩
    · simpa [toBallPair, hs] using (toMap_source R H).symm
    · simpa [toBallPair, ht] using (toMap_target R H).symm
  · rintro ⟨H, h0, h1⟩
    refine ⟨ofMap R H, ?_, ?_⟩
    · apply toMap_injective R
      simp [toMap_source, toMap_ofMap, h0, toBallPair]
    · apply toMap_injective R
      simp [toMap_target, toMap_ofMap, h1, toBallPair]

/-- Loops in `Π_R X`, in degree `n`, are Mathlib's generalized loops of dimension `n + 1`. -/
def loopsGenEquiv {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ) :
    (R.Pi.obj X).Loops hC x n ≃
      GenLoop (Fin (n + 1)) X (pointOfCell R x) :=
  (loopsBallEquiv R hC x n).trans
    (ballPairEquivGenLoop (n := n + 1) (pointOfCell R x))

lemma joined_iff_genHomotopic {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ)
    (a b : (R.Pi.obj X).Loops hC x n) :
    (R.Pi.obj X).underlying.Joined (n + 1) a.1 b.1 ↔
      GenLoop.Homotopic (loopsGenEquiv R hC x n a) (loopsGenEquiv R hC x n b) := by
  rw [joined_iff_globeRel, globeRel_iff_homotopic, ballPair_homotopic_iff_genLoop]
  rfl

/-- Homotopy groups of `Π_R X` are the cube-model homotopy groups of `X`, one dimension up. -/
def homotopyEquiv {X : TopCat.{u}} (hC : C.IsCoherator) (x : Cell R X 0) (n : ℕ) :
    (R.Pi.obj X).HomotopyGroup hC x n ≃
      HomotopyGroup (Fin (n + 1)) X (pointOfCell R x) :=
  Quot.congr (loopsGenEquiv R hC x n) (joined_iff_genHomotopic R hC x n)

lemma loopsGenEquiv_postcomp {X Y : TopCat.{u}} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : Cell R X 0) (n : ℕ) (z : (R.Pi.obj X).Loops hC x n) :
    loopsGenEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
        (loopsMap (R.Pi.map f) hC x n z) =
      ⟨f.hom.comp (loopsGenEquiv R hC x n z).1,
        fun y hy => by
          simp only [ContinuousMap.comp_apply]
          rw [(loopsGenEquiv R hC x n z).2 y hy]
          exact (by rw [postcomp_cell, pointOfCell_postcomp] :
            pointOfCell R ((underlyingMap (R.Pi.map f)).app 0 x) =
              f.hom (pointOfCell R x)).symm⟩ := by
  apply Subtype.ext
  have hL : (loopsGenEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
      (loopsMap (R.Pi.map f) hC x n z)).1 =
      (toBallPair R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
        (loopsMap (R.Pi.map f) hC x n z)).1.comp toBallMap := rfl
  have hR : (loopsGenEquiv R hC x n z).1 =
      (toBallPair R hC x n z).1.comp toBallMap := rfl
  have hpost := toBallPair_postcomp R f hC x n z
  have hassoc : (f.hom.comp (toBallPair R hC x n z).1).comp toBallMap =
      f.hom.comp ((toBallPair R hC x n z).1.comp toBallMap) :=
    ContinuousMap.comp_assoc _ _ _
  exact hL.trans <| (congrArg (fun t => t.comp toBallMap) hpost).trans <|
    hassoc.trans (congrArg (fun t => f.hom.comp t) hR.symm)

lemma homotopyMap_comm {X Y : TopCat.{u}} (f : X ⟶ Y) (hC : C.IsCoherator)
    (x : Cell R X 0) (n : ℕ) :
    homotopyEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n ∘
        homotopyMap (R.Pi.map f) hC x n =
      homotopyGroupMap (Fin (n + 1)) f (pointOfCell R x) ∘
        homotopyEquiv R hC x n := by
  funext q
  refine Quot.inductionOn q ?_
  intro z
  have hm : homotopyMap (R.Pi.map f) hC x n (Quot.mk _ z) =
      Quot.mk _ (loopsMap (R.Pi.map f) hC x n z) := rfl
  have hLY : homotopyEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
      (Quot.mk _ (loopsMap (R.Pi.map f) hC x n z)) =
      Quot.mk _ (loopsGenEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
        (loopsMap (R.Pi.map f) hC x n z)) := rfl
  have hLX : homotopyEquiv R hC x n (Quot.mk _ z) =
      Quot.mk _ (loopsGenEquiv R hC x n z) := rfl
  have hpost := loopsGenEquiv_postcomp R f hC x n z
  have hG : homotopyGroupMap (Fin (n + 1)) f (pointOfCell R x)
      (Quot.mk _ (loopsGenEquiv R hC x n z)) =
      Quot.mk _ (loopsGenEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n
        (loopsMap (R.Pi.map f) hC x n z)) := by
    have hraw : homotopyGroupMap (Fin (n + 1)) f (pointOfCell R x)
        (Quotient.mk _ (loopsGenEquiv R hC x n z)) =
        Quotient.mk _ ⟨f.hom.comp (loopsGenEquiv R hC x n z).1,
          fun y hy => by simp [(loopsGenEquiv R hC x n z).2 y hy]⟩ := rfl
    refine hraw.trans (congrArg (Quot.mk _) ?_)
    apply Subtype.ext
    exact (congrArg Subtype.val hpost).symm
  refine (congrArg (homotopyEquiv R hC ((underlyingMap (R.Pi.map f)).app 0 x) n) hm).trans ?_
  refine hLY.trans ?_
  exact hG.symm.trans (congrArg (homotopyGroupMap (Fin (n + 1)) f (pointOfCell R x)) hLX).symm

end HomotopyHypothesis.Comparison.FundamentalGroupoid.Cells
