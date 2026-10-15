import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Cellular.CellularTransport
import HomotopyHypothesis.Realization.Cellular.Representables
import HomotopyHypothesis.Realization.Cellular.SpherePushout
noncomputable section

open CategoryTheory Limits Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

set_option backward.isDefEq.respectTransparency false

universe u

variable {C : GlobularTheory.{u}} (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

/-- Disk comparisons commute with the source and target faces. -/
theorem realizationDiskIso_face (n : ℕ) (b : Bool) :
    L.map (show disk C n ⟶ disk C (n + 1) from
      yoneda.map (C.globes.map (Globe.face (Nat.lt_succ_self n) b))) ≫
        (realizationDiskIso R L adj (n + 1)).hom =
      (realizationDiskIso R L adj n).hom ≫
        oaiTopGlobes.map (Globe.face (Nat.lt_succ_self n) b) := by
  simp only [realizationDiskIso, Iso.trans_hom]
  let f : (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n + 1)⟩ :=
    C.globes.map (Globe.face (Nat.lt_succ_self n) b)
  have hn := realizationRepresentableIso_naturality R L adj f
  have htop := R.onGlobes.hom.naturality (Globe.face (Nat.lt_succ_self n) b)
  change R.functor.map f ≫ (R.onGlobes.app (Globe.mk (n + 1))).hom =
    (R.onGlobes.app (Globe.mk n)).hom ≫ oaiTopGlobes.map
      (Globe.face (Nat.lt_succ_self n) b) at htop
  calc
    _ = (realizationRepresentableIso R L adj (Shape.globe n)).hom ≫
        R.functor.map f ≫ (R.onGlobes.app (Globe.mk (n + 1))).hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (R.onGlobes.app (Globe.mk (n + 1))).hom) hn
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k => (realizationRepresentableIso R L adj (Shape.globe n)).hom ≫ k)
        htop

/-- A comparison of a realized globular boundary with the standard sphere. -/
structure BoundaryComparison (n : ℕ) where
  iso : L.obj (boundaryDisk C n) ≅ TopCat.diskBoundary.{u} n
  comm : L.map (I C n) ≫ (realizationDiskIso R L adj n).hom =
    iso.hom ≫ TopCat.diskBoundaryInclusion n

/-- The zero-dimensional boundary is empty. -/
def diskBoundaryZero_initial : IsInitial (TopCat.diskBoundary.{u} 0) := by
  haveI : IsEmpty (TopCat.diskBoundary.{u} 0) := ⟨fun x => by
    have hx : ‖x.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.down.2
    have hz : x.down.1 = 0 := Subsingleton.elim _ _
    simp [hz] at hx⟩
  letI : ∀ X : TopCat.{u}, Unique (TopCat.diskBoundary.{u} 0 ⟶ X) := fun X =>
    ⟨⟨TopCat.ofHom ⟨isEmptyElim, by fun_prop⟩⟩, fun f => by
      apply TopCat.ext
      intro x
      exact isEmptyElim x⟩
  exact IsInitial.ofUnique _

include adj

/-- Inductive boundary comparison using the two hemispheres of a sphere. -/
def realizationBoundaryComparison : (n : ℕ) → BoundaryComparison R L adj n
  | 0 => by
      letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
      have hi : IsInitial (L.obj (boundaryDisk C 0)) :=
        initialIsInitial.isInitialObj L _
      exact ⟨hi.uniqueUpToIso diskBoundaryZero_initial, hi.hom_ext _ _⟩
  | n + 1 => by
      letI : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
      let e := realizationBoundaryComparison n
      let d := realizationDiskIso R L adj n
      have s := (IsPushout.of_hasPushout (I C n) (I C n)).map L
      have t : IsPushout (L.map (I C n)) (L.map (I C n))
          (d.hom ≫ sphereFace n false) (d.hom ≫ sphereFace n true) :=
        (sphere_isPushout n).of_iso' e.iso d d (Iso.refl _)
          e.comm.symm e.comm.symm (by simp) (by simp)
      let iso : L.obj (boundaryDisk C (n + 1)) ≅ TopCat.diskBoundary (n + 1) :=
        s.isoIsPushout _ _ t
      refine ⟨iso, ?_⟩
      apply s.hom_ext
      · rw [← Category.assoc, ← L.map_comp]
        change L.map (pushout.inl (I C n) (I C n) ≫
          pushout.desc (J C n) (targetDisk C n) _) ≫ _ = _
        rw [pushout.inl_desc]
        rw [← Category.assoc, s.inl_isoIsPushout_hom _ _ t, Category.assoc,
          sphereFace_inclusion]
        exact realizationDiskIso_face R L adj n false
      · rw [← Category.assoc, ← L.map_comp]
        change L.map (pushout.inr (I C n) (I C n) ≫
          pushout.desc (J C n) (targetDisk C n) _) ≫ _ = _
        rw [pushout.inr_desc]
        rw [← Category.assoc, s.inr_isoIsPushout_hom _ _ t, Category.assoc,
          sphereFace_inclusion]
        exact realizationDiskIso_face R L adj n true

/-- Realized generating boundaries are standard boundary inclusions up to isomorphism. -/
def realizationBoundaryArrowIso (n : ℕ) :
    Arrow.mk (L.map (I C n)) ≅ Arrow.mk (TopCat.diskBoundaryInclusion.{u} n) :=
  Arrow.isoMk (realizationBoundaryComparison R L adj n).iso
    (realizationDiskIso R L adj n) (realizationBoundaryComparison R L adj n).comm.symm

/-- A realized generating boundary is a relative finite cell complex. -/
theorem realizationBoundary_mem (n : ℕ) :
    Top.relativeFiniteCellComplexes (L.map (I C n)) := by
  apply (Top.relativeFiniteCellComplexes.arrow_mk_iso_iff
    (realizationBoundaryArrowIso R L adj n)).mpr
  apply MorphismProperty.le_multiplicativeClosure _ _
  left
  exact MorphismProperty.le_pushouts _ _ (.mk n)

end HomotopyHypothesis.Realization.Cellular
