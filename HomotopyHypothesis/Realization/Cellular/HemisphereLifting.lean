import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Cellular.BoundaryComparison
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
import HomotopyHypothesis.Realization.Cellular.HemisphereExtension
import HomotopyHypothesis.Realization.Cellular.Representables
noncomputable section

open CategoryTheory Limits Topology
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

namespace HomotopyHypothesis.Realization.Cellular

universe u

/-- Upper hemisphere inclusions lift against path endpoint evaluation. -/
theorem hemisphere_hasLiftingProperty (Y : TopCat.{u}) (n : ℕ) :
    HasLiftingProperty (oaiTopGlobes.map (Globe.source n)) (pathEndpoints Y) := by
  constructor
  intro a b sq
  change TopCat.disk.{u} n ⟶ TopCat.of C(unitInterval, Y) at a
  change TopCat.disk.{u} (n + 1) ⟶ TopCat.of (Y × Y) at b
  let A : C(Ball n × unitInterval, Y) :=
    ⟨fun p => a (ULift.up p.1) p.2,
      continuous_eval.comp
        ((a.hom.continuous.comp (continuous_uliftUp.comp continuous_fst)).prodMk continuous_snd)⟩
  let b₀ : C(Ball (n + 1), Y) :=
    ⟨fun x => (b (ULift.up x)).1,
      continuous_fst.comp (b.hom.continuous.comp continuous_uliftUp)⟩
  let b₁ : C(Ball (n + 1), Y) :=
    ⟨fun x => (b (ULift.up x)).2,
      continuous_snd.comp (b.hom.continuous.comp continuous_uliftUp)⟩
  have hs (x : Ball n) :
      (a (ULift.up x) 0, a (ULift.up x) 1) =
        b (ULift.up (ballFace (Nat.lt_succ_self n) false x)) := by
    have h := ConcreteCategory.congr_hom sq.w (show TopCat.disk.{u} n from ULift.up x)
    change (a (ULift.up x) 0, a (ULift.up x) 1) =
      b (ULift.up (ballFace (Nat.lt_succ_self n) false x)) at h
    exact h
  have h₀ (x : Ball n) : A (x, 0) = b₀ (ballFace (Nat.lt_succ_self n) false x) :=
    congrArg Prod.fst (hs x)
  have h₁ (x : Ball n) : A (x, 1) = b₁ (ballFace (Nat.lt_succ_self n) false x) :=
    congrArg Prod.snd (hs x)
  obtain ⟨H, hface, hzero, hone⟩ := hemisphere_path_extension n A b₀ b₁ h₀ h₁
  let l : TopCat.disk.{u} (n + 1) ⟶ TopCat.of C(unitInterval, Y) :=
    TopCat.ofHom ((ContinuousMap.curry H).comp ⟨ULift.down, continuous_uliftDown⟩)
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply TopCat.ext
    intro x
    apply ContinuousMap.ext
    intro t
    exact hface x.down t
  · apply TopCat.ext
    intro x
    apply Prod.ext
    · exact hzero x.down
    · exact hone x.down

/-- Realized source maps lift against path endpoint evaluation. -/
theorem realizationSource_hasLiftingProperty {C : GlobularTheory.{u}} (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) (Y : TopCat.{u}) (n : ℕ) :
    HasLiftingProperty (L.map (J C n)) (pathEndpoints Y) := by
  let e : Arrow.mk (L.map (J C n)) ≅ Arrow.mk (oaiTopGlobes.map (Globe.source n)) :=
    Arrow.isoMk (realizationDiskIso R L adj n) (realizationDiskIso R L adj (n + 1))
      (realizationDiskIso_face R L adj n false).symm
  exact (HasLiftingProperty.iff_of_arrow_iso_left e (pathEndpoints Y)).mpr
    (hemisphere_hasLiftingProperty Y n)

end HomotopyHypothesis.Realization.Cellular
