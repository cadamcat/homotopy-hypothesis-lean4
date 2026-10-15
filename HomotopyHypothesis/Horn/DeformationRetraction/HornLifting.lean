import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.HornPrism
import HomotopyHypothesis.Realization.Boundary.RealizationBoundary
import HomotopyHypothesis.Realization.Boundary.SimplexDisk
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
import HomotopyHypothesis.Horn.DeformationRetraction.HornRealization
import HomotopyHypothesis.Horn.DeformationRetraction.Lifting
import HomotopyHypothesis.Horn.DeformationRetraction.PrismExtension
/-!
# Lifting properties of a realized horn

Coordinate retractions and homotopy extensions transfer to the realization of each horn.
-/

universe u

open CategoryTheory Limits
open HomotopyHypothesis.Henry HomotopyHypothesis.Realization.Boundary
open HomotopyHypothesis.Realization.Cellular

namespace HomotopyHypothesis.Horn.DeformationRetraction

/-- Realization coordinates without a universe lift. -/
noncomputable def simplexCoordinateHomeomorph (n : ℕ) :
    SemiSSet.realization.{u}.obj
      (SemiSSet.stdSimplex.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ≃ₜ
      ClosedCoordSimplex n :=
  (TopCat.homeoOfIso (realizationSimplexCoordsIso n)).trans Homeomorph.ulift

/-- Horn realization coordinates without a universe lift. -/
noncomputable def hornCoordinateHomeomorph (n : ℕ) (k : Fin (n + 1)) :
    SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor ≃ₜ
      coordinateHorn n k :=
  (hornRealizationHomeomorph n k).trans (Homeomorph.ulift.subtype (fun _ => Iff.rfl))

/-- The coordinate homeomorphisms respect the horn inclusion. -/
theorem hornCoordinateHomeomorph_square (n : ℕ) (k : Fin (n + 1))
    (x : SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor) :
    (hornCoordinateHomeomorph n k x).val =
      simplexCoordinateHomeomorph n (SemiSSet.realization.map (SemiSSet.horn n k).ι x) := rfl

/-- Every positive-dimensional realized horn inclusion has a continuous retraction. -/
theorem realization_horn_retraction (n : ℕ) (k : Fin (n + 2)) :
    ∃ r : SemiSSet.realization.{u}.obj
        (SemiSSet.stdSimplex.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))) ⟶
      SemiSSet.realization.{u}.obj (SemiSSet.horn (n + 1) k).toFunctor,
      SemiSSet.realization.map (SemiSSet.horn (n + 1) k).ι ≫ r = 𝟙 _ := by
  let eA := hornCoordinateHomeomorph.{u} (n + 1) k
  let eB := simplexCoordinateHomeomorph.{u} (n + 1)
  let r := TopCat.ofHom ((⟨eA.symm, eA.symm.continuous⟩ : C(_, _)).comp
    ((coordinateHornRetraction (Nat.zero_lt_succ n) k).comp ⟨eB, eB.continuous⟩))
  refine ⟨r, ?_⟩
  apply TopCat.ext
  intro x
  change eA.symm (coordinateHornRetraction (Nat.zero_lt_succ n) k
    (eB (SemiSSet.realization.map (SemiSSet.horn (n + 1) k).ι x))) = x
  rw [← hornCoordinateHomeomorph_square]
  change eA.symm (coordinateHornRetraction (Nat.zero_lt_succ n) k (eA x).val) = x
  rw [coordinateHornRetraction_fixed, eA.symm_apply_apply]

/-- A retraction supplies lifting against any map to a terminal object. -/
theorem hasLiftingProperty_terminal_of_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (r : B ⟶ A) (hir : i ≫ r = 𝟙 _) (Z : TopCat.{u}) :
    HasLiftingProperty i (terminal.from Z) := by
  constructor
  intro a b sq
  exact CommSq.HasLift.mk'
    { l := r ≫ a
      fac_left := by rw [← Category.assoc, hir, Category.id_comp]
      fac_right := Subsingleton.elim _ _ }

/-- Realized horns lift against maps to a point. -/
theorem realization_horn_hasLiftingProperty_terminal (Z : TopCat.{u})
    (q : Σ n : ℕ, Fin (n + 2)) :
    HasLiftingProperty (SemiSSet.realization.map (SemiSSet.horn (q.1 + 1) q.2).ι)
      (terminal.from Z) := by
  obtain ⟨r, hr⟩ := realization_horn_retraction.{u} q.1 q.2
  exact hasLiftingProperty_terminal_of_retraction _ r hr Z

/-- Realized horns lift against endpoint evaluation on any path space. -/
theorem realization_horn_hasLiftingProperty_endpoints (Z : TopCat.{u})
    (q : Σ n : ℕ, Fin (n + 2)) :
    HasLiftingProperty (SemiSSet.realization.map (SemiSSet.horn (q.1 + 1) q.2).ι)
      (pathEndpoints Z) := by
  let n := q.1
  let k := q.2
  let eA := hornCoordinateHomeomorph.{u} (n + 1) k
  let eB := simplexCoordinateHomeomorph.{u} (n + 1)
  let i := SemiSSet.realization.{u}.map (SemiSSet.horn (n + 1) k).ι
  constructor
  intro a b sq
  let A : C(coordinateHorn (n + 1) k × unitInterval, Z) :=
    ⟨fun p => a (eA.symm p.1) p.2,
      continuous_eval.comp
        ((a.hom.continuous.comp (eA.symm.continuous.comp continuous_fst)).prodMk continuous_snd)⟩
  let b₀ : C(ClosedCoordSimplex (n + 1), Z) :=
    ⟨fun x => (b (eB.symm x)).1, continuous_fst.comp (b.hom.continuous.comp eB.symm.continuous)⟩
  let b₁ : C(ClosedCoordSimplex (n + 1), Z) :=
    ⟨fun x => (b (eB.symm x)).2, continuous_snd.comp (b.hom.continuous.comp eB.symm.continuous)⟩
  have hface (x : coordinateHorn (n + 1) k) : i (eA.symm x) = eB.symm x.val := by
    apply eB.injective
    rw [← hornCoordinateHomeomorph_square]
    change (eA (eA.symm x)).val = eB (eB.symm x.val)
    rw [eA.apply_symm_apply, eB.apply_symm_apply]
  have hs (x : coordinateHorn (n + 1) k) :
      (A (x, 0), A (x, 1)) = b (eB.symm x.val) := by
    have h := ConcreteCategory.congr_hom sq.w (eA.symm x)
    change (a (eA.symm x) 0, a (eA.symm x) 1) = b (i (eA.symm x)) at h
    rw [hface] at h
    exact h
  obtain ⟨H, hhorn, hzero, hone⟩ := coordinateHorn_path_extension
    (Nat.zero_lt_succ n) k A b₀ b₁
    (fun x => congrArg Prod.fst (hs x)) (fun x => congrArg Prod.snd (hs x))
  let l := TopCat.ofHom (H.curry.comp ⟨eB, eB.continuous⟩)
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply TopCat.ext
    intro x
    apply ContinuousMap.ext
    intro t
    change H (eB (i x), t) = a x t
    rw [← hornCoordinateHomeomorph_square]
    rw [hhorn (eA x) t]
    change a (eA.symm (eA x)) t = a x t
    rw [eA.symm_apply_apply]
  · apply TopCat.ext
    intro x
    apply Prod.ext
    · change H (eB x, 0) = (b x).1
      rw [hzero]
      change (b (eB.symm (eB x))).1 = (b x).1
      rw [eB.symm_apply_apply]
    · change H (eB x, 1) = (b x).2
      rw [hone]
      change (b (eB.symm (eB x))).2 = (b x).2
      rw [eB.symm_apply_apply]

end HomotopyHypothesis.Horn.DeformationRetraction
