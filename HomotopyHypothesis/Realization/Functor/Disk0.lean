import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
/-!
# The 0-disk is contractible

For a topological realization `R` with left adjoint `L` of `Π_R`, the value of
the restricted realization at the marked object `D₀` is contractible: `L D₀`
is isomorphic to `R(D₀)` by the Yoneda lemma (maps out of a representable),
`R(D₀)` is the standard 0-disk by the realization property on globes, and the
0-disk — a closed ball — is contractible.
-/

open CategoryTheory CategoryTheory.Limits Opposite OAI.Grothendieck
open HomotopyHypothesis.Blueprint

namespace HomotopyHypothesis.Realization.Functor

universe u

variable {C : GlobularTheory.{u}} (R : OAIRealization C)
  (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

/-- The 0-disk model. -/
noncomputable abbrev disk0Model : C.Model := GlobularTheory.Model.disk C 0

/-- Maps out of `L D₀` are maps out of `R(D₀)`. -/
noncomputable def diskHomEquiv (X : TopCat.{u}) :
    (L.obj disk0Model ⟶ X) ≃ (R.functor.obj ⟨Shape.globe 0⟩ ⟶ X) :=
  (adj.homEquiv _ _).trans yonedaEquiv

/-- The representing isomorphism, as an isomorphism of coyoneda presheaves. -/
noncomputable def diskNatIso :
    coyoneda.obj (op (L.obj disk0Model)) ≅
      coyoneda.obj (op (R.functor.obj ⟨Shape.globe 0⟩)) :=
  NatIso.ofComponents (fun X => (diskHomEquiv R L adj X).toIso) (fun {X Y} f => by
    ext k
    show (diskHomEquiv R L adj Y) ((coyoneda.obj _).map f k) =
      (coyoneda.obj _).map f ((diskHomEquiv R L adj X) k)
    show yonedaEquiv ((adj.homEquiv _ _) (k ≫ f)) =
      ((diskHomEquiv R L adj X) k ≫ f)
    rw [adj.homEquiv_naturality_right]
    show (R.Pi.map f).app _ (yonedaEquiv ((adj.homEquiv _ _) k)) =
      ((diskHomEquiv R L adj X) k ≫ f)
    rfl)

/-- `L D₀` is isomorphic to `R(D₀)`. -/
noncomputable def diskIso :
    L.obj disk0Model ≅ R.functor.obj ⟨Shape.globe 0⟩ :=
  (Iso.unop (Functor.preimageIso coyoneda (diskNatIso R L adj))).symm

/-- `R(D₀)` is the standard 0-disk. -/
noncomputable def globe0Iso : R.functor.obj ⟨Shape.globe 0⟩ ≅ TopCat.disk.{u} 0 :=
  R.onGlobes.app (Globe.mk 0)

/-- The standard 0-disk is contractible. -/
theorem disk0Contractible : ContractibleSpace (TopCat.disk.{u} 0) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1) :=
    convex_closedBall _ _
  have hmem : (0 : EuclideanSpace ℝ (Fin 0)) ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hc : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1) :=
    hconv.contractibleSpace ⟨_, hmem⟩
  have hu : ContractibleSpace
      (ULift.{u, 0} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1)) :=
    @Homeomorph.contractibleSpace _ _ _ _ hc Homeomorph.ulift
  exact hu

/-- The value at `D₀` of the restricted realization is contractible. -/
theorem contractible_disk0_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (R : OAIRealization C) (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    ContractibleSpace ((Afin.ι hC ⋙ L).obj
      (HomotopyHypothesis.Blueprint.Packages.disk0 hC)) := by
  show ContractibleSpace (L.obj disk0Model)
  exact @Homeomorph.contractibleSpace _ _ _ _ disk0Contractible
    (TopCat.homeoOfIso ((diskIso R L adj).trans (globe0Iso (R := R))))

example {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    ContractibleSpace ((Afin.ι hC ⋙ L).obj
      (HomotopyHypothesis.Blueprint.Packages.disk0 hC)) :=
  contractible_disk0_proof hC R L adj

#print axioms contractible_disk0_proof

end HomotopyHypothesis.Realization.Functor
