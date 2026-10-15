import Mathlib.Topology.CompactOpen
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.TrivialCofibrationLift
import HomotopyHypothesis.Realization.Cellular.Brown
import HomotopyHypothesis.Realization.Cellular.HomotopyProperties
import HomotopyHypothesis.Realization.Cellular.Reduction
noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Topology
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

universe u

/-- The endpoint evaluation map on the continuous path space. -/
def pathEndpoints (Y : TopCat.{u}) : TopCat.of C(unitInterval, Y) ⟶ TopCat.of (Y × Y) :=
  TopCat.ofHom ⟨fun p => (p 0, p 1),
    (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

/-- Finite boundary-cell maps have the left lifting property against boundary-injective maps. -/
theorem finiteCellMaps_le_lifting (C : GlobularTheory.{u}) :
    finiteCellMaps C ≤ (MorphismProperty.ofHoms (fun n => I C n)).rlp.llp := by
  change ((MorphismProperty.ofHoms (fun n => I C n)).pushouts ⊔
    MorphismProperty.isomorphisms C.Model).multiplicativeClosure ≤ _
  apply (MorphismProperty.multiplicativeClosure_le_iff
    ((MorphismProperty.ofHoms (fun n => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model)
    (MorphismProperty.ofHoms (fun n => I C n)).rlp.llp).mpr
  exact sup_le (MorphismProperty.pushouts_le_llp_rlp _)
    (MorphismProperty.isomorphisms_le_of_containsIdentities _)

section

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

include adj

/-- Endpoint lifting for the realized hemispheres makes realized trivial cofibrations homotopy
equivalences. -/
theorem map_trivialCofibration_of_pathLifting
    (hJ : ∀ (Y : TopCat.{u}) (n : ℕ),
      HasLiftingProperty (L.map (J C n)) (pathEndpoints Y))
    {X Y : Afin C hC} (i : X ⟶ Y) (hi : cofibrations (Afin C hC) i)
    (hwi : weakEquivalences (Afin C hC) i) :
    Top.homotopyEquivalences ((Afin.ι hC ⋙ L).map i) := by
  letI := Blueprint.Packages.afin_isCylinderCategory hC
  obtain ⟨r, hir⟩ := IsCylinderCategory.exists_retraction i hi hwi
  let f := (Afin.ι hC ⋙ L).map i
  let g := (Afin.ι hC ⋙ L).map r
  have hfg : f ≫ g = 𝟙 ((Afin.ι hC ⋙ L).obj X) := by
    rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  let Z := (Afin.ι hC ⋙ L).obj Y
  have hp : (MorphismProperty.ofHoms (fun n => J C n)).rlp (R.Pi.map (pathEndpoints Z)) := by
    intro A B j hj
    cases hj with
    | mk n => exact (adj.hasLiftingProperty_iff _ _).mp (hJ Z n)
  have hx : (MorphismProperty.ofHoms (fun n => I C n)).rlp.llp (initial.to X.obj) :=
    finiteCellMaps_le_lifting C _ X.property
  have hii : (MorphismProperty.ofHoms (fun n => I C n)).rlp.llp ((Afin.ι hC).map i) :=
    finiteCellMaps_le_lifting C _ hi
  have hmodel : HasLiftingProperty ((Afin.ι hC).map i) (R.Pi.map (pathEndpoints Z)) :=
    Blueprint.Packages.trivialCofibration_lift hC _ hii hwi hx _ hp
  haveI : HasLiftingProperty f (pathEndpoints Z) :=
    (adj.hasLiftingProperty_iff _ _).mpr hmodel
  let a : ((Afin.ι hC ⋙ L).obj X) ⟶ TopCat.of C(unitInterval, Z) :=
    TopCat.ofHom ((ContinuousMap.curry ContinuousMap.fst).comp f.hom)
  let b : Z ⟶ TopCat.of (Z × Z) :=
    TopCat.ofHom ((g ≫ f).hom.prodMk (ContinuousMap.id Z))
  have sq : CommSq a f (pathEndpoints Z) b := by
    constructor
    apply TopCat.ext
    intro x
    apply Prod.ext
    · change f x = f (g (f x))
      exact congrArg f (ConcreteCategory.congr_hom hfg x).symm
    · rfl
  let H := sq.lift
  have hH : H ≫ pathEndpoints Z = b := sq.fac_right
  refine ⟨g, ?_, ?_⟩
  · rw [hfg]
  · refine ⟨{ toFun := fun p => H p.2 p.1
              continuous_toFun := continuous_eval.comp (H.hom.continuous.comp continuous_snd |>.prodMk continuous_fst)
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro x
      exact congrArg Prod.fst (ConcreteCategory.congr_hom hH x)
    · intro x
      exact congrArg Prod.snd (ConcreteCategory.congr_hom hH x)

/-- Cellular realization reduces to the boundary generators and endpoint lifting for hemispheres.
-/
theorem cellularRealization_of_cells_and_pathLifting
    (hI : ∀ n, Top.relativeFiniteCellComplexes (L.map (I C n)))
    (hJ : ∀ (Y : TopCat.{u}) (n : ℕ),
      HasLiftingProperty (L.map (J C n)) (pathEndpoints Y)) :
    IsCellularRealization (Afin.ι hC ⋙ L) := by
  letI := Blueprint.Packages.afin_isCylinderCategory hC
  apply cellularRealization_of_cells_and_weakEquivalences hC R L adj hI
  intro X Y f hf
  exact cylinder_brown_map (Afin.ι hC ⋙ L) Top.homotopyEquivalences
    (fun {_ _} => map_trivialCofibration_of_pathLifting hC R L adj hJ) f hf

end

end HomotopyHypothesis.Realization.Cellular
