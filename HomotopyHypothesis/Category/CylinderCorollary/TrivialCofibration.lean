import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.EndComparison
import HomotopyHypothesis.Category.CylinderCorollary.Fibrant
import HomotopyHypothesis.Category.CylinderCorollary.LiftingTest
import HomotopyHypothesis.Category.CylinderCorollary.TwoOutOfSix
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem full_source_smallObject (C : GlobularTheory.{u}) :
    (MorphismProperty.ofHoms (fun n : ℕ => J C n)).HasSmallObjectArgument.{u} :=
  smallObjectArgument_of_finiteDomains (fun n : ℕ => J C n)

theorem cutoff_cofibrant_of_boundary_cofibrant (hC : C.IsCoherator) (q : ℕ)
    {X : C.Model}
    (hX : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp (initial.to X)) :
    Cofibrant hC q ((cutoffFunctor hC q).obj X) := by
  intro P Q p hp f
  have hp' : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p.hom := by
    apply (boundary_rlp_iff p.hom).2
    intro n
    exact (boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n)
  let A := cutoffAdjunction hC q
  let a := A.homEquiv X Q f
  let := hX p.hom hp'
  have sq : CommSq (initial.to P.obj) (initial.to X) p.hom a :=
    ⟨initialIsInitial.hom_ext _ _⟩
  refine ⟨(A.homEquiv X P).symm sq.lift, ?_⟩
  apply (A.homEquiv X Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact sq.fac_right

theorem cutoff_source_cofibration (hC : C.IsCoherator) (q : ℕ) {X Y : C.Model}
    (i : X ⟶ Y)
    (hi : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp.llp i) :
    (sourceClass hC q 0).rlp.llp ((cutoffFunctor hC q).map i) := by
  intro P Q p hp
  apply ((cutoffAdjunction hC q).hasLiftingProperty_iff i p).2
  apply hi p.hom
  apply (source_rlp_iff p.hom).2
  intro n
  exact (sourceClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n)

theorem source_cofibration_retraction (hC : C.IsCoherator) {X Y : C.Model}
    (i : X ⟶ Y)
    (hi : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp.llp i) :
    ∃ z : Y ⟶ X, i ≫ z = 𝟙 X := by
  let := hi (terminal.from X) (HomotopyHypothesis.Blueprint.Packages.fibrant_proof hC X)
  have sq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

theorem weakEquivalence_of_source_cofibration (hC : C.IsCoherator) {X Y : C.Model}
    (i : X ⟶ Y)
    (hi : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp.llp i)
    (hX : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp (initial.to X)) :
    WeakEquivalence hC i := by
  obtain ⟨z, hz⟩ := source_cofibration_retraction hC i hi
  apply weakEquivalence_of_exactBoundaryTest hC i
  intro d bd y hy
  let q := d + 1
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let F := cutoffFunctor hC q
  have hFc : (sourceClass hC q 0).rlp.llp (F.map i) := cutoff_source_cofibration hC q i hi
  have hFX : Cofibrant hC q (F.obj X) := cutoff_cofibrant_of_boundary_cofibrant hC q hX
  have hFz : F.map i ≫ F.map z = 𝟙 (F.obj X) :=
    (F.map_comp i z).symm.trans ((congrArg F.map hz).trans (F.map_id X))
  have htest : GlobularSet.ExactBoundaryTest (underlyingMap (F.map i).hom) :=
    exactBoundaryTest_of_cutoff_path hC q 0 (F.map i) hFc hFX (F.map z) hFz
      (cylinderPathData hC q 0 (Nat.zero_le q) (expansionContraction_all hC q 1) (F.obj Y))
  let ηX := underlyingMap (cutoffUnit hC q X)
  let ηY := underlyingMap (cutoffUnit hC q Y)
  have hs : (underlyingMap i).comp ηY = ηX.comp (underlyingMap (F.map i).hom) :=
    congrArg underlyingMap ((cutoffAdjunction hC q).unit.naturality i)
  exact GlobularSet.exactBoundaryTest_at_of_low_square (underlyingMap i)
    (underlyingMap (F.map i).hom) ηX ηY hs htest d
    (fun k hk => cutoffUnit_low_bijective hC q X k (by dsimp [q]; omega))
    (cutoffUnit_low_bijective hC q Y d (by dsimp [q]; omega)).injective
    (cutoffUnit_low_bijective hC q Y (d + 1) le_rfl).surjective bd y hy

#print axioms full_source_smallObject
#print axioms cutoff_cofibrant_of_boundary_cofibrant
#print axioms cutoff_source_cofibration
#print axioms source_cofibration_retraction
#print axioms weakEquivalence_of_source_cofibration

end HomotopyHypothesis.Category.CylinderCorollary

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Category.CylinderCorollary

theorem trivialCofibration_lift_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {X Y P Q : C.Model}
    (i : X ⟶ Y) (hi : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp i) (hwi : W hC i)
    (hX : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp (initial.to X))
    (p : P ⟶ Q) (hp : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp p) :
    HasLiftingProperty i p := by
  let := full_source_smallObject C
  let S := MorphismProperty.ofHoms (fun n : ℕ => J C n)
  let F := MorphismProperty.factorizationData S.rlp.llp S.rlp i
  have hj : WeakEquivalence hC F.i := weakEquivalence_of_source_cofibration hC F.i F.hi hX
  have hwp : WeakEquivalence hC F.p := weakEquivalence_of_left_and_comp hC F.i F.p hj
    (by rw [F.fac]; exact hwi)
  have hpI : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp F.p := by
    rw [lifting_test_proof hC]
    exact ⟨hwp, F.hp⟩
  let := hi F.p hpI
  have sq : CommSq F.i i F.p (𝟙 Y) := ⟨by rw [Category.comp_id, F.fac]⟩
  let := F.hi p hp
  constructor
  intro a b ab
  have sq' : CommSq a F.i p (F.p ≫ b) := by
    constructor
    rw [← Category.assoc, F.fac, ab.w]
  refine CommSq.HasLift.mk' ⟨sq.lift ≫ sq'.lift, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, sq'.fac_left]
  · rw [Category.assoc, sq'.fac_right, ← Category.assoc, sq.fac_right, Category.id_comp]

#print axioms trivialCofibration_lift_proof

end HomotopyHypothesis.Blueprint.Packages
