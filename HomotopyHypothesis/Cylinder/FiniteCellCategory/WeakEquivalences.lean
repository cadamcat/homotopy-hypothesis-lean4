import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.Fibrant
import HomotopyHypothesis.Blueprint.Interfaces.LiftingTest
import HomotopyHypothesis.Blueprint.Interfaces.TrivialCofibrationLift
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceTwoOutOfSix
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

abbrev boundaryMaps (C : GlobularTheory.{u}) : MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : ℕ => I C n)

abbrev sourceMaps (C : GlobularTheory.{u}) : MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : ℕ => J C n)

abbrev ModelCofibrant {C : GlobularTheory.{u}} (X : C.Model) : Prop :=
  (boundaryMaps C).rlp.llp (initial.to X)

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

include hC

 theorem cutoff_boundary_rlp (q : ℕ) {P Q : CutoffModels C q} (p : P ⟶ Q)
    (hp : (boundaryClass hC q 0).rlp p) : (boundaryMaps C).rlp p.hom := by
  rintro _ _ _ ⟨n⟩
  exact (boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n)

 theorem cutoff_source_rlp (q : ℕ) {P Q : CutoffModels C q} (p : P ⟶ Q)
    (hp : (sourceClass hC q 0).rlp p) : (sourceMaps C).rlp p.hom := by
  rintro _ _ _ ⟨n⟩
  exact (sourceClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n)

 theorem modelCofibrant_cutoff (q : ℕ) {X : C.Model} (hX : ModelCofibrant X) :
    Cofibrant hC q ((cutoffFunctor hC q).obj X) := by
  intro P Q p hp f
  let := hX p.hom (cutoff_boundary_rlp hC q p hp)
  let adj := cutoffAdjunction hC q
  let a : X ⟶ Q.obj := adj.homEquiv X Q f
  have sq : CommSq (initial.to P.obj) (initial.to X) p.hom a :=
    ⟨initialIsInitial.hom_ext _ _⟩
  refine ⟨(adj.homEquiv X P).symm sq.lift, ?_⟩
  apply (adj.homEquiv X Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact sq.fac_right

 theorem source_llp_cutoff (q : ℕ) {X Y : C.Model} (i : X ⟶ Y)
    (hi : (sourceMaps C).rlp.llp i) :
    (sourceClass hC q 0).rlp.llp ((cutoffFunctor hC q).map i) := by
  intro P Q p hp
  apply ((cutoffAdjunction hC q).hasLiftingProperty_iff i p).2
  exact hi p.hom (cutoff_source_rlp hC q p hp)

 theorem source_llp_retraction {X Y : C.Model} (i : X ⟶ Y)
    (hi : (sourceMaps C).rlp.llp i) : ∃ r : Y ⟶ X, i ≫ r = 𝟙 X := by
  let := hi (terminal.from X) (Packages.fibrant hC X)
  have sq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

 theorem source_llp_exactBoundaryTest {X Y : C.Model} (i : X ⟶ Y)
    (hi : (sourceMaps C).rlp.llp i) (hX : ModelCofibrant X) :
    GlobularSet.ExactBoundaryTest (underlyingMap i) := by
  obtain ⟨r, hr⟩ := source_llp_retraction hC i hi
  intro d bd y hy
  let q := d+1
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let F := cutoffFunctor hC q
  let ηX := underlyingMap (cutoffUnit hC q X)
  let ηY := underlyingMap (cutoffUnit hC q Y)
  have hs : (underlyingMap i).comp ηY =
      ηX.comp (underlyingMap (F.map i).hom) :=
    congrArg underlyingMap ((cutoffAdjunction hC q).unit.naturality i)
  have test : GlobularSet.ExactBoundaryTest (underlyingMap (F.map i).hom) := by
    apply exactBoundaryTest_of_cutoff_path hC q 0 (F.map i)
      (source_llp_cutoff hC q i hi) (modelCofibrant_cutoff hC q hX) (F.map r)
    · exact (F.map_comp i r).symm.trans ((congrArg F.map hr).trans (F.map_id X))
    · exact cylinderPathData hC q 0 (Nat.zero_le q)
        (expansionContraction_all hC q 1) (F.obj Y)
  exact GlobularSet.exactBoundaryTest_at_of_low_square
    (underlyingMap i) (underlyingMap (F.map i).hom) ηX ηY hs test d
    (fun k hk => cutoffUnit_low_bijective hC q X k (by dsimp [q]; omega))
    (cutoffUnit_low_bijective hC q Y d (by dsimp [q]; omega)).1
    (cutoffUnit_low_bijective hC q Y (d+1) le_rfl).2 bd y hy

 theorem source_llp_weakEquivalence {X Y : C.Model} (i : X ⟶ Y)
    (hi : (sourceMaps C).rlp.llp i) (hX : ModelCofibrant X) : W hC i :=
  weakEquivalence_of_exactBoundaryTest hC i (source_llp_exactBoundaryTest hC i hi hX)

 theorem model_trivialCofibration_cobaseChange {A B X Q : C.Model}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (sq : IsPushout i f k j) (hi : (boundaryMaps C).rlp.llp i) (hwi : W hC i)
    (hA : ModelCofibrant A) (hX : ModelCofibrant X) : W hC j := by
  have hi' : (sourceMaps C).rlp.llp i :=
    fun _ _ p hp => Packages.trivialCofibration_lift hC i hi hwi hA p hp
  exact source_llp_weakEquivalence hC j
    ((sourceMaps C).rlp.llp.of_isPushout sq.flip hi') hX


instance weakEquivalence_twoOutOfThree : (W hC).HasTwoOutOfThreeProperty where
  comp_mem := (Packages.weakEquivalence_closure hC).2.comp_mem
  of_postcomp f g hg hfg :=
    (Packages.weakEquivalence_twoOutOfSix hC f g (𝟙 _) hfg (by simpa using hg)).1
  of_precomp f g hf hfg :=
    (Packages.weakEquivalence_twoOutOfSix hC (𝟙 _) f g (by simpa using hf) hfg).2.2.1

 theorem weakEquivalence_exactBoundaryTest {X Y : C.Model} (f : X ⟶ Y)
    (hf : W hC f) (hX : ModelCofibrant X) :
    GlobularSet.ExactBoundaryTest (underlyingMap f) := by
  let := smallObjectArgument_of_finiteDomains (fun n : ℕ => I C n)
  let F := MorphismProperty.factorizationData
    (boundaryMaps C).rlp.llp (boundaryMaps C).rlp f
  have hpW : W hC F.p := by
    have e := congrArg (fun P : MorphismProperty C.Model => P F.p)
      (Packages.lifting_test hC)
    exact (e.mp F.hp).1
  have hiW : W hC F.i := (W hC).of_postcomp F.i F.p hpW (by simpa using hf)
  have hiJ : (sourceMaps C).rlp.llp F.i :=
    fun _ _ p hp => Packages.trivialCofibration_lift hC F.i F.hi hiW hX p hp
  have ht := source_llp_exactBoundaryTest hC F.i hiJ hX
  intro n b y hy
  have hyp : Y.underlying.boundary n y =
      (underlyingMap F.p).boundaryMap n ((underlyingMap F.i).boundaryMap n b) := by
    have e := congrArg (fun t : X ⟶ Y => (underlyingMap t).boundaryMap n b) F.fac
    simpa only [underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp] using hy.trans e.symm
  obtain ⟨z, hzb, hzp⟩ := (hasLiftingProperty_I_iff n F.p).1
    (F.hp _ (MorphismProperty.ofHoms.mk n)) _ y hyp
  obtain ⟨x, hx, hj⟩ := ht n b z hzb
  refine ⟨x, hx, ?_⟩
  have h := (underlyingMap F.p).map_joined hj
  change Y.underlying.Joined n ((underlyingMap (F.i ≫ F.p)).app n x)
    ((underlyingMap F.p).app n z) at h
  rw [F.fac, hzp] at h
  exact h

end HomotopyHypothesis.Cylinder.FiniteCellCategory
