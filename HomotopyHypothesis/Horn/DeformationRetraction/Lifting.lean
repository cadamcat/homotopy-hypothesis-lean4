import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
/-!
# Lifting properties of realized relative horn complexes

The realization adjunction transfers the generic transfinite lifting theorem to spaces.
-/

universe u

open CategoryTheory Limits
open HomotopyHypothesis.Henry HomotopyHypothesis.Realization.Cellular

namespace HomotopyHypothesis.Horn.DeformationRetraction

/-- The realization adjunction. -/
noncomputable def realizationAdjunction :
    SemiSSet.realization.{u} ⊣ Presheaf.restrictedULiftYoneda.{u} SemiSSet.toTop := by
  change SemiSSet.stdSimplex.{u}.leftKanExtension SemiSSet.toTop.{u} ⊣ _
  exact Presheaf.uliftYonedaAdjunction _
    (SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u})

/-- Lifting for the realized generators extends over arbitrary relative horn complexes. -/
theorem realization_hornCells_hasLiftingProperty {X Y : TopCat.{u}} (p : X ⟶ Y)
    (hp : ∀ q : Σ n : ℕ, Fin (n + 2),
      HasLiftingProperty (SemiSSet.realization.map (SemiSSet.horn (q.1 + 1) q.2).ι) p)
    {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (MorphismProperty.ofHoms (fun q : Σ n : ℕ, Fin (n + 2) =>
        (SemiSSet.horn.{u} (q.1 + 1) q.2).ι))).pushouts j) :
    HasLiftingProperty (SemiSSet.realization.map j) p := by
  let W : MorphismProperty SemiSSet.{u} :=
    MorphismProperty.ofHoms (fun q : Σ n : ℕ, Fin (n + 2) =>
      (SemiSSet.horn.{u} (q.1 + 1) q.2).ι)
  have hr : W.rlp ((Presheaf.restrictedULiftYoneda.{u} SemiSSet.toTop).map p) := by
    intro U V i hi
    cases hi with
    | mk q => exact (realizationAdjunction.hasLiftingProperty_iff _ _).mp (hp q)
  exact (realizationAdjunction.hasLiftingProperty_iff j p).mpr
    ((W.transfiniteCompositions_pushouts_coproducts_le_llp_rlp _ hj) _ hr)

/-- Lifting against maps to a point gives a retraction; endpoint lifting gives its relative
homotopy to the identity. -/
theorem deformationRetract_of_lifting {A B : TopCat.{u}} (f : A ⟶ B)
    (hterminal : ∀ Z : TopCat.{u}, HasLiftingProperty f (terminal.from Z))
    (hendpoints : ∀ Z : TopCat.{u}, HasLiftingProperty f (pathEndpoints Z)) :
    ∃ r : B ⟶ A, f ≫ r = 𝟙 _ ∧
      (r ≫ f).hom.HomotopicRel (ContinuousMap.id _) (Set.range f.hom) := by
  haveI := hterminal A
  have sqr : CommSq (𝟙 A) f (terminal.from A) (terminal.from B) :=
    ⟨Subsingleton.elim _ _⟩
  let r := sqr.lift
  have hfr : f ≫ r = 𝟙 A := sqr.fac_left
  haveI := hendpoints B
  let a : A ⟶ TopCat.of C(unitInterval, B) :=
    TopCat.ofHom ((ContinuousMap.curry ContinuousMap.fst).comp f.hom)
  let b : B ⟶ TopCat.of (B × B) :=
    TopCat.ofHom ((r ≫ f).hom.prodMk (ContinuousMap.id B))
  have sq : CommSq a f (pathEndpoints B) b := by
    constructor
    apply TopCat.ext
    intro x
    apply Prod.ext
    · change f x = f (r (f x))
      exact congrArg f (ConcreteCategory.congr_hom hfr x).symm
    · rfl
  let H := sq.lift
  have hH : H ≫ pathEndpoints B = b := sq.fac_right
  have hA : f ≫ H = a := sq.fac_left
  refine ⟨r, hfr, ⟨{
    toFun := fun p => H p.2 p.1
    continuous_toFun := continuous_eval.comp
      ((H.hom.continuous.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    exact congrArg Prod.fst (ConcreteCategory.congr_hom hH x)
  · intro x
    exact congrArg Prod.snd (ConcreteCategory.congr_hom hH x)
  · intro t x hx
    obtain ⟨y, rfl⟩ := hx
    change H (f y) t = f (r (f y))
    have h := congrArg (fun q : C(unitInterval, B) => q t)
      (ConcreteCategory.congr_hom hA y)
    change H (f y) t = f y at h
    rw [h]
    exact congrArg f (ConcreteCategory.congr_hom hfr y).symm

end HomotopyHypothesis.Horn.DeformationRetraction
