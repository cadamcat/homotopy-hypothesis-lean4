import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.SmallObject
import HomotopyHypothesis.Category.SemiModelConstruction.TrivialFibrations
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [EssentiallySmall.{w} C]

theorem exists_small_generators (S : MorphismProperty C) :
    ∃ (I : MorphismProperty (Completion.{w} C)) (_ : MorphismProperty.IsSmall.{w} I),
      I.rlp = completionElementRLP S := by
  haveI : EssentiallySmall.{w} (Arrow C) :=
    (essentiallySmall_congr (Functor.mapArrowEquivalence (equivSmallModel.{w} C))).mpr
      inferInstance
  let P : ObjectProperty (Arrow C) := fun a => S a.hom
  haveI : ObjectProperty.EssentiallySmall.{w} P :=
    ObjectProperty.EssentiallySmall.of_le (show P ≤ ⊤ from le_top)
  obtain ⟨Q, _, hQ, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
  let family (a : Subtype Q) := completionSmallYoneda.{w}.map a.val.hom
  refine ⟨MorphismProperty.ofHoms family, MorphismProperty.isSmall_ofHoms.{w} family, ?_⟩
  ext X Y f
  constructor
  · intro hf A B i hi
    apply (completionSmallYoneda_lifting_iff i f).mp
    obtain ⟨i', hi', ⟨e⟩⟩ := hcover (Arrow.mk i) hi
    have hLift : HasLiftingProperty (completionSmallYoneda.map i'.hom) f :=
      hf (family ⟨i', hi'⟩)
        (MorphismProperty.ofHoms.mk (f := family) (⟨i', hi'⟩ : Subtype Q))
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (completionSmallYoneda.mapArrow.mapIso e) f).mpr hLift
  · intro hf A B i hi
    obtain ⟨a⟩ := hi
    exact (completionSmallYoneda_lifting_iff a.val.hom f).mpr
      (hf a.val.hom (hQ _ a.property))

theorem completion_trivialFibrations_eq_elementRLP :
    Completion.trivialFibrations.{w} C = completionElementRLP (cofibrations C) := rfl

theorem completion_fibrations_eq_elementRLP [CategoryWithWeakEquivalences C] :
    Completion.fibrations.{w} C =
      completionElementRLP (cofibrations C ⊓ weakEquivalences C) := by
  ext X Y f
  constructor
  · intro hf A B i hi
    exact hf i hi.1 hi.2
  · intro hf A B i hi hwi
    exact hf i ⟨hi, hwi⟩

theorem completion_hasFactorization_cof_trivFib [IsCofibrationCategory C] :
    MorphismProperty.HasFactorization (Completion.cofibrations.{w} C)
      (Completion.trivialFibrations C) := by
  haveI := completion_locallyPresentable.{w} (C := C)
  obtain ⟨I, _, hI⟩ := exists_small_generators.{w} (cofibrations C)
  haveI := smallObjectArgument_of_locallyPresentable I
  change MorphismProperty.HasFactorization
    (completionElementRLP (cofibrations C)).llp (completionElementRLP (cofibrations C))
  rw [← hI]
  infer_instance

theorem completion_hasFactorization_trivLLP_fib [CategoryWithWeakEquivalences C]
    [IsCofibrationCategory C] :
    MorphismProperty.HasFactorization (Completion.fibrations.{w} C).llp
      (Completion.fibrations C) := by
  haveI := completion_locallyPresentable.{w} (C := C)
  obtain ⟨J, _, hJ⟩ := exists_small_generators.{w} (cofibrations C ⊓ weakEquivalences C)
  haveI := smallObjectArgument_of_locallyPresentable J
  rw [completion_fibrations_eq_elementRLP, ← hJ]
  infer_instance

theorem completion_factor_cof_trivFib [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X Y : Completion.{w} C} (f : X ⟶ Y) :
    ∃ (Z : Completion.{w} C) (i : X ⟶ Z) (p : Z ⟶ Y),
      Completion.cofibrations C i ∧ Completion.fibrations C p ∧
        Completion.weakEquivalences C p ∧ i ≫ p = f := by
  haveI := completion_hasFactorization_cof_trivFib.{w} (C := C)
  let φ := MorphismProperty.factorizationData
    (Completion.cofibrations C) (Completion.trivialFibrations C) f
  have hp := (congrArg (fun S => S φ.p) (completion_trivialFibrations_eq (C := C))).mp φ.hp
  exact ⟨φ.Z, φ.i, φ.p, φ.hi, hp.1, hp.2, φ.fac⟩

#print axioms completion_hasFactorization_cof_trivFib
#print axioms completion_hasFactorization_trivLLP_fib
#print axioms completion_factor_cof_trivFib

end HomotopyHypothesis.Category.SemiModelConstruction
