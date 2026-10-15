import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Category.SemiModelConstruction.Basics
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.Generators
import HomotopyHypothesis.Category.SemiModelConstruction.Limits
import HomotopyHypothesis.Category.SemiModelConstruction.Retracts
import HomotopyHypothesis.Category.SemiModelConstruction.TrivialFibrations
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C] [EssentiallySmall.{w} C]

theorem completion_trivLLP_le_cof :
    (Completion.fibrations.{w} C).llp ≤ Completion.cofibrations C := by
  intro X Y i hi A B p hp
  apply hi p
  intro A' B' j hj hW
  exact hp j hj

theorem completion_trivCof_lifts_of
    (hTwo : (Completion.weakEquivalences.{w} C).HasTwoOutOfThreeProperty)
    (hTriv : ∀ ⦃X Y : Completion.{w} C⦄ (i : X ⟶ Y),
      IsCofibrantFor (Completion.cofibrations C) X →
        (Completion.fibrations C).llp i → Completion.weakEquivalences C i)
    {X Y : Completion.{w} C} (i : X ⟶ Y)
    (hX : IsCofibrantFor (Completion.cofibrations C) X)
    (hi : Completion.cofibrations C i) (hWi : Completion.weakEquivalences C i) :
    (Completion.fibrations C).llp i := by
  haveI := hTwo
  haveI := completion_hasFactorization_trivLLP_fib.{w} (C := C)
  let φ := MorphismProperty.factorizationData
    (Completion.fibrations C).llp (Completion.fibrations C) i
  have hjW := hTriv φ.i hX φ.hi
  have hpW : Completion.weakEquivalences C φ.p :=
    (Completion.weakEquivalences C).of_precomp φ.i φ.p hjW (by rw [φ.fac]; exact hWi)
  have hpT := completion_fibration_weakEquivalence_isTrivialFibration φ.p φ.hp hpW
  haveI := hi φ.p hpT
  exact (Completion.fibrations C).llp.of_retract
    (RetractArrow.ofLeftLiftingProperty φ.fac) φ.hi

theorem completion_isSemiModelCategory_of
    (hTwo : (Completion.weakEquivalences.{w} C).HasTwoOutOfThreeProperty)
    (hTriv : ∀ ⦃X Y : Completion.{w} C⦄ (i : X ⟶ Y),
      IsCofibrantFor (Completion.cofibrations C) X →
        (Completion.fibrations C).llp i → Completion.weakEquivalences C i) :
    IsSemiModelCategory (Completion.{w} C) (Completion.cofibrations C) (Completion.fibrations C)
      (Completion.weakEquivalences C) ∧
    ∀ X : Completion.{w} C, IsFibrantFor (Completion.fibrations C) X := by
  refine ⟨{
    hasFiniteLimits := completion_hasFiniteLimits
    hasFiniteColimits := completion_hasFiniteColimits
    twoOutOfThree := hTwo
    cof_retracts := completion_cofibrations_retracts
    fib_retracts := completion_fibrations_retracts
    W_retracts := completion_weakEquivalences_retracts
    lift_cof_trivFib := completion_lift_cof_trivFib
    lift_trivCof_fib := fun {_ _} i hX hi hW => completion_trivCof_lifts_of hTwo hTriv i hX hi hW
    factor_cof_trivFib := fun {_ _} f => completion_factor_cof_trivFib f
    factor_trivCof_fib := ?_ }, completion_isFibrant⟩
  intro X Y f hX
  haveI := completion_hasFactorization_trivLLP_fib.{w} (C := C)
  let φ := MorphismProperty.factorizationData
    (Completion.fibrations C).llp (Completion.fibrations C) f
  exact ⟨φ.Z, φ.i, φ.p, completion_trivLLP_le_cof _ φ.hi,
    hTriv φ.i hX φ.hi, φ.hp, φ.fac⟩

#print axioms completion_isSemiModelCategory_of

end HomotopyHypothesis.Category.SemiModelConstruction
