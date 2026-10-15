import HomotopyHypothesis.Blueprint.Henry.Topology
/-!
# Semi-model categories and Quillen equivalences

Semi-model categories in the sense of Spitzweck (H:356): the axioms of a model category,
except that the factorization into a trivial cofibration followed by a fibration, and the lifting of
trivial cofibrations against fibrations, are only required for maps with cofibrant domain. The
classes are given explicitly (a category may carry several structures). Only finite limits and
colimits are required, which is what the homotopy theory of the structure uses.

We also define Quillen equivalences (H:363) and the classes of the Quillen model structure on
spaces: cofibrations are the maps with the left lifting property against the maps having the right
lifting property against the boundary inclusions `∂𝔻 n ⟶ 𝔻 n`, and fibrations are the Serre
fibrations.
-/

universe v u v' u' w

open CategoryTheory Limits

namespace HomotopyHypothesis.Henry

section SemiModel

variable {C : Type u} [Category.{v} C]

/-- `X` is cofibrant for the class `cof`: the map from an initial object is in `cof`. -/
def IsCofibrantFor (cof : MorphismProperty C) (X : C) : Prop :=
  ∀ ⦃I : C⦄ (hI : IsInitial I), cof (hI.to X)

/-- `X` is fibrant for the class `fib`: the map to a terminal object is in `fib`. -/
def IsFibrantFor (fib : MorphismProperty C) (X : C) : Prop :=
  ∀ ⦃T : C⦄ (hT : IsTerminal T), fib (hT.from X)

variable (C) in
/-- A semi-model structure with cofibrations `cof`, fibrations `fib` and weak equivalences `W`
(H:356, following Spitzweck, Def 2.3). -/
structure IsSemiModelCategory (cof fib W : MorphismProperty C) : Prop where
  hasFiniteLimits : HasFiniteLimits C
  hasFiniteColimits : HasFiniteColimits C
  twoOutOfThree : W.HasTwoOutOfThreeProperty
  cof_retracts : cof.IsStableUnderRetracts
  fib_retracts : fib.IsStableUnderRetracts
  W_retracts : W.IsStableUnderRetracts
  lift_cof_trivFib : fib ⊓ W ≤ cof.rlp
  lift_trivCof_fib : ∀ ⦃X Y : C⦄ (i : X ⟶ Y), IsCofibrantFor cof X → cof i → W i →
    fib.llp i
  factor_cof_trivFib : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y), cof i ∧ fib p ∧ W p ∧ i ≫ p = f
  factor_trivCof_fib : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsCofibrantFor cof X →
    ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y), cof i ∧ W i ∧ fib p ∧ i ≫ p = f

variable {D : Type u'} [Category.{v'} D]

/-- A Quillen equivalence between semi-model structures (H:363): the right adjoint preserves
fibrations and trivial fibrations, and for cofibrant `X` and fibrant `Y` a map `L X ⟶ Y` is a weak
equivalence exactly when its adjoint `X ⟶ R Y` is. -/
structure IsQuillenEquivalence {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (cofC fibC WC : MorphismProperty C) (cofD fibD WD : MorphismProperty D) : Prop where
  map_fibration : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), fibD f → fibC (R.map f)
  map_trivialFibration : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), fibD f → WD f → WC (R.map f)
  weakEquivalence_iff : ∀ ⦃X : C⦄ ⦃Y : D⦄ (f : L.obj X ⟶ Y), IsCofibrantFor cofC X →
    IsFibrantFor fibD Y → (WD f ↔ WC (adj.homEquiv X Y f))

end SemiModel

namespace Top

/-- The inclusion `𝔻 n ⟶ 𝔻 n × [0, 1]`, `x ↦ (x, 0)`. -/
noncomputable def diskBottomInclusion (n : ℕ) :
    TopCat.disk.{w} n ⟶ TopCat.of (TopCat.disk.{w} n × TopCat.I.{w}) :=
  TopCat.ofHom ⟨fun x => (x, ⟨0, by simp⟩), by fun_prop⟩

/-- Cofibrations of the Quillen model structure on spaces: retracts of relative cell complexes,
i.e. the left lifting class of the right lifting class of `∂𝔻 n ⟶ 𝔻 n`. -/
def cofibrations : MorphismProperty TopCat.{w} := cellBoundaries.rlp.llp

/-- Serre fibrations: the right lifting class of `𝔻 n ⟶ 𝔻 n × [0, 1]`. -/
def fibrations : MorphismProperty TopCat.{w} :=
  (MorphismProperty.ofHoms (fun n : ℕ => diskBottomInclusion.{w} n)).rlp

end Top

end HomotopyHypothesis.Henry
