import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Category.SemiModelStructure.Flat
import HomotopyHypothesis.Category.SemiModelStructure.Transfinite
import HomotopyHypothesis.Category.SemiModelStructure.YonedaFacts
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.Generators
import HomotopyHypothesis.Category.SemiModelConstruction.Retracts
import HomotopyHypothesis.Category.SemiModelConstruction.SmallObject
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Cellular factorizations in the completion

The small object argument with generating maps `y c` (`c` a cofibration, resp. a trivial
cofibration, of `C`) factors every map as a relative cell complex followed by a trivial fibration,
resp. a fibration. Consequences: cofibrant objects are flat, and a map with cofibrant domain having
the left lifting property against all fibrations is a weak equivalence (Henry, *Algebraic models of
homotopy types*, Prop 2.4.13).
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C] [EssentiallySmall.{w} C]

/-- Small generators for the element-wise lifting classes, all of the form `y c`. -/
theorem exists_small_generators_cells (S : MorphismProperty C) :
    ∃ (I : MorphismProperty (Completion.{w} C)) (_ : MorphismProperty.IsSmall.{w} I),
      I.rlp = completionElementRLP S ∧
      ∀ ⦃P Q : Completion.{w} C⦄ (g : P ⟶ Q), I g → ∃ (Cc Dd : C) (c : Cc ⟶ Dd), S c ∧
        Nonempty (Arrow.mk g ≅ Arrow.mk (completionSmallYoneda.{w}.map c)) := by
  have : EssentiallySmall.{w} (Arrow C) :=
    (essentiallySmall_congr (Functor.mapArrowEquivalence (equivSmallModel.{w} C))).mpr
      inferInstance
  let P : ObjectProperty (Arrow C) := fun a => S a.hom
  have : ObjectProperty.EssentiallySmall.{w} P :=
    ObjectProperty.EssentiallySmall.of_le (show P ≤ ⊤ from le_top)
  obtain ⟨Q, _, hQ, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
  let family (a : Subtype Q) := completionSmallYoneda.{w}.map a.val.hom
  refine ⟨MorphismProperty.ofHoms family, MorphismProperty.isSmall_ofHoms.{w} family, ?_, ?_⟩
  · ext X Y f
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
  · rintro _ _ g ⟨a⟩
    exact ⟨_, _, a.val.hom, hQ _ a.property, ⟨Iso.refl _⟩⟩

/-- Cellular factorization: `f = i ≫ p` with `p` in the element-wise right lifting class of `S`,
`i` in its left lifting class, and, when the domain is flat, a flat middle object and `i` a weak
equivalence if `S` consists of trivial cofibrations. -/
theorem exists_cellular_factorization (S : MorphismProperty C) (P : Prop)
    (hS : ∀ ⦃A B : C⦄ (c : A ⟶ B), S c → cofibrations C c ∧ (P → weakEquivalences C c))
    {X Y : Completion.{w} C} (f : X ⟶ Y) :
    ∃ (Z : Completion.{w} C) (i : X ⟶ Z) (p : Z ⟶ Y), i ≫ p = f ∧
      completionElementRLP S p ∧ (completionElementRLP S).llp i ∧
      (IsFlat X → IsFlat Z ∧ (P → Completion.weakEquivalences C i)) := by
  obtain ⟨I, _, hI, hcells⟩ := exists_small_generators_cells.{w} S
  have := completion_locallyPresentable.{w} (C := C)
  obtain ⟨κ, hκ, hbot, hcard⟩ :=
    (smallObjectArgument_of_locallyPresentable I).exists_cardinal
  refine ⟨_, SmallObject.ιObj I κ f, SmallObject.πObj I κ f,
    SmallObject.ιObj_πObj I κ f, ?_, ?_, fun hX => ?_⟩
  · rw [← hI]; exact SmallObject.rlp_πObj I κ f
  · rw [← hI]; exact SmallObject.llp_rlp_ιObj I κ f
  · refine relativeCellComplex_flat P (fun _ a => ?_)
      (SmallObject.relativeCellComplexιObj I κ f) hX
    obtain ⟨Cc, Dd, c, hc, ⟨e⟩⟩ := hcells a.1.hom a.2
    exact ⟨Cc, Dd, c, (hS c hc).1, (hS c hc).2, ⟨e⟩⟩

/-- An initial object of the completion: the representable presheaf of an initial object. -/
theorem exists_initial_completion :
    ∃ (I : Completion.{w} C) (_ : IsInitial I), IsFlat I := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hyI⟩ := completionSmallYoneda_isInitial.{w} hI
  exact ⟨_, hyI, isFlat_yoneda I⟩

/-- Cofibrant objects of the completion are flat. -/
theorem isFlat_of_isCofibrant {X : Completion.{w} C}
    (hX : IsCofibrantFor (Completion.cofibrations C) X) : IsFlat X := by
  obtain ⟨I, hI, hIflat⟩ := exists_initial_completion.{w} (C := C)
  obtain ⟨Z, i, p, hip, hp, -, hZ⟩ :=
    exists_cellular_factorization (cofibrations C) False (fun _ _ c hc => ⟨hc, False.elim⟩)
      (hI.to X)
  have hpT : Completion.trivialFibrations C p := hp
  have : HasLiftingProperty (hI.to X) p := hX hI p hpT
  have sq : CommSq i (hI.to X) p (𝟙 X) := ⟨by rw [hip, Category.comp_id]⟩
  exact isFlat_of_retract sq.lift p sq.fac_right (hZ hIflat).1

/-- Henry, Prop 2.4.13: a map with cofibrant domain and the left lifting property against all
fibrations is a weak equivalence. -/
theorem completion_weakEquivalence_of_llp_fibrations {X Y : Completion.{w} C} (i : X ⟶ Y)
    (hX : IsCofibrantFor (Completion.cofibrations C) X)
    (hi : (Completion.fibrations C).llp i) : Completion.weakEquivalences C i := by
  obtain ⟨Z, j, p, hjp, hp, -, hZ⟩ :=
    exists_cellular_factorization (cofibrations C ⊓ weakEquivalences C) True
      (fun _ _ c hc => ⟨hc.1, fun _ => hc.2⟩) i
  have hpF : Completion.fibrations C p := by
    rw [completion_fibrations_eq_elementRLP]; exact hp
  have hjW := (hZ (isFlat_of_isCofibrant hX)).2 trivial
  have := hi p hpF
  have := completion_weakEquivalences_retracts.{w} (C := C)
  exact (Completion.weakEquivalences C).of_retract (RetractArrow.ofLeftLiftingProperty hjp) hjW

end HomotopyHypothesis.Category.SemiModelStructure
