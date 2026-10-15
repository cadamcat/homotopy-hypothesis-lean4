import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Cylinder.Classical
import HomotopyHypothesis.FiniteCategory.Restriction.Unit
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Compact
import HomotopyHypothesis.Category.SemiModelConstruction.Retracts
import HomotopyHypothesis.Category.SemiModelConstruction.TrivialFibrations
/-!
# The unit of the restricted Hom adjunction at cofibrant objects: reductions

For the restriction `R : TopCat ⥤ Completion FinCell` and a left adjoint `L ⊣ R`:

* an invertible unit is a weak equivalence of the completion;
* the units at retracts are retracts of units, so a weak-equivalence unit at a cellular object
  passes to every retract of it;
* every cofibrant object is a retract of an object built from the initial object by attaching the
  representable cells `y (∂𝔻 n) ⟶ y (𝔻 n)`, so it suffices to treat those cellular objects.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry Opposite

local instance : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
local instance : OrderBot Cardinal.aleph0.{u}.ord.ToType :=
  Cardinal.orderBotAleph0OrdToType

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation

/-- Isomorphisms of the completion of finite cell complexes are weak equivalences. -/
theorem completion_weakEquivalence_of_isIso {X Y : Completion.{u} FinCell.{u}} (f : X ⟶ Y)
    [IsIso f] : Completion.weakEquivalences FinCell.{u} f := by
  let _ : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  have hid : Completion.weakEquivalences FinCell.{u} (𝟙 X) :=
    Category.SemiModelConstruction.completion_trivialFibration_isWeakEquivalence _ (fun _ _ _ _ a b hab =>
      ⟨b, by simpa using hab.symm, rfl⟩)
  haveI := Completion.weakEquivalences_respectsIso.{u} FinCell.{u}
  exact (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (Iso.refl X) (asIso f) (by simp))).1 hid

variable (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
  {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}} (adj : L ⊣ topRestriction hι)

include adj in
/-- The unit at a retract is a retract of the unit. -/
theorem unit_weakEquivalence_of_retract {X C : Completion.{u} FinCell.{u}}
    (s : X ⟶ C) (p : C ⟶ X) (hsp : s ≫ p = 𝟙 X)
    (hC : Completion.weakEquivalences FinCell.{u} (adj.unit.app C)) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) := by
  let RL := L ⋙ topRestriction hι
  let h : RetractArrow (adj.unit.app X) (adj.unit.app C) :=
    { i := Arrow.homMk s (RL.map s) (adj.unit.naturality s)
      r := Arrow.homMk p (RL.map p) (adj.unit.naturality p)
      retract := by
        apply Arrow.hom_ext
        · exact hsp
        · change RL.map s ≫ RL.map p = 𝟙 _
          rw [← RL.map_comp, hsp, RL.map_id] }
  haveI := Category.SemiModelConstruction.completion_weakEquivalences_retracts.{u} (C := FinCell.{u})
  exact MorphismProperty.of_retract h hC

include adj in
/-- **Reduction to cellular objects.** If the unit is a weak equivalence at every object built
from an initial object by attaching representable cells `y (∂𝔻 n) ⟶ y (𝔻 n)`, then it is a weak
equivalence at every cofibrant object. -/
theorem unit_weakEquivalence_of_cellular
    (hcell : ∀ {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I),
      Nonempty (HomotopicalAlgebra.RelativeCellComplex.{u}
        (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
          (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}).homFamily) (hI.to C)) →
      Completion.weakEquivalences FinCell.{u} (adj.unit.app C))
    (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) := by
  letI : HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    FiniteCategory.Restriction.finCellCompletion_hasColimits
  obtain ⟨C, s, p, hsp, hC⟩ :=
    FiniteCategory.Restriction.exists_retract_of_boundaryCellular hι initialIsInitial hX
  exact unit_weakEquivalence_of_retract hι adj s p hsp (hcell initialIsInitial hC)

include adj in
/-- If the unit is invertible at every cellular object, it is a weak equivalence at every
cofibrant object. -/
theorem unit_weakEquivalence_of_cellular_isIso
    (hcell : ∀ {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I),
      Nonempty (HomotopicalAlgebra.RelativeCellComplex.{u}
        (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
          (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}).homFamily) (hI.to C)) →
      IsIso (adj.unit.app C))
    (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) :=
  unit_weakEquivalence_of_cellular hι adj (fun hI hC => by
    haveI := hcell hI hC
    exact completion_weakEquivalence_of_isIso _) X hX

/-- **Single-cell presentations.** A cellular object of the completion, built from an initial
object by transfinitely attaching coproducts of representable cells `y (∂𝔻 n) ⟶ y (𝔻 n)`, is also
a transfinite composition in which each step attaches a single representable cell (or is an
isomorphism): order the cells of each coproduct and concatenate. -/
def SingleCellPresentationStatement : Prop :=
  ∀ {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I),
    Nonempty (HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
        (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}).homFamily) (hI.to C)) →
    ∃ (J : Type u) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty ((FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔
        MorphismProperty.isomorphisms _).TransfiniteCompositionOfShape J (hI.to C))

/-- **The unit on single-cell complexes.** The unit is invertible at every object built from an
initial object by a transfinite composition of single representable cell attachments. -/
def SingleCellUnitStatement : Prop :=
  ∀ (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I),
    (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔
        MorphismProperty.isomorphisms _).TransfiniteCompositionOfShape J (hI.to C) →
      IsIso (adj.unit.app C)

/-- The unit is a weak equivalence at cofibrant objects, given single-cell presentations of
cellular objects and invertibility of the unit along single-cell complexes. -/
theorem unit_weakEquivalence_of_singleCell (hP : SingleCellPresentationStatement.{u})
    (hU : SingleCellUnitStatement hι adj) (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) := by
  refine unit_weakEquivalence_of_cellular_isIso hι adj (fun {I C} hI hC => ?_) X hX
  obtain ⟨J, _, _, _, _, ⟨c⟩⟩ := hP hI hC
  exact hU J hI c

include adj in
/-- The left adjoint takes pushouts of representable cells, and isomorphisms, to relative finite
cell complexes. -/
theorem singleCell_le_inverseImage_relativeFiniteCell :
    FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔ MorphismProperty.isomorphisms _ ≤
      Top.relativeFiniteCellComplexes.{u}.inverseImage L := by
  haveI : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  haveI : Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
    FiniteCategory.Cylinder.relativeFiniteCellComplexes_isStableUnderCobaseChange
  intro X Y q hq
  rcases hq with ⟨A, B, p, f, g, hp, sq⟩ | hq
  · change Top.relativeFiniteCellComplexes.{u} (L.map q)
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout (sq.map L)
      (FiniteCategory.Restriction.finCellBoundaryGenerators_map_mem_relativeFiniteCell hι adj p hp)
  · haveI : IsIso q := hq
    exact FiniteCategory.Cylinder.isomorphisms_le_relativeFiniteCellComplexes _
      (inferInstanceAs (IsIso (L.map q)))

/-- The image under the left adjoint of a transfinite composition of maps which it sends to
relative finite cell complexes. -/
noncomputable def chainMap {W : MorphismProperty (Completion.{u} FinCell.{u})}
    (hW : W ≤ Top.relativeFiniteCellComplexes.{u}.inverseImage L)
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : Completion.{u} FinCell.{u}} {f : X ⟶ Y}
    (c : W.TransfiniteCompositionOfShape J f) :
    Top.relativeFiniteCellComplexes.{u}.TransfiniteCompositionOfShape J (L.map f) := by
  haveI : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  haveI : PreservesWellOrderContinuousOfShape J L := ⟨fun _ _ => inferInstance⟩
  exact (c.ofLE hW).map

/-- The image under the left adjoint of a single-cell complex is a transfinite composition of
relative finite cell complexes. -/
noncomputable def singleCellChainMap {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : Completion.{u} FinCell.{u}} {f : X ⟶ Y}
    (c : (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔
      MorphismProperty.isomorphisms _).TransfiniteCompositionOfShape J f) :
    Top.relativeFiniteCellComplexes.{u}.TransfiniteCompositionOfShape J (L.map f) :=
  chainMap hι adj (singleCell_le_inverseImage_relativeFiniteCell hι adj) c

include adj in
/-- The left adjoint sends an initial object to a finite cell complex (the empty space). -/
theorem isFiniteCellComplex_L_initial {I : Completion.{u} FinCell.{u}} (hI : IsInitial I) :
    Top.IsFiniteCellComplex (L.obj I) := by
  haveI : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  have hLI : IsInitial (L.obj I) := IsInitial.isInitialObj L I hI
  have he : initial.to (L.obj I) = (initialIsInitial.uniqueUpToIso hLI).hom :=
    initialIsInitial.hom_ext _ _
  change Top.relativeFiniteCellComplexes (initial.to (L.obj I))
  rw [he]
  exact FiniteCategory.Cylinder.isomorphisms_le_relativeFiniteCellComplexes _
    (inferInstanceAs (IsIso (initialIsInitial.uniqueUpToIso hLI).hom))

/-- **Colimit step.** For a transfinite composition starting from an initial object, of maps
which the left adjoint sends to relative finite cell complexes, if the unit is invertible at every
stage then it is invertible at the colimit: the restriction of the left adjoint image commutes
with the colimit by compact support. -/
theorem unit_isIso_of_stages_of_le {W : MorphismProperty (Completion.{u} FinCell.{u})}
    (hW : W ≤ Top.relativeFiniteCellComplexes.{u}.inverseImage L)
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I)
    (c : W.TransfiniteCompositionOfShape J (hI.to C))
    (h : ∀ j, IsIso (adj.unit.app (c.F.obj j))) : IsIso (adj.unit.app C) := by
  let c' := chainMap hι adj hW c
  let P := c.isColimit
  let Q := topRestriction_isColimit_transfinite hι c' (isFiniteCellComplex_L_initial hι adj hI)
  let w : c.F ≅ c'.F ⋙ topRestriction hι :=
    NatIso.ofComponents (fun j => @asIso _ _ _ _ (adj.unit.app (c.F.obj j)) (h j))
      (fun g => adj.unit.naturality (c.F.map g))
  let e := P.coconePointsIsoOfNatIso Q w
  have he : adj.unit.app C = e.hom := by
    apply P.hom_ext
    intro j
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    have hc' : c'.incl.app j = L.map (c.incl.app j) := by
      simp [c', chainMap, MorphismProperty.TransfiniteCompositionOfShape.map,
        TransfiniteCompositionOfShape.map]
      rfl
    simp only [Functor.mapCocone_ι_app, hc']
    exact (adj.unit.naturality (c.incl.app j)).trans rfl
  rw [he]
  infer_instance

/-- **Colimit step** for single-cell complexes. -/
theorem unit_isIso_of_stages {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I)
    (c : (FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔
      MorphismProperty.isomorphisms _).TransfiniteCompositionOfShape J (hI.to C))
    (h : ∀ j, IsIso (adj.unit.app (c.F.obj j))) : IsIso (adj.unit.app C) :=
  unit_isIso_of_stages_of_le hι adj (singleCell_le_inverseImage_relativeFiniteCell hι adj) hI c h

end HomotopyHypothesis.FiniteCategory.UnitPresentation
