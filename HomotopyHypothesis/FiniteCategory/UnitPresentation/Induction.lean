import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Cylinder.Classical
import HomotopyHypothesis.FiniteCategory.Restriction.Unit
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Unit
/-!
# The unit along single-cell complexes: the induction

Let `X_•` be a transfinite composition, starting from an initial object of the completion, in which
each step attaches one representable cell `y (∂𝔻 n) ⟶ y (𝔻 n)` (or is an isomorphism). The unit
is invertible at every finite cellular extension of every stage `X_j`. This is proved by induction
on `j`: at the bottom, finite cellular extensions of an initial object are representable; a finite
cellular extension of a successor stage is one of the previous stage; and a limit stage is handled
by compact support (`UnitLimitStatement`). Together with `unit_isIso_of_stages` this gives the
invertibility of the unit at the colimit.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry Opposite

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation

variable (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
  {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}} (adj : L ⊣ topRestriction hι)

/-- The single-cell attachment class: pushouts of representable cells, and isomorphisms. -/
abbrev singleCells : MorphismProperty (Completion.{u} FinCell.{u}) :=
  FiniteCategory.Restriction.finCellBoundaryGenerators.{u}.pushouts ⊔ MorphismProperty.isomorphisms _

attribute [local instance] FiniteCategory.Restriction.finCellCompletion_hasColimits

include adj in
/-- Invertibility of the unit is invariant under isomorphism. -/
theorem unit_isIso_of_iso {X Y : Completion.{u} FinCell.{u}} (e : X ≅ Y)
    (h : IsIso (adj.unit.app Y)) : IsIso (adj.unit.app X) := by
  have hX : adj.unit.app X = e.hom ≫ adj.unit.app Y ≫ (L ⋙ topRestriction hι).map e.inv := by
    have hn := adj.unit.naturality e.hom
    simp only [Functor.id_map] at hn
    rw [reassoc_of% hn]
    change adj.unit.app X = adj.unit.app X ≫ (L ⋙ topRestriction hι).map e.hom ≫
      (L ⋙ topRestriction hι).map e.inv
    rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hX]
  infer_instance

/-- A finite cell complex with empty underlying space is initial in `FinCell`. -/
def finCell_isInitial_of_isEmpty (A : FinCell.{u}) (hA : IsEmpty A.obj) : IsInitial A :=
  IsInitial.ofUniqueHom
    (fun B => ObjectProperty.homMk (TopCat.ofHom
      ⟨fun x => isEmptyElim x, ⟨fun s _ => by rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]; exact isOpen_empty⟩⟩))
    (fun B f => by
      apply ObjectProperty.hom_ext
      ext x
      exact isEmptyElim x)

/-- The representable presheaf of an initial finite cell complex is initial in the completion. -/
def completionYoneda_isInitial {A : FinCell.{u}} (hA : IsInitial A) :
    IsInitial ((Completion.yoneda FinCell.{u}).obj A) :=
  IsInitial.ofUniqueHom
    (fun P => (FiniteCategory.Restriction.completionYonedaEquiv A P).symm
      (Classical.choice (P.property.1 hA)).default)
    (fun P f => by
      apply (FiniteCategory.Restriction.completionYonedaEquiv A P).injective
      letI := Classical.choice (P.property.1 hA)
      exact Subsingleton.elim _ _)

/-- The empty space, as a finite cell complex. -/
def finCellEmpty : FinCell.{u} :=
  ⟨TopCat.of PEmpty.{u + 1}, by
    change Top.relativeFiniteCellComplexes (initial.to (TopCat.of PEmpty.{u + 1}))
    have he : initial.to (TopCat.of PEmpty.{u + 1}) =
        (initialIsInitial.uniqueUpToIso TopCat.isInitialPEmpty).hom :=
      initialIsInitial.hom_ext _ _
    rw [he]
    exact FiniteCategory.Cylinder.isomorphisms_le_relativeFiniteCellComplexes _
      (inferInstanceAs (IsIso (initialIsInitial.uniqueUpToIso TopCat.isInitialPEmpty).hom))⟩

theorem finCellEmpty_isEmpty : IsEmpty finCellEmpty.{u}.obj :=
  inferInstanceAs (IsEmpty PEmpty)

/-- Finite cellular maps of the completion: finite composites of single-cell attachments and
isomorphisms. -/
abbrev finiteCellular : MorphismProperty (Completion.{u} FinCell.{u}) :=
  singleCells.multiplicativeClosure

/-- The Yoneda image of a map is recovered from its element. -/
theorem completionYoneda_map_equiv {A K : FinCell.{u}}
    (b : (Completion.yoneda FinCell.{u}).obj A ⟶ (Completion.yoneda FinCell.{u}).obj K) :
    (Completion.yoneda FinCell.{u}).map
      (show A ⟶ K from FiniteCategory.Restriction.completionYonedaEquiv A _ b) = b := by
  apply (FiniteCategory.Restriction.completionYonedaEquiv A _).injective
  have h := FiniteCategory.Restriction.completionYonedaEquiv_precomp
    (show A ⟶ K from FiniteCategory.Restriction.completionYonedaEquiv A _ b) (𝟙 _)
  rw [Category.comp_id] at h
  rw [h]
  rfl

/-- Objects isomorphic to representable objects. -/
def IsRepresentableObj (X : Completion.{u} FinCell.{u}) : Prop :=
  ∃ K : FinCell.{u}, Nonempty (X ≅ (Completion.yoneda FinCell.{u}).obj K)

/-- Attaching a single representable cell to a representable object gives a representable
object: the pushout of finite cell complexes along the cell is a finite cell complex, and the
Yoneda embedding preserves it. -/
theorem isRepresentableObj_of_singleCell {X X' : Completion.{u} FinCell.{u}} (g : X ⟶ X')
    (hg : singleCells g) (hX : IsRepresentableObj X) : IsRepresentableObj X' := by
  obtain ⟨K, ⟨e⟩⟩ := hX
  rcases hg with ⟨A₀, B₀, p, b, d, hp, sq⟩ | hg
  · obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff
      (FiniteCategory.Restriction.finCellBoundaryGenMap.{u}) p).1 hp
    let y := Completion.yoneda FinCell.{u}
    let eArr : Arrow.mk p ≅ Arrow.mk (FiniteCategory.Restriction.finCellBoundaryGenMap.{u} n) := eqToIso hn
    let eA : A₀ ≅ y.obj (FiniteCategory.Restriction.finCellBoundaryObj n) := Arrow.leftFunc.mapIso eArr
    let eB : B₀ ≅ y.obj (FiniteCategory.Restriction.finCellDiskObj n) := Arrow.rightFunc.mapIso eArr
    let b' : y.obj (FiniteCategory.Restriction.finCellBoundaryObj n) ⟶ y.obj K := eA.inv ≫ b ≫ e.hom
    let β : FiniteCategory.Restriction.finCellBoundaryObj n ⟶ K := FiniteCategory.Restriction.completionYonedaEquiv _ _ b'
    have hβ : y.map β = b' := completionYoneda_map_equiv b'
    -- the pushout of finite cell complexes
    let P := pushout β.hom (TopCat.diskBoundaryInclusion n)
    have hPush : IsPushout β.hom (TopCat.diskBoundaryInclusion n)
        (pushout.inl β.hom (TopCat.diskBoundaryInclusion n))
        (pushout.inr β.hom (TopCat.diskBoundaryInclusion n)) := IsPushout.of_hasPushout _ _
    have hinl : Top.relativeFiniteCellComplexes
        (pushout.inl β.hom (TopCat.diskBoundaryInclusion n)) := by
      apply MorphismProperty.le_multiplicativeClosure
      exact Or.inl ⟨_, _, _, _, _, ⟨n⟩, hPush⟩
    have hP : Top.IsFiniteCellComplex P := by
      change Top.relativeFiniteCellComplexes (initial.to P)
      letI : Top.relativeFiniteCellComplexes.IsMultiplicative := by
        unfold Top.relativeFiniteCellComplexes
        infer_instance
      simpa using Top.relativeFiniteCellComplexes.comp_mem _ _ K.property hinl
    let K' : FinCell.{u} := ⟨P, hP⟩
    let inl' : K ⟶ K' := ObjectProperty.homMk (pushout.inl _ _)
    let inr' : FiniteCategory.Restriction.finCellDiskObj n ⟶ K' := ObjectProperty.homMk (pushout.inr _ _)
    let sqF : Square FinCell.{u} :=
      { f₁₂ := FiniteCategory.Restriction.finCellBoundaryMap n
        f₁₃ := β
        f₂₄ := inr'
        f₃₄ := inl'
        fac := by
          apply (ObjectProperty.ι Top.IsFiniteCellComplex).map_injective
          exact hPush.w.symm }
    have hTop : (sqF.map (ObjectProperty.ι Top.IsFiniteCellComplex)).IsPushout := by
      change IsPushout (TopCat.diskBoundaryInclusion n) β.hom
        (pushout.inr β.hom (TopCat.diskBoundaryInclusion n))
        (pushout.inl β.hom (TopCat.diskBoundaryInclusion n))
      exact hPush.flip
    have hSquare : IsPushout (FiniteCategory.Restriction.finCellBoundaryMap n) β inr' inl' :=
      Square.IsPushout.of_map (ObjectProperty.ι Top.IsFiniteCellComplex) hTop
    have hY := FiniteCategory.Restriction.completionYoneda_map_cofPushout _ _ _ _ hSquare
      (FiniteCategory.Restriction.finCellBoundaryMap_cof n)
    rw [hβ] at hY
    -- compare with the given pushout square
    have sq' : IsPushout b' (y.map (FiniteCategory.Restriction.finCellBoundaryMap n))
        (e.inv ≫ g) (eB.inv ≫ d) := by
      refine IsPushout.of_iso sq eA e eB (Iso.refl _) ?_ ?_ ?_ ?_
      · simp [b']
      · exact eArr.hom.w.symm
      · simp
      · simp
    exact ⟨K', ⟨(sq'.isoIsPushout _ _ hY.flip)⟩⟩
  · haveI : IsIso g := hg
    exact ⟨K, ⟨(asIso g).symm ≪≫ e⟩⟩

/-- Finite cellular maps out of a representable object end at representable objects. -/
theorem isRepresentableObj_of_finiteCellular {X X' : Completion.{u} FinCell.{u}} (g : X ⟶ X')
    (hg : finiteCellular g) (hX : IsRepresentableObj X) : IsRepresentableObj X' := by
  induction hg with
  | of g hg => exact isRepresentableObj_of_singleCell g hg hX
  | id A => exact hX
  | comp_of f g _ hg ih => exact isRepresentableObj_of_singleCell g hg (ih hX)

/-- The induction hypothesis at an object `X`: the unit is invertible at every finite cellular
extension of `X` (in particular at `X` itself). -/
def UnitInvertibleOnExtensions (X : Completion.{u} FinCell.{u}) : Prop :=
  ∀ ⦃X' : Completion.{u} FinCell.{u}⦄ (g : X ⟶ X'), finiteCellular g → IsIso (adj.unit.app X')

include adj in
/-- **Base case**: finite cellular extensions of an initial object are representable, where the
unit is invertible. -/
theorem unitInvertibleOnExtensions_of_isInitial {X : Completion.{u} FinCell.{u}}
    (hX : IsInitial X) : UnitInvertibleOnExtensions hι adj X := by
  intro X' g hg
  have h0 : IsInitial finCellEmpty.{u} :=
    finCell_isInitial_of_isEmpty _ finCellEmpty_isEmpty
  have hXr : IsRepresentableObj X :=
    ⟨finCellEmpty, ⟨hX.uniqueUpToIso (completionYoneda_isInitial h0)⟩⟩
  obtain ⟨K, ⟨e⟩⟩ := isRepresentableObj_of_finiteCellular g hg hXr
  exact unit_isIso_of_iso hι adj e (FiniteCategory.Restriction.finCellRestriction_unit_isIso_yoneda hι adj K)

/-- **Successor step**: a finite cellular extension of a successor stage is a finite cellular
extension of the previous stage. -/
theorem unitInvertibleOnExtensions_of_singleCell {X Y : Completion.{u} FinCell.{u}} (f : X ⟶ Y)
    (hf : singleCells f) (hX : UnitInvertibleOnExtensions hι adj X) :
    UnitInvertibleOnExtensions hι adj Y := by
  intro Y' g hg
  apply hX (f ≫ g)
  exact (finiteCellular).comp_mem f g (MorphismProperty.le_multiplicativeClosure _ _ hf) hg

/-- **Limit step** (remaining input): at a limit stage of a single-cell complex starting from an
initial object, the unit is invertible on finite cellular extensions if it is so at all earlier
stages. A finite cellular extension of the limit stage descends to an earlier stage `j₀` (the
attaching maps come from finitely presentable representable objects); it is then the filtered
colimit of its pushouts to the later stages, and the left adjoint image is the colimit of a
transfinite composition of relative finite cell complexes starting from the empty space (first the
stages up to `j₀`, then the extension, then the pushed-out later stages), along which the
restriction functor commutes with colimits by compact support. -/
def UnitLimitStatement : Prop :=
  ∀ (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {I C : Completion.{u} FinCell.{u}} (hI : IsInitial I)
    (c : singleCells.TransfiniteCompositionOfShape J (hI.to C)) (j : J),
    Order.IsSuccLimit j → (∀ k < j, UnitInvertibleOnExtensions hι adj (c.F.obj k)) →
      UnitInvertibleOnExtensions hι adj (c.F.obj j)

/-- The induction: given the limit step, the unit is invertible along single-cell complexes. -/
theorem singleCellUnit_of_limit (hL : UnitLimitStatement hι adj) :
    SingleCellUnitStatement hι adj := by
  intro J _ _ _ _ I C hI c
  have hstage : ∀ j : J, UnitInvertibleOnExtensions hι adj (c.F.obj j) := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      have hj' : j = ⊥ := hj.eq_bot
      subst hj'
      exact unitInvertibleOnExtensions_of_isInitial hι adj (IsInitial.ofIso hI c.isoBot.symm)
    | succ j hj ih =>
      exact unitInvertibleOnExtensions_of_singleCell hι adj _ (c.map_mem j hj) ih
    | isSuccLimit j hj ih =>
      exact hL J hI c j hj ih
  exact unit_isIso_of_stages hι adj hI c
    (fun j => hstage j (𝟙 _) (MorphismProperty.multiplicativeClosure.id _))

include adj in
/-- **The unit at cofibrant objects**, from the two remaining inputs: single-cell presentations of
cellular objects and the limit step. -/
theorem unit_weakEquivalence_of_presentation_of_limit
    (hP : SingleCellPresentationStatement.{u}) (hL : UnitLimitStatement hι adj)
    (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) :=
  unit_weakEquivalence_of_singleCell hι adj hP (singleCellUnit_of_limit hι adj hL) X hX

end HomotopyHypothesis.FiniteCategory.UnitPresentation
