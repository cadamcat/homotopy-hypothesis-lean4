import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
universe v u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.CellComplex.Basic

theorem compactSpace_colimit_of_finite_shape
    {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ TopCat.{u})
    (hF : ∀ j, CompactSpace (F.obj j)) :
    CompactSpace (CategoryTheory.Limits.colimit F : TopCat.{u}) := by
  classical
  apply isCompact_univ_iff.mp
  rw [isCompact_iff_finite_subcover]
  intro ι U hUopen hU
  have hlocal (j : J) : ∃ t : Finset ι,
      (Set.univ : Set (F.obj j)) ⊆ ⋃ i ∈ t, (colimit.ι F j).hom ⁻¹' U i := by
    letI : CompactSpace (F.obj j) := hF j
    apply isCompact_univ.elim_finite_subcover
      (fun i => (colimit.ι F j).hom ⁻¹' U i)
      (fun i => (colimit.ι F j).hom.continuous.isOpen_preimage _ (hUopen i))
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU (Set.mem_univ _))
    exact Set.mem_iUnion.mpr ⟨i, by simpa [Set.mem_preimage] using hi⟩
  choose t ht using hlocal
  let s : Finset ι := Finset.univ.biUnion t
  refine ⟨s, ?_⟩
  intro x hx
  obtain ⟨j, y, hy⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep F x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht j (Set.mem_univ y))
  obtain ⟨hit, hyi⟩ := Set.mem_iUnion.mp hi
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ?_⟩
  refine ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hit⟩, ?_⟩
  rw [← hy]
  exact hyi

private theorem compactSpace_of_pushout
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ X} {q : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout f i q g) [CompactSpace A] [CompactSpace B] [CompactSpace X] :
    CompactSpace Y := by
  let F : WalkingSpan ⥤ TopCat.{u} := span f i
  have hcol : CompactSpace (CategoryTheory.Limits.colimit F : TopCat.{u}) :=
    compactSpace_colimit_of_finite_shape (J := WalkingSpan) F (by
      intro j
      cases j with
      | none => simpa [F] using (inferInstance : CompactSpace A)
      | some j => cases j with
        | left => simpa [F] using (inferInstance : CompactSpace X)
        | right => simpa [F] using (inferInstance : CompactSpace B))
  let e : Y ≅ CategoryTheory.Limits.colimit F :=
    IsColimit.coconePointUniqueUpToIso sq.isColimit (colimit.isColimit F)
  exact Homeomorph.compactSpace (TopCat.homeoOfIso e.symm)

theorem compactSpace_of_isFiniteCellComplex_proof {X : TopCat.{u}}
    (hX : HomotopyHypothesis.Henry.Top.IsFiniteCellComplex X) : CompactSpace X := by
  let G : MorphismProperty TopCat.{u} :=
    (HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u})
  have hGenerator : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y), G f →
      CompactSpace X → CompactSpace Y := by
    intro X Y f hf hX
    rcases hf with hp | hi
    · rcases hp with ⟨A, B, p, a, b, hp, sq⟩
      cases hp with
      | mk n =>
          letI : CompactSpace X := hX
          exact compactSpace_of_pushout sq
    · haveI : IsIso f := hi
      exact Homeomorph.compactSpace (TopCat.homeoOfIso (asIso f))
  have hFinite : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y),
      HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes f →
      CompactSpace X → CompactSpace Y := by
    intro X Y f hf
    change G.multiplicativeClosure f at hf
    induction hf with
    | of f hf => exact hGenerator f hf
    | id X => exact fun hX => hX
    | comp_of f g hf hg ih => exact fun hX => hGenerator g hg (ih hX)
  haveI : CompactSpace (⊥_ TopCat.{u}) := by
    exact Homeomorph.compactSpace
      (TopCat.homeoOfIso (TopCat.initialIsoPEmpty.{u}).symm)
  exact hFinite (initial.to X) hX inferInstance

theorem finCell_essentiallySmall_proof :
    EssentiallySmall.{u} HomotopyHypothesis.Henry.FinCell.{u} := by
  let P : ObjectProperty TopCat.{u} := ObjectProperty.ofObj
    (fun i : ℕ ⊕ (ℕ ⊕ Unit) =>
      match i with
      | Sum.inl n => diskBoundary.{u} n
      | Sum.inr (Sum.inl n) => disk.{u} n
      | Sum.inr (Sum.inr _) => ⊥_ TopCat.{u})
  let Q : ObjectProperty TopCat.{u} := P.colimitsClosure (fun _ : Unit => WalkingSpan)
  have hBoundary (n : ℕ) : Q (diskBoundary.{u} n) := by
    exact P.le_colimitsClosure (fun _ : Unit => WalkingSpan) _ ⟨Sum.inl n⟩
  have hDisk (n : ℕ) : Q (disk.{u} n) := by
    exact P.le_colimitsClosure (fun _ : Unit => WalkingSpan) _ ⟨Sum.inr (Sum.inl n)⟩
  have hInitial : Q (⊥_ TopCat.{u}) := by
    exact P.le_colimitsClosure (fun _ : Unit => WalkingSpan) _ ⟨Sum.inr (Sum.inr ())⟩
  have hGenerator : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y),
      (HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}) f → Q X → Q Y := by
    intro X Y f hf hX
    rcases hf with hp | hi
    · rcases hp with ⟨A, B, p, a, b, hp, sq⟩
      cases hp with
      | mk n =>
          exact Q.prop_of_isColimit sq.isColimit (by
            rintro (⟨⟩ | ⟨⟨⟩⟩)
            · exact hBoundary n
            · exact hX
            · exact hDisk n)
    · haveI : IsIso f := hi
      exact Q.prop_of_iso (asIso f) hX
  have hFinite : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y),
      HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes f → Q X → Q Y := by
    intro X Y f hf
    change (HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure f at hf
    induction hf with
    | of f hf => exact hGenerator f hf
    | id X => exact fun hX => hX
    | comp_of f g hf hg ih => exact fun hX => hGenerator g hg (ih hX)
  have hCells : HomotopyHypothesis.Henry.Top.IsFiniteCellComplex ≤ Q := by
    intro X hX
    change HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes (initial.to X) at hX
    exact hFinite (initial.to X) hX hInitial
  haveI : Small.{u} (ℕ ⊕ (ℕ ⊕ Unit)) := inferInstance
  haveI : ObjectProperty.EssentiallySmall.{u} P := inferInstance
  haveI : LocallySmall.{u} TopCat.{u} := inferInstance
  haveI : Small.{u} Unit := inferInstance
  haveI : Small.{u} WalkingSpan := inferInstance
  haveI : LocallySmall.{u} WalkingSpan := inferInstance
  haveI : ObjectProperty.EssentiallySmall.{u} Q := inferInstance
  have hSmall : ObjectProperty.EssentiallySmall.{u}
      HomotopyHypothesis.Henry.Top.IsFiniteCellComplex :=
    ObjectProperty.EssentiallySmall.of_le hCells
  letI : ObjectProperty.EssentiallySmall.{u}
      HomotopyHypothesis.Henry.Top.IsFiniteCellComplex := hSmall
  change EssentiallySmall.{u} HomotopyHypothesis.Henry.FinCell.{u}
  exact inferInstance

#print axioms compactSpace_of_isFiniteCellComplex_proof
#print axioms finCell_essentiallySmall_proof

end HomotopyHypothesis.CellComplex.Basic
