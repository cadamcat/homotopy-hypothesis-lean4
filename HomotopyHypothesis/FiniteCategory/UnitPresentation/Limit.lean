import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Cylinder.Classical
import HomotopyHypothesis.FiniteCategory.Restriction.Unit
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Induction
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Surgery
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Unit
import HomotopyHypothesis.Category.SemiModelStructure.PushoutColimit
/-!
# The unit along single-cell complexes: the limit step

A finite cellular extension `X'` of the colimit of a transfinite composition `X_•` comes from a
stage: `X' = colim X_• ⊔_{X_{k₀}} X₀'` for a finite cellular `X_{k₀} ⟶ X₀'` (the attaching maps
of the cells come from finitely presentable representable objects). Inserting `X_{k₀} ⟶ X₀'` into
the composition gives a transfinite composition starting from the initial object whose colimit is
`X'` and whose stages are finite cellular extensions of those of `X_•`; compact support then makes
the unit invertible at `X'`.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry Opposite

local instance : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation

attribute [local instance] FiniteCategory.Restriction.finCellCompletion_hasColimits

instance singleCells_isStableUnderCobaseChange :
    singleCells.{u}.IsStableUnderCobaseChange := by
  constructor
  intro A A' B B' f g f' g' sq hf
  rcases hf with hf | hf
  · exact Or.inl (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
  · exact Or.inr (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)

instance finiteCellular_isStableUnderCobaseChange :
    finiteCellular.{u}.IsStableUnderCobaseChange :=
  FiniteCategory.Cylinder.multiplicativeClosure_stableUnderCobaseChange _ (fun _ _ _ hf => Or.inr hf)

instance finiteCellular_respectsIso : finiteCellular.{u}.RespectsIso :=
  FiniteCategory.Cylinder.respectsIso_of_isomorphisms_le _
    (fun _ _ f hf => MorphismProperty.le_multiplicativeClosure _ _ (Or.inr hf))

theorem singleCells_le_finiteCellular : singleCells.{u} ≤ finiteCellular.{u} :=
  MorphismProperty.le_multiplicativeClosure _

variable (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
  {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}} (adj : L ⊣ topRestriction hι)

include adj in
theorem finiteCellular_le_inverseImage_relativeFiniteCell :
    finiteCellular.{u} ≤ Top.relativeFiniteCellComplexes.{u}.inverseImage L := by
  letI : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    unfold Top.relativeFiniteCellComplexes
    infer_instance
  exact (MorphismProperty.multiplicativeClosure_le_iff _ _).2
    (singleCell_le_inverseImage_relativeFiniteCell hι adj)

/-- The domains of the representable cells are finitely presentable. -/
theorem singleCell_source_isFinitelyPresentable {A B : Completion.{u} FinCell.{u}} (p : A ⟶ B)
    (hp : FiniteCategory.Restriction.finCellBoundaryGenerators.{u} p) : IsFinitelyPresentable.{u} A := by
  obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff (FiniteCategory.Restriction.finCellBoundaryGenMap.{u}) p).1 hp
  have e : A ≅ (Completion.yoneda FinCell.{u}).obj (FiniteCategory.Restriction.finCellBoundaryObj n) :=
    Arrow.leftFunc.mapIso (eqToIso hn)
  have := FiniteCategory.Restriction.completionYoneda_isCardinalPresentable (FiniteCategory.Restriction.finCellBoundaryObj n)
  exact isCardinalPresentable_of_iso e.symm _

section Descent

variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {W : MorphismProperty (Completion.{u} FinCell.{u})} {X Y : Completion.{u} FinCell.{u}}
  {f : X ⟶ Y} (c : W.TransfiniteCompositionOfShape J f)

/-- Descent data of a map out of the colimit along a stage. -/
def Descends {X' : Completion.{u} FinCell.{u}} (g : Y ⟶ X') : Prop :=
  ∃ (k₀ : J) (X₀' : Completion.{u} FinCell.{u}) (g₀ : c.F.obj k₀ ⟶ X₀') (v : X₀' ⟶ X'),
    finiteCellular g₀ ∧ IsPushout (c.incl.app k₀) g₀ g v

theorem descends_id : Descends c (𝟙 Y) :=
  ⟨⊥, _, 𝟙 _, c.incl.app ⊥, MorphismProperty.multiplicativeClosure.id _,
    IsPushout.id_vert _⟩

theorem descends_comp_singleCell {X₁ X₂ : Completion.{u} FinCell.{u}} (g : Y ⟶ X₁)
    (h : X₁ ⟶ X₂) (hg : Descends c g) (hh : singleCells h) : Descends c (g ≫ h) := by
  obtain ⟨k₀, X₀', g₀, v, hg₀, sq⟩ := hg
  let F₀ := c.F.obj k₀
  rcases hh with ⟨A, B, p, b, d, hp, sqh⟩ | hh
  · -- the attaching map factors through a stage of the pushout
    have h' : IsPushout (𝟙 (c.F.obj k₀) ≫ (Cocone.mk Y c.incl).ι.app k₀) g₀ g v := by
      simpa using sq
    have hcU := Category.SemiModelStructure.underPushoutIsColimit (c := Cocone.mk Y c.incl) c.isColimit
      g₀ (𝟙 _) g v h'
    have := singleCell_source_isFinitelyPresentable p hp
    obtain ⟨s, b₁, hb₁⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcU b
    let k₁ := s.right
    let φ : F₀ ⟶ c.F.obj k₁ := 𝟙 _ ≫ c.F.map s.hom
    let g₁ : c.F.obj k₁ ⟶ pushout φ g₀ := pushout.inl _ _
    let u₁ : pushout φ g₀ ⟶ X₁ :=
      pushout.desc (c.incl.app k₁ ≫ g) v
        (Category.SemiModelStructure.underPushout_leg_w (c := Cocone.mk Y c.incl) g₀ (𝟙 _) g v h' s)
    have hu₁ : b₁ ≫ u₁ = b := hb₁
    -- the square at the stage `k₁`
    have e1 : φ ≫ c.incl.app k₁ = c.incl.app k₀ := by
      have := c.incl.naturality s.hom
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      simp [φ, this]
    have e2 : pushout.inr φ g₀ ≫ u₁ = v := pushout.inr_desc _ _ _
    have sOuter : IsPushout (φ ≫ c.incl.app k₁) g₀ g (pushout.inr φ g₀ ≫ u₁) := by
      rw [e1, e2]; exact sq
    have sq₁ : IsPushout (c.incl.app k₁) g₁ g u₁ :=
      IsPushout.of_left sOuter (pushout.inl_desc _ _ _).symm (IsPushout.of_hasPushout φ g₀)
    -- attaching the cell at the stage `k₁`
    have t₂ : IsPushout b₁ p (pushout.inl b₁ p) (pushout.inr b₁ p) := IsPushout.of_hasPushout _ _
    have sqh' : IsPushout (b₁ ≫ u₁) p h d := by rw [hu₁]; exact sqh
    have sq₂ := IsPushout.of_left' sqh' t₂
    have sq₃ := sq₁.paste_vert sq₂
    refine ⟨k₁, _, g₁ ≫ pushout.inl b₁ p, _, ?_, sq₃⟩
    apply finiteCellular.comp_mem
    · exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
        (IsPushout.of_hasPushout φ g₀) hg₀
    · exact singleCells_le_finiteCellular _
        (Or.inl ⟨_, _, p, b₁, pushout.inr b₁ p, hp, t₂⟩)
  · haveI : IsIso h := hh
    refine ⟨k₀, X₀', g₀, v ≫ h, hg₀, ?_⟩
    exact sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso h) (by simp) (by simp)
      (by simp) (by simp)

/-- Finite cellular maps out of the colimit descend to a stage. -/
theorem descends_of_finiteCellular {X' : Completion.{u} FinCell.{u}} (g : Y ⟶ X')
    (hg : finiteCellular g) : Descends c g := by
  suffices H : ∀ {Z X' : Completion.{u} FinCell.{u}} (g : Z ⟶ X'), finiteCellular g →
      ∀ (e : Y = Z), Descends c (eqToHom e ≫ g) by
    simpa using H g hg rfl
  intro Z X' g hg
  induction hg with
  | of g hg =>
    intro e; subst e
    simpa using descends_comp_singleCell c (𝟙 _) g (descends_id c) hg
  | id Z =>
    intro e; subst e
    simpa using descends_id c
  | comp_of f g _ hg ih =>
    intro e; subst e
    simpa using descends_comp_singleCell c f g (by simpa using ih rfl) hg

/-- Descent data can be moved to a later stage. -/
theorem descends_raise {X' : Completion.{u} FinCell.{u}} {g : Y ⟶ X'} {k₀ : J}
    {X₀' : Completion.{u} FinCell.{u}} {g₀ : c.F.obj k₀ ⟶ X₀'} {v : X₀' ⟶ X'}
    (hg₀ : finiteCellular g₀) (sq : IsPushout (c.incl.app k₀) g₀ g v) {k₁ : J} (hk : k₀ ≤ k₁) :
    ∃ (X₁' : Completion.{u} FinCell.{u}) (g₁ : c.F.obj k₁ ⟶ X₁') (v₁ : X₁' ⟶ X'),
      finiteCellular g₁ ∧ IsPushout (c.incl.app k₁) g₁ g v₁ := by
  let φ := c.F.map (homOfLE hk)
  have e1 : φ ≫ c.incl.app k₁ = c.incl.app k₀ := by
    have := c.incl.naturality (homOfLE hk)
    simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using this
  let u₁ : pushout φ g₀ ⟶ X' := pushout.desc (c.incl.app k₁ ≫ g) v (by
    rw [← Category.assoc, e1]; exact sq.w)
  have e2 : pushout.inr φ g₀ ≫ u₁ = v := pushout.inr_desc _ _ _
  have sOuter : IsPushout (φ ≫ c.incl.app k₁) g₀ g (pushout.inr φ g₀ ≫ u₁) := by
    rw [e1, e2]; exact sq
  refine ⟨_, pushout.inl φ g₀, u₁, ?_,
    IsPushout.of_left sOuter (pushout.inl_desc _ _ _).symm (IsPushout.of_hasPushout φ g₀)⟩
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (IsPushout.of_hasPushout φ g₀) hg₀

end Descent

/-- **End step.** For a transfinite composition without maximal element of finite cellular maps
starting from an initial object, if the unit is invertible on finite cellular extensions of all
stages, then it is invertible on finite cellular extensions of the colimit. -/
theorem unitInvertibleOnExtensions_colimit {J : Type u} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J] {I C : Completion.{u} FinCell.{u}}
    (hI : IsInitial I) (c : finiteCellular.TransfiniteCompositionOfShape J (hI.to C))
    (h : ∀ k, UnitInvertibleOnExtensions hι adj (c.F.obj k)) :
    UnitInvertibleOnExtensions hι adj C := by
  intro X' g hg
  obtain ⟨k₀, X₀', g₀, v, hg₀, sq⟩ := descends_of_finiteCellular c g hg
  let k₁ := Order.succ k₀
  have hk₁ : ¬ Order.IsSuccLimit k₁ := fun hl => not_isMax k₀ (Order.IsSuccLimit.isMax hl)
  have hb : ⊥ < k₁ := lt_of_le_of_lt bot_le (Order.lt_succ k₀)
  obtain ⟨X₁', g₁, v₁, hg₁, sq₁⟩ := descends_raise c hg₀ sq (Order.le_succ k₀)
  let c' := Surgery.transfiniteComposition c k₁ hk₁ hb g₁ hg₁
  let P := pushout (c.incl.app k₁) g₁
  let c'' : finiteCellular.TransfiniteCompositionOfShape J (hI.to P) :=
    c'.ofArrowIso (Arrow.isoMk (Iso.refl _) (Iso.refl _) (hI.hom_ext _ _))
  have hstage : ∀ k, IsIso (adj.unit.app (c''.F.obj k)) := by
    intro k
    obtain ⟨e, he⟩ := Surgery.exists_stage_map c k₁ hk₁ hb g₁ hg₁ k
    exact h k e he
  have hP : IsIso (adj.unit.app P) :=
    unit_isIso_of_stages_of_le hι adj (finiteCellular_le_inverseImage_relativeFiniteCell hι adj)
      hI c'' hstage
  exact unit_isIso_of_iso hι adj (sq₁.isoPushout) hP

section Iio

variable {J : Type u} [LinearOrder J] {j : J} (hj : Order.IsSuccLimit j)

/-- The bottom element of `Set.Iio j` for a limit element `j`. -/
abbrev iioOrderBot [OrderBot J] : OrderBot (Set.Iio j) where
  bot := ⟨⊥, hj.bot_lt⟩
  bot_le k := bot_le (a := k.1)

/-- The successor order of `Set.Iio j` for a limit element `j`. -/
abbrev iioSuccOrder [SuccOrder J] : SuccOrder (Set.Iio j) where
  succ k := ⟨Order.succ k.1, Order.IsSuccLimit.succ_lt hj k.2⟩
  le_succ k := Order.le_succ k.1
  max_of_succ_le {k} h := by
    have hk : IsMax k.1 := Order.max_of_succ_le (show Order.succ k.1 ≤ k.1 from h)
    exact fun b hb => hk (show k.1 ≤ b.1 from hb)
  succ_le_of_lt {a b} h := Order.succ_le_of_lt (a := a.1) (b := b.1) h

theorem iio_noMaxOrder [SuccOrder J] (hj : Order.IsSuccLimit j) : NoMaxOrder (Set.Iio j) :=
  ⟨fun k => ⟨⟨Order.succ k.1, Order.IsSuccLimit.succ_lt hj k.2⟩,
    Order.lt_succ_of_not_isMax (fun hmax => lt_irrefl _ (lt_of_lt_of_le k.2 (hmax k.2.le)))⟩⟩

end Iio

/-- **Limit step.** -/
theorem unitLimit : UnitLimitStatement hι adj := by
  intro J _ _ _ _ I C hI c j hj ih
  letI := iioOrderBot hj
  letI := iioSuccOrder hj
  haveI := iio_noMaxOrder hj
  let φ := Set.principalSegIio j
  let c' : finiteCellular.TransfiniteCompositionOfShape (Set.Iio j) (hI.to (c.F.obj j)) :=
    { F := φ.monotone.functor ⋙ c.F
      isoBot := c.isoBot
      isWellOrderContinuous :=
        inferInstanceAs ((φ : Set.Iio j ≤i J).monotone.functor ⋙ c.F).IsWellOrderContinuous
      incl := (φ.cocone c.F).ι
      isColimit := c.F.isColimitOfIsWellOrderContinuous j hj
      fac := hI.hom_ext _ _
      map_mem := fun k hk => singleCells_le_finiteCellular _ (c.map_mem k.1
        (fun hmax => lt_irrefl _ (lt_of_lt_of_le k.2 (hmax k.2.le)))) }
  exact unitInvertibleOnExtensions_colimit hι adj hI c' (fun k => ih k.1 k.2)

/-- The unit is invertible along single-cell complexes. -/
theorem singleCellUnit : SingleCellUnitStatement hι adj :=
  singleCellUnit_of_limit hι adj (unitLimit hι adj)

include adj in
/-- **The unit at cofibrant objects**, given single-cell presentations of cellular objects. -/
theorem unit_weakEquivalence_of_singleCellPresentation
    (hP : SingleCellPresentationStatement.{u}) (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) :=
  unit_weakEquivalence_of_singleCell hι adj hP (singleCellUnit hι adj) X hX

end HomotopyHypothesis.FiniteCategory.UnitPresentation
