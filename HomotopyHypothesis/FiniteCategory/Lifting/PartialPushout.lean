import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
/-!
# Selected pushouts in the domain of a partial adjoint

Only the pushout of the interpreted span is needed to extend corepresentability across one
pushout. No assertion that every pushout exists in the target category is required.
-/

noncomputable section

universe u v u₁ v₁

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]

/-- The domain of a partial left adjoint is closed under isomorphisms. -/
theorem leftAdjointObjIsDefined_iso (N : X ⥤ C) {A B : C} (e : A ≅ B)
    (hB : N.leftAdjointObjIsDefined B) : N.leftAdjointObjIsDefined A := by
  letI : (N ⋙ coyoneda.obj (op B)).IsCorepresentable := hB
  exact ((N ⋙ coyoneda.obj (op B)).corepresentableBy.ofIso
    (Functor.isoWhiskerLeft N (coyoneda.mapIso e.op))).isCorepresentable

set_option backward.isDefEq.respectTransparency false in
/-- Corepresentability extends across a pushout whose partial-adjoint image span has a pushout. -/
theorem leftAdjointObjIsDefined_pushout (N : X ⥤ C)
    {A B T P : C} (f : A ⟶ B) (g : A ⟶ T) (k : B ⟶ P) (j : T ⟶ P)
    (sq : IsPushout f g k j)
    (hA : N.leftAdjointObjIsDefined A) (hB : N.leftAdjointObjIsDefined B)
    (hT : N.leftAdjointObjIsDefined T)
    (hPush : HasPushout
      (N.partialLeftAdjoint.map (ObjectProperty.homMk f :
        (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩))
      (N.partialLeftAdjoint.map (ObjectProperty.homMk g :
        (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨T, hT⟩))) :
    N.leftAdjointObjIsDefined P := by
  let f' : (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩ := ObjectProperty.homMk f
  let g' : (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨T, hT⟩ := ObjectProperty.homMk g
  let D := span f' g'
  let e := spanCompIso (ObjectProperty.ι N.leftAdjointObjIsDefined) f' g'
  let c : Cocone (D ⋙ ObjectProperty.ι N.leftAdjointObjIsDefined) :=
    (Cocone.precompose e.hom).obj (PushoutCocone.mk k j sq.w)
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv e _).symm sq.isColimit
  let e' := spanCompIso N.partialLeftAdjoint f' g'
  letI : HasPushout (N.partialLeftAdjoint.map f') (N.partialLeftAdjoint.map g') := hPush
  let psq := IsPushout.of_hasPushout (N.partialLeftAdjoint.map f') (N.partialLeftAdjoint.map g')
  let c' : Cocone (D ⋙ N.partialLeftAdjoint) :=
    (Cocone.precompose e'.hom).obj psq.cocone
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv e' _).symm psq.isColimit
  exact (Functor.corepresentableByCompCoyonedaObjOfIsColimit hc hc').isCorepresentable

set_option backward.isDefEq.respectTransparency false in
/-- A partial left adjoint preserves a pushout whose four objects lie in its domain. -/
theorem partialLeftAdjoint_isPushout (N : X ⥤ C)
    {A B T P : C} (f : A ⟶ B) (g : A ⟶ T) (k : B ⟶ P) (j : T ⟶ P)
    (sq : IsPushout f g k j)
    (hA : N.leftAdjointObjIsDefined A) (hB : N.leftAdjointObjIsDefined B)
    (hT : N.leftAdjointObjIsDefined T) (hP : N.leftAdjointObjIsDefined P) :
    IsPushout
      (N.partialLeftAdjoint.map (ObjectProperty.homMk f :
        (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩))
      (N.partialLeftAdjoint.map (ObjectProperty.homMk g :
        (⟨A, hA⟩ : N.PartialLeftAdjointSource) ⟶ ⟨T, hT⟩))
      (N.partialLeftAdjoint.map (ObjectProperty.homMk k :
        (⟨B, hB⟩ : N.PartialLeftAdjointSource) ⟶ ⟨P, hP⟩))
      (N.partialLeftAdjoint.map (ObjectProperty.homMk j :
        (⟨T, hT⟩ : N.PartialLeftAdjointSource) ⟶ ⟨P, hP⟩)) := by
  let A' : N.PartialLeftAdjointSource := ⟨A, hA⟩
  let B' : N.PartialLeftAdjointSource := ⟨B, hB⟩
  let T' : N.PartialLeftAdjointSource := ⟨T, hT⟩
  let P' : N.PartialLeftAdjointSource := ⟨P, hP⟩
  let f' : A' ⟶ B' := ObjectProperty.homMk f
  let g' : A' ⟶ T' := ObjectProperty.homMk g
  let k' : B' ⟶ P' := ObjectProperty.homMk k
  let j' : T' ⟶ P' := ObjectProperty.homMk j
  have sq' : IsPushout f' g' k' j' := IsPushout.of_map_of_faithful
    (ObjectProperty.ι N.leftAdjointObjIsDefined) sq
  let c := PushoutCocone.mk (N.partialLeftAdjoint.map k') (N.partialLeftAdjoint.map j')
    (by rw [← N.partialLeftAdjoint.map_comp, sq'.w, N.partialLeftAdjoint.map_comp])
  have hc : IsColimit c := by
    apply PushoutCocone.isColimitAux' c
    intro s
    let a := N.partialLeftAdjointHomEquiv (X := B') s.inl
    let b := N.partialLeftAdjointHomEquiv (X := T') s.inr
    have hab : f ≫ a = g ≫ b :=
      (N.partialLeftAdjointHomEquiv_map_comp f' s.inl).symm.trans
        ((congrArg (N.partialLeftAdjointHomEquiv (X := A')) s.condition).trans
          (N.partialLeftAdjointHomEquiv_map_comp g' s.inr))
    let q := sq.desc a b hab
    let r := (N.partialLeftAdjointHomEquiv (X := P') (Y := s.pt)).symm q
    refine ⟨r, ?_, ?_, ?_⟩
    · apply (N.partialLeftAdjointHomEquiv (X := B')).injective
      calc
        N.partialLeftAdjointHomEquiv (N.partialLeftAdjoint.map k' ≫ r) =
            k ≫ N.partialLeftAdjointHomEquiv r := N.partialLeftAdjointHomEquiv_map_comp k' r
        _ = k ≫ q := by simp [r]
        _ = a := sq.inl_desc _ _ _
    · apply (N.partialLeftAdjointHomEquiv (X := T')).injective
      calc
        N.partialLeftAdjointHomEquiv (N.partialLeftAdjoint.map j' ≫ r) =
            j ≫ N.partialLeftAdjointHomEquiv r := N.partialLeftAdjointHomEquiv_map_comp j' r
        _ = j ≫ q := by simp [r]
        _ = b := sq.inr_desc _ _ _
    · intro m hm₀ hm₁
      apply (N.partialLeftAdjointHomEquiv (X := P')).injective
      simp only [r, Equiv.apply_symm_apply]
      apply sq.hom_ext
      · exact (N.partialLeftAdjointHomEquiv_map_comp k' m).symm.trans
          ((congrArg (N.partialLeftAdjointHomEquiv (X := B')) hm₀).trans
            (sq.inl_desc a b hab).symm)
      · exact (N.partialLeftAdjointHomEquiv_map_comp j' m).symm.trans
          ((congrArg (N.partialLeftAdjointHomEquiv (X := T')) hm₁).trans
            (sq.inr_desc a b hab).symm)
  exact IsPushout.of_isColimit hc

#print axioms leftAdjointObjIsDefined_pushout
#print axioms partialLeftAdjoint_isPushout

end HomotopyHypothesis.FiniteCategory.Lifting
