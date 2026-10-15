import HomotopyHypothesis.Blueprint.Defs
/-!
# The fundamental groupoid functor is a right adjoint

For a topological realization `R` of a globular theory `C`, the fundamental
`∞`-groupoid functor `Π_R : Top ⥤ C.Model` is the nerve of the realization
functor `C.Obj ⥤ Top` restricted to models. It is a right adjoint: the nerve
into presheaves is a right adjoint (left Kan extension along the Yoneda
embedding, since spaces are cocomplete), and models form a full subcategory,
so whiskering the left adjoint with the inclusion gives a left adjoint of
`Π_R`.
-/

open CategoryTheory CategoryTheory.Limits Opposite OAI.Grothendieck
open HomotopyHypothesis.Blueprint

namespace HomotopyHypothesis.Realization.Functor

universe u

variable {C : GlobularTheory.{u}} (R : OAIRealization C)

/-- The forgetful inclusion of models into presheaves; the identity on homs. -/
abbrev modelToPresheaf : C.Model ⥤ (C.Objᵒᵖ ⥤ Type u) where
  obj X := X.presheaf
  map f := f

/-- The ULifted nerve of the realization functor. -/
noncomputable abbrev nerveULift : TopCat.{u} ⥤ (C.Objᵒᵖ ⥤ Type u) :=
  CategoryTheory.Presheaf.restrictedULiftYoneda.{u} R.functor

/-- The left Kan extension of the realization functor along the Yoneda embedding. -/
noncomputable abbrev lanL : (C.Objᵒᵖ ⥤ Type u) ⥤ TopCat.{u} :=
  (CategoryTheory.uliftYoneda.{u}).leftKanExtension R.functor

/-- The Kan extension is left adjoint to the ULifted nerve. -/
noncomputable def lanAdj : lanL R ⊣ nerveULift R :=
  CategoryTheory.Presheaf.uliftYonedaAdjunction.{u, u, u, 0, u + 1}
    (C := C.Obj) (ℰ := TopCat.{u}) (A := R.functor)
    (((CategoryTheory.uliftYoneda.{u}).leftKanExtension R.functor))
    ((((CategoryTheory.uliftYoneda.{u}).leftKanExtensionUnit R.functor)))

/-- The ULifted nerve agrees with the plain nerve underlying `Π_R`. -/
noncomputable def nerveIso : nerveULift R ≅ R.Pi ⋙ modelToPresheaf :=
  CategoryTheory.NatIso.ofComponents (fun X =>
    CategoryTheory.NatIso.ofComponents (fun c => (Equiv.ulift).toIso)
      (fun g => by ext x; rfl))
    (fun f => by ext c x; rfl)

/-- The candidate left adjoint of `Π_R`: the inclusion followed by Kan extension. -/
noncomputable abbrev piLeftAdjoint : C.Model ⥤ TopCat.{u} :=
  modelToPresheaf ⋙ lanL R

/-- The candidate is indeed left adjoint to `Π_R`. -/
noncomputable def piAdj : piLeftAdjoint R ⊣ R.Pi :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M X =>
        Equiv.trans ((lanAdj R).homEquiv _ _)
          (Equiv.trans ((CategoryTheory.Iso.refl _).homCongr ((nerveIso R).app X))
            (Equiv.refl _))
      homEquiv_naturality_left_symm := by
        intro M' M X f g
        show ((lanAdj R).homEquiv _ _).symm
            (modelToPresheaf.map f ≫ (g ≫ ((nerveIso R).app X).inv)) =
          (piLeftAdjoint R).map f ≫
            ((lanAdj R).homEquiv _ _).symm (g ≫ ((nerveIso R).app X).inv)
        exact (lanAdj R).homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right := by
        intro M X Y f g
        show (((lanAdj R).homEquiv _ _ (f ≫ g)) ≫ ((nerveIso R).hom.app Y)) =
          (((lanAdj R).homEquiv _ _ f) ≫ ((nerveIso R).hom.app X)) ≫ R.Pi.map g
        rw [(lanAdj R).homEquiv_naturality_right, Category.assoc,
          (nerveIso R).hom.naturality g, ← Category.assoc]
        rfl }

/-- `Π_R` has a left adjoint, the left Kan extension of the realization. -/
theorem pi_isRightAdjoint_proof {C : GlobularTheory.{u}} (R : OAIRealization C) :
    R.Pi.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨piAdj R⟩⟩

example {C : GlobularTheory.{u}} (R : OAIRealization C) :
    R.Pi.IsRightAdjoint :=
  pi_isRightAdjoint_proof R

#print axioms pi_isRightAdjoint_proof

end HomotopyHypothesis.Realization.Functor
