import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular
import HomotopyHypothesis.Completion.FinitelyCellular.Basic
/-
# Free models land in finitely cellular models.

For a globular theory, the free model on a shape (the representable presheaf)
is finitely cellular, and globular sums become pushouts along finite cell maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}}

/-- The free model on a shape, as a model. -/
abbrev FreeShape (S : OAI.Grothendieck.Shape) : C.Model :=
  GlobularTheory.Model.freeShape C S

/-- Maps between free models induced by shape maps. -/
abbrev FreeShapeMap {S T : OAI.Grothendieck.Shape} (f : S ⟶ T) :
    FreeShape (C := C) S ⟶ FreeShape (C := C) T :=
  GlobularTheory.Model.freeShapeMap C f

theorem freeShapeMap_comp {R S T : OAI.Grothendieck.Shape}
    (f : R ⟶ S) (g : S ⟶ T) :
    FreeShapeMap (C := C) (f ≫ g) =
      FreeShapeMap (C := C) f ≫ FreeShapeMap (C := C) g := by
  simp only [FreeShapeMap, GlobularTheory.Model.freeShapeMap, C.toTheoryData.arity.map_comp]
  exact yoneda.map_comp _ _

/-- The square exhibiting `F (S.attach)` as a pushout in models.
    For any model `X`, maps out of it correspond to matching tuples,
    which is exactly the pullback condition of `X.sums`. -/
theorem freeShape_attach_w (S : OAI.Grothendieck.Shape)
    (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    FreeShapeMap (C := C) (S.seam hl) ≫ FreeShapeMap (C := C) (S.inl b h hl hr) =
      FreeShapeMap (C := C) (OAI.Grothendieck.Shape.face hr false) ≫
        FreeShapeMap (C := C) (S.inr b h hl hr) := by
  rw [← freeShapeMap_comp, ← freeShapeMap_comp, OAI.Grothendieck.Shape.seam_inl]

theorem freeShape_attach_isPushout (S : OAI.Grothendieck.Shape)
    (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (FreeShapeMap (C := C) (S.seam hl))
      (FreeShapeMap (C := C) (OAI.Grothendieck.Shape.face hr false))
      (FreeShapeMap (C := C) (S.inl b h hl hr))
      (FreeShapeMap (C := C) (S.inr b h hl hr)) := by
  apply IsPushout.mk'
  · exact freeShape_attach_w S b h hl hr
  · -- Uniqueness: maps out of the pushout vertex are determined by components.
    intro T φ φ' h1 h2
    let φP : NatTrans (yoneda.obj (C.toTheoryData.arity.obj (S.attach b h hl hr))) T.presheaf := φ
    let φP' : NatTrans (yoneda.obj (C.toTheoryData.arity.obj (S.attach b h hl hr))) T.presheaf := φ'
    have h1P : yoneda.map (C.toTheoryData.arity.map (S.inl b h hl hr)) ≫ φP =
        yoneda.map (C.toTheoryData.arity.map (S.inl b h hl hr)) ≫ φP' := h1
    have h2P : yoneda.map (C.toTheoryData.arity.map (S.inr b h hl hr)) ≫ φP =
        yoneda.map (C.toTheoryData.arity.map (S.inr b h hl hr)) ≫ φP' := h2
    -- Yoneda images agree on both projections.
    have e1 : T.presheaf.map (C.toTheoryData.arity.map (S.inl b h hl hr)).op
        (yonedaEquiv φP) =
        T.presheaf.map (C.toTheoryData.arity.map (S.inl b h hl hr)).op
        (yonedaEquiv φP') := by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h1P]
    have e2 : T.presheaf.map (C.toTheoryData.arity.map (S.inr b h hl hr)).op
        (yonedaEquiv φP) =
        T.presheaf.map (C.toTheoryData.arity.map (S.inr b h hl hr)).op
        (yonedaEquiv φP') := by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h2P]
    -- Pullback uniqueness in `Type` gives equality of elements,
    -- via the equiv to the explicit pullback (a subtype of a product).
    have ht : yonedaEquiv φP = yonedaEquiv φP' := by
      have hPb := T.sums S b h hl hr
      let E := PullbackCone.IsLimit.equivPullbackObj hPb.isLimit
      have he : E (yonedaEquiv φP) = E (yonedaEquiv φP') := by
        apply Subtype.ext
        apply Prod.ext
        · exact e1
        · exact e2
      exact E.injective he
    have hPP : φP = φP' := yonedaEquiv.injective ht
    exact hPP
  · -- Existence: matching maps glue via `sumTuple`.
    intro T f g hfg
    let aP : NatTrans (yoneda.obj (C.toTheoryData.arity.obj S)) T.presheaf := f
    let bP : NatTrans (yoneda.obj (C.toTheoryData.arity.obj (Shape.globe h))) T.presheaf := g
    have habP : yoneda.map (C.toTheoryData.arity.map (S.seam hl)) ≫ aP =
        yoneda.map (C.toTheoryData.arity.map (Shape.face hr false)) ≫ bP := hfg
    have w : T.presheaf.map (C.toTheoryData.arity.map (S.seam hl)).op (yonedaEquiv aP) =
        T.presheaf.map (C.toTheoryData.arity.map (Shape.face hr false)).op (yonedaEquiv bP) := by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality, habP]
    let t : T.presheaf.obj (op (C.toTheoryData.arity.obj (S.attach b h hl hr))) :=
      T.sumTuple S b h hl hr (yonedaEquiv aP) (yonedaEquiv bP) w
    refine ⟨(yonedaEquiv.symm t : NatTrans _ _), ?_, ?_⟩
    · show yoneda.map (C.toTheoryData.arity.map (S.inl b h hl hr)) ≫
          yonedaEquiv.symm t = aP
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      exact T.sumTuple_left S b h hl hr _ _ _
    · show yoneda.map (C.toTheoryData.arity.map (S.inr b h hl hr)) ≫
          yonedaEquiv.symm t = bP
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      exact T.sumTuple_right S b h hl hr _ _ _

/-- Every free model on a shape is finitely cellular, by induction on the table. -/
theorem freeShape_mem (S : OAI.Grothendieck.Shape) :
    IsFinitelyCellular C (FreeShape (C := C) S) := by
  obtain ⟨n, T⟩ := S
  induction T with
  | globe n =>
    exact Packages.disk_finitelyCellular C n
  | attach T b h hl hr ih =>
    -- `S = ⟨last, T⟩` here; the attached shape is a pushout along a face.
    show finiteCellMaps C (initial.to (FreeShape (C := C)
      (OAI.Grothendieck.Shape.attach (⟨_, T⟩ : OAI.Grothendieck.Shape) b h hl hr)))
    have hface : finiteCellMaps C
        (FreeShapeMap (C := C) (OAI.Grothendieck.Shape.face hr false)) :=
      face_mem_finiteCellMaps hr false
    have hpush : finiteCellMaps C
        (FreeShapeMap (C := C)
          (OAI.Grothendieck.Shape.inl (⟨_, T⟩ : OAI.Grothendieck.Shape) b h hl hr)) :=
      finiteCellMaps_stable.of_isPushout
        (freeShape_attach_isPushout (⟨_, T⟩ : OAI.Grothendieck.Shape) b h hl hr)
        hface
    have heq : initial.to (FreeShape (C := C)
          (OAI.Grothendieck.Shape.attach (⟨_, T⟩ : OAI.Grothendieck.Shape) b h hl hr)) =
        initial.to (FreeShape (C := C) (⟨_, T⟩ : OAI.Grothendieck.Shape)) ≫
          FreeShapeMap (C := C)
            (OAI.Grothendieck.Shape.inl (⟨_, T⟩ : OAI.Grothendieck.Shape) b h hl hr) := by
      apply Subsingleton.elim
    rw [heq]
    exact MorphismProperty.comp_mem _ _ _ ih hpush

end HomotopyHypothesis.Completion.FinitelyCellular
