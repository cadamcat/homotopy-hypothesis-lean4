import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
universe u

open CategoryTheory Limits Opposite Convexity
open HomotopyHypothesis.Henry
open HomotopyHypothesis.Realization.Boundary

namespace HomotopyHypothesis.Simplicial.CycleRealization

/-- The realized point represented by a semi-simplex and barycentric weights. -/
noncomputable def simplexPoint {P : SemiSSet.{u}} {c : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (a : P.obj (op c)) (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    SemiSSet.realization.{u}.obj P :=
  (SemiSSet.realization.map (uliftYonedaEquiv.symm a)).hom
    ((realization_representable_iso c).inv.hom (ULift.up s))

/-- Restricting a semi-simplex agrees with applying its affine face map to the weights. -/
theorem simplexPoint_naturality {P : SemiSSet.{u}} {c d : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : c ⟶ d) (a : P.obj (op d)) (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    simplexPoint (P.map f.op a) s = simplexPoint a (StdSimplex.map f.hom.toOrderHom s) := by
  have hnat := (Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1}
    (SemiSSet.toTop.{u})).inv.naturality f
  have hpoint :
      (SemiSSet.realization.map (SemiSSet.stdSimplex.map f)).hom
        ((realization_representable_iso c).inv.hom (ULift.up s)) =
      (realization_representable_iso d).inv.hom
        (ULift.up (StdSimplex.map f.hom.toOrderHom s)) := by
    exact (congrArg (fun h => h.hom (ULift.up s)) hnat).symm
  have hleg : uliftYonedaEquiv.symm (P.map f.op a) =
      SemiSSet.stdSimplex.map f ≫ uliftYonedaEquiv.symm a :=
    uliftYonedaEquiv_symm_map f.op a
  dsimp only [simplexPoint]
  rw [hleg, Functor.map_comp]
  change (SemiSSet.realization.map (uliftYonedaEquiv.symm a)).hom
      ((SemiSSet.realization.map (SemiSSet.stdSimplex.map f)).hom
        ((realization_representable_iso c).inv.hom (ULift.up s))) = _
  rw [hpoint]
  rfl

/-- Realization sends a represented point to the point represented by the image semi-simplex. -/
theorem map_simplexPoint {P Q : SemiSSet.{u}} (α : P ⟶ Q)
    {c : HomotopyHypothesis.Henry.SemiSimplexCategory} (a : P.obj (op c))
    (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    (SemiSSet.realization.map α).hom (simplexPoint a s) =
      simplexPoint (α.app _ a) s := by
  change (SemiSSet.realization.map (uliftYonedaEquiv.symm a) ≫
    SemiSSet.realization.map α).hom _ = _
  rw [← Functor.map_comp, uliftYonedaEquiv_symm_comp]
  rfl

/-- Represented points in a representable realize to their affine barycentric images. -/
theorem simplexPoint_representable {c d : HomotopyHypothesis.Henry.SemiSimplexCategory} (f : c ⟶ d)
    (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    (realization_representable_iso d).hom.hom
      (simplexPoint (P := SemiSSet.stdSimplex.{u}.obj d) (ULift.up f) s) =
        ULift.up (StdSimplex.map f.hom.toOrderHom s) := by
  have hleg : uliftYonedaEquiv.symm (ULift.up f) = SemiSSet.stdSimplex.{u}.map f := by
    apply uliftYonedaEquiv.injective
    simp
  have hnat : SemiSSet.realization.map (SemiSSet.stdSimplex.map f) ≫
      (realization_representable_iso d).hom =
      (realization_representable_iso c).hom ≫ SemiSSet.toTop.map f := by
    simpa [realization_representable_iso, SemiSSet.realization] using
      (Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1}
        (SemiSSet.toTop.{u})).hom.naturality f
  dsimp only [simplexPoint]
  rw [hleg]
  change (SemiSSet.realization.map (SemiSSet.stdSimplex.map f) ≫
    (realization_representable_iso d).hom).hom _ = _
  rw [hnat]
  change (SemiSSet.toTop.map f).hom
    ((realization_representable_iso c).hom.hom
      ((realization_representable_iso c).inv.hom (ULift.up s))) = _
  exact congrArg (SemiSSet.toTop.map f).hom
    (Iso.inv_hom_id_apply (realization_representable_iso c) (ULift.up s))

/-- Every realization point is represented by a semi-simplex with barycentric weights. -/
theorem exists_simplexPoint (P : SemiSSet.{u}) (x : SemiSSet.realization.obj P) :
    ∃ (c : HomotopyHypothesis.Henry.SemiSimplexCategory) (a : P.obj (op c))
      (s : StdSimplex ℝ (Fin (c.obj.len + 1))), simplexPoint a s = x := by
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1} SemiSSet.realization :=
    Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      (A := SemiSSet.toTop.{u})
  let coc := SemiSSet.realization.mapCocone (Presheaf.coconeOfRepresentable P)
  have hc : IsColimit coc :=
    isColimitOfPreserves SemiSSet.realization (Presheaf.colimitOfRepresentable P)
  have hforget := isColimitOfPreserves (forget TopCat) hc
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hforget x
  let c := j.unop.obj.unop
  change SemiSSet.realization.obj (SemiSSet.stdSimplex.obj c) at y
  refine ⟨c, j.unop.val, ((realization_representable_iso c).hom.hom y).down, ?_⟩
  have hlift : ULift.up ((realization_representable_iso c).hom.hom y).down =
      (realization_representable_iso c).hom.hom y := by cases (realization_representable_iso c).hom.hom y; rfl
  dsimp only [simplexPoint]
  rw [hlift, Iso.hom_inv_id_apply]
  exact hy

end HomotopyHypothesis.Simplicial.CycleRealization
