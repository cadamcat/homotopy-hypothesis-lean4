import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Geometric realization of semi-simplicial representables

The realization of a representable semi-simplicial set is its standard topological simplex.
-/

universe u

open CategoryTheory Limits
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Boundary

/-- The realization of the representable semi-simplicial set on `[n]` is the standard topological
simplex. -/
noncomputable def realization_stdSimplex_iso (n : ℕ) :
    SemiSSet.realization.{u}.obj
        (SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ≅
      SemiSSet.toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) :=
  (Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1} (SemiSSet.toTop.{u})).app
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)

/-- The realization of any representable semi-simplicial set is its topological simplex. -/
noncomputable def realization_representable_iso (c : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c) ≅ SemiSSet.toTop.{u}.obj c :=
  (Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1} (SemiSSet.toTop.{u})).app c

/-- A colimit of a finite diagram of compact spaces is compact. -/
theorem compactSpace_colimit_of_finite_index {J : Type u} [Category J] [Finite J] [Small.{u} J]
    (F : J ⥤ TopCat.{u}) [HasColimit F] (hF : ∀ j, CompactSpace (F.obj j)) :
    CompactSpace ((colimit F : TopCat.{u})) := by
  classical
  apply isCompact_univ_iff.mp
  have hcol : IsColimit (((forget TopCat)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget TopCat) (colimit.isColimit F)
  have hcover : (⋃ j, Set.range (colimit.ι F j).hom) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol x
    exact ⟨j, y, hy⟩
  rw [← hcover]
  apply isCompact_iUnion
  intro j
  letI := hF j
  exact isCompact_range (colimit.ι F j).hom.continuous

/-- The boundary of a representable has only finitely many semi-simplices. -/
theorem finite_boundary_elements (n : ℕ) :
    Finite ((SemiSSet.boundary.{u} n).toFunctor.Elements) := by
  classical
  let P := (SemiSSet.boundary.{u} n).toFunctor
  have dim_le (e : P.Elements) : (e.obj.unop).obj.len ≤ n := by
    have hm : Mono e.val.val.down.hom := by
      exact e.val.val.down.property
    have hinj := (SimplexCategory.mono_iff_injective).mp hm
    have hcard := Fintype.card_le_of_injective
      (fun i : Fin ((e.obj.unop).obj.len + 1) => e.val.val.down.hom.toOrderHom i) hinj
    have hcard' : (e.obj.unop).obj.len + 1 ≤ n + 1 := by
      simpa [HomotopyHypothesis.Henry.SemiSimplexCategory.mk, Fintype.card_fin] using hcard
    omega
  let padded (e : P.Elements) (i : Fin (n + 1)) : Fin (n + 1) :=
    if h : i.val ≤ (e.obj.unop).obj.len then
      e.val.val.down.hom.toOrderHom ⟨i.val, by omega⟩
    else 0
  let pack (e : P.Elements) : Fin (n + 1) × (Fin (n + 1) → Fin (n + 1)) :=
    (⟨(e.obj.unop).obj.len, Nat.lt_succ_of_le (dim_le e)⟩, padded e)
  apply Finite.of_injective pack
  intro e e' h
  have hdim : (e.obj.unop).obj.len = (e'.obj.unop).obj.len :=
    congrArg Fin.val (congrArg Prod.fst h)
  have hobj : e.obj.unop = e'.obj.unop := by
    apply WideSubcategory.ext
    exact SimplexCategory.ext hdim
  have hobj' : e.obj = e'.obj := congrArg Opposite.op hobj
  have hfun : padded e = padded e' := congrArg Prod.snd h
  have hbase : (e'.obj.unop).obj = (e.obj.unop).obj :=
    congrArg (fun X : HomotopyHypothesis.Henry.SemiSimplexCategory => X.obj)
      (congrArg Opposite.unop hobj'.symm)
  have hbaseEq : congrArg (fun X : HomotopyHypothesis.Henry.SemiSimplexCategory => X.obj)
      (congrArg Opposite.unop hobj'.symm) = hbase := rfl
  have hinc : HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map ((eqToHom hobj').unop) =
      eqToHom hbase := by
    rw [eqToHom_unop, eqToHom_map]
    simpa [HomotopyHypothesis.Henry.SemiSimplexCategory.incl] using congrArg eqToHom hbaseEq
  have hincHom : ((eqToHom hobj').unop).hom = eqToHom hbase := hinc
  have hcomp : (eqToHom hobj').unop ≫ e.val.val.down = e'.val.val.down := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext
    ext i
    simp only [WideSubcategory.comp_def, SimplexCategory.comp_toOrderHom]
    rw [hincHom]
    change (e.val.val.down.hom.toOrderHom ((eqToHom hbase).toOrderHom i)).val =
      (e'.val.val.down.hom.toOrderHom i).val
    have hidx : (SimplexCategory.Hom.toOrderHom (eqToHom hbase)) i =
        ⟨i.val, by omega⟩ := by
      apply Fin.ext
      rw [SimplexCategory.eqToHom_toOrderHom]
      simp
    rw [hidx]
    have hiN : i.val ≤ n := by
      exact le_trans (Nat.le_of_lt_succ i.isLt) (dim_le e')
    have heq := congrFun hfun ⟨i.val, Nat.lt_succ_of_le hiN⟩
    simpa [padded, hdim, Nat.le_of_lt_succ i.isLt] using congrArg Fin.val heq

  apply Functor.Elements.ext e e' hobj'
  apply Subtype.ext
  apply ULift.ext
  change (eqToHom hobj').unop ≫ e.val.val.down = e'.val.val.down
  exact hcomp

/-- The realization of the boundary of a semi-simplicial simplex is compact. -/
theorem compactSpace_realization_boundary (n : ℕ) :
    CompactSpace (SemiSSet.realization.obj (SemiSSet.boundary.{u} n).toFunctor) := by
  classical
  let P := (SemiSSet.boundary.{u} n).toFunctor
  let D := Presheaf.functorToRepresentables P ⋙ SemiSSet.realization.{u}
  have hFinite : Finite P.Elements := finite_boundary_elements n
  letI : Finite P.Elements := hFinite
  letI : Finite P.Elementsᵒᵖ := Finite.of_injective (fun j : P.Elementsᵒᵖ => j.unop) (by
    intro j j' h
    cases j
    cases j'
    cases h
    rfl)
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1} SemiSSet.realization := by
    change PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1}
      (SemiSSet.stdSimplex.leftKanExtension SemiSSet.toTop)
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      (A := SemiSSet.toTop.{u})
  have hCompact : ∀ j : P.Elementsᵒᵖ, CompactSpace (D.obj j) := by
    intro j
    change CompactSpace (SemiSSet.realization.{u}.obj
      (SemiSSet.stdSimplex.{u}.obj ((Functor.Elements.π P).obj j.unop).unop))
    let e := realization_representable_iso ((Functor.Elements.π P).obj j.unop).unop
    exact @Homeomorph.compactSpace _ _ _ _ (by
      change CompactSpace (ULift (Convexity.StdSimplex ℝ
        (Fin (((Functor.Elements.π P).obj j.unop).unop.obj.len + 1))))
      exact Homeomorph.compactSpace Homeomorph.ulift.symm) (TopCat.homeoOfIso e).symm
  let c := SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable P)
  have hc : IsColimit c :=
    isColimitOfPreserves SemiSSet.realization.{u} (Presheaf.colimitOfRepresentable P)
  letI : Small.{u} P.Elementsᵒᵖ := small_self _
  letI : HasColimit D := by dsimp [D]; infer_instance
  let e : c.pt ≅ (colimit D : TopCat.{u}) := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  letI : CompactSpace ((colimit D : TopCat.{u})) := compactSpace_colimit_of_finite_index D hCompact
  change CompactSpace c.pt
  exact @Homeomorph.compactSpace _ _ _ _ inferInstance (TopCat.homeoOfIso e.symm)

end HomotopyHypothesis.Realization.Boundary
